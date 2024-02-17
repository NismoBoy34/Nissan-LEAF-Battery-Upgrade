//——————————————————————————————————————————————————————————————————————————————
// Description: 3-bus transparent CAN bridge with Battery upgrade SW for Nissan env200
// Author: Adam Saiyad, Julius Calzada (julius.jai@gmail.com)
// Revision: v1.1.3//added updates for quick charge 70% and battery pairing glitch p3102 error persistent cleared
// Revision: v1.1.4 // Adding of webserver and OTA eeprom saving functions 
// Revision: v1.2.8
// 06.28.2022: Migration to ESP32 Arduino environment
// 10.03.2022: Integrated earlyversion.c, can-bridge-firmware.h & nissan-can-structs.h
// 10.28.2022: Separated LEAF from ENV200
// 10.31.2022: Improved Web Request Processing
// 11.10.2022: Completed dynamic configurations for the following: LEAF_2011, LEAF_2014, E_NV_200, BATTERY_SWAP & BATTERY_SAVER
// 11.11.2022: Created separate cpp files for can_bridge_manager common, leaf and env200
// 11.18.2022: Added CURRENT_CONTROL_ENABLED equivalent to CHARGECURRENT from leaf-can-bridge-3-port-master project
// 11.26.2022: Integrated configurable parameters for: BATTERY_SAVER_ENABLED/DISABLED, GLIDE_IN_DRIVE_ENABLED/DISABLED, CAPACITY_BOOST_ENABLED/DISABLED
// 12.02.2022: Updated CHARGECURRENT implementation for ID0x54B using CurrentControl Web parameters
// 12.04.2022: Merging of Inverter Upgrade based on https://github.com/dalathegreat/Nissan-LEAF-Inverter-Upgrade/blob/main/can-bridge-inverter.c
// 12.06.2022: Updated Charge Current logic - 1) Start conditions are charging state and fan speed; 2) Display kW for 15sec and revert to SOC
// 12.31.2022: Fix charge current functions Fix regen power and motor power Fix Glide and drive add code 
//——————————————————————————————————————————————————————————————————————————————

#include <Arduino.h>
#include "can_bridge_manager_common.h"
#include "can_bridge_manager_env200.h"
#include "can_driver.h"
#include "helper_functions.h"
#include "config.h"

// Available data depending on vehicle configuration (refer config.h)
#if defined(CAN_BRIDGE_FOR_ENV200)
  //General variables
  static volatile	uint16_t	main_battery_soc	= 0; //Declared under other variables
  static volatile uint16_t	GIDS 				= 0; 
  static volatile	uint8_t		charging_state		= 0; //Declared under other variables

  //CAN message templates
  static can_frame_t  instrumentCluster5E3	= {.can_id = 0x5E3, .can_dlc = 5, .data = {0x8E,0x00,0x00,0x00,0x80}};
#endif

//——————————————————————————————————————————————————————————————————————————————
// [ENV200] CAN Bridge Main Handler
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_ENV200
void ENV200_CAN_Bridge_Manager(void){ 
  
	//--- Monitor CAN0 & CAN1 receptions
	#ifdef CAN_CH0_ENABLED
	if(true == CAN0_NewFrameIsAvailable()) {
		#ifdef SERIAL_DEBUG_MONITOR
		Serial.println("CAN0 Message is received");
		#endif //#ifdef SERIAL_DEBUG_MONITOR
    
		CANMessage ch0_rxdata;
		can_frame_t ch0_frame;
		uint16_t ch0_i;
		CAN0_ReadNewFrame(ch0_rxdata);
		ch0_frame.can_id = ch0_rxdata.id;
		ch0_frame.can_dlc = ch0_rxdata.len;
		for(ch0_i=0; ch0_i<ch0_frame.can_dlc; ch0_i++) {
		  ch0_frame.data[ch0_i] = ch0_rxdata.data[ch0_i];
		}
    
		//Call CAN1 event handler
		ENV200_CAN_Handler(CAN_CHANNEL_0, ch0_frame);
	}
	#endif //CAN_CH0_ENABLED


	#ifdef CAN_CH1_ENABLED
	if(true == CAN1_NewFrameIsAvailable()) {
		#ifdef SERIAL_DEBUG_MONITOR
		Serial.println("CAN1 Message is received");
		#endif //#ifdef SERIAL_DEBUG_MONITOR

		CANMessage ch1_rxdata;
		can_frame_t ch1_frame;
		uint16_t ch1_i;
		CAN1_ReadNewFrame(ch1_rxdata);
		ch1_frame.can_id = ch1_rxdata.id;
		ch1_frame.can_dlc = ch1_rxdata.len;
		for(ch1_i=0; ch1_i<ch1_frame.can_dlc; ch1_i++) {
		  ch1_frame.data[ch1_i] = ch1_rxdata.data[ch1_i];
		}

		//Call CAN1 event handler
		ENV200_CAN_Handler(CAN_CHANNEL_1, ch1_frame );
	}
	#endif //CAN_CH1_ENABLED  
}
#endif //#ifdef CAN_BRIDGE_FOR_ENV200

//——————————————————————————————————————————————————————————————————————————————
// [ENV200]CAN handler - evaluates received data, tranlate and transmits to the other CAN bus
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_ENV200
void ENV200_CAN_Handler(uint8_t can_bus, can_frame_t new_rx_frame){	
  
	can_frame_t frame;  
	uint16_t i;
	uint16_t temp; //Temporary variable
  
	memcpy(&frame, &new_rx_frame, sizeof(new_rx_frame));

	//Debugging format
	//if CAN_CHANNEL 0 -> "0|   |..."
	//if CAN_CHANNEL 1 -> "1|   |..."
	//if CAN_CHANNEL 2 -> "2|   |..."
	char strbuf[] = "0|   |                \n"; 
	if(CAN_CHANNEL_1 == can_bus){ strbuf[0] = '1'; }
	if(CAN_CHANNEL_2 == can_bus){ strbuf[0] = '2'; }  

	//Evaluate according to received ID    
	switch(frame.can_id){

		//---Translation for ID 0x1F2
		case 0x1F2: 
			charging_state = frame.data[2];

		//ToDo: Behavior for 0x1F2 must be defined
		// For now, just display the message in debug monitor
		char * str;
		canframe_to_str(str, frame);
		#ifdef SERIAL_DEBUG_MONITOR
		Serial.println(str);
		#endif //#ifdef SERIAL_DEBUG_MONITOR
      
		break;

		//---Translation for ID 0x55B
		case 0x55B: 
			main_battery_soc = (frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6); //Capture SOC% needed for QC_rescaling
			main_battery_soc /= 10; //Remove decimals, 0-100 instead of 0-100.0

			//ToDo: Confirm the use of main_battery_soc. Fixed instrumentCluster5E3 value is to be transmitted
				
			//Upon reading 0x55B coming from battery every 100ms, send missing message towards battery
			//ToDo: Confirm if (CAN0(Rx) -> CAN1(Tx) and vice versa)? or (CAN0(Rx) -> CAN0(Tx) and CAN1(Rx) -> CAN0(Tx))? 
			if(CAN_CHANNEL_0 == can_bus)
			{
				//instrumentCluster5E3  = {.can_id = 0x5E3, .can_dlc = 5, .data = {0x8E,0x00,0x00,0x00,0x80}};
				buffer_send_can0(instrumentCluster5E3);
			}
			else
			{
				//instrumentCluster5E3  = {.can_id = 0x5E3, .can_dlc = 5, .data = {0x8E,0x00,0x00,0x00,0x80}};
				buffer_send_can1(instrumentCluster5E3);
			}

			//Display SOC when 0x55B is received      
			char * str_soc;
			uint32_to_str(str_soc, main_battery_soc);
			#ifdef SERIAL_DEBUG_MONITOR
			Serial.println("[ID 0x55B] Battery SOC(%): ");
			Serial.print(str_soc);
			#endif //#ifdef SERIAL_DEBUG_MONITOR     
		break;

		//---Translation for ID 0x5BC
		case 0x5BC: 
			if((frame.data[5] & 0x10) == 0x00)
			{ //LB_MAXGIDS is 0, store GIDS
				GIDS = ((frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6));
			}
				
			//Avoid blinking GOM by always writing remaining GIDS
			frame.data[0] = GIDS >> 2;
			frame.data[1] = (GIDS << 6) & 0xC0;
			frame.data[5] = frame.data[5] & 0x03; //Clear LB_Output_Power_Limit_Reason and LB_MaxGIDS
		break;

		//--- Translation for ID 0x59E
		case 0x59E:   // QC capacity message
			//Calculate new LBC_QC_CapRemaining value
			temp = ((230 * main_battery_soc)/100); // Crazy advanced math
			frame.data[3] = (frame.data[3] & 0xF0) | ((temp >> 5) & 0xF); // store the new LBC_QC_CapRemaining
			frame.data[4] = ((temp & 0x1F) <<3) | (frame.data[4] & 0x07); // to the 59E message out to vehicle
			calc_crc8(&frame);
		break;
	
		default:
		break;
	}
  
	//--- Gateway all messages except the unwanted IDs
	//ToDo: Unwanted messages must be defined
	uint8_t blocked = 0;
	switch(frame.can_id){
		case 0xABC: //Example on block
			blocked = 1;
		break;
    
		default:
			blocked = 0;
		break;
	}

	//Gateway messages that are not blocked
	if(!blocked) {
		#if defined (CAN_CH0_ENABLED) //Priority 1: CAN Channel 0 with Channel 2
		if(CAN_CHANNEL_0 == can_bus){
			buffer_send_can2(frame);
		}else if(CAN_CHANNEL_2 == can_bus) {
			buffer_send_can0(frame);
		}
		else{
			#ifdef SERIAL_DEBUG_MONITOR
			Serial.println("CAN Channel 1 is not used for gatewaying");
			#endif //#ifdef SERIAL_DEBUG_MONITOR
		}
		
		#elif defined (CAN_CH1_ENABLED) //Priority 2: Channel 1 with Channel 2
		if(CAN_CHANNEL_1 == can_bus){
			buffer_send_can2(frame);
		}else if(CAN_CHANNEL_2 == can_bus) {
			buffer_send_can1(frame);
		}
		else{
			#ifdef SERIAL_DEBUG_MONITOR
			Serial.println("CAN Channel 0 is not used for gatewaying");
			#endif //#ifdef SERIAL_DEBUG_MONITOR
		}
		
		#else
			#error "CAN 0 or CAN 1 must be paired with CAN 2 for Gatewaying."
		#endif		
	}
	//--- End of Messages Gateway
			
	//Post processing for debugging
	SID_to_str(strbuf + 2, frame.can_id);
	canframe_to_str(strbuf + 6, frame);
	#ifdef SERIAL_DEBUG_MONITOR
	Serial.println(strbuf);
	#endif //#ifdef SERIAL_DEBUG_MONITOR
}
#endif// CAN_BRIDGE_FOR_ENV200
