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
#include "can_bridge_manager_leaf.h"
#include "can_bridge_manager_leaf_inverter_upgrade.h"
#include "can_driver.h"
#include "helper_functions.h"
#include "config.h"

#if defined(CAN_BRIDGE_FOR_LEAF)
  static volatile  uint8_t   repeat_can        = 1;  //repeat CAN1 to CAN2 and vice versa (transparent bridge mode)
#endif

//---Start of earlyversion.c

static uint8_t  qc_speed_gen4[13] = {50, 60, 70,90,125,125,125,105,100, 90, 80, 70, 50};  //Speed in Amps
//actual temp        -15 -12 -9 -6  -3  10  23  36  40   42  45  47  50
//bars             0   1    2  3   4   5   6   7   8   9   10  11  12

/* variables for battery swap */
static uint8_t		swap_1dc_byte4[5]		= {0x01, 0x01, 0x00, 0x00, 0x0C}; 
static uint8_t		swap_1dc_byte5[5]		= {0x0C, 0xD8, 0xC0, 0xCC, 0xFF};
static uint8_t		swap_1dc_byte6[5]		= {0xD9, 0xC6, 0xC7, 0xDC, 0xFC};

//Lookup table temperature ZE0,	offset       -40	0   1   2   3   4   5   6   7   8   9   10  11  12
static uint8_t		temp_lut[13]						 = {25, 28, 31, 34, 37, 50, 63, 76, 80, 82, 85, 87, 90};

//quick charging variables
static volatile	uint8_t		SOC_stopcharging		    = 99; //At what SOC should the charge be aborted
static volatile	uint8_t		end_of_charge			      = 0;
static volatile	uint8_t		charging_state			    = 0;
static volatile	uint8_t		prev_charging_state     = 0;
static volatile	uint8_t		starting_up				      = 0;
static volatile	uint8_t		qc_fix_active			      = 0;
static volatile	uint16_t	qc_current				      = 0x9c4;
static volatile uint16_t  qc_power                = 0x9c4; //in 0.1kW increments, offset -100
static volatile	uint16_t	sc_current				      = 320; //in 0.1kW increments, offset -100
static volatile	uint8_t		sc_skips				        = 50;

//other variables
static volatile	uint8_t		can_busy				        = 0;
static volatile	uint16_t	main_battery_soc		    = 0; //Needed to make dash SOC work on 2014+ and for usb output

static volatile	uint8_t		swap_idx				        = 0;
static volatile	uint8_t		swap_5c0_idx			      = 0;
static volatile	uint16_t	startup_counter			    = 0; //counts number of 10ms frames since startup
static volatile	uint16_t	shutdown_counter		    = 0;
static volatile	uint8_t		VCM_WakeUpSleepCommand	= 0;
static volatile	uint8_t		CANMASK					        = 0;
static volatile	uint8_t		ALU_question			      = 0;
static volatile	uint8_t		cmr_idx					        = QUICK_CHARGE;

//#ifdef LEAF_2011
static volatile	uint8_t		skip_5bc				        = 1; //for 2011 battery swap, skip 4 messages
static volatile	uint8_t		alternate_5bc			      = 0; //for 2011 battery swap
static volatile	uint16_t	total_capacity_wh		    = 0;//for 2011 battery swap
static volatile	uint16_t	current_capacity_wh		  = 0;//for 2011 battery swap
//#endif //#ifdef LEAF_2011

static volatile	uint8_t		seen_1da				        = 0;//for 2011 battery swap TODO, add more to ifdef to save memory
static volatile	uint16_t	current_capacity_gids	  = 0;//for 2011 battery swap TODO, define as u8? to save memory
static volatile	uint8_t		main_battery_temp		    = 0;//for 2011 battery swap
static volatile	uint8_t		msg_1d4_byte6			      = 0;
static volatile	uint8_t		user_chargestop			    = 0; //tries to fix FULLCAP limit on gen1 Leafs, also used for debug prints

static volatile	uint32_t	pack_voltage			      = 0;
static volatile	int16_t		motor_amps				      = 0;
static volatile	uint8_t		parked					        = 1; //fix for ready off error/charge off error: set bat current to zero when 11a[0] high nibble is 0
static volatile	uint8_t		shifter_state			      = 0;
static volatile	uint16_t	main_cell_voltages[97];
static volatile	uint16_t	main_min_max_voltage[2];		//for now, just contains min/max
static volatile	uint8_t		battery_request_idx		  = 0;
			can_frame_t battery_voltage_request   = {.can_id = 0x79B, .can_dlc = 8, .data = {2,0x21,2,0,0,0,0,0}}; //Emulates a Leafspy request for voltages
			can_frame_t battery_next_line_request = {.can_id = 0x79B, .can_dlc = 8, .data = {0x30, 1, 0, 0xff, 0xff, 0xff, 0xff, 0xff}};
static volatile	uint8_t		battery_can_bus			    = 2;	//keeps track on which CAN bus the battery talks
static volatile	uint16_t	i						            = 0; //for the 96 voltage pairs TODO, define as u8 to save mem
static volatile	uint8_t		alternate_7bb			      = 1;
static volatile	uint8_t		ignore_7bb				      = 0;
static volatile	uint8_t		dont_query_battery		  = 0;

//timer variables
static volatile	uint8_t		ten_sec_timer		        = 1;	//increments on every sec_timer underflow
static volatile	uint16_t	sec_timer			          = 1;	//actually the same as ms_timer but counts down from 1000
static volatile	uint8_t		sec_interrupt		        = 0;	//signals main loop to output debug data every second

#ifdef BATTERY_SAVER //Defines for BatterySaver
#define FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX 50
static volatile	uint16_t	ChargeSetModeCounter 	= 0;
static volatile	uint8_t 	timeToSetCapacityDisplay = 0;
static volatile	uint8_t		SetCapacityDisplay 		= 0;
#endif //#ifdef BATTERY_SAVER

//bits															                        10					        10					        4				      8				          7			      1				      3	(2 space)		      1					        5						          13
static volatile	Leaf_2011_5BC_message swap_5bc_remaining	= {.LB_CAPR = 0x12C, .LB_FULLCAP = 0x32, .LB_CAPSEG = 0, .LB_AVET = 50, .LB_SOH = 99, .LB_CAPSW = 0, .LB_RLIMIT = 0, .LB_CAPBALCOMP = 1, .LB_RCHGTCON = 0b01001, .LB_RCHGTIM = 0};
static volatile	Leaf_2011_5BC_message swap_5bc_full			  = {.LB_CAPR = 0x12C, .LB_FULLCAP = 0x32, .LB_CAPSEG = 12, .LB_AVET = 50, .LB_SOH = 99, .LB_CAPSW = 1, .LB_RLIMIT = 0, .LB_CAPBALCOMP = 1, .LB_RCHGTCON = 0b01001, .LB_RCHGTIM = 0};
static volatile	Leaf_2011_5BC_message leaf_40kwh_5bc;
static volatile	Leaf_2011_5C0_message swap_5c0_max			  = {.LB_HIS_DATA_SW = 1, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 66, .LB_HIS_TEMP = 66, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x39, .LB_DTC = 0};
static volatile	Leaf_2011_5C0_message swap_5c0_avg			  = {.LB_HIS_DATA_SW = 2, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 64, .LB_HIS_TEMP = 64, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x28, .LB_DTC = 0};
static volatile	Leaf_2011_5C0_message swap_5c0_min			  = {.LB_HIS_DATA_SW = 3, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 64, .LB_HIS_TEMP = 64, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x15, .LB_DTC = 0};
static volatile	Leaf_2011_state state;
static volatile	can_frame_t		saved_5bc_frame				      = {.can_id = 0x5BC, .can_dlc = 8};
	
//battery swap fixes?
static volatile	can_frame_t		swap_390_message  = {.can_id = 0x355, .can_dlc = 8, .data = {4,0,1,0,0,0,0x3C,0}};
static volatile	car_state		whats_happening		  = {.run_state = CAR_OFF, .HV_bus_voltage = 300};
			static can_frame_t		swap_605_message	  = {.can_id = 0x605, .can_dlc = 1, .data = {0}};
			static can_frame_t		swap_679_message	  = {.can_id = 0x679, .can_dlc = 1, .data = {0}};
			static can_frame_t		swap_607_message	  = {.can_id = 0x607, .can_dlc = 1, .data = {0}};

//---End of earlyversion.c

// leaf-can-bridge-3-port-master

static volatile  uint8_t   current_11A_shifter_state   = 0;
#ifdef GLIDE_IN_DRIVE_ENABLED()
#define FADE_OUT_CAP_AFTER_SETTING_REGEN 20
volatile  uint8_t   previous_11A_shifter_state    = 0;
volatile  uint8_t   disable_regen_toggle      = 0;
volatile  uint8_t   eco_active            = 0;
#endif

static volatile  car_state   vehicle_state   = {.run_state = CAR_OFF, .HV_bus_voltage = 300};
static volatile  uint8_t   end_of_charge_but_not_full = 0;

#ifdef CHARGECURRENT
//variables used for ChargeCurrent
static volatile  uint16_t  CurrentSetModeCounter = 0;
static volatile  uint16_t  max_current = 320; //in 0.1kW increments, offset -10 // Max power that battery can be charged with, we use this variable as override
static volatile  uint16_t  battery_current_demand = 0; //the charge max signal that battery is requesting right now (LB_MAX_POWER_FOR_CHARGER)
static volatile  uint8_t   SetPercentageDisplay = 0;
static volatile  uint8_t   takeoverSOCdisplay = 0;
#endif

#ifdef RAPIDGATEDODGER
static volatile  uint8_t   QC35kWlimiter = 0;
static volatile  uint8_t   QC25kWlimiter = 0;
#endif

static uint8_t  qc_speed[13];

/* Quick-charging defines */
#define MIN_QC_POWER 40      //in 0.025kW steps, so 40=1kW
#define MAX_VOLTAGE_QC 396    //max voltage for quick charging
#define QC_HYSTERESIS 6     //in 0.5V steps, so 6=3V

//--- End of leaf-can-bridge-3-port-master

static uint16_t MAX_CELL_VOLTAGE = 4130; //default = CAPACITY_BOOST_DISABLED

static bool startChargeCurrentDisplay = false;
static uint8_t previous_charging_state;
static uint8_t previous_FanSpeed;

void LEAF_CAN_Bridge_Manager_Init(void)
{
  //--------------------------------------
  // Battery Selection
  //--------------------------------------
  //#define BATTERY_24KWH()       (Battery_Selection == Battery_Selection_24Kwh)
  //#define BATTERY_30KWH()       (Battery_Selection == Battery_Selection_30Kw)
  //#define BATTERY_40KWH()       (Battery_Selection == Battery_Selection_40Kwh)
  //#define BATTERY_62KWH()       (Battery_Selection == Battery_Selection_62Kwh)
  //#define BATTERY_BRUTE_FORCE() (Battery_Selection == Battery_Selection_BruteForce_30KWh_24KWH_LBC) // Is this referring to BATTERY_SWAP???
 
  //#ifdef BATTERY_24KWH
  if( BATTERY_24KWH() )
  {
    //qc_speed[13] = {15, 20, 30,50,125,125,125,105,100, 90, 80, 60, 30};  //Speed in Amps
    qc_speed[0] = 15;  qc_speed[1] = 20;  qc_speed[2] = 30; qc_speed[3] = 50;  qc_speed[4] = 125; qc_speed[5] = 125; qc_speed[6] = 125; 
    qc_speed[7] = 105; qc_speed[8] = 100; qc_speed[9] = 90; qc_speed[10] = 80; qc_speed[11] = 60; qc_speed[12] = 30;
  }
  //#endif
  
  //#ifdef BATTERY_30KWH
  if( BATTERY_30KWH() )
  {
    //qc_speed[13] = {15, 30, 40,60,125,125,125,105,100, 90, 80, 60, 30};  //Speed in Amps
    qc_speed[0] = 15;  qc_speed[1] = 30;  qc_speed[2] = 40; qc_speed[3] = 60;  qc_speed[4] = 125; qc_speed[5] = 125; qc_speed[6] = 125; 
    qc_speed[7] = 105; qc_speed[8] = 100; qc_speed[9] = 90; qc_speed[10] = 80; qc_speed[11] = 60; qc_speed[12] = 30;    
  }
  //#endif

  //#ifdef BATTERY_40KWH
  if( BATTERY_40KWH() )
  {
    //qc_speed[13] = {15, 30, 60,80,125,125,125,105,100, 90, 80, 60, 30};  //Speed in Amps
    qc_speed[0] = 15;  qc_speed[1] = 30;  qc_speed[2] = 60; qc_speed[3] = 80;  qc_speed[4] = 125; qc_speed[5] = 125; qc_speed[6] = 125; 
    qc_speed[7] = 105; qc_speed[8] = 100; qc_speed[9] = 90; qc_speed[10] = 80; qc_speed[11] = 60; qc_speed[12] = 30;
  }
  //#endif
  
  //#ifdef BATTERY_62KWH
  if( BATTERY_62KWH() )
  {
    //qc_speed[13] = {15, 30, 70,90,125,125,125,105,100, 90, 80, 60, 30};  //Speed in Amps
    qc_speed[0] = 15;  qc_speed[1] = 30;  qc_speed[2] = 70; qc_speed[3] = 90;  qc_speed[4] = 125; qc_speed[5] = 125; qc_speed[6] = 125; 
    qc_speed[7] = 105; qc_speed[8] = 100; qc_speed[9] = 90; qc_speed[10] = 80; qc_speed[11] = 60; qc_speed[12] = 30;
  }

  // Charge timer minutes lookup values
//#ifdef BATTERY_24KWH
if( BATTERY_24KWH() )
#define time_100_with_200V_in_minutes 430
#define time_80_with_200V_in_minutes 340
#define time_100_with_100V_in_minutes 700
#define time_80_with_100V_in_minutes 560
#define time_100_with_QC_in_minutes 60
#define time_80_with_66kW_in_minutes 150
#define time_100_with_66kW_in_minutes 190
//#endif

//#ifdef BATTERY_30KWH
if( BATTERY_30KWH() )
#define time_100_with_200V_in_minutes 600
#define time_80_with_200V_in_minutes 480
#define time_100_with_100V_in_minutes 900
#define time_80_with_100V_in_minutes 720
#define time_100_with_QC_in_minutes 60
#define time_80_with_66kW_in_minutes 200
#define time_100_with_66kW_in_minutes 245
//#endif

//#ifdef BATTERY_40KWH
if( BATTERY_40KWH() )
#define time_100_with_200V_in_minutes 730
#define time_80_with_200V_in_minutes 580
#define time_100_with_100V_in_minutes 800  //Actually 1230 at 0% and 0 at 100% //Correct values?
#define time_80_with_100V_in_minutes 640  //Actually 792 at 0% and 0 at 80% //Correct values?
#define time_100_with_QC_in_minutes 80
#define time_80_with_66kW_in_minutes 270
#define time_100_with_66kW_in_minutes 335
//#endif

//#ifdef BATTERY_62KWH
if( BATTERY_62KWH() )
#define time_100_with_200V_in_minutes 1130
#define time_80_with_200V_in_minutes 900
#define time_100_with_100V_in_minutes 2000
#define time_80_with_100V_in_minutes 1600
#define time_100_with_QC_in_minutes 80
#define time_80_with_66kW_in_minutes 430
#define time_100_with_66kW_in_minutes 535
//#endif
  //#endif

  //#define MAX_CELL_VOLTAGE 4200
  if( CAPACITY_BOOST_ENABLED() )
  {
     MAX_CELL_VOLTAGE = 4200;
  }
  else // CAPACITY_BOOST_DISABLED
  {
    MAX_CELL_VOLTAGE = 4130;
  }
}

//——————————————————————————————————————————————————————————————————————————————
// [LEAF] CAN Bridge Main Handler
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_LEAF
void LEAF_CAN_Bridge_Manager(void){
Serial.println("canbridgeleaftest1");
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
    
    //Call CAN0 event handler
    if( INVERTER_UPGRADE_ENABLED() )
    {
      LEAF_CAN_Handler_Inverter_Upgrade(CAN_CHANNEL_0, ch0_frame);
    }
    else
    {
      LEAF_CAN_Handler(CAN_CHANNEL_0, ch0_frame);
    }
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
    if( INVERTER_UPGRADE_ENABLED() )
    {
      LEAF_CAN_Handler_Inverter_Upgrade(CAN_CHANNEL_1, ch1_frame );  
    }
    else
    {
      LEAF_CAN_Handler(CAN_CHANNEL_1, ch1_frame );
    }
  }
  #endif //CAN_CH1_ENABLED  

}
#endif //#ifdef CAN_BRIDGE_FOR_LEAF

//——————————————————————————————————————————————————————————————————————————————
// [LEAF] CAN handler - evaluates received data, tranlate and transmits to the other CAN bus
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_LEAF
void LEAF_CAN_Handler(uint8_t can_bus, can_frame_t new_rx_frame){  
//  print("test2"\n,24);
	can_frame_t frame;
	uint16_t temp_amps;
  
	//---Start of earlyversion.c
	//#ifdef LEAF_2011
	uint16_t capacity_80 = (total_capacity_wh / 10) * 8; //for 2011
	//#endif //#ifdef LEAF_2011
  
	uint16_t temp2; //Temporary variable used in many functions	
  
	//#ifdef BATTERY_SAVER
	uint8_t FanSpeed = 0;
	uint8_t VentModeStatus = 0;
	uint8_t mux_5bc_CapacityCharge = 0;
	//#endif //#ifdef BATTERY_SAVER
	//---End of earlyversion.c

	memcpy(&frame, &new_rx_frame, sizeof(new_rx_frame));

	//Debugging format
	//if CAN_CHANNEL 0 -> "0|   |..."
	//if CAN_CHANNEL 1 -> "1|   |..."
	//if CAN_CHANNEL 2 -> "2|   |..."
	char strbuf[] = "0|   |                \n"; 
	if(CAN_CHANNEL_1 == can_bus){ strbuf[0] = '1'; }
	if(CAN_CHANNEL_2 == can_bus){ strbuf[0] = '2'; }

	//Evaluate according to received ID
	#ifdef LEAF_TRANSLATION_ENABLED    
	switch(frame.can_id){

    //---Translation for ID 0x1DC
    //case 0x1DC:  //when we see a CAN message with id 0x1DC....
    //  frame.data[0] = 0xFF; //change byte 0 to 0xFF
    //  frame.data[1] = 0xFF; //etc. ....
    //  frame.data[2] = 0xFF;
    //  frame.data[3] = 0xFF;
    //  frame.data[4] = 0x1F; //let's do 0x1F here, just for shits and giggles
    //  frame.data[5] = 0xFF;
    //  frame.data[6] = 0xFC; //I feel like making byte 6 0xFC today                
    //  calc_crc8(&frame);    //this routine calculates the CRC using radix 0x85 and puts that CRC in frame.data[7]
    //  break;
	  
	//---Start of earlyversion.c
	
	case 0x1D4:
		if((charging_state == CHARGING_SLOW) || (charging_state == CHARGING_QUICK)){
			if(frame.data[6] == 0x60 && msg_1d4_byte6 == 0xE0){
				user_chargestop = 1;
				#ifdef USB_SERIAL
				print("User interrupted charge\n",24);
				#endif
			}
		}
	break;
	
	case 0x1DA:
		temp_amps = ((frame.data[2] & 0x07) << 8) + frame.data[3];						//extract motor current from frame data
		if(temp_amps > 1024){ motor_amps = (int16_t) -2048 + (int16_t) temp_amps;}		//convert from twos complement to native signed
		else{ motor_amps = (int16_t) temp_amps;}										//
		motor_amps = -motor_amps / 4;													//scale. //motor_amps is used for charge error off fix on ZE0
				
		seen_1da = 10;	//this variable is used to make the motor controller happy on shutdown
	break;
	
	case 0x1DB:
    battery_can_bus = can_bus; // Guarantees that voltage request go to right bus. Without this there is a risk that the Leafspy requests get sent to VCM instead of HVBAT
    pack_voltage = (frame.data[2] << 2) | ((frame.data[3] & 0xC0) >> 6);      //the pack voltage is in bytes 2 and 3[6-7], in units of 0.5V/LSB
    vehicle_state.HV_bus_voltage = pack_voltage / 2;                //store in our car state variable
        
    if(frame.data[2] == 0xFF){
      starting_up |= 1;
    } else {
      starting_up &= ~1;
    }
      
    //#ifdef BATTERY_SWAP
    if(BATTERY_SWAP_ENABLED())
    {
      //#ifdef LEAF_2011
      if( NISSAN_ZE0_2011_2012() )
      {
        //seems like we just need to clear any faults and show permission
        if(VCM_WakeUpSleepCommand == 3){ //VCM command: wakeup
          frame.data[3] = (frame.data[3] & 0xC0) | 0x2A; //FRLYON=1, INTERLOCK=1, POUT=normal limit
        }
            
        //#ifdef BATTERY_SAVER
        if(BATTERY_SAVER_ENABLED())
        {
          if(!starting_up){
            if((charging_state == CHARGING_SLOW) && (main_battery_soc >= SOC_stopcharging)){ //custom line for batterysaver
              end_of_charge_but_not_full = 1;
              #ifdef USB_SERIAL
              print("BatterySaver limit reached: charge stopped\n",43);
              #endif
            }
          }
        }
        //#endif //#ifdef BATTERY_SAVER
            
        if((charging_state == CHARGING_SLOW) && (pack_voltage > (MAX_VOLTAGE*2+4))){
          end_of_charge = 1;
          #ifdef USB_SERIAL
          print("Pack overvoltage: charge stopped\n",33);
          #endif
        }
            
        if(!starting_up){
          if(main_battery_soc > vehicle_state.max_charge_percentage)//The 80 / 100% option on older LEAF
          {
            if (vehicle_state.max_charge_percentage == 80){
              end_of_charge_but_not_full = 1; 
            }
            else{
              end_of_charge = 1;
            }
                
            #ifdef USB_SERIAL
            print("Programmed end of charge\n",25);
            #endif
          }
        }    
          
        frame.data[1] = frame.data[1] & 0xE0; //blank any error flags
        frame.data[4] = 0;            //unused in 2011 Leaf (usable SOC in 2013+)
        frame.data[5] = 0;            //unused in 2011 Leaf (also blank in 2013+)
        frame.data[6] = frame.data[6] & 0x03; //blank this as well (unused in 2013+)
          
        if(end_of_charge){
          frame.data[1] = (frame.data[1] & 0xE0) | 2; //request charging stop
          frame.data[3] = (frame.data[3] & 0xEF) | 0x10; //full charge completed
          sc_current = 133;               //reset slow charge current, 133 = 3.3kW ((133*0.1)-10= 3.3kW)
          qc_power = 1250;                //reset QC current
        }
            
        if(end_of_charge_but_not_full){ //Used on 2011 Leaf to not confuse chargebars
          frame.data[1] = (frame.data[1] & 0xE0) | 2; //request charging stop
          sc_current = 133;               //reset slow charge current, 133 = 3.3kW ((133*0.1)-10= 3.3kW)
          qc_power = 1250;                //reset QC current
        }
      }    
      //#endif //#ifdef LEAF_2011
      
      //#ifdef LEAF_2014
      if( NISSAN_AZE0_2013_2017() )
      {
        //slightly different, this one has usable SOC on byte 4[6:0]
        if(VCM_WakeUpSleepCommand == 3){ //VCM command: wakeup
          frame.data[3] = (frame.data[3] & 0xC0) | 0x2A; //FRLYON=1, INTERLOCK=1, POUT=normal limit
        }
        
        //#ifdef BATTERY_SAVER
        if(BATTERY_SAVER_ENABLED())
        {
          if(!starting_up){
            if((charging_state == CHARGING_SLOW) && (main_battery_soc >= SOC_stopcharging)){ //custom line for BatterySaver 
              end_of_charge = 1;
              #ifdef USB_SERIAL
              print("BatterySaver limit reached: charge stopped\n",43);
              #endif
            }
          }
        }
        //#endif //#ifdef BATTERY_SAVER
            
        if((charging_state == CHARGING_SLOW) && (pack_voltage > (MAX_VOLTAGE*2))){
          end_of_charge = 1;
          #ifdef USB_SERIAL
          print("Pack overvoltage: charge stopped\n",33);
          #endif
        }
                      
        frame.data[1] = frame.data[1] & 0xE0; //blank errors and request charging stop
        frame.data[4] = main_battery_soc;   //usable SOC reflects actual SOC
        frame.data[5] = 0;            //blank
        frame.data[6] = frame.data[6] & 0x03; //blank 7:2        
            
        if(end_of_charge){
          frame.data[1] = (frame.data[1] & 0xE0) | 2; //request charging stop
          frame.data[3] = (frame.data[3] & 0xEF) | 0x10; //full charge completed
          sc_current = 133;               //reset slow charge current
          qc_power = 1250;                //reset QC current
        }    
        //#endif //#ifdef LEAF_2014
      }
    }
    //#endif #ifdef BATTERY_SWAP

    //#ifdef BATTERY_SAVER
    if( BATTERY_SAVER_ENABLED() )
    {
      if (timeToSetCapacityDisplay > 0) //Visualize the max-charge also with SOC display whilst the user is setting it
      {
        frame.data[4] = (SOC_stopcharging-1);
      }
    }
    //#endif
    
    //#ifdef CHARGECURRENT
    if(CURRENT_CONTROL_ENABLED())
    {
      if (takeoverSOCdisplay > 0) //visualize kW setting with SOC display
      {
        frame.data[4] = SetPercentageDisplay;
      }
    }                
    //#endif
      
    calc_crc8(&frame);
  break;
	
	case 0x68C:
	case 0x603:
		startup_counter = 0; //car starting
		end_of_charge = 0;
		user_chargestop = 0;
		#ifdef USB_SERIAL
		print("Vehicle is waking up\n",21);
		#endif
	break;
	
  case 0x1DC:
    if(frame.data[0] == 0xFF){
      starting_up |= 2;
    } else {
      starting_up &= ~2;
    }
      
    //#ifdef BATTERY_SWAP //This ifdef writes the battery ID
    if( BATTERY_SWAP_ENABLED() )
    {    
      if(startup_counter == 0){
        frame.data[0] = 0xFF;
        frame.data[1] = 0xFF;
        frame.data[2] = 0xFF;
        frame.data[3] = 0xFF;
        frame.data[4] = 0x1F;
        frame.data[5] = 0xFF;
        frame.data[6] = 0xFC;
      } else if(startup_counter < 7){
        frame.data[0] = 0xFF;
        frame.data[1] = 0xFF;
        frame.data[2] = 0xFF;
        frame.data[3] = 0xFF;
      } else {
        frame.data[0] = 0xB4; //max power 180kW v3.09 test
        frame.data[1] = 0x3F; //max regen
          
        if((charging_state != CHARGING_SLOW) && (charging_state != CHARGING_QUICK)){
          frame.data[2] = 0x8F; 
          frame.data[3] = 0xFD;
        } else { //We are charging
          frame.data[2] = 0x83; //upper nibble is regen, lower is LB_BPCMAX (max power for charger), max=0x3E8
          frame.data[3] = 0xE9; //upper 6 bits is LB_BPCMAX, lower is charge power status, 01=normal
        }
      }
        
      if((charging_state == CHARGING_SLOW) || (charging_state == CHARGING_QUICK))
      { //Set BPURATE to max to allow chademo to ramp to target instantly
        frame.data[4] = (frame.data[4] & 0x1F) | 7 << 5;
      }
    }    
    //#endif //#ifdef BATTERY_SWAP

    if(!starting_up){
      if(charging_state == CHARGING_QUICK)
      {        
        //Determine maximum QC power
        vehicle_state.max_QC_power = qc_speed[vehicle_state.HV_bat_temperature_bars]; //limit based on temperature
        vehicle_state.max_QC_power *= 20;
            
        //Ramp to target
        if(pack_voltage > 2*MAX_VOLTAGE_QC) //if battery is over 396V
        {
          if(qc_power > MIN_QC_POWER)
          {
            qc_power--; //reduce power
          }
        }
      
        if(pack_voltage < (2*MAX_VOLTAGE_QC-QC_HYSTERESIS)) //if battery is under 393V
        { 
          if(qc_power < vehicle_state.max_QC_power)
          {
            qc_power++; //increase power 
          }
        }
            
        //Limit if needed
        if(qc_power > vehicle_state.max_QC_power) qc_power = vehicle_state.max_QC_power; //Current has gone above max
        if(qc_power <= MIN_QC_POWER) qc_power = 0; //Current has dropped below minimum level, zero it!
            
        #ifdef RAPIDGATEDODGER
        if (QC25kWlimiter) //We want 25kW max
        {
          temp2 = 70; //70A
          temp2 *= 20;
          if(qc_power > temp2)
          {
            qc_power = temp2;
          }
        }
        else if(QC35kWlimiter) //We want 35kW max
        {
          temp2 = 90; //90A
          temp2 *= 20;
          if(qc_power > temp2)
          {
            qc_power = temp2; 
          }   
        }
        else
        {
          //No rapidgatedodger active
        }
        #endif
            
        //Stop if needed
        if(main_battery_soc > 95) end_of_charge = 1; //Always stop Chademo if SOC goes over 95%
        if(end_of_charge) qc_power = 0;
            
        frame.data[2] = (frame.data[2] & 0xF0) | ((qc_power >> 8) & 0xF);
        frame.data[3] = (uint8_t) (qc_power & 0xFF);
      }
      else if (charging_state == CHARGING_SLOW)
      {            
        //#ifdef BATTERY_SWAP
        if( BATTERY_SWAP_ENABLED() )
        {    
          sc_skips--;
          if(!sc_skips){
            if(main_min_max_voltage[1] > MAX_CELL_VOLTAGE){ if(sc_current > 102) sc_current--; }//reduce current when we hit the max pack voltage
            if(main_min_max_voltage[1] < (MAX_CELL_VOLTAGE-5)){ if(sc_current < 320) sc_current++; }//increase when we hit 1v below max pack
            if(sc_current <= 104)
            {
              end_of_charge = 1; //end charge when 300W or less is being delivered by the charger
              #ifdef USB_SERIAL
              print("Current reduced: charge stopped gracefully\n",43);
              #endif
            }
            
            if(sc_current > 102){sc_skips = 250;} //6kW/min
            if(sc_current > 133){sc_skips = 150;} //10kW/min
            if(sc_current > 166){sc_skips = 100;} //0.1kW/s
            if(sc_current > 200){sc_skips = 50;}  //skew rate of approx. 0.2kW/s (30kW/min)
          }
            
          frame.data[2] = (frame.data[2] & 0xF0) | (sc_current >> 6);
          frame.data[3] = (sc_current << 2) | 3;

        //    #else            
        //    #endif //#ifdef BATTERY_SWAP
        }
      } 
      else 
      { //No charging ongoing, limit battery parameters
      
        //#ifdef BATTERY_SWAP
        if( BATTERY_SWAP_ENABLED() )
        { 
          /* REGENERATIVE BRAKING TUNING */
          // Determine the max allowed amount of regen based on voltage
          if(vehicle_state.HV_bus_voltage <= 385){
            frame.data[1] = 0x0f; //max regen 60kW
          } else if(vehicle_state.HV_bus_voltage > 400){
            frame.data[1] = 0x00; //no regen
          } else {
            frame.data[1] = (400 - vehicle_state.HV_bus_voltage); //Regen goes from 0-f at 1V/bit from 385-400V
          }
          
          vehicle_state.regen = frame.data[1]; //Store actual amount of allowed regen in struct
            
          // Determine if regen needs to be limited due to extreme battery temperature
          if(vehicle_state.HV_bat_temperature_bars >= 9){ //HOT battery
            temp2 = 0x06; //24kW of regen
            if (vehicle_state.regen > temp2) //Protection, only modify regen if voltage_max_regen is bigger than temperature_max_regen.
            {
              frame.data[1] = temp2; //24kW of regen
              vehicle_state.regen = 0x06; //Store the new actual amount of allowed regen in struct
            }
          }
          if(vehicle_state.HV_bat_temperature_bars <= 3){ //COLD battery
            temp2 = 0x06; //24kW of regen //TODO: 2 bars of temperature should result in 3 bubbles being taken away
            if (vehicle_state.regen > temp2) //Protection, only modify regen if voltage_max_regen is bigger than temperature_max_regen.
            {
              frame.data[1] = 0x06; //24kW of regen (3? bubbles)
              vehicle_state.regen = 0x06; //Store the new actual amount of allowed regen in struct
              if(vehicle_state.HV_bat_temperature_bars <= 2)
              {
                frame.data[1] = 0x03; //12kW of regen (2 bubbles)
                vehicle_state.regen = 0x03; //Store the new actual amount of allowed regen in struct
              }
              if(vehicle_state.HV_bat_temperature_bars <= 1)
              {
                frame.data[1] = 0x02; //8kW of regen (x bubbles)
                vehicle_state.regen = 0x02; //Store the new actual amount of allowed regen in struct
              }
            }
          }
            
          /* OUTPUT POWER AVAILABLE TUNING */
          // Determine max allowed DISCHARGE power based on temperature bars
          // Heating system reserves 10kW when active!
          switch(vehicle_state.HV_bat_temperature_bars)
          {
            case 12:
            frame.data[0] = 0x28; //40?kW allowed, 4bubbles away, TURTLE ILLUMINATED
            break;
            case 11:
            frame.data[0] = 0x32; //50kW allowed, 3bubbles away
            break;
            case 10:
            frame.data[0] = 0x41; //65kW allowed, 1bubbles away
            break;
            case 9:
            frame.data[0] = 0x46; //70kW allowed, 1bubbles away
            break;
            case 8:
            frame.data[0] = 0x50; //80kW allowed from battery
            break;
            case 7:
            break;
            case 6:
            break;
            case 5:
            break;
            case 4:
            break;
            case 3:
            frame.data[0] = 0x50; //80kW allowed from battery, 1bubbles away
            break;
            case 2:
            frame.data[0] = 0x46; //70kW allowed, 2bubbles away
            break;
            case 1:
            frame.data[0] = 0x41; //65kW allowed, 3bubbles away
            break;
            case 0:
            frame.data[0] = 0x41; //65kW allowed, 3bubbles away
            break;
            default:
            break;
          }
            
        //    #endif //#ifdef BATTERY_SWAP
        }
      }
    }
        
    if(startup_counter < 255) startup_counter++;
        
    //#ifdef CHARGECURRENT
    if( CURRENT_CONTROL_ENABLED() )
    {
      //Check what battery is currently requesting as max charger kW
      battery_current_demand = ((frame.data[2] & 0x0F) << 6 | (frame.data[3] >> 2));

      //Only overwrite max current if the battery requested is bigger than the maximum you want to limit it to.
      //Otherwise there is risk that battery wants to reduce to 500W, and you are forcing it to 3.3kW!
      if (charging_state == CHARGING_SLOW && battery_current_demand > max_current)
      {
        //Here is how to overwrite the maximum allowed current going into the battery
        frame.data[2] = (frame.data[2] & 0xF0) | (max_current >> 6);
        frame.data[3] = (max_current << 2) | 3;
      }
    }
    //#endif //CHARGECURRENT
        
    //#ifdef DISABLE_REGEN_IN_DRIVE
    if( GLIDE_IN_DRIVE_ENABLED() )
    {
      //This section is used for enabling glide in drive
      if(disable_regen_toggle && (current_11A_shifter_state == SHIFT_D)){
        if(!eco_active)
        {
          frame.data[1] = (frame.data[1] & 0xC0);//Zero out regen in D
          frame.data[2] = (frame.data[2] & 0x0F);
          vehicle_state.regen = 0;
        }
      } 
    }   
    //#endif //#ifdef DISABLE_REGEN_IN_DRIVE
    
    calc_crc8(&frame);
  break;
	
	case 0x50B:
		VCM_WakeUpSleepCommand = (frame.data[3] & 0xC0) >> 6;
		CANMASK	= (frame.data[2] & 0x04) >> 2;
	break;
	
	case 0x50C:
		ALU_question = frame.data[4];
	break;
	
	case 0x55B:
		#ifdef ISOLATION_ERROR_FIX
		//insulation resistance fix DO NOT ENABLE BY MISTAKE
		if(frame.data[4] != 0xFF){
			frame.data[4] = 250;
			frame.data[5] = frame.data[5] & 0xFE;	//blank LB_IRSEN
			calc_crc8(&frame);
		}
		#endif
		
		//#ifdef BATTERY_SWAP
        if( BATTERY_SWAP_ENABLED() )
        {
  			if(ALU_question == 0xB2){
  				frame.data[2] = 0xAA;
  			} else {
  				frame.data[2] = 0x55;
  			}
  			
  			if(CANMASK == 0){
  				frame.data[6] = (frame.data[6] & 0xCF) | 0x20;
  			} else {
  				frame.data[6] = (frame.data[6] & 0xCF) | 0x10;
  			}
  
  			frame.data[5] = frame.data[5] & 0xC0; //blank LB_IRSEN TODO: DALA should this line be removed?
        }
		//#endif //#ifdef BATTERY_SWAP

		main_battery_soc = (frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6); //Dala capture SOC needed for dashboard (and stopping charge)
		main_battery_soc /= 10; //Remove decimals, 0-100 instead of 0-100.0 TODO: rewrite with temp2 variable, to reduce soc datatype to u8
			
		calc_crc8(&frame);
	break;
	
	case 0x5BC:
		if(frame.data[0] != 0xFF){
			starting_up &= ~4;
		} else {
			starting_up |= 4;
		}				
		
		//#ifdef BATTERY_SAVER
        if( BATTERY_SAVER_ENABLED() )
        {
  			//Section for visualizing the max charge with the help of capacity bars on the dash
  			mux_5bc_CapacityCharge = (frame.data[4] & 0x0F); //Save the mux containing info if we have capacity or chargebars in the message [8 / 9] [40kWh 14/15]
  			if (timeToSetCapacityDisplay > 0)
  			{
  				//#ifdef BATTERY_40KWH
				if( BATTERY_40KWH() )
  				{
					if (mux_5bc_CapacityCharge == 15) {frame.data[2] = (uint8_t) ((frame.data[2] & 0x0F) | SetCapacityDisplay << 4);} //Confirmed working
  				}
  				//#endif
            
  				//#ifdef BATTERY_30KWH
				if( BATTERY_30KWH() )
				{
					if (mux_5bc_CapacityCharge == 8) {frame.data[2] = (uint8_t) ((frame.data[2] & 0x0F) | SetCapacityDisplay << 4);} //TODO test with Per?
				}
  				//#endif
  					
  				//#ifdef BATTERY_24KWH
				if( BATTERY_24KWH() )
				{
					if (mux_5bc_CapacityCharge == 8) {frame.data[2] = (uint8_t) ((frame.data[2] & 0x0F) | SetCapacityDisplay << 4);}
				}
  				//#endif
  			}
        }
		//#endif//#ifdef BATTERY_SAVER
				
		//#ifdef BATTERY_SWAP
		if( BATTERY_SWAP_ENABLED() )
		{
			//#ifdef LEAF_2011
			if( NISSAN_ZE0_2011_2012() )
			{
				if(frame.data[0] != 0xFF){
					if((frame.data[5] & 0x10) == 0x00){
						convert_array_to_5bc(&leaf_40kwh_5bc, (uint8_t *) &frame.data);
						swap_5bc_remaining.LB_CAPR = leaf_40kwh_5bc.LB_CAPR;
						swap_5bc_full.LB_CAPR = leaf_40kwh_5bc.LB_CAPR;
						current_capacity_gids = swap_5bc_full.LB_CAPR;
						current_capacity_wh = swap_5bc_full.LB_CAPR * 80;
						main_battery_temp = frame.data[3] / 20;
						whats_happening.HV_bat_temperature_bars = main_battery_temp;						
						main_battery_temp = temp_lut[main_battery_temp] + 1;
						whats_happening.HV_bat_temperature = main_battery_temp;
					} else {
						//first byte is battery avg temp, but in a different format, namely % of segments (e.g. 0x7D = 125/240=0.52x12=6 segs)
						//old format was degrees C, with a LUT, so we need to reverse the LUT...
						//main_battery_temp = frame.data[0] / 20;					
					}
				
					//swap_5bc_remaining.LB_AVET = main_battery_temp;
					//swap_5bc_full.LB_AVET = main_battery_temp;
				} else {
					swap_5bc_remaining.LB_CAPR = 0x3FF;
					swap_5bc_full.LB_CAPR = 0x3FF;
					swap_5bc_remaining.LB_RCHGTIM = 0;
					swap_5bc_remaining.LB_RCHGTCON = 0;
				}
			
				skip_5bc--;
				if(!skip_5bc){
					switch(cmr_idx){
						case QUICK_CHARGE:
							swap_5bc_full.LB_RCHGTIM = (capacity_80 - current_capacity_wh) / 766;
							cmr_idx = NORMAL_CHARGE_200V_100;
							break;
						case NORMAL_CHARGE_200V_100:
							swap_5bc_remaining.LB_RCHGTIM = (total_capacity_wh - current_capacity_wh) / 55;
							swap_5bc_full.LB_RCHGTIM = swap_5bc_remaining.LB_RCHGTIM;
							cmr_idx = NORMAL_CHARGE_200V_80;
							break;
						case NORMAL_CHARGE_200V_80:
							if(current_capacity_wh <= capacity_80){swap_5bc_remaining.LB_RCHGTIM = 0;}
							else{swap_5bc_remaining.LB_RCHGTIM = (capacity_80 - current_capacity_wh) / 55; }
							swap_5bc_full.LB_RCHGTIM = swap_5bc_remaining.LB_RCHGTIM;
							cmr_idx = NORMAL_CHARGE_100V_100;
							break;
						case NORMAL_CHARGE_100V_100:
							swap_5bc_remaining.LB_RCHGTIM = (total_capacity_wh - current_capacity_wh) / 28;
							swap_5bc_full.LB_RCHGTIM = swap_5bc_remaining.LB_RCHGTIM;
							cmr_idx = NORMAL_CHARGE_100V_80;
							break;
						case NORMAL_CHARGE_100V_80:
							if(current_capacity_wh <= capacity_80){swap_5bc_remaining.LB_RCHGTIM = 0;}
							else{swap_5bc_remaining.LB_RCHGTIM = (capacity_80 - current_capacity_wh) / 28; }
							swap_5bc_full.LB_RCHGTIM = swap_5bc_remaining.LB_RCHGTIM;
							cmr_idx = QUICK_CHARGE;
							break;
					}
				
					swap_5bc_remaining.LB_RCHGTCON = cmr_idx;
					swap_5bc_full.LB_RCHGTCON = cmr_idx;
					swap_5bc_remaining.LB_AVET = main_battery_temp;
					swap_5bc_full.LB_AVET = main_battery_temp;
				
					//2011 leaf just cannot cope with capacities >24kWh
					//when quick charging, we change capacity to reflect a proportion of 21.3kWh (266 GIDs) DALA: Is this why the QC jumps from 36->46%? Veefil? Maybe try removing this section for 24kWh?
					if( BATTERY_24KWH() )
					{
						//#ifndef BATTERY_24KWH
						if(charging_state == CHARGING_QUICK){
							temp2 = main_battery_soc * 300; //e.g. 55 * 300 = 16500
							temp2 = temp2 / 100; //e.g. 16500/100 = 165
							swap_5bc_remaining.LB_CAPR = temp2;
							swap_5bc_full.LB_CAPR = temp2;
						}
						//#endif //#ifndef BATTERY_24KWH
					}
				
					if(alternate_5bc){
						convert_5bc_to_array(&swap_5bc_remaining, (uint8_t *) &saved_5bc_frame.data);
						alternate_5bc = 0;
					} else {
						convert_5bc_to_array(&swap_5bc_full, (uint8_t *) &saved_5bc_frame.data);
						alternate_5bc = 1;
					}				
				
					skip_5bc = 5;
				}			
				//frame = saved_5bc_frame;			
			}
			//#endif //#ifdef LEAF_2011
			
			//#ifdef LEAF_2014
			if( NISSAN_AZE0_2013_2017() )
			{
				//5bc on 2014 looks extremely similar to 2018, except for the extra switch, so we remove and ignore that
				if((frame.data[5] & 0x10) == 0x00){
					convert_array_to_5bc(&leaf_40kwh_5bc, (uint8_t *) &frame.data);
					leaf_40kwh_5bc.LB_CAPR;
				}
				frame.data[0] = leaf_40kwh_5bc.LB_CAPR >> 2;
				frame.data[1] = (leaf_40kwh_5bc.LB_CAPR << 6) & 0xC0;
				frame.data[5] = frame.data[5] & 0x03;

         main_battery_temp = frame.data[3] / 20; //Temperature needed for charger section
         vehicle_state.HV_bat_temperature_bars = main_battery_temp; //Store amount of temperature bars
         main_battery_temp = temp_lut[main_battery_temp] + 1; //write main_battery_temp to be used by 5C0 message
         vehicle_state.HV_bat_temperature = main_battery_temp; //Store amount of temperature in *C

         //Correct charge timer estimates
       //This code is WIP, currently the 3.3 and 6.6kW times are good, but 100V is messed up somehow. Seems to be differences in LEAF firmware
        cmr_idx = ((frame.data[5] & 0x03) << 3) | ((frame.data[6] & 0xE0) >> 5);
        switch(cmr_idx){
          case 0: //QC
          break;
          case 5: //6.6kW 100%
            temp2 = (time_100_with_66kW_in_minutes - ((time_100_with_66kW_in_minutes * main_battery_soc)/100));
            frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
            frame.data[7] = (temp2 & 0xFF);
          break;
          case 8: //200V 100%
            temp2 = (time_100_with_200V_in_minutes - ((time_100_with_200V_in_minutes * main_battery_soc)/100));
            frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
            frame.data[7] = (temp2 & 0xFF);
          break;
          case 11: //100V 100%
            temp2 = (time_100_with_100V_in_minutes - ((time_100_with_100V_in_minutes * main_battery_soc)/100));
            frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
            frame.data[7] = (temp2 & 0xFF);
          break;
          case 18: //6.6kW 80%
            if(main_battery_soc < 80)
            {
              temp2 = (time_80_with_66kW_in_minutes - ((time_80_with_66kW_in_minutes * (main_battery_soc+20))/100));
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }
            else
            {
              temp2 = 0; //0 since we are over 80% SOC
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }
          break;
          case 21: //200V 80%
            if(main_battery_soc < 80)
            {
              temp2 = (time_80_with_200V_in_minutes - ((time_80_with_200V_in_minutes * (main_battery_soc+20))/100));
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }
            else
            {
              temp2 = 0; //0 since we are over 80% SOC
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }
          break;
          case 24: //100V 80%
            if(main_battery_soc < 80)
            {
              temp2 = (time_80_with_100V_in_minutes - ((time_80_with_100V_in_minutes * (main_battery_soc+20))/100));
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }
            else
            {
              temp2 = 0; //0 since we are over 80% SOC
              frame.data[6] = (frame.data[6] & 0xE0) | (temp2 >> 8);
              frame.data[7] = (temp2 & 0xFF);
            }        
				//#endif //#ifdef LEAF_2014
			}
		}
		//#endif //#ifdef BATTERY_SWAP				
				
	break;

  case 0x54B: //100ms AC Auto amp, collect button presses for setting charge max percentage
    #ifdef RAPIDGATEDODGER
    VentModeStatus = (frame.data[3]);
    FanSpeed = ((frame.data[4] & 0xF8) >> 3); //Fan speed is 0-7
    #endif
        
    #ifdef RAPIDGATEDODGER
    if ((charging_state == CHARGING_QUICK) && (FanSpeed == 6))
    {
      QC35kWlimiter = 1;
    }
    if ((charging_state == CHARGING_QUICK) && (FanSpeed == 7))
    {
      QC25kWlimiter = 1;
    }
    #endif
        
    //#ifdef BATTERY_SAVER //Only set charge max when not charging, recirc is on AND fan speed is max (7) AND shift state is P
    if( BATTERY_SAVER_ENABLED() )
    {
      if ((charging_state != CHARGING_SLOW) && (FanSpeed == 7) && (VentModeStatus == 0x09) && (current_11A_shifter_state == SHIFT_P)) 
      {
        if (ChargeSetModeCounter < 255)
        {
          ChargeSetModeCounter++; //increment for each 100ms can message
        }
              
        if (ChargeSetModeCounter > 70) //70 messages = 7s held
        {
          SOC_stopcharging = 100;
          //#ifdef LEAF_2014
          if( NISSAN_AZE0_2013_2017() )
          {
            SetCapacityDisplay = 15; //15 = 12 capacity bars = 100% charge limiter
          }
          //#endif
          
          //#ifdef LEAF_2011
          if( NISSAN_ZE0_2011_2012() )
          {
            SetCapacityDisplay = 13; //13 = 12 capacity bars = 100% charge limiter
          }
          //#endif
          
          timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
          #ifdef USB_SERIAL
          print("BatterySaver: Setpoint 100%\n",27);
          #endif
        }
        else if (ChargeSetModeCounter > 50) //50 messages = 5s held
        {
          SOC_stopcharging = 93;
          //#ifdef LEAF_2014
          if( NISSAN_AZE0_2013_2017() )
          {
            SetCapacityDisplay = 13; //13 = 11 capacity bars = 92% charge limiter
          }
          //#endif
          
          //#ifdef LEAF_2011
          if( NISSAN_ZE0_2011_2012() )
          {
            SetCapacityDisplay = 12; //12 = 11 capacity bars = 92% charge limiter
          }
          //#endif
          
          timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
          #ifdef USB_SERIAL
          print("BatterySaver: Setpoint 92%\n",27);
          #endif
        }
        else if (ChargeSetModeCounter > 30) //30 messages = 3s held
        {
          SOC_stopcharging = 84;
          //#ifdef LEAF_2014
          if( NISSAN_AZE0_2013_2017() )
          {
            SetCapacityDisplay = 12; //12 = 10 capacity bars = 83% charge limiter
          }
          //#endif          
          
          //#ifdef LEAF_2011
          if( NISSAN_ZE0_2011_2012() )
          {
            SetCapacityDisplay = 11; //11 = 10 capacity bars = 83% charge limiter
          }
          //#endif
          
          timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
          #ifdef USB_SERIAL
          print("BatterySaver: Setpoint 83%\n",27);
          #endif
        }
        else
        {
          //Condition has been held for less than 2s, do nothing
        }
      }
      else //Conditions no longer fulfilled
      {
        ChargeSetModeCounter = 0; //Reset the counter as soon as conditions no longer are valid
        if (timeToSetCapacityDisplay > 0) //Slowly decrease the capacity readout
        {
          timeToSetCapacityDisplay--;
        }
      }
    }
    //#endif //BATTERY_SAVER

    //---------------------------------------
    // Start of Charge Current implementation
    //---------------------------------------
    
    //Step 1: Wait for trigger
    //Conditions: charging_state is CHARGING_SLOW and FanSpeed becomes 7   
    
    if ( (charging_state == CHARGING_SLOW) && ((FanSpeed == 7) && (previous_FanSpeed != 7)) )
    {
      if ( CURRENT_CONTROL_ENABLED() )
        {
          startChargeCurrentDisplay = true;
          takeoverSOCdisplay = 1;
          TIMER_Start();
        }        
    }

    //Step 2: Display Charge Current according to Web Configuration and set charge Current if ( CURRENT_CONTROL_ENABLED() )
    if  ( CURRENT_CONTROL_ENABLED() )  
    {
      if(CURRENT_CONTROL_UNRESTRICTED_KW())
      {
        max_current = 320; //Set to unrestricted, should prevent remote heating to activate this mode!
        
        if( startChargeCurrentDisplay == true )
        { timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 15; //15 = 12 capacity bars = Maximum speed
        SetPercentageDisplay = 66; //66% on dashboard = 6.6kW 
        }
      }        
      else if(CURRENT_CONTROL_1p0_KW())
      {
        max_current = 110; //1,0kW
        if( startChargeCurrentDisplay == true )
        {
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 7; //7 = 6 capacity bars = 1kW
        SetPercentageDisplay = 10; //10% on dashboard = 1.0kW
        }
      }
      else if(CURRENT_CONTROL_2p0_KW())
      {
        max_current = 120; //2.0kW
        if( startChargeCurrentDisplay == true )
        {
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 8; //8 = 7 capacity bars = 2kW
        SetPercentageDisplay = 20; //20% on dashboard = 2.0kW
        }
      }
      else if(CURRENT_CONTROL_3p0_KW())
      {
        max_current = 130; //3.0kW
        if( startChargeCurrentDisplay == true ){
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 9; //9 = 8 capacity bars = 3kW
        SetPercentageDisplay = 30; //30% on dashboard = 3.0kW
        }
      }
      else if (CURRENT_CONTROL_4p0_KW())
      {
        max_current = 140; //4.0kW
        if( startChargeCurrentDisplay == true ){
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 11; //11 = 9 capacity bars = 4kW
        SetPercentageDisplay = 40; //40% on dashboard = 4.0kW
        }
      }
      else if (CURRENT_CONTROL_6p0_KW())
      {
        max_current = 160; //6.0kW
        if( startChargeCurrentDisplay == true ){
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 13; //13 = 11 capacity bars = 6kW
        SetPercentageDisplay = 60; //60% on dashboard = 6.0kW
        }
      }
      else
      {
        //set to max allowed charge speed
        max_current = 320; //22.0kW (future proofing for 3-phase charger ;) )
        if( startChargeCurrentDisplay == true ){
        timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
        SetCapacityDisplay = 15; //15 = 12 capacity bars = Maximum speed
        SetPercentageDisplay = 66; //66% on dashboard = 6.6kW
        }  
      }       
    }

    //Step 3: Revert to SOC after 15secs
    if( (startChargeCurrentDisplay == true) && TIMER_Expired(15) )
    {
      startChargeCurrentDisplay == false;
        
      //Display SOC      
      takeoverSOCdisplay = 0;
    }

    //---------------------------------------
    // End of Charge Current implementation
    //---------------------------------------
    
    //#ifdef CHARGECURRENT
    //if( CURRENT_CONTROL_ENABLED() )
    //{
    //  if (charging_state == CHARGING_SLOW /*&& FanSpeed == 7 && VentModeStatus == 0x09 */) //0x09=Recirculation
    //  {
    //    if (CurrentSetModeCounter < 255) //overflow handling
    //    {
    //      CurrentSetModeCounter++;
    //    }
    // 
    //    if (CURRENT_CONTROL_UNRESTRICTED_KW() && (CurrentSetModeCounter > 160)) //160 messages = 16s held = Unrestricted
    //    {
    //      max_current = 320; //Set to unrestricted, should prevent remote heating to activate this mode!
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 15; //15 = 12 capacity bars = Maximum speed
    //      SetPercentageDisplay = 66; //66% on dashboard = 6.6kW
    //    }
    //    
    //    if (CURRENT_CONTROL_1p0_KW() && (CurrentSetModeCounter > 140)) //140 messages = 14s held = 1.0kW
    //    {
    //      max_current = 110; //1,0kW
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 7; //7 = 6 capacity bars = 1kW
    //      SetPercentageDisplay = 10; //10% on dashboard = 1.0kW
    //    }
    //    else if (CURRENT_CONTROL_2p0_KW() && (CurrentSetModeCounter > 120)) // 12s held
    //    {
    //      max_current = 120; //2.0kW
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 8; //8 = 7 capacity bars = 2kW
    //      SetPercentageDisplay = 20; //20% on dashboard = 2.0kW
    //    }
    //    else if (CURRENT_CONTROL_3p0_KW() && (CurrentSetModeCounter > 100)) // 10s held
    //   {
    //      max_current = 130; //3.0kW
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 9; //9 = 8 capacity bars = 3kW
    //      SetPercentageDisplay = 30; //30% on dashboard = 3.0kW
    //    }
    //    else if (CURRENT_CONTROL_4p0_KW() && (CurrentSetModeCounter > 80)) // 8s held
    //    {
    //      max_current = 140; //4.0kW
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 11; //11 = 9 capacity bars = 4kW
    //      SetPercentageDisplay = 40; //40% on dashboard = 4.0kW
    //    }
    //    //else if (CURRENT_CONTROL_5p0_KW() && (CurrentSetModeCounter > 60)) // 6s held
    //    //{
    //    //  max_current = 150; //5.0kW
    //    //  timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //    //  SetCapacityDisplay = 12; //12 = 10 capacity bars = 5kW
    //    //  SetPercentageDisplay = 50; //50% on dashboard = 5.0kW
    //    //}
    //    else if (CURRENT_CONTROL_6p0_KW() && (CurrentSetModeCounter > 40)) // 4s held
    //    {
    //      max_current = 160; //6.0kW
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 13; //13 = 11 capacity bars = 6kW
    //      SetPercentageDisplay = 60; //60% on dashboard = 6.0kW
    //    }
    //    else
    //    {
    //      //Condition has been held for less than 4s, set to max allowed charge speed
    //      max_current = 320; //22.0kW (future proofing for 3-phase charger ;) )
    //      timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
    //      SetCapacityDisplay = 15; //15 = 12 capacity bars = Maximum speed
    //      takeoverSOCdisplay = 1;
    //      SetPercentageDisplay = 66; //66% on dashboard = 6.6kW
    //    }
    //  }
    //  else //Conditions no longer fulfilled
    //  {
    //    CurrentSetModeCounter = 0; //Reset the counter as soon as conditions no longer are valid
    //    if (timeToSetCapacityDisplay > 0) //Slowly decrease the capacity readout
    //    {
    //      timeToSetCapacityDisplay--;
    //      if(timeToSetCapacityDisplay == 0)
    //      {
    //        takeoverSOCdisplay = 0;
    //      }
    //    }
    //  }
    //}
    //#endif //CHARGECURRENT
  break;
	
	//#ifdef BATTERY_SWAP
	case 0x5C0:
		if( BATTERY_SWAP_ENABLED() )
		{		
			swap_5c0_max.LB_HIS_TEMP = main_battery_temp;
			swap_5c0_max.LB_HIS_TEMP_WUP = main_battery_temp;
			swap_5c0_avg.LB_HIS_TEMP = main_battery_temp;
			swap_5c0_avg.LB_HIS_TEMP_WUP = main_battery_temp;
			swap_5c0_min.LB_HIS_TEMP = main_battery_temp;
			swap_5c0_min.LB_HIS_TEMP_WUP = main_battery_temp;
				
			if(swap_5c0_idx == 0){
				//convert_5c0_to_array(&swap_5c0_max, (uint8_t *) &frame.data);
			} else if(swap_5c0_idx == 1){
				//convert_5c0_to_array(&swap_5c0_min, (uint8_t *) &frame.data);
			} else {
				//convert_5c0_to_array(&swap_5c0_avg, (uint8_t *) &frame.data);
			}
				
			swap_5c0_idx++;
			if(swap_5c0_idx > 2) swap_5c0_idx = 0;
		}
	break;
	//#endif //#ifdef BATTERY_SWAP
	
	case 0x11A:
		shifter_state = frame.data[0];
		if((frame.data[0] & 0xF0) == 0){ parked = 1;
		} else {						 parked = 0;}

          current_11A_shifter_state = (frame.data[0] & 0xF0);
        #if( GLIDE_IN_DRIVE_ENABLED () )
        eco_active = ((frame.data[1] & 0x10)>>4);
//{ timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_CHARGEMAX;
//        SetCapacityDisplay = 15; //15 = 12 capacity bars = Maximum speed
 //       SetPercentageDisplay = 66; //66% on dashboard = 6.6kW 
//        }
        if(previous_11A_shifter_state == SHIFT_D){ //If we go from D to N, toggle the regen disable feature
          if(current_11A_shifter_state == SHIFT_N){
            if(disable_regen_toggle == 0){
              disable_regen_toggle = 1;
              timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_REGEN;
              SetPercentageDisplay = 999;
            }
            else{
              disable_regen_toggle = 0;
              timeToSetCapacityDisplay = FADE_OUT_CAP_AFTER_SETTING_REGEN;
              SetPercentageDisplay = 111;
            }
          }
        }

        previous_11A_shifter_state = (frame.data[0] & 0xF0);
        #endif
break;
	
	case 0x1F2:
		prev_charging_state = charging_state;
		charging_state = frame.data[2];
				
		//#ifdef LEAF_2011
		if( NISSAN_ZE0_2011_2012() )
		{
			if(frame.data[0] & 0x80){
				whats_happening.max_charge_percentage = 80;
			} else {
				whats_happening.max_charge_percentage = 100;
			}
				
			//#ifdef BATTERY_SWAP
			if( BATTERY_SWAP_ENABLED() )
			{
				if(seen_1da && charging_state == CHARGING_IDLE){ //DALA, does this require bridge to be setup near VCM? Since VCM sends 1F2
					frame.data[2] = 0;
					seen_1da--;
				}
			}
			//frame.data[3] = 0xA0;	//change from gen1->gen4+ DALA, does not help yet
			//calc_sum4(&frame);
			//#endif//#ifdef BATTERY_SWAP
		//#endif //#ifdef LEAF_2011
		}
	break;
	
	case 0x59E:   // QC capacity message, adjust for AZE0 with 30/40/62kWh pack swaps
		frame.data[2] = 0x0E; //Set LB_Full_Capacity_for_QC to 23000Wh (default value for 24kWh LEAF)
		frame.data[3] = 0x60;
		//Calculate new LBC_QC_CapRemaining value
		temp2 = ((230 * main_battery_soc)/100); // Crazy advanced math
		frame.data[3] = (frame.data[3] & 0xF0) | ((temp2 >> 5) & 0xF); // store the new LBC_QC_CapRemaining
		frame.data[4] = ((temp2 & 0x1F) <<3) | (frame.data[4] & 0x07); // to the 59E message out to vehicle
		calc_crc8(&frame);
	break;
	
	case 0x79B:
		dont_query_battery = 1; //leaf spy / OVMS is active, disable our own battery sampling
	break;
	
	case 0x7BB:
		//we're only interested in group 02 data
		if((charging_state != CHARGING_SLOW) && (charging_state != CHARGING_QUICK)) break;
				
		if(frame.data[0] == 0x10){
			//battery_7bb_idx = 0;
			ignore_7bb = 0;
			if(frame.data[3] != 2) ignore_7bb = 1;
		}
				
		if(ignore_7bb) break;
				
		//if(!dont_query_battery) send_can(battery_can_bus, battery_next_line_request);
				
		//we get 29 lines of data, each holding 12-bit values in 16-bit containers
		//as there are 7 data bytes per message, each message shifts the data by 1 byte
		if(frame.data[0] == 0x10){ //first frame is anomalous
			battery_request_idx = 0;					
			main_cell_voltages[battery_request_idx++] = (frame.data[4] << 8) | frame.data[5];
			main_cell_voltages[battery_request_idx++] = (frame.data[6] << 8) | frame.data[7];
			goto end_7bb;
		}
	
		if(frame.data[6] == 0xFF && frame.data[0] == 0x2C){  //last frame as well
			//no cell data is in this frame, but as it's the last we know we can
			//do some data manipulation here
			main_min_max_voltage[0] = 9999;
			main_min_max_voltage[1] = 0;
			for(i = 0; i < 96; i++){
				if(main_min_max_voltage[0] > main_cell_voltages[i]) main_min_max_voltage[0] = main_cell_voltages[i];
				if(main_min_max_voltage[1] < main_cell_voltages[i]) main_min_max_voltage[1] = main_cell_voltages[i];
			}					
					
			//#ifdef BATTERY_SWAP
			if( BATTERY_SWAP_ENABLED() )
			{
				if(main_min_max_voltage[1] >= (MAX_CELL_VOLTAGE + 50)){ //emergency stop at 50mV above MAX_CELL_VOLTAGE
					end_of_charge = 1;
					#ifdef USB_SERIAL
					print("Cell overvoltage: charge stopped\n",33);
					#endif
				}
			}
			//#endif //BATTERY_SWAP_ENABLED
					
			goto end_7bb;
		}
				
		if((frame.data[0] % 2) == 0){ //even frames
			main_cell_voltages[battery_request_idx++]  |= frame.data[1];
			main_cell_voltages[battery_request_idx++]	= (frame.data[2] << 8) | frame.data[3];
			main_cell_voltages[battery_request_idx++]	= (frame.data[4] << 8) | frame.data[5];
			main_cell_voltages[battery_request_idx++]	= (frame.data[6] << 8) | frame.data[7];
		} else { //odd frames
			main_cell_voltages[battery_request_idx++]	= (frame.data[1] << 8) | frame.data[2];
			main_cell_voltages[battery_request_idx++]	= (frame.data[3] << 8) | frame.data[4];
			main_cell_voltages[battery_request_idx++]	= (frame.data[5] << 8) | frame.data[6];
			main_cell_voltages[battery_request_idx]		= (frame.data[7] << 8);
		}				
		
		end_7bb:
		//battery_7bb_idx++;
	break;
			
	//---End of earlyversion.c
  
    default:
      break;
  }

  //Post processing
  //store last charging state and fan speed
  //previous_charging_state = charging_state;
  //previous_FanSpeed = FanSpeed;
  
  #endif //#ifdef LEAF_TRANSLATION_ENABLED

  //——————————————————————————————————————————————————————————————————————————————
  // START OF BRUTEFORCE UPGRADE
  //——————————————————————————————————————————————————————————————————————————————
  #ifdef LEAF_BRUTEFORCE_UPGRADE 

  uint8_t mux_5bc_CapCharge     = 0;
  uint8_t corrected_chargebars  = 0;
  uint16_t total_gids           = 0;
  uint16_t total_voltage        = 0;
  volatile  uint8_t   charging_state            = 0;
  volatile  uint8_t   voltage_samples           = 0;
  volatile  uint8_t   LBC_CapacityBars          = 0;
  volatile  uint16_t  voltage_sum               = 0;
  volatile  uint16_t  filtered_voltage          = 345; //Initialized to 345, otherwise it will be 0 for a few seconds before enough filtering has happened
  volatile  uint16_t  LBC_MainGids              = 0;
  volatile  uint16_t  LBC_StateOfCharge         = 0;
  volatile  uint16_t  LBC_BatteryVoltageSignal  = 0;
    
  switch(frame.can_id){
    case 0x1DB:
      //Check what voltage the LBC reports  (10 bits, all 8bits from frame[2], and 2 bits from frame[3] 0xC0)
      total_voltage = (frame.data[2] << 2) | ((frame.data[3] & 0xC0) >> 6);
      LBC_BatteryVoltageSignal = (total_voltage/2); //Convert LBC battery voltage to human readable voltage (1 LSB = 0.5V)
    break;
    
    case 0x55B:
      //Check what SOC the LBC reports  (10 bits, all 8bits from frame[0], and 2 bits from frame[1] 0xC0)
      LBC_StateOfCharge = (frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6);  //Further improvement idea, modify this also!
    break;
    
    case 0x5BC: //This frame contains: GIDS, temp readings, capacity bars and mux
      mux_5bc_CapCharge = (frame.data[4] & 0x0F); //Save the mux containing info if we have capacity or chargebars in the message [8 / 9] Only valid for 2014+!
      //Filter battery voltage measurement
      if (voltage_samples < 20) //Keep summing up voltage averages
      {
        voltage_sum += LBC_BatteryVoltageSignal;
        voltage_samples++;
      }
      else
      {
        filtered_voltage = (voltage_sum/20); //When we have enough samples, write an average (this helps during low SOC)
        voltage_samples = 0;
        voltage_sum = 0;
      }

      if(charging_state != 0x20) //Don't manipulate anything if car is slowcharging. Causes a TDC from TCU otherwise for 2013+ leafs
      {
        LBC_MainGids = (frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6); //check how many the stock GIDs the BMS reports (10 bits, all 8bits from frame[0], and 2 bits from frame[1] 0xC0)

        if(LBC_MainGids>=10)
        {
          total_gids = (LBC_MainGids + EXTRAGIDS); //This algorithm has a drawback, it wont age as the battery does!
          
          if (total_gids >= 320) {
            corrected_chargebars = 14; //12
          }
          else if (total_gids >= 295){
            corrected_chargebars = 13; //11
          }
          else if (total_gids >= 270){
            corrected_chargebars = 12; //10
          }
          else if (total_gids >= 245){
            corrected_chargebars = 11; //9
          }
          else if (total_gids >= 220){
            corrected_chargebars = 10; //8
          }
          else if (total_gids >= 195){
            corrected_chargebars = 9; //7
          }
          else if (total_gids >= 170){
            corrected_chargebars = 8; //6
          }
          else if (total_gids >= 145){
            corrected_chargebars = 7; //5
          }
          else if (total_gids >= 120){
            corrected_chargebars = 6; //4
          }
          else if (total_gids >= 95){
            corrected_chargebars = 5; //3
          }
          else if (total_gids >= 70){
            corrected_chargebars = 4; //3
          }
          else{
            corrected_chargebars = 3;
          }
        }
        else if(LBC_MainGids<=9) //There is still some juice left in the battery when it reports 0gids. (ca 30% on a 30kWh bruteforce)
        {            //Start estimating SOC from battery voltage
          if(filtered_voltage >= 347) { //7GIDS = 347V on 24kWh LBC (345V is roughly 27% on 30kWh leaf)
            total_gids = 60;
            corrected_chargebars = 3;
          }
          else if(filtered_voltage >= 346) { //358V = 45% SOC on 30kWh Leaf //351V = 37% SOC on 30kWh Leaf //345V is roughly 27% on 30kWh leaf
            total_gids = 57;
            corrected_chargebars = 3;
          }
          else if(filtered_voltage >= 345) {
            total_gids = 55;
            corrected_chargebars = 3;
          }
          else if(filtered_voltage >= 344) {
            total_gids = 52;
            corrected_chargebars = 3;
          }
          else if(filtered_voltage >= 343) {
            total_gids = 48; //at 48gids the stock BMS triggers LBW!
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 342) {
            total_gids = 45;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 341) {
            total_gids = 42;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 340) {
            total_gids = 40;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 339) {
            total_gids = 38;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 338) {
            total_gids = 36;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 337) { //337V = 21.4%<->18% SOC on 30kWh Leaf (with low mV diff!) (3.51V min)
            total_gids = 34;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 336) {
            total_gids = 32;
            corrected_chargebars = 2;
          }
          else if(filtered_voltage >= 335) {
            total_gids = 30;
            corrected_chargebars = 1;
          }
          else if(filtered_voltage >= 334) {
            total_gids = 25;
            corrected_chargebars = 1;
          }
          else if(filtered_voltage >= 333) {
            total_gids = 20;
            corrected_chargebars = 1;
          }
          else if(filtered_voltage >= 332) {
            total_gids = 15;
            corrected_chargebars = 1;
          }
          else if(filtered_voltage >= 331) {
            total_gids = 10;
            corrected_chargebars = 1;
          }
          else if(filtered_voltage >= 330) {
            total_gids = 5;
            corrected_chargebars = 0;
          }
          else if(filtered_voltage <= 329) { //Contactors will open at ~300V, but it's not worth mapping this area. One single cell can trigger turtle quite easily here.
            total_gids = LBC_MainGids;
            corrected_chargebars = 0;
          }
          else {
            total_gids = LBC_MainGids;
            corrected_chargebars = 0;
          }
        }
        
        //Add the total GIDs
        frame.data[0] = (uint8_t) (total_gids >> 2);
        frame.data[1] = (uint8_t) ((frame.data[1] & 0x3F) | (total_gids & 3) << 6);
        
        //Write capacity and charge bars (this is only valid for AZE0 leaf)
        if (mux_5bc_CapCharge == 9) //Only when the muxed field is equal to 9, capacity bars can be written
        {
          //frame.data[2] = (uint8_t) ((frame.data[2] & 0x0F) | spoofed_capacity << 4); //This will write 15/15, causing capacity to read full. Useful if you cannot reset the BMS
        }
        else if (mux_5bc_CapCharge == 8) //Only when the muxed field is equal to 8, charge bars can be written
        {
          frame.data[2] = (uint8_t) ((frame.data[2] & 0x0F) | corrected_chargebars << 4);
        }
      }
      break;
      
      case 0x1F2: //Collect the charging state (Needed for 2013+ Leafs, throws DTC otherwise) [VCM->LBC]
        charging_state = frame.data[2];
      break;
      
      default:
      break;
   }  
  
  #endif //#ifdef LEAF_BRUTEFORCE_UPGRADE
  //——————————————————————————————————————————————————————————————————————————————
  // END OF BRUTEFORCE UPGRADE
  //——————————————————————————————————————————————————————————————————————————————

  //--- Gateway all messages except the unwanted IDs
  //if you enable CAN repeating between bus 1 and 2, we end up here 
  if(repeat_can){
    
    //you can blacklist certain messages or message contents like this, blocking them from both being forwarded and being displayed
    uint8_t blacklist = 0;
    #ifdef LEAF_BLACKLISTING_ENABLED 
    switch(frame.can_id){       

    //--- Start of earlyversion.c
      
      #ifdef BATTERY_SWAP
      case 0x1DA:
        shutdown_counter = 2; //force the sending of battery messages until inverter stops communicating
      break;
      
      case 0x633: //new 40kWh message
        blacklist = 1;
      break;
      
      case 0x1C2: //new 40kWh message
        blacklist = 1;
      break;
      
      case 0x5EB: //new 40kWh message
        blacklist = 1;
      break;
      
      case 0x1DB:
        if((VCM_WakeUpSleepCommand == 0) && (shutdown_counter > 0)) shutdown_counter--;
      break;
      #endif
      
      case 0x7BB:
      case 0x79B:
        //blacklist = 1;
      break;
      
      default:
        blacklist = 0;
      break;
          
    //--- End of earlyversion.c
    }
    #endif //#ifdef LEAF_BLACKLISTING_ENABLED

    //ToDo: Must confirm the correct CAN Channels connected to VCM and LBC
    if(!blacklist){
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
  }
  //--- End of Messages Gateway
      
  //Post processing for debugging
  SID_to_str(strbuf + 2, frame.can_id);
  canframe_to_str(strbuf + 6, frame);
  #ifdef SERIAL_DEBUG_MONITOR
  Serial.println(strbuf);
  #endif //#ifdef SERIAL_DEBUG_MONITOR
	}
}
#endif// CAN_BRIDGE_FOR_LEAF
