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
// 11.26.2022: Integrated configurable parameters for: BATTERY_SAVER_ENABLED/DISABLED, GLIDE_IN_DRIVE_ENABLED/DISABLED, 
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

//Lookup table temperature ZE0,  offset -40     0    1   2   3  4    5   6   7   8   9  10  11  12
static uint8_t    temp_lut[13]      = {25, 28, 31, 34, 37, 50, 63, 76, 80, 82, 85, 87, 90};

//quick charging variables
static volatile uint8_t   charging_state          = 0;

//other variables
static volatile uint16_t  main_battery_soc        = 0; //Needed to make dash SOC work on 2014+
static volatile uint16_t  battery_soc_pptt      = 0;
static volatile int16_t   dash_soc          = 0;
#define LB_MIN_SOC 0
#define LB_MAX_SOC 1000
#define MINPERCENTAGE 50 //Adjust this value to tune what realSOC% will display as 0% on the dash
#define MAXPERCENTAGE 950 //Adjust this value to tune what realSOC% will display as 100% on the dash

static volatile uint8_t   swap_idx            = 0;
static volatile uint8_t   swap_5c0_idx          = 0;
static volatile uint8_t   VCM_WakeUpSleepCommand    = 0;
static volatile uint8_t   CANMASK             = 0;
static volatile uint8_t   ALU_question          = 0;
static volatile uint8_t   cmr_idx             = QUICK_CHARGE;
static volatile uint16_t GIDS         = 0;

//#ifdef LEAF_2011
static volatile uint8_t   skip_5bc                = 1; //for 2011 battery swap, skip 4 messages
static volatile uint8_t   alternate_5bc           = 0; //for 2011 battery swap
static volatile uint16_t  total_capacity_wh       = 0;//for 2011 battery swap
static volatile uint16_t  current_capacity_wh     = 0;//for 2011 battery swap
static volatile uint8_t seconds_without_1f2 = 0;  // bugfix: 0x603/69C/etc. isn't sent upon charge start on the gen1 Leaf, so we need to trigger our reset on a simple absence of messages

//#endif //#ifdef LEAF_2011

static volatile uint8_t   seen_1da                = 0;//for 2011 battery swap TODO, add more to ifdef to save memory
static volatile uint16_t  current_capacity_gids   = 0;//for 2011 battery swap TODO, define as u8? to save memory
static volatile uint8_t   main_battery_temp       = 0;//for 2011 battery swap

static volatile uint8_t   battery_can_bus         = 2;  //keeps track on which CAN bus the battery talks

//timer variables

//bits                                                      10                  10                  4             8                 7           1             3 (2 space)         1                 5                     13
static volatile Leaf_2011_5BC_message swap_5bc_remaining  = {.LB_CAPR = 0x12C, .LB_FULLCAP = 0x32, .LB_CAPSEG = 0, .LB_AVET = 50, .LB_SOH = 99, .LB_CAPSW = 0, .LB_RLIMIT = 0, .LB_CAPBALCOMP = 1, .LB_RCHGTCON = 0b01001, .LB_RCHGTIM = 0};
static volatile Leaf_2011_5BC_message swap_5bc_full       = {.LB_CAPR = 0x12C, .LB_FULLCAP = 0x32, .LB_CAPSEG = 12, .LB_AVET = 50, .LB_SOH = 99, .LB_CAPSW = 1, .LB_RLIMIT = 0, .LB_CAPBALCOMP = 1, .LB_RCHGTCON = 0b01001, .LB_RCHGTIM = 0};
static volatile Leaf_2011_5BC_message leaf_40kwh_5bc;
static volatile Leaf_2011_5C0_message swap_5c0_max        = {.LB_HIS_DATA_SW = 1, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 66, .LB_HIS_TEMP = 66, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x39, .LB_DTC = 0};
static volatile Leaf_2011_5C0_message swap_5c0_avg        = {.LB_HIS_DATA_SW = 2, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 64, .LB_HIS_TEMP = 64, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x28, .LB_DTC = 0};
static volatile Leaf_2011_5C0_message swap_5c0_min        = {.LB_HIS_DATA_SW = 3, .LB_HIS_HLVOL_TIMS = 0, .LB_HIS_TEMP_WUP = 64, .LB_HIS_TEMP = 64, .LB_HIS_INTG_CUR = 0, .LB_HIS_DEG_REGI = 0x02, .LB_HIS_CELL_VOL = 0x15, .LB_DTC = 0};
static volatile Leaf_2011_state state;
static volatile can_frame_t   saved_5bc_frame             = {.can_id = 0x5BC, .can_dlc = 8};
  
//battery swap fixes
static volatile can_frame_t   swap_390_message  = {.can_id = 0x355, .can_dlc = 8, .data = {4,0,1,0,0,0,0x3C,0}};
      static can_frame_t    swap_605_message    = {.can_id = 0x605, .can_dlc = 1, .data = {0}};
      static can_frame_t    swap_679_message    = {.can_id = 0x679, .can_dlc = 1, .data = {0}};
      static can_frame_t    swap_607_message    = {.can_id = 0x607, .can_dlc = 1, .data = {0}};
static volatile  uint8_t   ticker100ms   = 0;
static can_frame_t ZE1_625_message = {.can_id = 0x625, .can_dlc = 6, .data = {0x02, 0x00, 0xff, 0x1d, 0x20, 0x00}};             // Sending 625 removes U215B [HV BATTERY]
static can_frame_t ZE1_5C5_message = {.can_id = 0x5C5, .can_dlc = 8, .data = {0x40, 0x01, 0x2F, 0x5E, 0x00, 0x00, 0x00, 0x00}}; // Sending 5C5 Removes U214E [HV BATTERY]
static can_frame_t ZE1_5EC_message = {.can_id = 0x5EC, .can_dlc = 1, .data = {0x00}};
static can_frame_t ZE1_355_message = {.can_id = 0x355, .can_dlc = 8, .data = {0x14, 0x0a, 0x13, 0x97, 0x10, 0x00, 0x40, 0x00}};
volatile static uint8_t ticker40ms = 0;
static can_frame_t ZE1_3B8_message = {.can_id = 0x3B8, .can_dlc = 5, .data = {0x7F, 0xE8, 0x01, 0x07, 0xFF}}; // Sending 3B8 removes U1000 and P318E [HV BATTERY]
volatile static uint8_t content_3B8 = 0;
volatile static uint8_t flip_3B8 = 0;

static uint8_t  qc_speed[13];





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
  //#endif

}

//——————————————————————————————————————————————————————————————————————————————
// [LEAF] CAN Bridge Main Handler
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_LEAF
void LEAF_CAN_Bridge_Manager(void){

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
    LEAF_CAN_Handler(CAN_CHANNEL_0, ch0_frame);
    
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
    LEAF_CAN_Handler(CAN_CHANNEL_1, ch1_frame );
    
  }
  #endif //CAN_CH1_ENABLED  

}
#endif //#ifdef CAN_BRIDGE_FOR_LEAF

//——————————————————————————————————————————————————————————————————————————————
// [LEAF] CAN handler - evaluates received data, tranlate and transmits to the other CAN bus
//——————————————————————————————————————————————————————————————————————————————
#ifdef CAN_BRIDGE_FOR_LEAF
void LEAF_CAN_Handler(uint8_t can_bus, can_frame_t new_rx_frame){  
  uint16_t temp;
  can_frame_t frame;
  
  //#ifdef LEAF_2011
  uint16_t capacity_80 = (total_capacity_wh / 10) * 8; //for 2011
  //#endif //#ifdef LEAF_2011
  
  uint16_t temp2; //Temporary variable used in many functions 
  
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
  
  #ifdef MESSAGE_0x284
  case 0x284:
    // Upon reading VCM originating 0x284 every 20ms, send the missing message(s) to the inverter every 40ms
    ticker40ms++;
  
    if (ticker40ms > 1)
    {
      ticker40ms = 0;
      //send_can(battery_can_bus, ZE1_355_message); // 40ms
      buffer_send_can2(ZE1_355_message);// 40ms
    }
    break;
    #endif // #ifdef MESSAGE_0x284

  #ifdef MESSAGE_0x1DA
  case 0x1DA:
  if(NISSAN_ZE0_2011_2012())
  {
    seen_1da = 10;  //this variable is used to make the motor controller happy on shutdown
  }
  
  break;
  #endif //#ifdef MESSAGE_1DA

  #ifdef MESSAGE_0x1DB
  case 0x1DB:
    //battery_can_bus = can_bus; // Guarantees that messages go to right bus. Without this there is a risk that the messages get sent to VCM instead of HVBAT
  
  if(NISSAN_ZE0_2011_2012())
  {
    // seems like we just need to clear any faults and show permission
    if (VCM_WakeUpSleepCommand == 3)
    {          // VCM command: wakeup
      frame.data[3] = (frame.data[3] & 0xD7) | 0x28; // FRLYON=1, INTERLOCK=1
    }
  }

  if( NISSAN_AZE0_2013_2017() ) 
  {
    //Calculate the SOC% value to send to the dash (Battery sends 10-95% which needs to be rescaled to dash 0-100%)
    dash_soc = LB_MIN_SOC + (LB_MAX_SOC - LB_MIN_SOC) * (battery_soc_pptt - MINPERCENTAGE) / (MAXPERCENTAGE - MINPERCENTAGE); 
    if (dash_soc < 0)
    { //avoid underflow
        dash_soc = 0;
    }
    if (dash_soc > 1000)
    { //avoid overflow
        dash_soc = 1000;
    }
    dash_soc = (dash_soc/10);
    frame.data[4] = (uint8_t) dash_soc;  //If this is not written, soc% on dash will say "---"
  }
        
  calc_crc8(&frame);
  break;
  #endif //#ifdef MESSAGE_0x1DB
  //case 0x68C:
  //case 0x603:
   // charging_state = 0; //Reset charging state 
  //break;

  #ifdef MESSAGE_0x50B
  case 0x50B:
    VCM_WakeUpSleepCommand = (frame.data[3] & 0xC0) >> 6;
   
   if(NISSAN_ZE0_2011_2012())
   { 
    CANMASK = (frame.data[2] & 0x04) >> 2;
   }
   
    break;
    #endif //#ifdef MESSAGE_0x50B

  #ifdef MESSAGE_0x50C
  case 0x50C:
    ALU_question = frame.data[4];
        //send_can(battery_can_bus, ZE1_625_message); // 100ms
        //send_can(battery_can_bus, ZE1_5C5_message); // 100ms
        //send_can(battery_can_bus, ZE1_3B8_message); // 100ms
    buffer_send_can2(ZE1_625_message); // 100ms  
    buffer_send_can2(ZE1_5C5_message); // 100ms   
    buffer_send_can2(ZE1_3B8_message); // 100ms 
      
        content_3B8++;
        //This takes advantage of the modulus operator % to reset the value of content_3B8 to 0 once it reaches 15.
        //It also eliminates the need for an if statement and a conditional check, which improves performance (but sacrifices readability)
        if (content_3B8 > 14)
        {
            content_3B8 = 0;
        }
        
        ZE1_3B8_message.data[2] = content_3B8; // 0 - 14 (0x00 - 0x0E)

        if (flip_3B8)
        {
          flip_3B8 = 0;
          ZE1_3B8_message.data[1] = 0xC8;
        }
        else
        {
          flip_3B8 = 1;
          ZE1_3B8_message.data[1] = 0xE8;
        }

  break;
   #endif //#ifdef MESSAGE_0x50C

   #ifdef MESSAGE_0x55B
  case 0x55B:

        if( BATTERY_SWAP_ENABLED() )
        {
        if(ALU_question == 0xB2){
          frame.data[2] = 0xAA;
        } else {
          frame.data[2] = 0x55;
        }
        if(NISSAN_ZE0_2011_2012())
        {
        if(CANMASK == 0){
          frame.data[6] = (frame.data[6] & 0xCF) | 0x20;
        } else {
          frame.data[6] = (frame.data[6] & 0xCF) | 0x10;
               }
        }
        }
        

    battery_soc_pptt = ((frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6)); //Capture SOC% 0-100.0%
        main_battery_soc = (battery_soc_pptt / 10); // Capture SOC% 0-100
      
    calc_crc8(&frame);
  break;
  #endif //#ifdef MESSAGE_0x55B

  #ifdef MESSAGE_0x5BC
  case 0x5BC:     
        
    if( BATTERY_SWAP_ENABLED() )
    {
      //#ifdef LEAF_2011
      if( NISSAN_ZE0_2011_2012() )
      {
        temp = ((frame.data[4] & 0xFE) >> 1); // Collect SOH value
        if (frame.data[0] != 0xFF){
             // If everything is normal (no output power limit reason)
                        convert_array_to_5bc(&leaf_40kwh_5bc, (uint8_t *)&frame.data);
                        swap_5bc_remaining.LB_CAPR = leaf_40kwh_5bc.LB_CAPR;
                        swap_5bc_full.LB_CAPR = leaf_40kwh_5bc.LB_CAPR;
                        swap_5bc_remaining.LB_SOH = temp;
                        swap_5bc_full.LB_SOH = temp;
                        main_battery_temp = frame.data[3] / 20;
                        main_battery_temp = temp_lut[main_battery_temp] + 1;
          } else {
            //output power limited         
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
        if((frame.data[5] & 0x10) == 0x00){ //LB_MAXGIDS is 0, store actual GIDS remaining to this variable
                    GIDS = (uint16_t) ((frame.data[0] << 2) | ((frame.data[1] & 0xC0) >> 6));
                }
                //Avoid blinking GOM by always writing remaining GIDS
                frame.data[0] = (uint8_t)(GIDS >> 2);
                frame.data[1] = (GIDS << 6) & 0xC0;

         main_battery_temp = frame.data[3] / 20; //Temperature needed for charger section
         main_battery_temp = temp_lut[main_battery_temp] + 1; //write main_battery_temp to be used by 5C0 message
         
        //#endif //#ifdef LEAF_2014
      }
    
    //#endif //#ifdef BATTERY_SWAP        
   #endif // #ifdef MESSAGE_0x5BC    
  break;
  
  //#ifdef BATTERY_SWAP
  #ifdef MESSAGE_0x5C0
  case 0x5C0:
  //send_can(battery_can_bus, ZE1_5EC_message);//500ms
    buffer_send_can2(ZE1_5EC_message); // 500ms
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
  #endif //#ifdef MESSAGE_0x5C0
  
  #ifdef MESSAGE_0x1F2
  case 0x1F2:

    charging_state = frame.data[2];
        
    //#ifdef LEAF_2011
    if( NISSAN_ZE0_2011_2012() )
    {
        seconds_without_1f2 = 0; // Keep resetting this variable, vehicle is not turned off
      //#ifdef BATTERY_SWAP
      if( BATTERY_40KWH() || BATTERY_62KWH() )
      {
        if(seen_1da && charging_state == CHARGING_IDLE){ 
          frame.data[2] = 0;
          seen_1da--;
        }
      }
    }
  break;
    #endif //#ifdef MESSAGE_0x1F2

    #ifdef MESSAGE_0x59E
  case 0x59E:   // QC capacity message, adjust for AZE0 with 30/40/62kWh pack swaps
    frame.data[2] = 0x0E; //Set LB_Full_Capacity_for_QC to 23000Wh (default value for 24kWh LEAF)
    frame.data[3] = 0x60;
    
    //Calculate new LBC_QC_CapRemaining value
    temp2 = ((230 * main_battery_soc)/100); // Crazy advanced math
    frame.data[3] = (frame.data[3] & 0xF0) | ((temp2 >> 5) & 0xF); // store the new LBC_QC_CapRemaining
    frame.data[4] = ((temp2 & 0x1F) <<3) | (frame.data[4] & 0x07); // to the 59E message out to vehicle
    calc_crc8(&frame);
  break;
    #endif //#ifdef MESSAGE_0x59E

    #ifdef MESSAGE_0x68C
      case 0x68C:
     #endif// #ifdef MESSAGE_0x68C

     #ifdef MESSAGE_0x603
  case 0x603:
      //reset_state(); // Reset all states, vehicle is starting up
      //buffer_send_can1
      //send_can(battery_can_bus, swap_605_message); // Send these ZE1 messages towards battery
      //send_can(battery_can_bus, swap_607_message);
      charging_state = 0; //Reset charging state
      buffer_send_can2(swap_605_message); // Send these ZE1 messages towards battery
      buffer_send_can2(swap_607_message);
      
  break;
       #endif // #ifdef MESSAGE_0x603
    
    default:
      break;
  }


  #endif //#ifdef LEAF_TRANSLATION_ENABLED

  //——————————————————————————————————————————————————————————————————————————————
  // START OF BRUTEFORCE UPGRADE
/*  //——————————————————————————————————————————————————————————————————————————————
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
  
  #endif //#ifdef LEAF_BRUTEFORCE_UPGRADE */
  //——————————————————————————————————————————————————————————————————————————————
  // END OF BRUTEFORCE UPGRADE
  //——————————————————————————————————————————————————————————————————————————————

  //--- Gateway all messages except the unwanted IDs
  //if you enable CAN repeating between bus 1 and 2, we end up here 
  if(repeat_can){
    
    //you can blacklist certain messages or message contents like this, blocking them from both being forwarded and being displayed
    uint8_t blacklist = 0;
    #ifdef LEAF_BLACKLISTING_ENABLED 
  /*  switch(frame.can_id){       

    //--- Start of earlyversion.c
      
      #ifdef BATTERY_SWAP
      case 0x1DA:
        
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

    */
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
#endif// CAN_BRIDGE_FOR_LEAF
