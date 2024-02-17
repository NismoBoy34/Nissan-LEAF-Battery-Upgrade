# Nissan-Leaf-Esp32-Can-Bridge 
# Author: Adam Saiyad (adamsaiyad@gmail.com) , Julius Calzada (julius.jai@gmail.com) Credit to @dalathegreat for his efforts and assistance this far 
An Arduino IDE based migration to Esp32 based off Muxsan/Dala MicroChip atmel can Bridge https://github.com/dalathegreat/Nissan-env200-Battery-Upgrade
Due to the Chip shortage and shortages of other components this library was created to offer a more accessible and attainable method to allow the can bridge to be produced .
It has been tested thorougly in the environment of a vehicle using an Esp32 Devkit and a made up mcp2525 board .
The Build includes a method of changing between EN200 and Nissan Leaf functions easily from the config.h file . (please ensure to select the correct vehicle before compiling )

Working and tested does translation on both Inverter and Battery code in a Stable manner .
Working list .
1. Translation works on Battery code tested on 30Kwh and 40Kwh and 62Kwh Batteries on the AZE0 leaf
2. Code works on the ze0 Leaf for the 40Kwh battery
3. Ota works and code updates for both Data and Code files
4. Charging adaptation was working needs work to get it working where a user can select which charge speed they want on AC charging .
5. Battery selection works 100% Via Webpage
6. Vehicle selection works 100% via webpage 

Issue list below needs input from the community to improve the project .
1. Fix Issue of enabling only one working section or portion of code for either battery or inverter and not both at the same time
2. Code needs a tidy its very messy
3. autodetect esp32 based chip to set canbus speed for 32u type Esp32 variants else canbus does not work correctly
4. Leafspy crashes and looses info when using the bridge both on bluetooth and wifi models of obd2 readers i think this is canbus overload issue ( too much polling happening )
5. Ac charging selection via web was working but not working now
6. add on features possibly a webpage to handle information tracking Charge current ? Voltage of pack ? Soc ? Can message display of what is flowing through the bridge in real time ?
7. 
