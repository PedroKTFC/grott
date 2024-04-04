import select
import socket
import queue
import textwrap
##- import libscrc # new approach to calculatinng crc locally should mean no longer needed
import threading
import time
import http.server
import json, codecs 
from itertools import cycle
from io import BytesIO
from datetime import datetime
from urllib.parse import urlparse, parse_qs, parse_qsl  
from collections import defaultdict

# grottserver.py emulates the server.growatt.com website and is initial developed for debugging and testing grott.
# Updated: 2023-09-19
# Version:
verrel = "0.0.14e"

# Declare Variables (to be moved to config file later)
serverhost = "0.0.0.0"
serverport = 5781
httphost = "0.0.0.0"
httpport = 5782
verbose = False #True
verbput = False
verbget = False
verbreadreg = False
#firstping = False
sendseq = 1
#Time to sleep waiting on API response 
ResponseWaitInterval = 0.5
#Total time in seconds to wait on Iverter Response 
MaxInverterResponseWait = 10 
#Total time in seconds to wait on Datalogger Response 
MaxDataloggerResponseWait = 5

# Some constants to make code easier to read
InverterReadRegistersCommand = "05"
DataLoggerSendCommand = "19"
InverterWriteSingleRegisterCommand = "06"
InverterWriteMultiRegistersCommand = "10"

NoRetryRegisterReads = 5

# CRC table created at startup
crc_table = (
0x0000,0xc0c1,0xc181,0x0140,0xc301,0x03c0,0x0280,0xc241,
0xc601,0x06c0,0x0780,0xc741,0x0500,0xc5c1,0xc481,0x0440,
0xcc01,0x0cc0,0x0d80,0xcd41,0x0f00,0xcfc1,0xce81,0x0e40,
0x0a00,0xcac1,0xcb81,0x0b40,0xc901,0x09c0,0x0880,0xc841,
0xd801,0x18c0,0x1980,0xd941,0x1b00,0xdbc1,0xda81,0x1a40,
0x1e00,0xdec1,0xdf81,0x1f40,0xdd01,0x1dc0,0x1c80,0xdc41,
0x1400,0xd4c1,0xd581,0x1540,0xd701,0x17c0,0x1680,0xd641,
0xd201,0x12c0,0x1380,0xd341,0x1100,0xd1c1,0xd081,0x1040,
0xf001,0x30c0,0x3180,0xf141,0x3300,0xf3c1,0xf281,0x3240,
0x3600,0xf6c1,0xf781,0x3740,0xf501,0x35c0,0x3480,0xf441,
0x3c00,0xfcc1,0xfd81,0x3d40,0xff01,0x3fc0,0x3e80,0xfe41,
0xfa01,0x3ac0,0x3b80,0xfb41,0x3900,0xf9c1,0xf881,0x3840,
0x2800,0xe8c1,0xe981,0x2940,0xeb01,0x2bc0,0x2a80,0xea41,
0xee01,0x2ec0,0x2f80,0xef41,0x2d00,0xedc1,0xec81,0x2c40,
0xe401,0x24c0,0x2580,0xe541,0x2700,0xe7c1,0xe681,0x2640,
0x2200,0xe2c1,0xe381,0x2340,0xe101,0x21c0,0x2080,0xe041,
0xa001,0x60c0,0x6180,0xa141,0x6300,0xa3c1,0xa281,0x6240,
0x6600,0xa6c1,0xa781,0x6740,0xa501,0x65c0,0x6480,0xa441,
0x6c00,0xacc1,0xad81,0x6d40,0xaf01,0x6fc0,0x6e80,0xae41,
0xaa01,0x6ac0,0x6b80,0xab41,0x6900,0xa9c1,0xa881,0x6840,
0x7800,0xb8c1,0xb981,0x7940,0xbb01,0x7bc0,0x7a80,0xba41,
0xbe01,0x7ec0,0x7f80,0xbf41,0x7d00,0xbdc1,0xbc81,0x7c40,
0xb401,0x74c0,0x7580,0xb541,0x7700,0xb7c1,0xb681,0x7640,
0x7200,0xb2c1,0xb381,0x7340,0xb101,0x71c0,0x7080,0xb041,
0x5000,0x90c1,0x9181,0x5140,0x9301,0x53c0,0x5280,0x9241,
0x9601,0x56c0,0x5780,0x9741,0x5500,0x95c1,0x9481,0x5440,
0x9c01,0x5cc0,0x5d80,0x9d41,0x5f00,0x9fc1,0x9e81,0x5e40,
0x5a00,0x9ac1,0x9b81,0x5b40,0x9901,0x59c0,0x5880,0x9841,
0x8801,0x48c0,0x4980,0x8941,0x4b00,0x8bc1,0x8a81,0x4a40,
0x4e00,0x8ec1,0x8f81,0x4f40,0x8d01,0x4dc0,0x4c80,0x8c41,
0x4400,0x84c1,0x8581,0x4540,0x8701,0x47c0,0x4680,0x8641,
0x8201,0x42c0,0x4380,0x8341,0x4100,0x81c1,0x8081,0x4040,
)

# tables of registers to read (data logger and inverter registers need to be read slightly differently). See https://github.com/johanmeijer/grott/blob/Beta-(2.8.x)/documentatie/registers.md
datalogger_registers_table = (
{"register": 4, "name": "Interval", "description": "update interval, Ascii, e.g 5 or 1 or 0.5"},
{"register": 17, "name": "growatt_ip", "description": "Growatt server ip addres, Ascii, set for redirection to Grott e.g. 192.168.0.206"},
{"register": 18, "name": "growatt_port", "description": "Growatt server Port, Num, set for redirection to Grott e.g. 5279"},
{"register": 31, "name": "datetime", "description": "current date-time, Ascii, e.g 2022-05-17 21:01:50"}
)
inverter_registers_table = (
{"register": 1000, "name": "Float charge current limit", "description": "When charge current battery need is lower than this value, enter nto float charge", "value": "", "unit": "0.1", "initial": "600"},
{"register": 1044, "name": "Priority", "description": "ForceChrEn / ForceDischrEn Load first / Bat first / Grid first", "value": "0:Load (default) 1:Battery 2:Grid", "unit": "int", "initial": "0"},
{"register": 1060, "name": "BuckUpsFunEn", "description": "Ups function enable or disable", "value": "Enable: 1 Disable: 0", "unit": "int", "initial": ""},
{"register": 1061, "name": "BuckUPSVoltSet", "description": "UPS output voltage", "value": "0:230 1:208 2:240", "unit": "int", "initial": "230v"},
{"register": 1062, "name": "UPSFreqSet", "description": "UPS output frequency", "value": "0:50Hz 1:60Hz", "unit": "int", "initial": "50Hz"},
{"register": 1070, "name": "GridFirstDischargePowerRate", "description": "Discharge Power Rate when Grid First", "value": "0-100", "unit": "1%", "initial": ""},
{"register": 1071, "name": "GridFirstStopSOC", "description": "Stop Discharge soc when Grid First", "value": "0-100", "unit": "1%", "initial": ""},
{"register": 1080, "name": "Grid First Start Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1081, "name": "Grid First Stop Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1082, "name": "Grid First Stop Switch 1", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1083, "name": "Grid First Start Time 2", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1084, "name": "Grid First Stop Time 2", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1085, "name": "Grid First Stop Switch 2", "description": "Enable: 1 Disable: 0 ForceDischarge Switch&LCD_SET_FORCE_TRUE_2)==LCD_SET_FORCE_TRUE_2", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1086, "name": "Grid First Start Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1087, "name": "Grid First Stop Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1088, "name": "Grid First Stop Switch 3", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1090, "name": "Bat FirstPower Rate", "description": "Charge Power Rate when Bat First", "value": "0-100", "unit": "1%", "initial": ""},
{"register": 1091, "name": "Bat First stop SOC", "description": "Stop Charge soc when Bat First", "value": "0-100", "unit": "1%", "initial": ""},
{"register": 1092, "name": "AC charge Switch", "description": "When Bat First Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1100, "name": "Bat First Start Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1101, "name": "Bat First Stop Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1102, "name": "Bat First on/off Switch 1", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1103, "name": "Bat First Start Time 2", "description": "High eight bit: hour Low eight bit: minute",	"value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1104, "name": "Bat First Stop Time 2", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1105, "name": "Bat First on/off Switch 2", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1106, "name": "Bat First Start Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1107, "name": "Bat First Stop Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1108, "name": "Bat First on/off Switch 3", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1109, "name": "NoName", "description": "Load First Discharge Stopped Soc", "value": "0-100", "unit": "int", "initial": ""},
{"register": 1110, "name": "Load First Start Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1111, "name": "Load First Stop Time 1", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1112, "name": "Load First on/off Switch 1", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1113, "name": "Load First Start Time 2", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1114, "name": "Load First Stop Time 2", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1115, "name": "Load First on/off Switch 2", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""},
{"register": 1116, "name": "Load First Start Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1117, "name": "Load First Stop Time 3", "description": "High eight bit: hour Low eight bit: minute", "value": "0-23 0-59", "unit": "hextime", "initial": ""},
{"register": 1118, "name": "Load First on/off Switch 3", "description": "Enable: 1 Disable: 0", "value": "0 or 1", "unit": "int", "initial": ""}
)

# Formats multi-line data
def format_multi_line(prefix, string, size=80):
    size -= len(prefix)
    if isinstance(string, bytes):
        string = ''.join(r'\x{:02x}'.format(byte) for byte in string)
        if size % 2:
            size -= 1
    return '\n'.join([prefix + line for line in textwrap.wrap(string, size)])


# encrypt / decrypt data.
def decrypt(decdata):

    ndecdata = len(decdata)

    # Create mask and convert to hexadecimal
    mask = "Growatt"
    hex_mask = ['{:02x}'.format(ord(x)) for x in mask]
    nmask = len(hex_mask)

    # start decrypt routine
    unscrambled = list(decdata[0:8])  # take unscramble header

    for i, j in zip(range(0, ndecdata-8), cycle(range(0, nmask))):
        unscrambled = unscrambled + [decdata[i+8] ^ int(hex_mask[j], 16)]

    result_string = "".join("{:02x}".format(n) for n in unscrambled)

    ##print("\t - " + "Grott - data decrypted V2")
    return result_string

def validate_record(xdata): 
    # validata data record on length and CRC (for "05" and "06" records)
    
    data = bytes.fromhex(xdata)
    crc = 0
    ldata = len(data)
    len_orgpayload = int.from_bytes(data[4:6],"big")
    header = "".join("{:02x}".format(n) for n in data[0:8])
    protocol = header[6:8]

    if protocol in ("05","06"):
        lcrc = 4
        crc = int.from_bytes(data[ldata-2:ldata],"big")
    else: 
        lcrc = 0

    len_realpayload = (ldata*2 - 12 -lcrc) / 2

    if protocol != "02" :
        crc_calc = calculateCRC (data[0:ldata-2])

    if len_realpayload == len_orgpayload :
        returncc = 0
        if protocol != "02" and crc != crc_calc:     
            returncc = 8    
    else : 
        returncc = 8

    return(returncc)
    
def validate_inverter_time_register_value (check_register):
    for row in inverter_registers_table:
        if check_register == row["register"]:
            ## The register is valid but is it a time register?
            if row["unit"] == "hextime":
                found = True
            else:
                found = False
            break
    else: found = False
    return found
    
def validate_is_hex_time (check_value):
    ## Does the value integer convert to a two byte hex value where the high byte
    ## is in the range 0-23 and the low byte in the range 0-59
    high = (check_value >> 8) & 0xff
    low = check_value & 0xff
    if high in range (0,24) and low in range (0,60):
        passes = True
    else:
        passes = False
    return passes

def htmlsendresp(self, responserc, responseheader,  responsetxt) : 
        #send response
        self.send_response(responserc)
        self.send_header('Content-type', responseheader)
        self.end_headers()
        self.wfile.write(responsetxt.encode('UTF-8')) # encode so in main code only deal with strings
        if verbose: print("\t - Grotthttpserver - http response send: ", responserc, responseheader, responsetxt)

def createtimecommand(protocol,loggerid,sequenceno) : 
        protocol = protocol
        loggerid = loggerid 
        sequenceno = sequenceno
        bodybytes = loggerid.encode('utf-8')
        body = bodybytes.hex()
        if protocol == "06" :
            body = body + "0000000000000000000000000000000000000000"
        register = 31
        body = body + "{:04x}".format(int(register))
        currenttime = str(datetime.now().replace(microsecond=0))
        timex = currenttime.encode('utf-8').hex()
        timel = "{:04x}".format(int(len(timex)/2))
        body = body + timel + timex 
        #calculate length of payload = body/2 (str => bytes) + 2 bytes invertid + command. 
        bodylen = int(len(body)/2+2)
        
        #create header
        header = "0001" + "00" + protocol + "{:04x}".format(bodylen) + "0118"
        #print(header) 
        body = header + body 
        body = bytes.fromhex(body)
        if verbose: 
            print("\t - Grottserver - Time plain body : ")
            print(format_multi_line("\t\t ",body))

        if protocol != "02" :
            #encrypt message 
            body = decrypt(body) 
            crc16 = calculateCRC (bytes.fromhex(body))
            body = bytes.fromhex(body) + crc16.to_bytes(2, "big")
        
        if verbose:
            print("\t - Grottserver - Time command created :")
            print(format_multi_line("\t\t ",body))

        #just to be sure delete register info     
        try: 
            del commandresponse["18"]["001f"] 
        except: 
            pass 

        return(body)

def read_register (self, register, dataloggerid, sendcommand, inverterid=""):
    global sendseq
    
    bodybytes = dataloggerid.encode('utf-8')
    body = bodybytes.hex()

    if loggerreg[dataloggerid]["protocol"] == "06" :
        body = body + "0000000000000000000000000000000000000000"
    body = body + "{:04x}".format(int(register))
    #assumption now only 1 reg query; other put below end register
    body = body + "{:04x}".format(int(register))
    #calculate length of payload = body/2 (str => bytes) + 2 bytes invertid + command. 
    bodylen = int(len(body)/2+2)
    
    #device id for datalogger is by default "01" for inverter deviceid is inverterid!
    deviceid = "01"
    # test if it is inverter command and set 
    if sendcommand == InverterReadRegistersCommand:
        deviceid = (loggerreg[dataloggerid][inverterid]["inverterno"])

    header = "{:04x}".format(sendseq) + "00" + loggerreg[dataloggerid]["protocol"] + "{:04x}".format(bodylen) + deviceid + sendcommand
    sendseq += 1
    body = header + body 
    body = bytes.fromhex(body)

    if verbreadreg:
        print("\t - Grotthttpserver - unencrypted get command:")
        print(format_multi_line("\t\t ",body))

    if loggerreg[dataloggerid]["protocol"] != "02" :
        #encrypt message 
        body = decrypt(body) 
        crc16 = calculateCRC (bytes.fromhex(body))
        body = bytes.fromhex(body) + crc16.to_bytes(2, "big")

    # add header
    if verbreadreg:
        print("\t - Grotthttpserver: Get command created :")
        print(format_multi_line("\t\t ",body))

    # queue command 
    qname = loggerreg[dataloggerid]["ip"] + "_" + str(loggerreg[dataloggerid]["port"])

    # Message may get "lost" and no reply received so retry a few times
    i = 0
    while i < NoRetryRegisterReads:
        i += 1
        self.send_queuereg[qname].put(body) # Add message to queue 
        responseno = "{:04x}".format(sendseq)
        regkey = "{:04x}".format(int(register))
        try: 
            del commandresponse[sendcommand][regkey] 
        except: 
            pass 

        #wait for response
        #Set #retry waiting loop for datalogger or inverter 
        if sendcommand == InverterReadRegistersCommand :
           wait = round(MaxInverterResponseWait/ResponseWaitInterval)
        else :
            wait = round(MaxDataloggerResponseWait/ResponseWaitInterval)

        formatval = "dec"   # Default to dec. May need to provide a format for each register in register arrays?
        for x in range(wait):
            if verbreadreg: print("\t - Grotthttpserver - wait for GET response")
            try: 
                comresp = commandresponse[sendcommand][regkey]
                
                if sendcommand == InverterReadRegistersCommand :
                    if formatval == "dec" : 
                        comresp["value"] = str (int(comresp["value"],16))
                    elif formatval == "text" : 
                        comresp["value"] = codecs.decode(comresp["value"], "hex").decode('utf-8')
                responsetxt = comresp["value"]
                return responsetxt

            except  : 
                #wait and try again
                time.sleep(ResponseWaitInterval)
            
        try: 
            if comresp["value"] != "" : 
                responsetxt = comresp["value"]
                return responsetxt

        except : 
            continue
    return "-" # If no valid response is received return a -

def read_all_registers (self, first_register, last_register, dataloggerid, sendcommand, inverterid=""):
    global sendseq

    ## Reads all inverter registers from the provided first_register to the last_register
    
    bodybytes = dataloggerid.encode('utf-8')
    body = bodybytes.hex()

    if loggerreg[dataloggerid]["protocol"] == "06" :
        body = body + "0000000000000000000000000000000000000000"
    body = body + "{:04x}".format(int(first_register))
    body = body + "{:04x}".format(int(last_register))
    #calculate length of payload = body/2 (str => bytes) + 2 bytes invertid + command. 
    bodylen = int(len(body)/2+2)
    
    #device id for datalogger is by default "01" for inverter deviceid is inverterid!
    deviceid = "01"
    # test if it is inverter command and set 
    if sendcommand == InverterReadRegistersCommand:
        deviceid = (loggerreg[dataloggerid][inverterid]["inverterno"])

    header = "{:04x}".format(sendseq) + "00" + loggerreg[dataloggerid]["protocol"] + "{:04x}".format(bodylen) + deviceid + sendcommand
    sendseq += 1
    body = header + body 
    body = bytes.fromhex(body)

    if verbreadreg:
        print("Read all registers - unencrypted get command:")
        print(format_multi_line("\t ",body))

    if loggerreg[dataloggerid]["protocol"] != "02" :
        #encrypt message 
        body = decrypt(body) 
        crc16 = calculateCRC (bytes.fromhex(body))
        body = bytes.fromhex(body) + crc16.to_bytes(2, "big")

    if verbreadreg:
        print("Read all registers - Get command created :")
        print(format_multi_line("\t ",body))

    # queue command 
    qname = loggerreg[dataloggerid]["ip"] + "_" + str(loggerreg[dataloggerid]["port"])

    # Message may get "lost" and no reply received so retry a few times
    i = 0
    while i < NoRetryRegisterReads:
        i += 1
        self.send_queuereg[qname].put(body) # Add message to queue 
        responseno = "{:04x}".format(sendseq)
        regkey = "{:04x}".format(int(first_register))
        try: 
            del commandresponse[sendcommand][regkey] 
        except: 
            pass 

        #wait for response
        #Set #retry waiting loop for datalogger or inverter 
        if sendcommand == InverterReadRegistersCommand :
           wait = round(MaxInverterResponseWait/ResponseWaitInterval)
        else :
            wait = round(MaxDataloggerResponseWait/ResponseWaitInterval)

        formatval = "dec"   # Default to dec. May need to provide a format for each register in register arrays?
        for x in range(wait):
            if verbreadreg: print("Read all registers - wait for GET response")
            try: 
                comresp = commandresponse[sendcommand][regkey]
                
                if sendcommand == InverterReadRegistersCommand :
                    if formatval == "dec" : 
                        comresp["value"] = str (int(comresp["value"],16))
                    elif formatval == "text" : 
                        comresp["value"] = codecs.decode(comresp["value"], "hex").decode('utf-8')
                responsetxt = comresp["value"]
                return responsetxt

            except  : 
                #wait and try again
                time.sleep(ResponseWaitInterval)
            
        try: 
            if comresp["value"] != "" : 
                responsetxt = comresp["value"]
                return responsetxt

        except : 
            continue
    return "-" # If no valid response is received return a -
   
def hextime_to_string (s):
    # s is string representation of the 2 byte time value
    x = int(s)
    u = str((x >> 8) & 0xff).zfill(2) # Upper byte (fill to 2 digits as 1:5 looks odd!) (fill to 2 digits as 1:5 looks odd!)
    l = str(x & 0xff).zfill(2) # Lower byte (fill to 2 digits as 1:5 looks odd!)
    return u + ":" + l

class GrottHttpRequestHandler(http.server.BaseHTTPRequestHandler):
    def __init__(self, send_queuereg, *args):
        self.send_queuereg = send_queuereg
        super().__init__(*args)
    
    def do_GET(self):
        global sendseq

        try: 
            if verbget: print("\t - Grotthttpserver - Get received ")
            #parse url
            url = urlparse(self.path)
            urlquery = parse_qs(url.query)
            print ("Url is: ", self.path)
            
            if self.path == '/':
                self.path = "grott.html"

            #only allow files from current directory
            if self.path[0] == '/':
                self.path =self.path[1:len(self.path)]
                
            #if self.path.endswith(".html") or self.path.endswith(".ico"):
            if self.path == "grott.html" or self.path == "favicon.ico":
                try:
                    f = open(self.path, 'rb')
                    self.send_response(200)
                    if self.path.endswith(".ico") : 
                        self.send_header('Content-type', 'image/x-icon')
                    else: 
                        self.send_header('Content-type', 'text/html')
                    self.end_headers()
                    self.wfile.write(f.read())
                    f.close()
                    return
                except IOError:
                    responsetxt = b"<h2>Welcome to Grott the growatt inverter monitor</h2><br><h3>Made by Ledidobe, Johan Meijer</h3>"
                    responserc = 200 
                    responseheader = "text/html"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    return
                    
            elif self.path.startswith ("registers"):
                responsetxt = "<h2>List of register values:</h2>"
                responserc = 200 
                responseheader = "text/html"

                # Can only read data logger registers one at a time
                sendcommand = DataLoggerSendCommand
                # Add table header row
                responsetxt += "<h3>Data logger registers</h3><table border=\"1\"><tr><th>Reg</th><th>Reading</th><th>Name</th><th>Description</th></tr>"
                # Check passed inverter serial number is one we have
                # loggerreg typically contains: {'dataloggerSN': {'ip': '172.16.0.1', 'port': 49999, 'protocol': '06', 'inverterSN': {'inverterno': '01', 'power': 0}}}
                # There's only one data logger
                for dataloggerSN in loggerreg.keys():
                    for register in datalogger_registers_table:
                        register_value = read_register (self, register["register"], dataloggerSN, sendcommand)
                        responsetxt += "<tr><td>" + str(register["register"]) + "</td><td>" + register_value + "</td><td>" + register["name"] + "</td><td>" + register["description"] + "</td></tr>"
                responsetxt += "</table>"

                # Can read all inverter registers in one go
                sendcommand = InverterReadRegistersCommand
                #Add table header row
                responsetxt += "<h3>Inverter registers</h3><table border=\"1\"><tr><th>Reg</th><th>Reading</th><th>Name</th><th>Description</th><th>Value</th><th>Unit</th><th>Initial</th></tr>"
                # Check passed inverter serial number is one we have
                for dataloggerSN in loggerreg.keys():
                    list_of_keys = list(loggerreg[dataloggerSN].keys()) # Tortuous method of getting the inverter S/N as it's a key
                    inverterSN = list_of_keys[3]
                    result = read_all_registers (self, inverter_registers_table[0]['register'], inverter_registers_table[-1]['register'], dataloggerSN, InverterReadRegistersCommand, inverterSN)

                    for register in inverter_registers_table:
                        register_value = multi_regs_read[register["register"]]
                        register_value = str (int(register_value,16))

                        if register["unit"] == "hextime": register_value = hextime_to_string (register_value) # Convert two byte values to legible time
                        responsetxt += "<tr><td>" + str(register["register"]) + "</td><td>" + register_value + "</td><td>" + register["name"] + "</td><td>" + register["description"] + "</td><td>" + register["value"] + "</td><td>" + register["unit"] + "</td><td>" + register["initial"] + "</td></tr>"
                responsetxt += "</table><br>"
                htmlsendresp(self,responserc,responseheader,responsetxt)
                
            elif self.path.startswith("info"):
                    #retrieve grottserver status                 
                    if verbget: print("\t - Grotthttpserver - Status requested")
                    
                    
                    print("\t - Grottserver #active threads count: ", threading.active_count())
                    activethreads = threading.enumerate()
                    for idx, item in enumerate(activethreads):
                        print("\t - ", item)
                    
                    try: 
                        import os, psutil
                        #print(os.getpid())
                        print("\t - Grottserver memory in use : ", psutil.Process(os.getpid()).memory_info().rss/1024**2)   
                    
                    except: 
                        print("\t - Grottserver PSUTIL not available no process information can be printed")

                    #retrieve grottserver status               
                    print("\t - Grottserver connection queue : ")
                    print("\t - ", list(send_queuereg.keys()))
                    #responsetxt = json.dumps(list(send_queuereg.keys())).encode('utf-8') 
                    responsetxt = b"<h2>Grottserver info generated, see log for details</h2>" 
                    responserc = 200 
                    responseheader = "text/html"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    return

            elif self.path.startswith("datalogger") or self.path.startswith("inverter") :
                if self.path.startswith("datalogger"):
                    if verbget: print("\t - " + "Grotthttpserver - datalogger get received : ", urlquery)     
                    sendcommand = DataLoggerSendCommand
                else:
                    if verbget: print("\t - " + "Grotthttpserver - inverter get received : ", urlquery)     
                    sendcommand = InverterReadRegistersCommand
                
                #validcommand = False
                if urlquery == {} : 
                    #no command entered return loggerreg info:
                    responsetxt = json.dumps(loggerreg).encode('utf-8')
                    responserc = 200 
                    responseheader = "text/html"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    return
                
                else: 
                    
                    try: 
                        #is valid command specified? 
                        command = urlquery["command"][0] 
                        #print(command)
                        if command in ("register", "regall") :
                            if verbget: print("\t - " + "Grotthttpserver: get command: ", command)     
                        else :
                            #no valid command entered
                            responsetxt = 'no valid command entered'
                            responserc = 400 
                            responseheader = "text/html"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    except: 
                        responsetxt = 'no command entered'
                        responserc = 400 
                        responseheader = "text/html"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return

                    # test if datalogger  and / or inverter id is specified.
                    try:     
                        if sendcommand == InverterReadRegistersCommand : 
                            inverterid_found = False
                            try: 
                                #test if inverter id is specified and get loggerid 
                                inverterid = urlquery["inverter"][0] 
                                for key in loggerreg.keys() : 
                                    for key2 in loggerreg[key].keys() :   
                                        if key2 == inverterid :
                                            dataloggerid = key
                                            inverterid_found = True
                                            break 
                            except : 
                                inverterid_found = False
                        
                            if not inverterid_found : 
                                responsetxt = 'no or no valid invertid specified'
                                responserc = 400 
                                responseheader = "text/html"
                                htmlsendresp(self,responserc,responseheader,responsetxt)
                                return   

                            try: 
                                # is format keyword specified? (dec, text, hex)
                                formatval = urlquery["format"][0] 
                                if formatval not in ("dec", "hex","text") :
                                    responsetxt = 'invalid format specified'
                                    responserc = 400 
                                    responseheader = "text/body"
                                    htmlsendresp(self,responserc,responseheader,responsetxt)
                                    return
                            except: 
                                # no set default format op dec. 
                                formatval = "dec"
                            
                        if sendcommand == DataLoggerSendCommand : 
                            # if read datalogger info. 
                            dataloggerid = urlquery["datalogger"][0] 
                            
                            try: 
                                # Verify dataloggerid is specified
                                dataloggerid = urlquery["datalogger"][0] 
                                test = loggerreg[dataloggerid]
                            except:     
                                responsetxt = 'invalid datalogger id '
                                responserc = 400 
                                responseheader = "text/body"
                                htmlsendresp(self,responserc,responseheader,responsetxt)
                                return
                    except:     
                            # do not think we will come here 
                            responsetxt = 'no datalogger or inverterid specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return

                    # test if register is specified and set reg value. 
                    if command == "register":
                        #test if valid reg is applied
                        if int(urlquery["register"][0]) >= 0 and int(urlquery["register"][0]) < 4096 : 
                            register = urlquery["register"][0]
                        else: 
                            responsetxt = 'invalid reg value specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    elif command == "regall" :
                        comresp  = commandresponse[sendcommand]
                        responsetxt = json.dumps(comresp).encode('utf-8')
                        responserc = 200 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return
                        

                    else: 
                        responsetxt = 'command not defined or not available yet'
                        responserc = 400 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return
                        
                bodybytes = dataloggerid.encode('utf-8')
                body = bodybytes.hex()

                if loggerreg[dataloggerid]["protocol"] == "06" :
                    body = body + "0000000000000000000000000000000000000000"
                body = body + "{:04x}".format(int(register))
                #assumption now only 1 reg query; other put below end register
                body = body + "{:04x}".format(int(register))
                #calculate length of payload = body/2 (str => bytes) + 2 bytes invertid + command. 
                bodylen = int(len(body)/2+2)

                #device id for datalogger is by default "01" for inverter deviceid is inverterid!
                deviceid = "01"
                # test if it is inverter command and set 
                if sendcommand == InverterReadRegistersCommand:
                    deviceid = (loggerreg[dataloggerid][inverterid]["inverterno"])
                    print("\t - Grotthttpserver: selected deviceid :", deviceid)

                header = "{:04x}".format(sendseq) + "00" + loggerreg[dataloggerid]["protocol"] + "{:04x}".format(bodylen) + deviceid + sendcommand
                sendseq += 1
                body = header + body
                body = bytes.fromhex(body)

                if verbget:
                    print("\t - Grotthttpserver - unencrypted get command:")
                    print(format_multi_line("\t\t ",body))

                if loggerreg[dataloggerid]["protocol"] != "02" :
                    #encrypt message 
                    body = decrypt(body) 
                    crc16 = calculateCRC (bytes.fromhex(body))
                    body = bytes.fromhex(body) + crc16.to_bytes(2, "big")

                # add header
                if verbget:
                    print("\t - Grotthttpserver: Get command created :")
                    print(format_multi_line("\t\t ",body))

                # queue command 
                qname = loggerreg[dataloggerid]["ip"] + "_" + str(loggerreg[dataloggerid]["port"])
                self.send_queuereg[qname].put(body)
                responseno = "{:04x}".format(sendseq)
                regkey = "{:04x}".format(int(register))
                try: 
                    del commandresponse[sendcommand][regkey] 
                except: 
                    pass 

                
                #wait for response
                #Set #retry waiting loop for datalogger or inverter 
                if sendcommand == InverterReadRegistersCommand :
                    wait = round(MaxInverterResponseWait/ResponseWaitInterval)
                    #if verbget: print("\t - Grotthttpserver - wait Cycles:", wait )
                else :
                    wait = round(MaxDataloggerResponseWait/ResponseWaitInterval)
                    #if verbget: print("\t - Grotthttpserver - wait Cycles:", wait )

                for x in range(wait):
                    if verbget: print("\t - Grotthttpserver - wait for GET response")
                    try: 
                        comresp = commandresponse[sendcommand][regkey]
                        
                        if sendcommand == InverterReadRegistersCommand :
                            if formatval == "dec" : 
                                comresp["value"] = int(comresp["value"],16)
                            elif formatval == "text" : 
                                comresp["value"] = codecs.decode(comresp["value"], "hex").decode('utf-8')
                        responsetxt = json.dumps(comresp)
                        responserc = 200 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        if verbget: print("\t - Grotthttpserver: response success in wait loop:", responsetxt)
                        return

                    except  : 
                        #wait for second and try again
                         #Set retry waiting cycle time loop for datalogger or inverter 
                        
                        time.sleep(ResponseWaitInterval)
        
                try: 
                    if comresp != "" : 
                        responsetxt = json.dumps(comresp)
                        responserc = 200 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        if verbget: print("\t - Grotthttpserver: response success outside wait loop:", responsetxt)
                        return

                except : 
                    responsetxt = 'no or invalid response received'
                    responserc = 400 
                    responseheader = "text/body"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    if verbget: print("\t - Grotthttpserver: response failed :", responsetxt)
                    return
                
                responsetxt = 'OK'
                responserc = 200 
                responseheader = "text/body"
                if verbget: print("\t - " + "Grott: datalogger command response :", responserc, responsetxt, responseheader)     
                htmlsendresp(self,responserc,responseheader,responsetxt)
                return

            elif self.path == 'help':
                responserc = 200 
                responseheader = "text/body"
                responsetxt = 'No help available yet'
                htmlsendresp(self,responserc,responseheader,responsetxt)
                return
            else:
                self.send_error(400, "Bad request")
                if verbget: print("\t - Grotthttpserver: Bad request: ", self.path)
        
        except Exception as e:
            print("\t - Grottserver - exception in httpserver thread - get occured at line: ", e.__traceback__.tb_lineno, e)    

    def do_PUT(self):
        global sendseq

        try: 
            if verbput: print("\t - Grott: datalogger PUT received")
            print ("Url is: ", self.path)
            
            url = urlparse(self.path)
            urlquery = parse_qs(url.query)
            
            #only allow files from current directory
            if self.path[0] == '/':
                self.path =self.path[1:len(self.path)]
            
            if self.path.startswith("datalogger") or self.path.startswith("inverter") :
                if self.path.startswith("datalogger"):
                    if verbput: print("\t - Grotthttpserver - datalogger PUT received : ", urlquery)     
                    sendcommand = "18"
                else:
                    if verbput: print("\t - Grotthttpserver - inverter PUT received : ", urlquery)     
                    # Must be an inverter. Use 06 for now. May change to 10 later.
                    sendcommand = InverterWriteSingleRegisterCommand        
                
                if urlquery == "" : 
                    #no command entered return loggerreg info:
                    responsetxt = 'empty put received'
                    responserc = 400 
                    responseheader = "text/html"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    return
                
                else: 
                    
                    try: 
                        #is valid command specified? 
                        command = urlquery["command"][0] 
                        if command in ("register", "multiregister", "datetime") :
                            if verbput: print("\t - Grotthttpserver - PUT command: ", command)     
                        else :
                            responsetxt = 'no valid command entered'
                            responserc = 400 
                            responseheader = "text/html"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    except: 
                        responsetxt = 'no command entered'
                        responserc = 400 
                        responseheader = "text/html"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return

                    # test if datalogger  and / or inverter id is specified.
                    try:     
                        if sendcommand == InverterWriteSingleRegisterCommand: 
                            inverterid_found = False
                            try: 
                                #test if inverter id is specified and get loggerid 
                                inverterid = urlquery["inverter"][0] 
                                for key in loggerreg.keys() : 
                                    for key2 in loggerreg[key].keys() :   
                                        if key2 == inverterid :
                                            dataloggerid = key
                                            inverterid_found = True
                                            break 
                            except : 
                                inverterid_found = False
                        
                            if not inverterid_found : 
                                responsetxt = 'no or invalid invertid specified'
                                responserc = 400 
                                responseheader = "text/html"
                                htmlsendresp(self,responserc,responseheader,responsetxt)
                                return   
                            
                        if sendcommand == "18" : 
                            # if read datalogger info. 
                            dataloggerid = urlquery["datalogger"][0] 

                            try: 
                                # Verify dataloggerid is specified
                                dataloggerid = urlquery["datalogger"][0] 
                                test = loggerreg[dataloggerid]

                            except:     
                                responsetxt = 'invalid datalogger id '
                                responserc = 400 
                                responseheader = "text/body"
                                htmlsendresp(self,responserc,responseheader,responsetxt)
                                return
                    except:     
                            # do not think we will come here 
                            responsetxt = 'no datalogger or inverterid specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return

                    # test if register is specified and set reg value. 

                    if command == "register":
                        #test if valid reg is applied
                        if int(urlquery["register"][0]) >= 0 and int(urlquery["register"][0]) < 4096 : 
                            register = urlquery["register"][0]
                        else: 
                            responsetxt = 'invalid reg value specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    
                        try: 
                            value = urlquery["value"][0]
                        except: 
                            responsetxt = 'no value specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    
                        if value == "" : 
                            responsetxt = 'no value specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                    
                    elif command == "timeslot" :
                        # Switch to multiregister command
                        sendcommand = InverterWriteMultiRegistersCommand

                        # TODO: Too much copy/paste here. Refactor into methods.

                        ## The format of the command is:
                        ## //server:port/inverter?command=timeslot&startregister=STARTREG&inverter=INVERTER&starttime=STARTTIME&endtime=ENDTIME&enable=ENABLE
                        
                        ## Check for valid start register (next register must also be a time one). Pattern is [start, end, enable]
                        register_found = False
                        responsetxt = 'No start register specified'
                        try: 
                            start_register = urlquery["startregister"][0] 
                            responsetxt = 'Invalid start register specified (not hextime) ' + start_register
                            register_found = validate_inverter_time_register_value (int(start_register), True)
                        except : 
                            register_found = False
                        if not register_found : 
                            responserc = 400 
                            responseheader = "text/html"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                        if not validate_inverter_time_register_value (int(start_register)+1):
                            responsetxt = 'Start register not followed by a time register'
                            responserc = 400 
                            responseheader = "text/html"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return

                        # Check for start time
                        value_found = False
                        responsetxt = 'No start time specified'
                        try: 
                            start_time = urlquery["starttime"][0]
                            responsetxt = 'Start time not a valid time ' + start_time
                            value_found = validate_is_hex_time (int(start_time))
                        except:
                            value_found = False
                        if not value_found : 
                            responserc = 400
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                            
                        # Check for end time
                        value_found = False
                        responsetxt = 'No end time specified'
                        try: 
                            end_time = urlquery["endtime"][0]
                            responsetxt = 'End time not a valid time ' + end_time
                            value_found = validate_is_hex_time (int(end_time))
                        except:
                            value_found = False
                        if not value_found : 
                            responserc = 400
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                            
                        ## Times are valid but is end time later than start?
                        if int(end_time) < int(start_time):
                            responsetxt = 'Start time after end time'
                            responserc = 400 
                            responseheader = "text/html"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                            
                        ## Finally check enable/disable flag specified and is 0 or 1
                        value_found = False
                        responsetxt = 'No enable flag specified'
                        try: 
                            en_dis_able_flag = urlquery["enable"][0]
                            responsetxt = 'Enable flag not 0 or 1 ' + en_dis_able_flag
                            value_found = int(en_dis_able_flag) in (0,1)
                        except:
                            value_found = False
                        if not value_found : 
                            responserc = 400
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                            
                        # TODO: Check the value is the right length for the given start/end registers

                    elif command == "datetime" :
                        #process set datetime, only allowed for datalogger!!! 
                        if sendcommand == InverterWriteSingleRegisterCommand:
                            responsetxt = 'datetime command not allowed for inverter'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                        #prepare datetime 
                        register = 31
                        value = str(datetime.now().replace(microsecond=0))   

                    else: 
                        # Start additional command processing here,  to be created: translate command to register (from list>)
                        responsetxt = 'command not defined or not available yet'
                        responserc = 400 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return
                    
                    #test value:                
                    if sendcommand == InverterWriteSingleRegisterCommand : 
                        try: 
                            # is format keyword specified? (dec, text, hex)
                            formatval = urlquery["format"][0] 
                            if formatval not in ("dec", "hex","text") : 
                                responsetxt = 'invalid format specified'
                                responserc = 400 
                                responseheader = "text/body"
                                htmlsendresp(self,responserc,responseheader,responsetxt)
                                return
                        except: 
                            # no set default format op dec. 
                            formatval = "dec"
                        
                        #convert value if necessary 
                        if formatval == "dec" :
                            #input in dec (standard)
                            value = int(value)
                        elif formatval == "text" : 
                            #input in text
                            value = int(value.encode('utf-8').hex(),16) 
                        else : 
                            #input in Hex
                            value = int(value,16)

                        if value < 0 and value > 65535 : 
                            responsetxt = 'invalid value specified'
                            responserc = 400 
                            responseheader = "text/body"
                            htmlsendresp(self,responserc,responseheader,responsetxt)
                            return
                        
                # start creating command 

                bodybytes = dataloggerid.encode('utf-8')
                body = bodybytes.hex()

                if loggerreg[dataloggerid]["protocol"] == "06" :
                    body = body + "0000000000000000000000000000000000000000"
                
                if sendcommand == InverterWriteSingleRegisterCommand: 
                    value = "{:04x}".format(value)
                    valuelen = ""
                else:   
                    value = value.encode('utf-8').hex()
                    valuelen = int(len(value)/2)
                    valuelen = "{:04x}".format(valuelen) 

                if sendcommand == InverterWriteMultiRegistersCommand:
                    body = body + "{:04x}".format(int(start_register)) + "{:04x}".format(int(start_register)+2) + "{:04x}".format(int(start_time)) + "{:04x}".format(int(end_time)) + "{:04x}".format(int(en_dis_able_flag))
                else :
                    body = body + "{:04x}".format(int(register)) + valuelen + value

                bodylen = int(len(body)/2+2)          

                #device id for datalogger is by default "01" for inverter deviceid is inverterid!
                deviceid = "01"
                # test if it is inverter command and set deviceid
                if sendcommand in (InverterWriteSingleRegisterCommand,InverterWriteMultiRegistersCommand):
                    deviceid = (loggerreg[dataloggerid][inverterid]["inverterno"])
                print("\t - Grotthttpserver: selected deviceid :", deviceid)

                #create header
                header = "{:04x}".format(sendseq) + "00" + loggerreg[dataloggerid]["protocol"] + "{:04x}".format(bodylen) + deviceid + sendcommand
                sendseq += 1
                body = header + body
                body = bytes.fromhex(body)

                if verbput:
                    print("\t - Grotthttpserver - unencrypted put command:")
                    print(format_multi_line("\t\t ",body))
                
                if loggerreg[dataloggerid]["protocol"] != "02" :
                    #encrypt message 
                    body = decrypt(body) 
                    crc16 = calculateCRC (bytes.fromhex(body))
                    body = bytes.fromhex(body) + crc16.to_bytes(2, "big")

                # queue command 
                qname = loggerreg[dataloggerid]["ip"] + "_" + str(loggerreg[dataloggerid]["port"])
                self.send_queuereg[qname].put(body)
                responseno = "{:04x}".format(sendseq)
                if sendcommand == InverterWriteMultiRegistersCommand:
                    regkey = "{:04x}".format(int(start_register))# + "{:04x}".format(int(end_register))
                else :
                    regkey = "{:04x}".format(int(register))

                try: 
                    #delete response: be aware a 18 command give 19 response, 06 send command gives 06 response in different format! 
                    if sendcommand == "18" :
                        del commandresponse[sendcommand][regkey] 
                    else: 
                        del commandresponse[sendcommand][regkey] 
                except: 
                    pass 

                #wait for response
                #Set #retry waiting loop for datalogger or inverter 
                if sendcommand in (InverterWriteSingleRegisterCommand, InverterWriteMultiRegistersCommand):
                    wait = round(MaxInverterResponseWait/ResponseWaitInterval)
                    if verbput: print("\t - Grotthttpserver - wait Cycles:", wait )
                else :
                    wait = round(MaxDataloggerResponseWait/ResponseWaitInterval)
                    if verbput: print("\t - Grotthttpserver - wait Cycles:", wait )

                for x in range(wait):
                    if verbput: print("\t - Grotthttpserver - wait for PUT response")
                    try: 
                        #read response: be aware a 18 command give 19 response, 06 send command gives 06 response in differnt format! 
                        if sendcommand == "18" :
                            comresp = commandresponse["18"][regkey]
                        else: 
                            comresp = commandresponse[sendcommand][regkey]
                        if verbput: print("\t - " + "Grotthttperver - Commandresponse ", responseno, register, commandresponse[sendcommand][regkey]) 
                        break
                    except: 
                        #wait for second and try again
                        #Set retry waiting cycle time loop for datalogger or inverter 
                        time.sleep(ResponseWaitInterval)
                try: 
                    if comresp != "" : 
                        responsetxt = json.dumps(comresp) ##'OK'
                        responserc = 200 
                        responseheader = "text/body"
                        htmlsendresp(self,responserc,responseheader,responsetxt)
                        return

                except : 
                    responsetxt = 'No or invalid response received'
                    responserc = 400 
                    responseheader = "text/body"
                    htmlsendresp(self,responserc,responseheader,responsetxt)
                    return

                
                responsetxt = json.dumps(comresp) ##'OK'
                responserc = 200 
                responseheader = "text/body"
                if verbput: print("\t - " + "Grott: datalogger command response :", responserc, responsetxt, responseheader)     
                htmlsendresp(self,responserc,responseheader,responsetxt)
                return

        except Exception as e:
            print("\t - Grottserver - exception in httpserver thread - put occured at line: ", e.__traceback__.tb_lineno, e)    
        

class GrottHttpServer:
    """This wrapper will create an HTTP server where the handler has access to the send_queue"""

    def __init__(self, httphost, httpport, send_queuereg):
        def handler_factory(*args):
            """Using a function to create and return the handler, so we can provide our own argument (send_queue)"""
            return GrottHttpRequestHandler(send_queuereg, *args)

        self.server = http.server.HTTPServer((httphost, httpport), handler_factory)
        self.server.allow_reuse_address = True
        print(f"\t - GrottHttpserver - Ready to listen at: {httphost}:{httpport}")

    def run(self):
        print("\t - GrottHttpserver - server listening")
        print("\t - GrottHttpserver - Response interval wait time: ", ResponseWaitInterval)
        print("\t - GrottHttpserver - Datalogger ResponseWait: ", MaxDataloggerResponseWait)
        print("\t - GrottHttpserver - Inverter ResponseWait: ", MaxInverterResponseWait)
        self.server.serve_forever()


class sendrecvserver:
    def __init__(self, host, port, send_queuereg):   
        self.server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server.setblocking(0)
        self.server.bind((host, port))
        self.server.listen(5)

        self.inputs = [self.server]
        self.outputs = []
        self.send_queuereg = send_queuereg
        
        print(f"\t - Grottserver - Ready to listen at: {host}:{port}")

    def run(self):
        print("\t - Grottserver - server listening")
        while self.inputs:
            readable, writable, exceptional = select.select(
                self.inputs, self.outputs, self.inputs)

            for s in readable:
                self.handle_readable_socket(s)

            for s in writable:
                self.handle_writable_socket(s)

            for s in exceptional:
                self.handle_exceptional_socket(s)

    def handle_readable_socket(self, s):
        try:
            if s is self.server:
                self.handle_new_connection(s)
                if verbose: print("\t - " + "Grottserver - input received: ", self.server)
            else:
                # Existing connection
                try:
                    data = s.recv(1024)
                    
                    
                    test_data = decrypt(data)
                    print("Next read message: ", test_data)


                    if data:
                        self.process_data(s, data)
                    else:
                        # Empty read means connection is closed, perform cleanup
                        self.close_connection(s)
                #except ConnectionResetError:
                except:
                    self.close_connection(s) 
            
        except Exception as e:
            print("\t - Grottserver - exception in server thread - handle_readable_socket : ", e)
            #print("\t - socket: ",s)    


    def handle_writable_socket(self, s):
        try: 
            #with print statement no crash, without crash, does sleep solve this problem ? 
            time.sleep(0.1)
            
            if s.fileno() == -1 : 
                print("\t - Grottserver - socket closed")
                return
            try: 
                #try for debug 007
                client_address, client_port = s.getpeername()
            except: 
                print("\t - Grottserver - socket closed :")
                #print("\t\t ", s )
                #s.close
                pass

            try: 
                qname = client_address + "_" + str(client_port)
                next_msg = self.send_queuereg[qname].get_nowait()
                
                
                test_data = decrypt(next_msg)
                print("Next write message: ", test_data)


                if verbose:
                    print("\t - " + "Grottserver - get response from queue: ", qname + " msg: ")
                    print(format_multi_line("\t\t ",next_msg))
                s.send(next_msg)
                
            except queue.Empty:
                pass

        except Exception as e:
            print("\t - Grottserver - exception in server thread - handle_writable_socket : ", e)
            #print("\t\t ", s)
            #self.close_connection(s)
            #print(s)

    def handle_exceptional_socket(self, s):
        if verbose: print("\t - " + "Grottserver - Encountered an exception")
        self.close_connection(s)

    def handle_new_connection(self, s):
        try: 
            connection, client_address = s.accept()
            connection.setblocking(0)
            self.inputs.append(connection)
            self.outputs.append(connection)
            print(f"\t - Grottserver - Socket connection received from {client_address}")
            client_address, client_port = connection.getpeername()
            qname = client_address + "_" + str(client_port)

            #create queue
            send_queuereg[qname] = queue.Queue()
            #print(send_queuereg)
            if verbose: print(f"\t - Grottserver - Send queue created for : {qname}")
        except Exception as e:
            print("\t - Grottserver - exception in server thread - handle_new_connection : ", e) 
            #self.close_connection(s)   


    def close_connection(self, s):
        try: 
            #client_address, client_port = s.getpeername() 
            print("\t - Grottserver - Close connection : ", s)
            #print(client_address, client_port)
            if s in self.outputs:
                self.outputs.remove(s)
            self.inputs.remove(s)
            client_address, client_port = s.getpeername() 
            qname = client_address + "_" + str(client_port)
            del send_queuereg[qname]
            ### after this also clean the logger reg. To be implemented ? 
            for key in loggerreg.keys() : 
                #print(key, loggerreg[key])
                #print(key, loggerreg[key]["ip"], loggerreg[key]["port"])
                if loggerreg[key]["ip"] == client_address and loggerreg[key]["port"] == client_port :
                    del loggerreg[key] 
                    print("\t - Grottserver - config information deleted for datalogger and connected inverters : ", key)
                    # to be developed delete also register information for this datalogger (and  connected inverters).  Be aware this need redef of commandresp!
                    break     
            s.close()
        
        except Exception as e:
            print("\t - Grottserver - exception in server thread - close connection in line: ", e.__traceback__.tb_lineno, e)   
            #print("\t\t ", s )  

            # try: 
            #     s.close()
            # except:     
            #     print("\t - Grottserver - socket close error",s)

    def check_connections(self):
        #""" Check if the client(s) are/is still connected """
        for i, connection in enumerate(self.all_connections):
            print(self.all_connections)
            try:
                connection.send(b'PING')
                data = connection.recv(1024)
                if len(data) == 0:
                    del self.all_connections[i]
                    del self.all_addresses[i]
            except ConnectionError:
                del self.all_connections[i]
                del self.all_addresses[i]    

    def process_data(self, s, data):
        
        # Prevent generic errors: 
        try: 
        
            # process data and create response
            client_address, client_port = s.getpeername()
            qname = client_address + "_" + str(client_port)
            
            #V0.0.14: default response on record to none (ignore record)
            response = None

            # Display data
            print(f"\t - Grottserver - Data received from : {client_address}:{client_port}")
            if verbose:
                print("\t - " + "Grottserver - Original Data:")
                print(format_multi_line("\t\t ", data))
            
            #validate data (Length + CRC for 05/06)
            #join gebeurt nu meerdere keren! Stroomlijnen!!!! 
            vdata = "".join("{:02x}".format(n) for n in data)
            #validatecc = validate_record(vdata)
            validatecc = 0
            if validatecc != 0 : 
                print(f"\t - Grottserver - Invalid data record received, processing stopped for this record")
                #Create response if needed? 
                #self.send_queuereg[qname].put(response)
                return  

            # Create header
            header = "".join("{:02x}".format(n) for n in data[0:8])
            sequencenumber = header[0:4]
            protocol = header[6:8]
            #command = header[14:16]
            rectype = header[14:16]
            if protocol in ("05","06") :
                result_string = decrypt(data) 
            else :         
                result_string = "".join("{:02x}".format(n) for n in data)
            if verbose:
                print("\t - Grottserver - Plain record: ")
                print(format_multi_line("\t\t ", result_string))
            loggerid = result_string[16:36]
            loggerid = codecs.decode(loggerid, "hex").decode('utf-8') 

            # Prepare response
            if rectype in ("16"):
                # if ping send data as reply
                response = data
                if verbose:
                    print("\t - Grottserver - 16 - Ping response: ")
                    print(format_multi_line("\t\t ", response))
                
                    #v0.0.14a: create temporary also logger record at ping (to support shinelink without inverters)

                try:
                    loggerreg[loggerid].update({"ip" : client_address, "port" : client_port, "protocol" : header[6:8]})
                except: 
                    loggerreg[loggerid] = {"ip" : client_address, "port" : client_port, "protocol" : header[6:8]}
                    print("\t - Grottserver - Datalogger id added by Ping: ", loggerreg[loggerid] ) 
            

            #v0.0.14: remove "29" (no response will be sent for this record!)          
            elif rectype in ("03", "04", "50", "1b", "20"):
                # if datarecord send ack.
                print("\t - Grottserver - " + header[12:16] + " data record received")
                
                # create ack response
                if protocol == '02': ## Changed to use protocol, clearer!
                    #protocol 02, unencrypted ack
                    response = bytes.fromhex(header[0:8] + '0003' + header[12:16] + '00')
                else: 
                    # protocol 05/06, encrypted ack
                    headerackx = bytes.fromhex(header[0:8] + '0003' + header[12:16] + '47')
                    # Create CRC 16 Modbus
                    crc16 = calculateCRC (headerackx)
                    # create response
                    response = headerackx + crc16.to_bytes(2, "big")
                if verbose:
                    print("\t - Grottserver - Response: ")
                    print(format_multi_line("\t\t", response))

                if rectype in ("03") : 
                # init record register logger/inverter id (including sessionid?)
                # decrypt body. 
                    if protocol in ("05","06") : ## Changed to use protocol, clearer!
                        #print("header1 : ", header[6:8])
                        result_string = decrypt(data) 
                    else :         
                        result_string = data.hex()   
            
                    loggerid = result_string[16:36]
                    loggerid = codecs.decode(loggerid, "hex").decode('utf-8')
                    if protocol in ("02","05") : ## Changed to use protocol, clearer!
                        inverterid = result_string[36:56]
                    else : 
                        inverterid = result_string[76:96]
                    inverterid = codecs.decode(inverterid, "hex").decode('utf-8')

                    try:
                        loggerreg[loggerid].update({"ip" : client_address, "port" : client_port, "protocol" : header[6:8]})
                    except: 
                        loggerreg[loggerid] = {"ip" : client_address, "port" : client_port, "protocol" : header[6:8]}

                    #add invertid
                    loggerreg[loggerid].update({inverterid : {"inverterno" : header[12:14], "power" : 0}} ) 
                    #send response
                    self.send_queuereg[qname].put(response) 
                    #wait some time before response is processed 
                    time.sleep(1)
                    # Create time command en put on queue
                    response = createtimecommand(protocol,loggerid,"0001")
                    if verbose: print("\t - Grottserver 03 announce data record processed") 

            elif rectype in (DataLoggerSendCommand, InverterReadRegistersCommand, InverterWriteSingleRegisterCommand, InverterWriteMultiRegistersCommand, "18"):
                if verbose: print("\t - Grottserver - " + header[12:16] + " Command Response record received, no response needed")
                
                offset = 0
                if protocol in ("06") : 
                    offset = 40

                register = int(result_string[36+offset:40+offset],16)
                if rectype == InverterReadRegistersCommand: 
                    #value = result_string[40+offset:44+offset]
                    #v0.0.14: test if empty response is sent (this will give CRC code as values)
                    #print("length resultstring:", len(result_string))
                    #print("result starts on:", 48+offset) 
                    if len(result_string) == 48+offset :
                        if verbose: print("\t - Grottserver - empty register get response recieved, response ignored")  
                        value = ""
                    else: 
                        value = result_string[44+offset:48+offset]
                elif rectype == InverterWriteSingleRegisterCommand: 
                    result = result_string[40+offset:42+offset] 
                    #print("06 response result :", result)
                    value = result_string[42+offset:46+offset]      
                elif rectype == "18" : 
                    result = result_string[40+offset:42+offset] 
                elif rectype == InverterWriteMultiRegistersCommand:
                    ## For multi writes we only get a single byte status just before the crc (I think)
                    result = result_string[44+offset:46+offset]
                else : 
                    # "19" response take length into account    
                    valuelen = int(result_string[40+offset:44+offset],16)

                    #value = codecs.decode(result_string[44+offset:44+offset+valuelen*2], "hex").decode('utf-8') 
                    value = codecs.decode(result_string[44+offset:44+offset+valuelen*2], "hex").decode('ISO-8859-1')
                
                regkey = "{:04x}".format(register)
                if rectype == InverterWriteSingleRegisterCommand: 
                    # command 06 response has ack (result) + value. We will create a 06 response and a 05 response (for reg administration)
                    commandresponse[InverterWriteSingleRegisterCommand][regkey] = {"value" : value , "result" : result}                
                    commandresponse[InverterReadRegistersCommand][regkey] = {"value" : value}
                ## This was an if but I think it should be an elif as else below will overwrite line above
                elif rectype in (InverterWriteMultiRegistersCommand, "18"): ## was == "18" :
                    commandresponse[rectype][regkey] = {"result" : result}                
                else : 
                    #rectype 05 or 19 
                    commandresponse[rectype][regkey] = {"value" : value} 
                    print ("Response is: ", commandresponse[rectype][regkey])
                    
                    ## If there are multiple register values, build array
                    first_register = int(result_string[36+offset:40+offset],16)
                    last_register = int(result_string[40+offset:44+offset],16)
                    if rectype == "05" and first_register != last_register:
                        ## Build array
                        nr_values = last_register - first_register
                        i = 0
                        while i <= nr_values:
                            multi_regs_read[first_register + i] = result_string[44+offset+(i*4):48+offset+(i*4)]
                            i += 1
                        print ("All registers: ", multi_regs_read)
                            
                response = None

#            elif rectype in (InverterWriteMultiRegistersCommand):
#                if verbose: print("\t - Grottserver - " + header[12:16] + " #record received, no response needed")
#
#                startregister = int(result_string[76:80],16)
#                endregister = int(result_string[80:84],16)
#                value = result_string[84:86]
#                
#                regkey = "{:04x}".format(startregister) + "{:04x}".format(endregister)
#                commandresponse[rectype][regkey] = {"value" : value} 
#
#                response = None
            
            elif rectype in ("29") :
                if verbose: print("\t - Grottserver - " + header[12:16] + " record received, no response needed")
                response = None

            #elif rectype in ("99") :
                #placeholder for communicating from html server to sendrecv server
            #    if verbose: 
            #        print("\t - Grottserver - " + header[12:16] + " Internal Status request")
            #        print("\t - request     - ",  loggerid
            #    response = None

            else:
                if verbose: print("\t - Grottserver - Unknown record received:")
                    
                response = None

            if response is not None:
                #qname = client_address + "_" + str(client_port)
                if verbose:
                    print("\t - Grottserver - Put response on queue: ", qname, " msg: ")
                    print(format_multi_line("\t\t ", response))
                self.send_queuereg[qname].put(response) 
        except Exception as e:
            print("\t - Grottserver - exception in main server thread occured in line: ", e.__traceback__.tb_lineno, e)        

def calculateCRC (data):
    crc = 0xFFFF
    for data_byte in data:
        idx = crc_table[(crc ^ int(data_byte)) & 0xFF]
        crc = ((crc >> 8) & 0xFF) ^ idx
    return crc

if __name__ == "__main__":

    print("\t - Grottserver - Version: " + verrel)

    send_queuereg = {} 
    loggerreg = {}
    
    multi_regs_read = {}
    # response from command is written is this variable (for now flat, maybe dict later)
    commandresponse =  defaultdict(dict)

    http_server = GrottHttpServer(httphost, httpport, send_queuereg)
    device_server = sendrecvserver(serverhost, serverport, send_queuereg)

    http_server_thread = threading.Thread(target=http_server.run)
    device_server_thread = threading.Thread(target=device_server.run)

    http_server_thread.start()
    device_server_thread.start()

    while True:
       time.sleep(5)
