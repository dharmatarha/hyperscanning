# -*- coding: utf-8 -*-
"""
Created on Tue Jan 23 16:18:37 2018

New version of the JointStory script, rewritten for the Harvard - Dartmouth
connection. The earlier versions had a NAT traversal-related bug.

For argument options, type
$ python JointStory.py --help


----------------------------------------


LOGIC OF PROGRAM:

(1) System clocks of the control computers need to be synched before
experiment, either by using the same NTP servers or by synching to
GPS time signal. THIS PROGRAM DOES NOT DO THAT FOR YOU !

(2) Creates audio link between distant sites. First, it uses crude hole
punching for NAT traversal, then trasmits audio with dual UDP streams.
UDP packets are uncompressed audio data appended with timestamps

(3) Synchronizes task start on both control computers using timestamp
exchanges and a common start time derived from those timestamps

(4) Uses Psychopy for visual stimuli (task instructions + turn-taking
control) and keyboard events during the task.


---------------------------------------


IMPLEMENTATION NOTES:

- For audio, the script relies on pyAudio, so - in principle - it runs on
multiple OS (tested only on Ubuntu 16.04 and OS X 10.11 though)

- Current version handles TTLs in two different ways. First, it simply
records and timestamps keyboard inputs that equal a preset value -
this method supports scanner sites like Princeton and Harvard. Second,
it reads in triggers coming through a serial port, as at Dartmouth.
Edit the magic numbers section to adapt the settings.
The command line option --LOGTTL controls only the second option, as
that is the more complex, using a separate subprocess, while the other
only consists of catching key presses

- Audio transmission is via UDP streams. Prepare for a few lost
packages. To account for fluctuations in travel time / losses, the
program uses a simple two-ended continuous audio buffer, with only
occasional health reports. Nothing adaptive about it. The audio chunk
and buffer size can be controlled with command line options --CHUNK and
--BUFFER

- Synching start across computers is done using a third UDP socket-pair.

- Capable of simple NAT traversal (UDP hole punching), works with one,
but not with two firewalls, so a static IP is required at least on one
end if NATs are present

- Includes a wrapper around stunclient for exploring current NAT properties,
controlled with input option --STUN

- Uses PsychoPy for controlling visuals, as a result it works on python
2.7 atm. Damn PsychoPy is still only talking about migrating.

- Hardcoded variables are all in the magicNumbers function. If you need
to set some parameter, that's where you look.

- Has a built-in re-tell part at the end of the trial. That is,
after the channel is closed, participants are prompted to retell the
story/stories.

- A bunch of command line options are for selecting the type of trial.
--TRIALTYPE sets joint/individual condition for the story (trial)
--WHICHSEED controls the story prompt subjects receive
--ROLE sets who starts the story (trial)


---------------------------------------


TO IMPROVE:

- Correct file handling, based on input arguments of pair and condition number.
Right now it simply saves everything into the working directory and file names
do not contain any identifier (e.g. date, pair number, etc)

- Saving a separate settings file with all variables used for that run?

- Re-tell is very hacky. We keep sending the packets even after audio output is
shut off at both ends. It works fine, but is painfully stupid. Instead, we
should probably close the audio input stream at the end of the story and open
it again for re-tell with a simpler callback function.

- Use psychopy's core.Clock with getLastResetTime to capture its start,
then use event.getKeys with timeStamped argument set to the core.Clock,
this ensures very precise timing info both on visual events and key presses /
ttls



@author: adamb
"""


#%% Imports

# imports providing backward compatibility to 2.7
from __future__ import print_function
from __future__ import division
from __future__ import unicode_literals
from builtins import range
from builtins import map
from builtins import bytes
from io import open
# imports we would have anyways
import argparse
import socket
import pyaudio
import sys
import time
import struct
import subprocess
import re
import wave
from operator import sub
import csv
import multiprocessing
import serial


#%% Python 2.7 / 3 compatibility parts
# get python 3 flush arg behavior on 2.7 for print function
if sys.version_info[:2] < (3, 3):
    old_print = print

    def print(*args, **kwargs):
        flush = kwargs.pop('flush', False)
        old_print(*args, **kwargs)
        file = kwargs.get('file', sys.stdout)
        if flush and file is not None:
            file.flush()
# get python 3 user input behavior
if hasattr(__builtins__, 'raw_input'):
    input = raw_input


#%% MAGIC NUMBERS aka hardcoded variables, default values
def magicNumbers(ROLE, TRIALTYPE, WHICHSEED):
    # UDP hole punch timeout (time for handshake), in seconds
    punchTimeout = 30
    # default audio settings: mono, 16kHz sampling, 16bit encoding
    CHANNELS = 1
    RATE = 16000
    FORMAT = pyaudio.paInt16
    # default filenames (for saving audio)
    savefileOut = 'RecordedAudio'
    savefileIn1 = 'ReceivedAudio'
    savefileIn2 = 'PlayedAudio'
    savefileLog = 'TimingsLog.txt'
    savefileTTL = 'TTLtimestamps.txt'
    # default port numbers
    # local
    portIn = 30002
    portOut = 30001
    # remote
    PortIn = 30002
    PortOut = 30001
    PortComm = 30003

    # serial settings dictionary
    serialSettings = {
        'mount': '/dev/ttyUSB0',  # on ubuntu this works well
        'baud': 115200,
        'timeout': 0   # non-blocking; returns upon receiving 8 bits
        }

    # Settings for the visual and storytelling/retell part, incl text
    # time for each countdown (turn)
    turntime = 30
    # start counter for countdown
    timeDiff = 0
    # number of turns
    turnN = 30
    # start counter for turns
    turnCurrent = 1
    # letter size
    letterH = 0.06
    # time for showing sintructions at the beginning
    instTime = 30
    # time variable for start synch in seconds
    startLag = 10
    # time for re-tell in seconds
    retellLength = 300
    # instructions to be displayed in the beginning, depending on trial type
    if TRIALTYPE == 0:
        instText1 = ('Your task is to build a story together with '
                     'the other participant.\n\n'
                     'You will take turns in doing so. Each turn lasts ' +
                     str(turntime) + ' seconds and there will be ' +
                     str(turnN) + ' turns, so you will have ' +
                     '{0:.0f}'.format(turntime*turnN/60) + ' minutes for the' +
                     ' whole story.\n'
                     'There will be a timer on the display showing the time '
                     'left from the current turn. In the lower part you will '
                     'also see the current turn number. \n'
                     'You may take the story into any direction you want, but '
                     'build upon the contributions of the other participant. '
                     'Ideally, the story should sound as one story-line, '
                     'your contributions should be hard to tell apart from '
                     'those coming from your partner. \n')
    elif TRIALTYPE == 1:
        instText1 = ('Your task is to build a story alone, '
                     'independent from the other participant.\n\n'
                     'You will take turns in creating your own stories. '
                     'Each turn lasts ' + str(turntime) + ' seconds and ' +
                     'there will be ' + str(turnN) + ' turns, so you will ' +
                     'have ' + '{0:.0f}'.format(turntime*turnN/60) +
                     ' minutes for the whole story.\n'
                     'There will be a timer on the display showing the time '
                     'left from the current turn. In the lower part you will '
                     'also see the current turn number. \n'
                     'Remember, you build your own story now, '
                     'you do not have to take anything from the other '
                     'story into account. '
                     'Ideally, at the end we will have two separate stories '
                     'built around the same topic. \n'
                     'Nevertheless, pay attention to the other story as well, '
                     'make sure to follow it.')
    # story topic intructions, depending on which seed is set
    if WHICHSEED == 0:
        instText2 = ('For this trial, create a story about a group of '
                     'students having first contact with aliens.')
    elif WHICHSEED == 1:
        instText2 = ('For this trial, create a story about a child, '
                     'who somehow becomes the President of the USA.')
    elif WHICHSEED == 2:
        instText2 = ('For this trial, create a story about a family, '
                     'where the child gets into trouble.')
    elif WHICHSEED == 3:
        instText2 = ('For this trial, create a story about someone '
                     'finding a genie lamp')
    elif WHICHSEED == 4:
        instText2 = ('For this trial, create a story about a grad student '
                     'having a very unusual day')
    # text for the start sequence
    instText3 = 'We start in '
    # turn texts, dependent on the role set in input args
    if ROLE == 0:
        turnText1 = 'YOUR turn. Go on with the story!'
        turnText2 = 'NOT your turn. Listen to your partner!'
    elif ROLE == 1:
        turnText2 = 'YOUR turn. Go on with the story!'
        turnText1 = 'NOT your turn. Listen to your partner!'
    # text for the end screen
    retellText1a = ('Time is up. In the next part of the this trial your task '
                    'is to retell the story you created with your partner.'
                    '\n\nYou will have ' + '{0:.0f}'.format(retellLength/60) +
                    ' minutes to do so. Do not go for a '
                    'word-by-word reconstruction, but try to include '
                    'every detail you can, we are interested in how well '
                    'you remember the story.\n'
                    'During retell, a timer will show how much time you have '
                    'left. Try to use the whole ' +
                    '{0:.0f}'.format(retellLength/60) + ' minutes.'
                    )
    retellText1b = ('Time is up. In the next part of the this trial your task '
                    'is to retell both stories that you and your partner '
                    'created. Please start with your partner\'s story.'
                    '\n\nFor each story, you will have ' +
                    '{0:.1f}'.format(retellLength/60/2) +
                    ' minutes for retell. Do not go for '
                    'a word-by-word reconstruction, but try to include '
                    'every detail you can, we are interested in how well '
                    'you remember the story.\n'
                    'During retell, a timer will show first how much time you '
                    'have left for retelling the other\'s story. Then it will '
                    'switch to showing how much time you have left for '
                    'retelling your story. Try to use the whole ' +
                    '{0:.1f}'.format(retellLength/60/2) + ' minutes for both '
                    'stories.'
                    )
    retellText2a = ('Start retelling the story.')
    retellText2b = ('Start retelling your partner\'s story.')
    retellText2c = ('Start retelling your story.')

    # keys to check at various times
    keylist = ['s', '5', 'escape','ó']

    return(punchTimeout, CHANNELS, RATE, FORMAT, savefileOut,
           savefileIn1, savefileIn2, savefileLog, savefileTTL, portIn, portOut,
           PortIn, PortOut, PortComm, serialSettings, turntime, timeDiff,
           instText1, instText2, instText3, turnText1, turnText2, retellText1a,
           retellText1b, retellText2a, retellText2b, retellText2c, turnN,
           turnCurrent, letterH, instTime,
           startLag, retellLength, keylist)


#%% Function for recording ttl signals at DBIC
# Important details:
# (1) we expect TTLs to arrive through a serial-to-usb adapter
# (2) defined mount point is for Ubuntu at DBIC, WILL BE DIFFERENT! on other OS
def serialLog(serialSettings, queueTTL):
    # open the serial object
    s = serial.Serial(
        serialSettings['mount'],
        serialSettings['baud'],
        timeout=serialSettings['timeout']
    )
    s.flushInput()
    # local timing variables
    start_time_serial = time.time()
    time_now_serial = time.time()
    prev_time_serial = 0

    with open('SerialTTL_log.txt', 'w') as logfile:
        print('{0} {1}'.format('start time:', start_time_serial), file=logfile)
        print('time,delta', file=logfile)
        counter = 0
        while True:
            # if escape key was pressed, and signal is sent through queue,
            # terminate
            if not queueTTL.empty():
                break
            # otherwise just read out serial port
            s_in = s.read()
            if s_in != '':
                counter += 1
                time_now_serial = time.time() - start_time_serial
                delta = time_now_serial - prev_time_serial
                prev_time_serial = time_now_serial
                print('{0},{1},{2}'.format(time_now_serial, delta, counter),
                      file=logfile)
    return


#%% STUN query function
# Wrapper around the really cool stunclient tool. When STUN arg is set to 1,
# we just call it in a subprocess and capture some of its output.
# Strictly speaking, this function is not needed for the script to work, it is
# included here for NAT diagnostic purposes.

def stunQuery():
    # list of a few servers to try
    serverList = [
                'stun.ekiga.net',
                'stun.xten.com',
                'stun.ideasip.com',
                'stun.wtfismyip.com'
                ]

    # try servers until we get a successful test,
    # write output to terminal (NAT behavior type, internal and mapped
    # addressses, etc)
    stunFlag = False
    for i in serverList:
        print('Trying stun server ', i, '...')
        try:
            stunOutput = subprocess.check_output(
                        ['stunclient', '--mode', 'full', i],
                        universal_newlines=True)
            if bool(re.search('Behavior test: success', stunOutput)):
                for lines in stunOutput.splitlines():
                    print(lines)
                stunFlag = True
                break
        except:
            print('Stun query failed...')
    # if all queries fail, we have a problem Houston
    if not stunFlag:
        print('All stun queries failed, no successful NAT behavior test')
    return stunFlag


#%% Socket function
# Opens simple UDP socket, binds it to given port number at localhost.

def openSocket(port):
    socketFlag = False
    # define socket
    try:
        socketUDP = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        print('\nSocket created')
    except socket.error:
        print('\nFailed to create UDP socket')
    # bind port
    host = ''  # localhost
    try:
        socketUDP.bind((host, port))
        print('\nUDP socket bound to local port: ', port)
        socketFlag = True
    except socket.error:
        print('\nFailed to bind UDP socket to local port ', port)
    return socketFlag, socketUDP


#%% Hole punch function
# Remember, we assumed that there is one side behind NAT. That side
# needs to initiate UDP hole punching (NAT traversal). This function
# handles UDP hole punching in eiher case, for both in- and outgoing
# communication

def punchThrough(NAT, socketIn, socketOut, socketComm, punchTimeout):

    global IP, PortIn, PortOut, PortComm
    # if other side is behind NAT, script just waits for connection,
    # both for socketIn and socketOut
    if NAT == 0:
        print('\n\nWaiting for other end to initiate handshake...\n')
        start = time.time()
        recFlag = False
        # for this part, socket is non-blocking with a timeout
        socketIn.settimeout(1)
        socketOut.settimeout(1)
        socketComm.settimeout(1)
        # until there is incoming message or max time is up
        while (not recFlag) & (abs(time.time()-start) < punchTimeout):
            try:
                incomingIn, addressIn = socketIn.recvfrom(1024)
                incomingOut, addressOut = socketOut.recvfrom(1024)
                incomingComm, addressComm = socketComm.recvfrom(1024)
                # if we have incoming message "szevasz"
                if (bool(incomingIn == 'szevasz'.encode()) &
                    bool(incomingOut == 'szevasz'.encode()) &
                    bool(incomingComm == 'szevasz'.encode()) &
                        bool(addressIn[0] == addressOut[0])):
                        print('\nHandshake initiated from ', addressIn[0], ':',
                              addressIn[1], ' and :', addressOut[1])
                        IP = addressIn[0]

                        # NEW PART, SETTING REMOTE PORTS ACCORDING TO 
                        # ADDRESS OF INCOMING PACKETS
                        PortOut = addressIn[1]
                        PortIn = addressOut[1]
                        PortComm = addressComm[1]
                        print('\nRemote ports are',
                              PortIn, PortOut, PortComm, '\n')

                        recFlag = True
            except:
                print('No handshake message yet...', end='\r', flush=True)
        # if time is over
        if not recFlag:
            IP = []
            return recFlag

        # send answer, wait until handshake is confirmed
        print('\nResponding...\n')
        recFlag = False
        start = time.time()
        # send answer and listen to next message, until time is up
        while (not recFlag) & (abs(time.time()-start) < punchTimeout):
            try:
                socketIn.sendto('helloszia'.encode(), (IP, PortOut))
                socketOut.sendto('helloszia'.encode(), (IP, PortIn))
                socketComm.sendto('helloszia'.encode(), (IP, PortComm))
            except:
                print('\n\nCould not send "helloszia" packet to ', IP)
            # see if there was answer
            try:
                incomingIn, addressIn = socketIn.recvfrom(1024)
                incomingOut, addressOut = socketOut.recvfrom(1024)
                incomingComm, addressComm = socketComm.recvfrom(1024)
                if (bool(incomingIn == 'kuldj egy jelet'.encode()) &
                   bool(addressIn[0] == IP) &
                   bool(incomingOut == 'kuldj egy jelet'.encode()) &
                   bool(addressOut[0] == IP) &
                   bool(incomingComm == 'kuldj egy jelet'.encode()) &
                   bool(addressComm[0] == IP)):
                    print('\nHandshake confirmed, other end is ready\n')
                    recFlag = True
            except:
                print('No confirmation yet', end='\r', flush=True)
        # if there was no asnwer in the maximum allowed time
        if not recFlag:
            IP = []

    # if other end is behind NAT, it initiates hole punching. We assume
    # current side to be reachable via public IP and given port
    if NAT == 1:
        # actual handshake part
        print('\n\nInitiating handshake...\n')
        start = time.time()
        recFlag = False
        # for this part, socket is non-blocking with a timeout
        socketIn.settimeout(1)
        socketOut.settimeout(1)
        socketComm.settimeout(1)
        # send handshake and listen for answer until time is up
        # when sending, make sure to "cross" the in and out ports between
        # local and remote
        print('\nSending handshake message "szevasz"...\n')
        while (not recFlag) & (abs(time.time()-start) < punchTimeout):
            try:
                socketIn.sendto('szevasz'.encode(), (IP, PortOut))
                socketOut.sendto('szevasz'.encode(), (IP, PortIn))
                socketComm.sendto('szevasz'.encode(), (IP, PortComm))
            except:
                print('\n\nCould not send "szevasz" packet to ', IP,)
            # see if there was answer
            try:
                incomingIn, addressIn = socketIn.recvfrom(1024)
                incomingOut, addressOut = socketOut.recvfrom(1024)
                incomingComm, addressComm = socketComm.recvfrom(1024)
                if (bool(incomingIn == 'helloszia'.encode()) &
                   bool(addressIn[0] == IP) &
                   bool(incomingOut == 'helloszia'.encode()) &
                   bool(addressOut[0] == IP) &
                   bool(incomingComm == 'helloszia'.encode()) &
                   bool(addressComm[0] == IP)):
                    print('\nReceived answer, handshake confirmed\n')
                recFlag = True
            except:
                print('No proper answer yet', end='\r', flush=True)
        # if time is over
        if not recFlag:
            return recFlag

        # if handshake was successful, send a signal asking for audio
        if recFlag:
            # repeat final message a few times
            # "cross" in and out ports across machines again
            for i in range(5):
                socketIn.sendto('kuldj egy jelet'.encode(),
                                (IP, PortOut))
                socketOut.sendto('kuldj egy jelet'.encode(),
                                 (IP, PortIn))
                socketComm.sendto('kuldj egy jelet'.encode(),
                                  (IP, PortComm))
            print('\nUDP hole punched, we are happy and shiny\n')

    # flush the sockets before we go on
    start = time.time()
    while abs(start-time.time()) < 1:
        try:
            incomingIn = socketIn.recv(1024)
            incomingOut = socketOut.recv(1024)
            incomingComm = socketComm.recv(1024)
        except:
            pass
    return recFlag


#%% Callback function fro non-blocking pyaudio (portaudio) input
# Important!! We put everything that is to be done with the data into
# the callback function. Specifically, callback saves input audio,
# handles timestamps, counters and sends UDP packets.

# Expects output file to be open and ready for writing.
# Expects UDP socket and connection to server ready.
# Expects packetCounter to be set up.

def callbackInput(in_data, frame_count, time_info, status):
    # keep track of chunks
    global chunkCounter
    # refresh counter
    chunkCounter += 1
    # following line changed for python 2.7
    bytepacket = struct.pack('<l', chunkCounter)
    # write out new data before we mess with it
    fOut.write(in_data)
    # create bytearray from the audio chunk, so we can expand it
    dataArray = bytearray(in_data)
    # append data with timestamp and packetCounter
    timestamp = time.time()
    bytestamp = struct.pack('<d', timestamp)  # convert float into bytes
    # extend dataArray, get final packet to send
    dataArray.extend(bytepacket)
    dataArray.extend(bytestamp)
    in_data = bytes(dataArray)
    # send new data to other side
    try:
        socketOut.sendto(in_data, (IP, PortIn))
    except socket.error:
        print('Failed to send packet, chunkCounter = '+str(chunkCounter))
    # display progress
    if chunkCounter % 250 == 0:
        print('Chunk no ', chunkCounter, 'sent successfully\n')
    # return data and flag
    return (in_data, pyaudio.paContinue)


#%% Callback function for non-blocking pyaudio (portaudio) output.

# In this version, we use a simple continuous buffer that collects
# all incoming packets on one end and is read out by the callback on the other.
# Important!!
# Expects output files to be open and ready for writing.
# Expects UDP socket and connection to server ready.
# Expects all four counters + changeFlag to be set up.
def callbackOutput(in_data, frame_count, time_info, status):
    global lastData, underFlowFlag
    # once the buffer is filled for the first time, startFlag is set and
    # callback can read from it
    if startFlag:
        # first check if there is enough data available to read
        if len(audioBuffer) > CHUNK*2:
            data = audioBuffer[0:CHUNK*2]
            del audioBuffer[0:CHUNK*2]
            lastData = data
        # if buffer is empty, update the underflow counter
        else:
            data = lastData
            underFlowFlag += 1

    # until startFlag is set, callback reads from a silence buffer (zeros)
    else:
        if len(silenceBuffer) > CHUNK*2:
            data = silenceBuffer[0:CHUNK*2]
            del silenceBuffer[0:CHUNK*2]
            lastData = data
        else:
            data = lastData

    data = bytes(data)
    fIn2.write(data)
    return data, pyaudio.paContinue


#%% Function to set up mic
# Uses pyaudio (portaudio) for a non-blocking input device.
# Device is default input set on platform.

def micOpen(FORMAT, CHANNELS, RATE, CHUNK):
    p = pyaudio.PyAudio()
    stream = p.open(format=FORMAT,
                    channels=CHANNELS,
                    rate=RATE,
                    input=True,
                    frames_per_buffer=CHUNK,
                    stream_callback=callbackInput,
                    start=False)  # IMPORTANT: don't start yet
    return stream, p


#%% Function to open output device
# Uses pyaudio (portaudio). Chooses default output device on platform.

def speakersOpen(FORMAT, CHANNELS, RATE, CHUNK):
    # open pyaudio (portaudio) device
    p = pyaudio.PyAudio()
    # open portaudio output stream
    stream = p.open(format=FORMAT,
                    channels=CHANNELS,
                    rate=RATE,
                    output=True,
                    frames_per_buffer=CHUNK,
                    stream_callback=callbackOutput,
                    start=False)  # IMPORTANT: don't start yet
    return stream, p


#%% Function to strip packetCounter and client timestamp from UDP packets
# the last 8 bytes is the timestamp, the 4 before that is the packetNumber

def packetParser(dataIn):
    dataArray = bytearray(dataIn)
    audio = dataArray[0:len(dataIn)-12]
    # using struct unpack to stay compatible with 2.7
    packetNumber = struct.unpack('<l', dataArray[len(dataIn)-12:len(dataIn)-8])
    packetNumber = packetNumber[0]
    timePacket = struct.unpack('<d', dataArray[len(dataIn)-8:len(dataIn)])
    return audio, packetNumber, timePacket


#%% CLeanup function for input (microphone)
# Close and terminate pyaudio, close socket, close files.
def cleanupInput():
    print('\nTransmission finished, cleaning up input...\n')
    # end signal in UDP packet
    for i in range(5):
        try:
            closePacket = b'koszihello'
            socketOut.sendto(closePacket, (IP, PortIn))
            print('Sending closing packets', end='\r', flush=True)
        except:
            print('Sending closing packet failed')
    print('\nClosing portaudio input device, sockets, files\n')
    # pyaudio
    streamInput.stop_stream()
    streamInput.close()
    pIn.terminate()
    # sockets
    socketOut.close()
    socketComm.close()
    # files
    fOut.close()
    return


#%% CLeanup function for output (speakers)
# Close and terminate pyaudio, close socket, close files.
def cleanupOutput():
    print('\nTransmission finished, cleaning up output...\n')
    print('\nClosing portaudio output device, sockets, files\n')
    # pyaudio
    streamOutput.stop_stream()
    streamOutput.close()
    pOut.terminate()
    # sockets
    socketIn.close()
    # files
    fIn1.close()
    fIn2.close()
    return


#%% Wave creator function for the binary recorded data
def wavmaker(filename, CHANNELS, RATE):
    # create wav for audio
    f = open(filename, 'rb')
    audio = f.read()
    wavef = wave.open(filename+'.wav', 'w')
    wavef.setnchannels(CHANNELS)
    wavef.setsampwidth(2)
    wavef.setframerate(RATE)
    wavef.writeframes(audio)
    wavef.close()
    f.close()
    return


#%% Cleanup on keypress ESC
def EscCleanup(queueInput, queueOutput, queueTTL, audioInput, audioOutput,
               serialTTL, fLog, fTTL, win):
    print('\nUser pressed ESC, quitting\n')
    # killing audio I/O
    queueInput.put('die')
    queueOutput.put('die')
    queueTTL.put('die')
    audioInput.join()
    audioOutput.join()
    if serialTTL:
        serialTTL.join()
    time.sleep(1)
    # close log files
    fLog.close()
    fTTL.close()
    # clean up visual
    win.close()
    return


#%% Function to open all needed sockets and handle NAT

# def networkInit(STUN, NAT, portIn, portOut):
def networkInit(STUN, NAT, portIn, portOut, punchTimeout):
    global socketIn, socketOut, socketComm
    # if STUN was asked
    if STUN:
        stunFlag = stunQuery()
        if not stunFlag:
            print('\n\nSTUN query failed, something is wrong. Check ' +
                  'connection. Do you have stuntman installed?')
    # UPD sockets for transmission
    socketFlag, socketOut = openSocket(portOut)
    if not socketFlag:
        print('\n\nCould not create or bind UDP socket. Wtf.')
        sys.exit()
    socketFlag, socketIn = openSocket(portIn)
    if not socketFlag:
        print('\n\nCould not create or bind UDP socket. Wtf.')
        sys.exit()
    socketFlag, socketComm = openSocket(PortComm)
    if not socketFlag:
        print('\n\nCould not create or bind UDP socket. Wtf.')
        sys.exit()
    # Hole punch
    recFlag = punchThrough(NAT, socketIn, socketOut, socketComm, punchTimeout)
    if not recFlag:
        print('\n\nSomething went wrong at NAT traversal. Pfff.')
        sys.exit()
    # set sockets to non-blocking
    socketOut.settimeout(0)
    socketIn.settimeout(0.1)
    socketComm.settimeout(0.1)
    return


#%% Main input (microphone) function. Handles audio input and
# transmission. Should be called in separate process (multiprocessing!),
# after networkInit(), at the same time as outputProcess()

def inputProcess(FORMAT, CHANNELS, RATE, CHUNK, queueInput):

    global chunkCounter, streamInput, pIn
    # init chunkCounter
    chunkCounter = 0
    # open input dev
    streamInput, pIn = micOpen(FORMAT, CHANNELS, RATE, CHUNK)

    # print start message
    print('\nEverything seems all right, channel open on our side.\n')

    # start input stream
    start = time.time()
    streamInput.start_stream()

    # wait until all audio is sent
    while streamInput.is_active():
        time.sleep(0.01)
        # if escape key was pressed, terminate
        if not queueInput.empty():
            break

    # message
    print(str(chunkCounter)+' chunks sent, time taken: ' +
          str(time.time()-start))

    # input cleanup
    cleanupInput()

    return


#%% Main output (receiver) function. Handles audio output and
# packet control. Should be called in separate process (multiprocessing!),
# after networkInit(), at the same time as inputProcess()

def outputProcess(BUFFER, CHUNK, FORMAT, CHANNELS,
                  RATE, queueOutput):

    # these need to be global...
    global underFlowFlag, startFlag, audioBuffer, streamOutput
    global pOut, silenceBuffer, lastData

    # initialize buffer underflow / overflow flags, callback start flag
    underFlowFlag = 0
    startFlag = 0
    overFlowFlag = 0

    # Lists to store incoming packet numbers, client side timestamps and
    # server side timestamps
    packetListClient = list()
    packetListClient.append(0)
    timeListClient = list()
    timeListServer = list()

    # open output dev
    streamOutput, pOut = speakersOpen(FORMAT, CHANNELS, RATE, CHUNK)
    print('\nAudio output set up, waiting for transmission.')

    # counter for all received UDP packets
    packetCounter = 0

    # create buffer for incoming packets
    audioBuffer = bytearray()

    # start stream with a silent buffer (silence buffer)
    silenceBuffer = b'x\00'*2*CHUNK*BUFFER
    silenceBuffer = bytearray(silenceBuffer)
    lastData = silenceBuffer[0:CHUNK*2]
    streamOutput.start_stream()

    # Main loop: listen for UDP, fill buffer, hand it to output stream
    while True:
        # if escape key was pressed, ,terminate
        if not queueOutput.empty():
            break
        # receive UDP packet - remember this is in non-blocking mode now!
        packet = []
        try:
            packet = socketIn.recv(CHUNK*4)
        except:
            pass
        # if we recieved anything
        if packet:
            # other end can end session by sending a specific message
            # ('koszihello')
            if packet == b'koszihello':
                print('Koszihello (end message) received, finishing output')
                break
            # parse packet into data and the rest
            data, packetNumber, timePacket = packetParser(packet)
            # adjust packet counter
            packetCounter += 1

            # do a swap if packetNumber is smaller than last
            if packetNumber > 3:
                if packetNumber < packetListClient[-1]:
                    try:  # buffer could be empty...
                        audioBuffer.extend(audioBuffer[-CHUNK*2:])
                        audioBuffer.extend[-CHUNK*4:-CHUNK*2] = data
                    except:
                        audioBuffer.extend(data)
                else:
                    # otherwise just append audioBuffer with new data
                    audioBuffer.extend(data)
            else:
                # otherwise just append audioBuffer with new data
                audioBuffer.extend(data)

            # get server-side timestamp right after writing data to buffer
            timeListServer.append(time.time())

            # set startFlag for callback once buffer is filled for the first
            # time
            if packetCounter == BUFFER:
                startFlag = 1

            # if audioBuffer is getting way too long, chop it back, the
            # treshold is two times the normal size
            if len(audioBuffer) > 2*CHUNK*BUFFER*2:
                del audioBuffer[0:2*CHUNK*BUFFER]
                overFlowFlag += 1

            # display state
            if packetCounter % 250 == 0:
                print('Chunk no ', packetCounter, 'received successfully')
                print('Current buffer size: '+str(len(audioBuffer)))

            # append timePacket and packetNumber lists
            packetListClient.append(packetNumber)
            timeListClient.append(float(timePacket[0]))
            # write audio part to file
            fIn1.write(data)

    # end messages
    messagesOutput(packetCounter, timeListServer, timeListClient,
                   packetListClient, overFlowFlag)
    # cleanup
    cleanupOutput()

    return


#%% Function to display closing stats and messages for output
def messagesOutput(packetCounter, timeListServer, timeListClient,
                   packetListClient, overFlowFlag):
    # summary message
    print('\n\n'+str(packetCounter) +
          ' chunks received, time taken for all chunks: ' +
          str(timeListServer[-1]-timeListServer[0]))
    # more diagnostic messages
    print('\nReceived '+str(packetCounter)+' audio chunks')
    # underflow events
    print('\nBuffer underflow occured '+str(underFlowFlag)+' times')
    # overflow events
    print('\nBuffer overflow occured '+str(overFlowFlag)+' times')
    # print average transmission time
    timeListDiff = list(map(sub, timeListServer, timeListClient))
    print('\nAverage difference between client and server side timestamps: ',
          sum(timeListDiff) / len(timeListDiff), ' secs \n\nClient timestamp '
          'is taken after reading audio input buffer \nServer timestamp is '
          'taken when pushing the received data into audio output buffer\n\n')
    # Saving data
    # write out timestamps into a csv file
    output = open('timestamps.csv', 'wb')
    writer = csv.writer(output)
    for packet, client, server, diff in zip(packetListClient, timeListClient,
                                            timeListServer, timeListDiff):
        writer.writerow((packet, client, server, diff))
    output.close()
    return


#%% Function to integrate the pieces and run the whole shitstorm
def goGo(NAT, STUN, ROLE, TRIALTYPE, WHICHSEED, LOGTTL):
    # these need to be global for callbacks
    global fIn1, fIn2, fOut, PortIn, PortOut, PortComm

    # load all settings, magic numbers
    [punchTimeout, CHANNELS, RATE, FORMAT, savefileOut,
     savefileIn1, savefileIn2, savefileLog, savefileTTL, portIn, portOut,
     PortIn, PortOut, PortComm, serialSettings, turntime, timeDiff, instText1,
     instText2, instText3, turnText1, turnText2, retellText1a, retellText1b,
     retellText2a, retellText2b, retellText2c,
     turnN, turnCurrent, letterH, instTime, startLag,
     retellLength, keylist] = magicNumbers(ROLE, TRIALTYPE, WHICHSEED)

    # networkInit
    networkInit(STUN, NAT, portIn, portOut, punchTimeout)

    # open files we will use for writing stuff out
    fIn1 = open(savefileIn1, 'wb')
    fIn2 = open(savefileIn2, 'wb')
    fOut = open(savefileOut, 'wb')
    fLog = open(savefileLog, 'w')  # text file
    fTTL = open(savefileTTL, 'w')  # text file
    startTTLTime = time.time()
    fTTL.write('TTL logging startTime: '+str(startTTLTime)+'\n\n')

    # audio I/O processes and TTL recording run in separate processes
    queueInput = multiprocessing.Queue()
    queueOutput = multiprocessing.Queue()
    queueTTL = multiprocessing.Queue()
    audioInput = multiprocessing.Process(name='audioInput',
                                         target=inputProcess,
                                         args=(FORMAT,
                                               CHANNELS,
                                               RATE,
                                               CHUNK,
                                               queueInput,))
    audioOutput = multiprocessing.Process(name='audioOutput',
                                          target=outputProcess,
                                          args=(BUFFER,
                                                CHUNK,
                                                FORMAT,
                                                CHANNELS,
                                                RATE,
                                                queueOutput,))
    audioInput.start()
    audioOutput.start()
    # if LOGTTL, start serial listening process
    if LOGTTL:
        serialTTL = multiprocessing.Process(name='serialTTL',
                                            target=serialLog,
                                            args=(serialSettings,
                                                  queueTTL,))
        serialTTL.start()
    else:
        serialTTL = False


    #%% Crazy & Stupid part: importing late, because psychopy breaks stuff on
    # mac otherwise, if imported before multiprocesses have started
    from psychopy import core, visual, event


    #%% Start Visual part
    # set up window: black, fullscreen, try a common size for projectors
    try:
        win = visual.Window([1366, 768],
                            color='black',
                            monitor='testMonitor',
                            fullscr=True)
    except:
        print('\nProblem while setting up window')
        sys.exit()

    # Audio check screen (waiting)
    waitText = 'Check audio, press s to start'
    waitInst = visual.TextStim(win,
                               waitText,
                               color='white',
                               height=letterH)
    waitInst.draw()
    win.flip()

    # to capture keypress event times correctly, we start a clock and get event
    # times relative to that
    keyClock = core.Clock()
    # start time of clock in unix time
    keyClockStart = keyClock.getLastResetTime()

    # wait for key presses (INCLUDING TTL)
#    startSyncStamp = time.time()
#    while True and (time.time()-startSyncStamp < 4):
    while True:
        core.wait(0.01)
        # capture key presses, timing is relative to keyClock
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if 's' was pressed, go on
            if keys[0][0] == 's':
                break
            # if event.getKeys returns a '5' or 'ó', its a TTL
            elif keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return


    #%% Synch computers
    # Synch process: (1) handshake to start, (2) exchange time stamps,
    # derive common start time (average of time stamps + startLag)
    commFlag = True
    incoming = []
    # first a handshake for synch
    print('\nStarting synch\n')
    while commFlag:
        core.wait(0.01)
        # capture keys (TTL)
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return
        # send packets
        try:
            socketComm.sendto('syncTimeNow'.encode(), (IP, PortComm))
        except:
            print('\nProblem sending a syncTimeNow packet...\n')
            pass
        try:
            incoming = socketComm.recv(CHUNK)
        except:
            pass
        if incoming == 'syncTimeNow'.encode():
            incoming = []
            # time stamp on our side
            timeHere = time.time()
            print('\nReceived synch handshake, sending timeHere',
                  str(timeHere), '\n')
            while True:
                keys = event.getKeys(keylist,
                                     timeStamped=keyClock)
                if keys:
                    # if event.getKeys returns a '5' or 'ó', its a TTL
                    if keys[0][0] == '5' or keys[0][0] == 'ó':
                        fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
                    # escape quits
                    elif keys[0][0] == 'escape':
                        EscCleanup(queueInput, queueOutput, queueTTL,
                                   audioInput, audioOutput, serialTTL,
                                   fLog, fTTL, win)
                        return
                # send our time stamp
                for i in range(2):
                    try:
                        socketComm.sendto(struct.pack('<d', timeHere),
                                          (IP, PortComm))
                    except:
                        print('\nProblem sending a timeHere packet...\n')
                        pass
                # read out socket
                try:
                    incoming = socketComm.recv(CHUNK)
                except:
                    pass
                # if read out data is what we would expect, create startTime
                if bool(incoming) & bool(len(incoming) == 8):
                    print('\nGot incoming time\n')
                    # unpack time stamp from other side
                    timeThere = struct.unpack('<d', incoming)[0]
                    print('\nIncoming timeThere is',
                          str(timeThere), '\n')
                    # start is at the max of the two timestamps
                    # + a predefined lag
                    startTimeCommon = max(timeThere, timeHere) + startLag
                    print('\nGot shared startTimeCommon:',
                          str(startTimeCommon), '\n')
                    commFlag = False
                    # insurance policy - send it last time
                    for i in range(2):
                        socketComm.sendto(struct.pack('<d', timeHere),
                                          (IP, PortComm))
                    break
    # Put up a synch screen while we are waiting for startTimeCommon
    synchText = 'Synching start with other site...'
    synchStim = visual.TextStim(win,
                                synchText,
                                color='white',
                                height=letterH)
    synchStim.draw()
    win.flip()
    # log startTimeCommon
    fLog.write('startTimeCommon: ' + str(startTimeCommon) + '\n')
    # common start is synched at a precision of
    # keyboard polling (few ms) + ntp diff + hardware jitter
    while time.time() < startTimeCommon:
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return
    # log audio file object positions at start
    fLog.write('Audio file positions at startTimeCommon:\n')
    fLog.write('fIn1: ' + str(fIn1.tell()) + '\n')
    fLog.write('fIn2: ' + str(fIn2.tell()) + '\n')
    fLog.write('fOut: ' + str(fOut.tell()) + '\n')


    #%% Instructions
    # Instructions: basic text instructions, two pages
    instructions1 = visual.TextStim(win,
                                    instText1,
                                    color='white',
                                    height=letterH)
    instructions2 = visual.TextStim(win,
                                    instText2,
                                    pos=[0, 0.1],
                                    color='white',
                                    height=letterH)

    # draw, flip and give some time (instTime) for reading
    instructions1.draw()
    win.flip()
    # capture key presses /TTLs
    while (time.time()-startTimeCommon) < instTime:
        core.wait(0.01)
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return
    instructions2.draw()
    win.flip()
    # escape jumps instructions
    while (time.time()-startTimeCommon) < (instTime + instTime/5):
        core.wait(0.01)
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return

    # countback before start, topic
    for seconds in reversed(range(5)):
        # put up the correct number on display
        instructions3 = visual.TextStim(win,
                                        instText3+str(seconds+1),
                                        pos=[0, -0.1],
                                        color='white',
                                        height=letterH)
        instructions2.draw()  # keep on display the last instruction as well
        instructions3.draw()
        win.flip()
        startCountbackFlip = time.time()
        # capture keypresses / TTLs while waiting for next countback second
        while time.time()-startCountbackFlip < 1:
            keys = event.getKeys(keylist,
                                 timeStamped=keyClock)
            if keys:
                # if event.getKeys returns a '5' or 'ó', its a TTL
                if keys[0][0] == '5' or keys[0][0] == 'ó':
                    fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
                # escape quits
                elif keys[0][0] == 'escape':
                    EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                               audioOutput, serialTTL, fLog, fTTL, win)
                    return
            core.wait(0.01)


    #%% Turntaking stimulus
    # Prepare stimulus for real task part, first flip
    # basic texts, turn number dependent
    stimText1 = visual.TextStim(win,
                                turnText1,
                                pos=[0, 0.4],
                                color='white',
                                height=letterH)
    stimText2 = visual.TextStim(win,
                                turnText2,
                                pos=[0, 0.4],
                                color='white',
                                height=letterH)
    # timer part
    timerText = str((turntime-timeDiff))
    stimTimer = visual.TextStim(win,
                                timerText,
                                pos=[0, 0],
                                color='white',
                                height=letterH)
    # relative turn timer
    turnText = 'Turn ' + str(turnCurrent) + ' of ' + str(turnN)
    stimTurn = visual.TextStim(win,
                               turnText,
                               pos=[0, -0.4],
                               color='white',
                               height=letterH)
    # draw all prepared stimuli for first frame
    stimText1.draw()
    stimTimer.draw()
    stimTurn.draw()


    #%% Turntaking loop - Start countbacks
    # standard psychopy clock
    while (time.time() - startTimeCommon) < instTime + instTime/5 + 5:
        core.wait(0.005)
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return
    # flip, display stimulus
    win.flip()
    startClock = core.Clock()
    startStamp = startClock.getLastResetTime()
    # log start time
    fLog.write('\nTurn taking stimuli startStamp: ' + str(startStamp) + '\n\n')
    # loop until time is up
    while startClock.getTime() < turnN*turntime:

        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return

        # check things only once in every 30 ms, wait otherwise
        core.wait(0.03)

        # check if timerText needs to be updated or not
        if startClock.getTime() >= (timeDiff+1):
            timeDiff += 1
            timerText = str(turntime-(timeDiff % turntime))
            stimTimer = visual.TextStim(win,
                                        timerText,
                                        pos=[0, 0],
                                        color='white',
                                        height=letterH)

            # check if we also need to update on the turn level
            if startClock.getTime() >= turnCurrent*turntime:
                turnCurrent += 1
                turnText = 'Turn '+str(turnCurrent)+' of ' + str(turnN)
                stimTurn = visual.TextStim(win,
                                           turnText,
                                           pos=[0, -0.4],
                                           color='white',
                                           height=letterH)
                # log audio file pointer positions at turn changes
                fLog.write('local time: ' + str(time.time()) + '\n')
                fLog.write('fIn1: ' + str(fIn1.tell()) + '\n')
                fLog.write('fIn2: ' + str(fIn2.tell()) + '\n')
                fLog.write('fOut: ' + str(fOut.tell()) + '\n')

            # redraw the changing stimuli
            if turnCurrent % 2 == 1:
                stimText1.draw()
            else:
                stimText2.draw()
            stimTimer.draw()
            stimTurn.draw()
            win.flip()

    # end of story part, partial cleanup, terminate audio output
    queueOutput.put('die')
    audioOutput.join()


    #%% Retell
    # stimuli we will use, first the instructions
    if TRIALTYPE == 0:
        retellStim1 = visual.TextStim(win,
                                      retellText1a,
                                      pos=[0, 0],
                                      color='white',
                                      height=letterH)
        # and text for a timer doing the countdown, at start position
        timerText = 'Time left: ' + '{0:.0f}'.format(retellLength) + ' secs'
        # we also need a prompt to ask participants to start
        retellStim2 = visual.TextStim(win,
                                      retellText2a,
                                      pos=[0, 0.3],
                                      color='white',
                                      height=letterH)
    elif TRIALTYPE == 1:
        retellStim1 = visual.TextStim(win,
                                      retellText1b,
                                      pos=[0, 0],
                                      color='white',
                                      height=letterH)
        # and text for a timer doing the countdown, at start position
        timerText = 'Time left: ' + '{0:.0f}'.format(retellLength/2) + ' secs'
        # we also need a prompt to ask participants to start
        retellStim2 = visual.TextStim(win,
                                      retellText2b,
                                      pos=[0, 0.3],
                                      color='white',
                                      height=letterH)
    # and the actual timer visual stim doing the countdown, sing timerText
    retellTimer = visual.TextStim(win,
                                  timerText,
                                  pos=[0, -0.3],
                                  color='white',
                                  height=letterH)

    # put up instructions on display
    retellStim1.draw()
    win.flip()
    # leave instructions up for instTime or esc key
    instRetellStart = time.time()
    while time.time()-instRetellStart < instTime:
        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return
        core.wait(0.01)

    # put up starter display for retell
    retellStim2.draw()
    retellTimer.draw()
    # set timeDiff back
    timeDiff = 0

    # start!
    win.flip()
    startClockRetell = core.Clock()
    startStampRetell = startClockRetell.getLastResetTime()
    # log start time
    fLog.write('\n\nstartStampRetell: ' + str(startStampRetell) + '\n\n')
    # loop until time is up
    while startClockRetell.getTime() < retellLength:

        keys = event.getKeys(keylist,
                             timeStamped=keyClock)
        if keys:
            # if event.getKeys returns a '5' or 'ó', its a TTL
            if keys[0][0] == '5' or keys[0][0] == 'ó':
                fTTL.write(str(keys[0][1] + keyClockStart)+'\n')
            # escape quits
            elif keys[0][0] == 'escape':
                EscCleanup(queueInput, queueOutput, queueTTL, audioInput,
                           audioOutput, serialTTL, fLog, fTTL, win)
                return

        # check things only once in every 30 ms, wait otherwise
        core.wait(0.02)

        # retellStim2 change flag for TRIALTYPE == 1
        retellStim2Flag = True

        # check if timerText needs to be updated or not
        if startClockRetell.getTime() >= (timeDiff+1):
            timeDiff += 1
            # this part is changed to allow for showing the time separately for
            # the first and the second stories in case TRIALTYPE == 1,
            # aka Individual stories condition
            if TRIALTYPE:
                # If it is the first half, show the time accordingly:
                if timeDiff < retellLength/2:
                    timerText = 'Time left: ' +\
                                '{0:.0f}'.format(retellLength/2-timeDiff) +\
                                ' secs'
                # If it is the second half, show the time accordingly:
                else:
                    if retellStim2Flag:
                        retellStim2 = visual.TextStim(win,
                                                      retellText2c,
                                                      pos=[0, 0.3],
                                                      color='white',
                                                      height=letterH)
                        retellStim2Flag = False
                    timerText = 'Time left: ' +\
                                '{0:.0f}'.format(retellLength-timeDiff) +\
                                ' secs'
            # if Joint story, aka TRIALTYPE == 0
            else:
                timerText = 'Time left: ' +\
                                '{0:.0f}'.format(retellLength-timeDiff) +\
                                ' secs'
            retellTimer = visual.TextStim(win,
                                          timerText,
                                          pos=[0, -0.3],
                                          color='white',
                                          height=letterH)
            retellStim2.draw()
            retellTimer.draw()
            win.flip()
            # log audio file pointer position at timer changes
            fLog.write('local time: ' + str(time.time()) + '\n')
            fLog.write('fOut: ' + str(fOut.tell()) + '\n')

    # end message
    endText = 'Time is up, this trial has ended'
    endStim = visual.TextStim(win,
                              endText,
                              pos=[0, 0],
                              color='white',
                              height=letterH)
    endStim.draw()
    win.flip()
    # last fLog event
    fLog.write('\n\nRetell end time: '+str(time.time()))
    fLog.write('fOut: ' + str(fOut.tell()) + '\n')


    #%% Clean up
    # if things went through cleanly, terminate audio input now
    queueInput.put('die')
    # terminate serial TTL recordings if we ever started
    if LOGTTL:
        queueTTL.put('die')
    # final time
    print('\nTime since start of actual task (startClock): ' +
          str(startClock.getTime()))
    # wait for audio to close
    audioInput.join()
    # wait for serial TTL listening process to join
    if LOGTTL:
        serialTTL.join()
    # create wav files
    for file in [savefileOut, savefileIn1, savefileIn2]:
        wavmaker(file, CHANNELS, RATE)

    # give some time for end message
    core.wait(2)
    # close log files + psychopy stuff
    fLog.close()
    fTTL.close()
    win.close()

    return


#%% MAIN
if __name__ == '__main__':

    # input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-n',
        '--NAT',
        nargs='?',
        type=int,
        default=0,
        help='Flag for local NAT: set to 0 if ports are forwarded through ' +
             'NAT, set to 1 otherwise. If 1, provide IP as well! Default = 0')
    parser.add_argument(
        '-c',
        '--CHUNK',
        nargs='?',
        type=int,
        default=512,
        help='Audio chunk (packet) size in frames (1 frame = 2 bytes with ' +
             'current format settings). Integer. Default = 512')
    parser.add_argument(
        '-i',
        '--IP',
        nargs='?',
        type=str,
        default='',
        help='If NAT = 1, provide IP (ipv4) in string for NAT traversal. ' +
             'Ignored if NAT = 0. Default = empty string')
    parser.add_argument(
        '-b',
        '--BUFFER',
        nargs='?',
        type=int,
        default=4,
        help='No. of chunks to buffer for audio output. Integer. Default = 4')
    parser.add_argument(
        '-s',
        '--STUN',
        nargs='?',
        type=int,
        default=0,
        help='Flag to run stunclient (1) or not (0) ' +
             'at the beginning of the script. Requires installed ' +
             'stunclient. Default = 0')
    parser.add_argument(
        '-r',
        '--ROLE',
        nargs='?',
        type=int,
        default=0,
        help='Flag to set the story starter: ' +
             '0 means that local participant goes first, 1 means local ' +
             'participant is second. Default = 0')
    parser.add_argument(
        '-t',
        '--TRIALTYPE',
        nargs='?',
        type=int,
        default=0,
        help='Flag to set trial type: ' +
             '0 means joint story, 1 means individual stories. Default = 0')
    parser.add_argument(
        '-w',
        '--WHICHSEED',
        nargs='?',
        type=int,
        default=0,
        help='Topic (story seed) number for current trial. Integer. ' +
             'Default = 0, aka alien contact')
    parser.add_argument(
        '-l',
        '--LOGTTL',
        nargs='?',
        type=int,
        default=1,
        help='Flag for logging scanner ttl signals and their timestamps: ' +
             '0 means no ttl log (for testing outside scanner), 1 means ' +
             'ttl log. Default = 1')
    args = parser.parse_args()

    # check inputs
    if 0 <= args.NAT <= 1:
        pass
    else:
        raise ValueError('Unexpected value for argument NAT ',
                         '(should be 0 or 1)')
    # the following check for power of two is a really cool trick!
    if ((args.CHUNK != 0) and ((args.CHUNK & (args.CHUNK - 1)) == 0) and
       (not (args.CHUNK < 128)) and (not (args.CHUNK > 4096))):
        pass
    else:
        raise ValueError('CHUNK should be power of two, between 128 and 4096.')
    if 1 <= args.BUFFER <= 25:
        pass
    else:
        raise ValueError('Unexpected value for argument BUFFER. ',
                         '(please have it 1 <= and <= 25.')
    if 0 <= args.STUN <= 1:
        pass
    else:
        raise ValueError('Unexpected value for argument STUN ',
                         '(should be 0 or 1)')
    if 0 <= args.ROLE <= 1:
        pass
    else:
        raise ValueError('Unexpected value for argument ROLE ',
                         '(should be 0 or 1)')
    if 0 <= args.TRIALTYPE <= 1:
        pass
    else:
        raise ValueError('Unexpected value for argument TRIALTYPE ',
                         '(should be 0 or 1)')
    if 0 <= args.WHICHSEED <= 4:
        pass
    else:
        raise ValueError('Unexpected value for argument WHICHSEED ',
                         '(should be int between 0 and 4)')
    if 0 <= args.LOGTTL <= 1:
        pass
    else:
        raise ValueError('Unexpected value for argument LOGTTL ',
                         '(should be 0 or 1)')

    # some global -local handling:
    # anything used later in callbacks needs to be global
    global IP, BUFFER, CHUNK
    IP = args.IP
    BUFFER = args.BUFFER
    CHUNK = args.CHUNK

    # Run experiment (function goGo)
    goGo(args.NAT,
         args.STUN,
         args.ROLE,
         args.TRIALTYPE,
         args.WHICHSEED,
         args.LOGTTL)

    # End
    print('\n\nEverything ended / closed the way we expected. Goodbye!\n\n')


