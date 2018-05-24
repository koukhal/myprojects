#!/usr/bin/python
'''
Created on 24 oct. 2016

 Intrasoft, 2016
 EUDOR V3 - preIngest (BACKLOG)
 Control and Valid the SIP packages on the front-end from the BACKLOG Service
 Name           : preIngestBacklog.py
 Version        : 2.4
 Modif date     : 01/12/2016    : check if work exists and change the insert to update
                : 15/02/2017    : use the zip command of system to modify the SIP package (resolve issue of the large file) 
                : 23/02/2017    : cancel the backup of the package
                : 09/08/2017    : Correction multiple key
                : 24/01/2018    : Add concil as new key 
                : 24/01/2018    : Processing the expressions for the keys not identified in contentids
                : 03/04/2018    : Add legissum key
                : 26/04/2018    : Add swd and join keys 

'''

import sys
import os
import sys
import os
import shutil
import logging
import datetime
import time
import zipfile
from zipfile import is_zipfile, ZipFile, ZIP_DEFLATED
import psycopg2
import hashlib
import smtplib
import textwrap
import lxml
from os import path
import subprocess

from email.MIMEMultipart import MIMEMultipart
from email.MIMEText import MIMEText
from logging.handlers import RotatingFileHandler
from xml.dom import minidom
from lxml import etree
from os.path import exists

import heapq
from _elementtree import XML



#Version
global version
version ="2.4"

# Parsing variables
tree=""

#DMD List
list_rdf = []
list_dmdid = []
list_chksum = []
list_chksumtype = []
list_mimetype = []

#AMD List
list_amdid = []
list_techmdid = []
list_amdrdf = []
list_amdchksum = []
list_amdchksumtype = []
list_amdmimetype = []

#File Section List
list_fileid = []
list_filemimetype = []
list_filechksum = []
list_filechksumtype = []
list_filename = []

# List to compare HKey
list_hkeytable = []
list_hkeyfilename = []
list_hkey_chksum = []
list_hkey_chksumtype = []

list_2Compare = []
tupMetsInfo =("")

listExpression=[]
listWork=[]
listManifestation=[]

errorMessage=""
serieTodest=""
metsdocid =""

DMDdic={
    "dmdid" : [],
    "rdfile" : [],
    "checksumtype" : [],
    "checksum" : [],
    "mimetype" : [],
}

AMDdic={
    "mimetype" : [],
    "checksumtype" : [],
    "checksum" : [],
    "rdfile" : [],
    "techmdid" : [],
    "amdid" : [],
}

FILEdic={
    "fileid" : [],
    "checksumtype" : [],
    "checksum" : [],
    "filename" : [],
    "mimetype" : [],
}

HKeydic={
    "filename" : [],
    "checksumtype" : [],
    "checksum" : [],
}


totalFilesinMETS=0
typeOfAction =""

#
# Logger
#
def initLogger():

    try :
        logFile=os.path.join(logdir,'sipcontrol_detailled.log')
        
        # Creation du logger
        global logger
        logger = logging.getLogger()
        logger.setLevel(logging.DEBUG)

        # Creation du formatter
        formatter = logging.Formatter('%(asctime)s : %(levelname)s : %(message)s',datefmt='%Y-%m-%d %H:%M:%S')
        # Creation d'un handler
        file_handler = RotatingFileHandler(logFile, 'a',  5242880,20)
        # Niveau sur DEBUG
        # Ajouter au handler
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(formatter)
        logger.addHandler(file_handler)

        return True

    except Exception, le :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : Error %s' % le
        return False
#
# Send Email
#
def sendEMail(message,sip):
    try :

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : Send email to %s ' % destinataire

        # Prepare the message
        Subject = "Pre-Ingest Module - BACKLOG : %s" % sip
        message = textwrap.dedent("""\
        From: %s
        To: %s
        Subject: %s
        X-Priority : %d
        Hello,

        The module preIngest has encountered the following issue :

        %s

        For more information please see the logs .

        """ % (smtp_login,destinataire, Subject,2, message))

        # Send the message
        server = smtplib.SMTP('%s' %smtp_server,'%d' %smtp_port)
        server.starttls()
        server.login("%s" %smtp_login, "%s" %smtp_pwd)

        server.sendmail("%s" %smtp_login, "%s" %destinataire, message)
        server.quit()

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : Email sent to %s.' % destinataire

        return True

    except Exception, e :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : Error %s' % e
        logger.error('Error %s' % e)
        return False

#
# Clean workdir (remove all files except zip)
#
def removeFiles(source,sip):
    for filename in os.listdir(source) :
        if  not (filename.endswith("zip")):
            os.remove(source + "/" + filename)
            logger.info('Delete %s from %s' % (filename,source))


#
# Parse configuration in using minidom
#
def parseConfig(configFile):

    try:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Parse XML configuration file ...."
        doc = minidom.parse(configFile)

        lglevel = doc.getElementsByTagName("loglevel")[0]
        global loglevel
        loglevel=getNodeText(lglevel)

        input = doc.getElementsByTagName("input")[0]
        global source
        source=getNodeText(input)

        output = doc.getElementsByTagName("output")[0]
        global destination
        destination=getNodeText(output)

        rejected = doc.getElementsByTagName("rejected")[0]
        global rejdir
        rejdir=getNodeText(rejected)

        replog = doc.getElementsByTagName("logdir")[0]
        global logdir
        logdir = getNodeText(replog)

        workrep = doc.getElementsByTagName("workdir")[0]
        global workdir
        workdir = getNodeText(workrep)
        
        waitrep = doc.getElementsByTagName("waitdir")[0]
        global waitdir
        waitdir = getNodeText(waitrep)
        
        bckrep = doc.getElementsByTagName("backupdir")[0]
        global backupdir
        backupdir = getNodeText(bckrep)

        mdp = doc.getElementsByTagName("password")[0]
        pwd=getNodeText(mdp)

        user = doc.getElementsByTagName("user")[0]
        userID=getNodeText(mdp)

        hostname = doc.getElementsByTagName("hostname")[0]
        hostID=getNodeText(hostname)

        DBName = doc.getElementsByTagName("DBName")[0]
        DB = getNodeText(DBName)

        portnum = doc.getElementsByTagName("PortNum")[0]
        portID=getNodeText(portnum)

        site = doc.getElementsByTagName("site")[0]
        global sipsite
        sipsite=getNodeText(site)

        serverName = doc.getElementsByTagName("server")[0]
        global sipserver
        sipserver=getNodeText(serverName)

        schema = doc.getElementsByTagName("metsSchema")[0]
        global metsSchema
        metsSchema=getNodeText(schema)

        smtpS = doc.getElementsByTagName("smtpserver")[0]
        global smtp_server
        smtp_server=getNodeText(smtpS)

        smtpPort = doc.getElementsByTagName("smtpport")[0]
        global smtp_port
        smtp_port=getNodeText(smtpPort)
        smtp_port = int(smtp_port)

        smtpLog = doc.getElementsByTagName("smtplogin")[0]
        global smtp_login
        smtp_login=getNodeText(smtpLog)

        smtpPwd = doc.getElementsByTagName("smtppwd")[0]
        global smtp_pwd
        smtp_pwd=getNodeText(smtpPwd)

        dest = doc.getElementsByTagName("destinataire")[0]
        global destinataire
        destinataire=getNodeText(dest)

        delai = doc.getElementsByTagName("tempo")[0]
        global tempo
        tempo=getNodeText(delai)
        tempo = int(tempo)



        print "Parameters  : "
        print "--------------"
        print "Site        : ",sipsite," - Server : ",sipserver
        print "Log level   : ",loglevel
        print "Directory   : ",source," - ",destination," - ",rejdir," - ",logdir, " -" ,workdir
        print "Database    : ",DB," - ",hostID," - ",portID," - ",userID
        print "==================================================================="

        # Store DB connection into tup
        global tupDB
        tupDB = (DB, hostID, userID, pwd, portID)

        return True

    except Exception, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : Error %s' % e
        return False

#
# Return the  value of the node
#
def getNodeText(node):

    nodelist = node.childNodes
    result = []
    for node in nodelist:
        if node.nodeType == node.TEXT_NODE:
            result.append(node.data)
    return ''.join(result)

#
# Get oldest SIP in folder
#
def oldestFile (rootfolder, count, extension):
    return heapq.nsmallest(count,
        (os.path.join(dirname, filename)
        for dirname, dirnames, filenames in os.walk(rootfolder)
        for filename in filenames
        if filename.endswith(extension)),
        key=lambda fn: os.stat(fn).st_mtime)

#
# List packages in directory
#
def scandir(dir):

    try :
        # Check if STOP File exists
        STOPFILE = os.path.join(dir, "STOP")
        # Check if STOP file exists
        if (os.path.isfile(STOPFILE)):
            return "STOP"
                
        oldFile = oldestFile (dir, count=1, extension=".zip")
        
        if len(oldFile) == 0:
            #print "None SIP found"
            return None
        else :
            global sip_paquet
            sip_paquet = oldFile[0]
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print ""
            print "--------"+fdate+" %s ------------------------------" % os.path.basename(sip_paquet)
                        
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
       
            #print fdate+' : SIP found %s' % sip_paquet
               
            if sip_paquet is not None :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate+' : SIP %s found ' % sip_paquet
                return sip_paquet                      
            else :
                return None
        
    except Exception, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+' : Error %s' % e
        logger.error('%s'  % e)
        return False          

def checkWorkexists(idcellar,collectiontocheck):
    
    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]
    
    global packagetype
    
    try:
        # Check if SIP exists in DB
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : Verify if %s WORK already exists in database" % sip
        logger.info(' Verify if %s WORK already exists in database' % sip)
        
        sQuery= "SELECT count(*) from workpub "
        sQuery += " where idcellar = '%s' " %idcellar
        logger.info('Execute Query : %s' % sQuery)

        # Database Connection
        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()
        result=cur.execute(sQuery)
        count_row = cur.fetchone()
        count = count_row[0]
        cur.close()
        con.close()
        
        if count == 0:
            logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
            logger.info('Execute Query : %s' % sQuery)
            # Database Connection
            con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
            cur = con.cursor()
            cur.execute(sQuery)
            con.commit()
            cur.close()
            con.close()
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate+ " : %s(%s) not exists in database " % (collectiontocheck,idcellar)
            logger.info('%s(%s) not exists in database ' % (collectiontocheck,idcellar))        
           
            packagetype ='create'
            return None
        
        else :
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate+ " : %s(%s) already exists in database " % (collectiontocheck,idcellar)
            logger.info('%s(%s) already exists in database ' % (collectiontocheck,idcellar))         
            
            packagetype ='update'
            return True
        
    #except psycopg2.DatabaseError, e:
    except psycopg2.DatabaseError, e:
        # Get the most recent exception
        exceptionType, exceptionValue, exceptionTraceback = sys.exc_info()
        # Exit the script and print an error telling what happened.
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Error %s " % e
        logger.error('Error during a database transaction')
        logger.error('%s ' %e)
        sendEMail("Error during a database transaction %s : " %e,sip)
        sys.exit("Database connection failed!\n ->%s" % (exceptionValue))
        
              
#
# Compare total files in the SIP package with METS XML
#
def compareTotalFiles(sip):

    totalinzip=0

    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
    print fdate+ " : Compare total files of %s " % sip
    print fdate + " : Total Files referenced in METS : ",totalFilesinMETS
    logger.info('Compare total files of %s ' % sip)

    # total files in SIP package
    file = os.path.join(workdir,sip)
    zfile = zipfile.ZipFile(file)
    for file in zfile.namelist():
        totalinzip= totalinzip+1

    totalinzipssmets= totalinzip - 1
    ts = time.time()
    print fdate + " : Total Files in ZIP (without manifest) : ",totalinzipssmets
    logger.info('Total Files referenced in METS %d / Total Files in ZIP %d  ' % (totalFilesinMETS,totalinzipssmets))

    cmp= totalinzipssmets - totalFilesinMETS
    logger.info('Difference between files referenced in METS and presents in ZIP : %d' % (cmp))

    if cmp !=0 :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : Difference between files referenced in METS and presents in ZIP %d/%d " % (totalFilesinMETS,(totalinzip-1))
        logger.info('Difference between files referenced in METS and presents in ZIP (%d)' % cmp)
        sendEMail("Difference between files referenced in METS and presents in ZIP (%d)" % cmp,sip)

    return cmp

#
# Modify METS XML
#
def modifMetsXML (xmlfile):
    
    try :
        xmlpath = os.path.join(workdir,xmlfile)
        
        global tree
        tree = etree.parse(xmlpath)
        root = tree.getroot()

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : Start reading the  METS XML %s " % xmlfile
        logger.info('Start reading the  METS XML %s ' % xmlfile)
        # Get information of the root

        for getAttrib in root.attrib:
            #print " " + root.attrib['TYPE']
            if root.attrib['TYPE'] == 'create':
                #print " changement"
                root.attrib['TYPE'] = 'update'
                tree.write(xmlpath)

        #print open("example.xml").read()
        return True
    except Exception, e:
        print "%s"%e
        return False

#
# Update DB
#
def updateDB(Query):
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]

    try:
        # Database Connection
        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()

        logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
        logger.info('Execute Query : %s' % Query)

        cur.execute(Query)
        con.commit()
        cur.close()
        con.close()
        return True
    except psycopg2.DatabaseError, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Error %s " % e
        logger.error('Error during a database transaction')
        logger.error('%s ' %e)
        sendEMail("Error during a database transaction %s : " %e,sip)
        con.rollback()
        cur.close()
        con.close()
        return False

#
# Move SIP to destination mentionned
#
def moveSIP(src,dest,sipTomove):

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
       
        if not os.path.exists(dest):
            os.makedirs(dest)
            
        source=os.path.join(src,sipTomove)
        destination=os.path.join(dest,sipTomove)
        
        print fdate + " : Move %s to %s " % (source,destination)
        logger.info('Move %s to %s' % (source,destination))
        shutil.move(source, destination)
        
#
# Store SIP in database
#
def storeSIPtoDB(sip,Query):

    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]

    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
 
    try:

        # Check if SIP exists in DB
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : Verify if %s already exists in database" % sip
        logger.info('Verify if %s already exists in database' % sip)
        
        selectQuery= "SELECT count(packagename) from infopackage "
        selectQuery += " where packagename = '%s' " % sip
        logger.info('Execute Query : %s' % selectQuery)
        
        # Database Connection
        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()
        result=cur.execute(selectQuery)
        count_row = cur.fetchone()
        count = count_row[0]
        cur.close()
        con.close()
        
        if count == 0:
            logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
            logger.info('Execute Query : %s' % Query)
            # Database Connection
            con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
            cur = con.cursor()
            cur.execute(Query)
            con.commit()
            cur.close()
            con.close()
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate+ " : %s recorded in database " % sip
            return True
        
        else :
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : SIP package %s already exists in INFOPACKAGE " % sip
            logger.info('SIP package %s already exists in INFOPACKAGE  ' % sip)            
            sendEMail("SIP package already exists in INFOPACKAGE .",sip)  
            return False
        
    #except psycopg2.DatabaseError, e:
    except psycopg2.DatabaseError, e:
        # Get the most recent exception
        exceptionType, exceptionValue, exceptionTraceback = sys.exc_info()
        # Exit the script and print an error telling what happened.
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Error %s " % e
        logger.error('Error during a database transaction')
        logger.error('%s ' %e)
        sendEMail("Error during a database transaction %s : " %e,sip)
        sys.exit("Database connection failed!\n ->%s" % (exceptionValue))


#
# Check opening ZIP File
#
def openingZip(zfile):
    
    sipFile = os.path.basename(zfile)
    
    try :
        # Check ZIP file 
            myZIP = zipfile.ZipFile(zfile)
            retval = myZIP.testzip()
        
            # Opening of the ZIP failed
            if retval is not None:
                destRej=os.path.join(rejdir,sipFile)
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                print fdate+ " : SIP %s is corrupted !!!" % sipFile
                logger.error('File %s is corrupted ' % sipFile)
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : Move %s to %s " % (sipFile,destRej)
                logger.info('Move SIP to Rejected %s' % destRej)
                #shutil.move(zfile, destRej)
                sendEMail("Error during the opening of SIP. ",sipFile)
                # update database
                Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the opening of SIP' "
                Query += " ,process_date ='%s' " % processdate
                Query += " where packagename ='%s' " % sipFile
                retupd=updateDB(Query)
                if retupd == False:
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    print fdate + " : 'Error during to the update of theDB  - %s" %sip
                    logger.error('Error during to the insertion in DB - %s' %sip)
                    sys.exit(1)
                myZIP.close()
                return False
            
            # Opening of the ZIP OK
            else :
                # Store SIP in DATABASE
                ########################
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : %s opened OK" % sipFile
                logger.info("opened OK %s" % sipFile)
                myZIP.close()
                return True

    # Opening of the ZIP failed
    except Exception, e:                
                destRej=os.path.join(rejdir,sipFile)
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                print fdate+ " : Error during the opening of SIP %s :%s " %(sipFile,e)
                logger.error('%s' % e)
                sendEMail("Error during the opening of SIP : %s : " %e,sipFile)
                print fdate + " : Move ",sipFile , " to ",destRej
                logger.info('Move SIP to Rejected %s' % destRej)
                #shutil.move(zfile, destRej)
                # update database
                Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the opening of SIP' "
                Query += " ,process_date ='%s' " % processdate
                Query += " where packagename ='%s' " % sipFile
                retupd=updateDB(Query)
                if retupd == False:
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    print fdate + " : 'Error during to the update of theDB  - %s" %sipFile
                    logger.error('Error during to the insertion in DB - %s' %sipFile)
                    sys.exit(1)
                myZIP.close()
                return False
            
#
# Extract only METS file to check
#
def dezipMETS(metsFile,outDir,sip):

    try :
        metsXMLtmp=os.path.splitext(metsFile)[0]
        global metsXML
        metsXML=metsXMLtmp+".mets.xml"
        metsPath = os.path.join(outDir,metsFile)
       
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Unzip (METS XML) %s to %s . " % (metsXML,outDir)
        processdate = fdate
        logger.info('Unzip (METS XML) %s to %s .' % (metsXML,outDir))
        myZIP = zipfile.ZipFile(metsPath)

        for item in myZIP.namelist():
            if item == metsXML:
                myZIP.extract(item, outDir)
                
        metsXMLPath =  os.path.join(outDir,metsXML)        
        if os.path.isfile(metsXMLPath) == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            processdate = fdate
            print fdate + " : The METS file %s doesnt exist in SIP ." %metsXML
            sendEMail("The METS file %s doesnt exist in SIP ." %metsXML,sip)
            Query = "UPDATE infopackage SET status ='ERROR', description ='The METS file doesnt exist in SIP .' "
            Query += " , process_date ='%s' " % processdate
            Query += " where packagename ='%s' " % sip
            retupd=updateDB(Query)
            if retupd == False:
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : 'Error during to the update of the DB  - %s ." %sip
                logger.error('Error during to the update of the DB  - %s .' %sip)
                sys.exit(1)
            myZIP.close()
            return False        
                
        return True
    except zipfile.BadZipfile , ze :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        processdate = fdate
        print fdate + ': %s' % ze
        sendEMail("Error to uncompress the package %s : %s " %(sip,ze),sip)
        logger.error('%s' % ze)
        # update database
        Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the METS XML extraction .' "
        Query += " , process_date ='%s' " % processdate
        Query += " where packagename ='%s' " % sip
        retupd=updateDB(Query)
        if retupd == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : 'Error during to the update of the DB  - %s" %sip
            logger.error('Error during to the update of the DB  - %s' %sip)
            sys.exit(1)
        myZIP.close()
        return False

#
# Valid METS Schema
#
def validXML(xmlschema, metsfile,sip):

# Validating of the Schema
    try:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Validating schema %s " %xmlschema
        doc = etree.parse(xmlschema)
        schema = etree.XMLSchema(doc)
        
    except lxml.etree.XMLSchemaParseError , e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        processdate = fdate
        
        print fdate + " : Error during the schema validating %s " %xmlschema
        print fdate + " : %s : " %e
        logger.error('Error during the schema validating %s :' %xmlschema)
        logger.error('%s' %e)
        sendEMail("Error during the schema validating - %s : %s"  %(xmlschema,e),sip)
        # update database
        Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the schema validation (XSD) .'"  
        Query += " ,process_date ='%s' " % processdate
        Query += " where packagename ='%s' " % sip
        retupd=updateDB(Query)
        if retupd == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : 'Error during to the update of theDB  - %s" %sip
            logger.error('Error during to the update to DB - %s' %sip)
            sys.exit(1)
  
        return False


    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
    print fdate + " : Schema %s validated sucessfully " %xmlschema
    logger.info('Schema %s validated sucessfully ' %xmlschema)

# Validating of the METS XML
    metsxml = os.path.join(workdir,metsfile)
    try:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Validating METS XML %s " %metsfile
        doc = etree.parse(metsxml)
        schema.assertValid(doc)
        
    except lxml.etree.DocumentInvalid, e :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        processdate = fdate
        
        print fdate + " : Error during the validating of the METS XML %s " %metsfile
        print fdate + " : %s " %e
        logger.error('Error during the validating of the METS XML %s' %metsfile)
        logger.error('%s' %e)
       
        sendEMail("Error during the validating of the METS XML - %s : %s"  %(metsfile,e),sip)
        # update database
        Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the METS XML Validation.'"
        Query += " ,process_date ='%s' " % processdate
        Query += " where packagename ='%s' " % sip
        retupd=updateDB(Query)
        if retupd == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : 'Error during to the update of theDB  - %s" %sip
            logger.error('Error during to the update to DB - %s' %sip)
            sys.exit(1)

        return False
    
    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
    print fdate + " : METS XML %s validated sucessfully " %metsfile
    logger.info('METS XML %s validated sucessfully ' %metsfile)

    return True   

# 
# Parse METS XML
def parseMetsXML(xmlfile):

    amdID="";
    techMDID="";
    dmdID="";
    refFILE="";
    fileID="";
    fchksum="";
    fmimetype="";
    
    # Iniatialize Dictionnaire
    DMDdic={}
    AMDdic={}
    FILEdic={}

    
    try:

        #DMD List
        del list_rdf[:]
        del list_dmdid[:]
        del list_chksum[:]
        del list_chksumtype[:]
        del list_mimetype[:]

        #AMD List
        del list_amdid[:]
        del list_techmdid[:]
        del list_amdrdf[:]
        del list_amdchksum[:]
        del list_amdchksumtype[:]
        del list_amdmimetype[:]

        #File Section List
        del list_fileid[:]
        del list_filemimetype[:]
        del list_filechksum[:]
        del list_filechksumtype[:]
        del list_filename[:]

        # List to compare HKey
        del list_hkeyfilename[:]
        del list_hkey_chksum[:]
        del list_hkey_chksumtype[:]
        del list_hkeytable[:]
        
        del listExpression[:]
        del listManifestation[:]
        del listWork[:]

        metsFile = os.path.join(workdir,xmlfile)
        global tree
        tree = etree.parse(metsFile)
        root = tree.getroot()

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : Start reading the  METS XML %s " % xmlfile
        logger.info('Start reading the  METS XML %s ' % xmlfile)
        # Get information of the root
        for getAttrib in root.attrib:
            if getAttrib == 'PROFILE':
                profile = root.attrib[getAttrib]
                #print '{0}="{1}"'.format(getAttrib, root.attrib[getAttrib])
                #print "PROFILE : %s " % profile
            if getAttrib == 'TYPE':
                type = root.attrib[getAttrib]
                global typeOfAction
                typeOfAction = type

        # Get information of the METS Header
        metsHDR = root.find("{http://www.loc.gov/METS/}metsHdr")
        create = metsHDR.attrib.get('CREATEDATE')
        #print "Create : %s"  % create

        for node in metsHDR.getchildren():
            if node.tag == "{http://www.loc.gov/METS/}metsDocumentID" :
                metsDocID = node.text

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : METSHDR readed"
        logger.info('METSHDR : %s - %s - %s - %s' % (type,profile,create,metsDocID))
        # Get information of the Descrptive Metada (DMDSEC)

        for child in root:
            if child.tag == '{http://www.loc.gov/METS/}dmdSec' :
                dmdID = child.attrib.get('ID')
                DMDdic = {"dmdid":dmdID}
                list_dmdid.append(dmdID)
                #print "DMD ID : %s"  % dmdID
                for node in child.getchildren():
                    if node.tag == "{http://www.loc.gov/METS/}mdRef" :
                        #print node.tag, node.attrib, node.text, node.tail
                        refRDF = node.attrib.get('{http://www.w3.org/1999/xlink}href')
                        #print "RDF File : %s"  % refRDF
                        list_rdf.append(refRDF)
                        list_hkeyfilename.append(refRDF)
                        list_hkeytable.append("dmdsec")
                        
                        chksumtype = node.attrib.get('CHECKSUMTYPE')
                        if chksumtype is not None:
                            #print "CheckSum type : %s"  % chksumtype
                            list_chksumtype.append(chksumtype)
                            list_hkey_chksumtype.append(chksumtype)                              

                        chksum = node.attrib.get('CHECKSUM')
                        if chksum is not None:
                            #print "CheckSum : %s"  % chksum
                            list_chksum.append(chksum)
                            list_hkey_chksum.append(chksum)
                   
                            
                        mimetype = node.attrib.get('MIMETYPE')
                        #print "MIME Type : %s"  % mimetype
                        list_mimetype.append(mimetype)

        #print ""
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : DMDSEC readed"
        logger.info('DMDSEC : %s - %s - %s - %s' % (DMDdic,refRDF,chksum,mimetype))

        # Get information of the Descrptive Metada (AMDSEC)
        for child in root:
            if child.tag == '{http://www.loc.gov/METS/}amdSec' :
                amdID = child.attrib.get('ID')
                #print "AMD ID : %s"  % amdID
                #if amdID != null :
                list_amdid.append(amdID)

                for node in child.getchildren():
                    if node.tag == "{http://www.loc.gov/METS/}techMD" :
                        techMDID = node.attrib.get('ID')
                        #print "techMD ID : %s"  % techMDID
                        list_techmdid.append(techMDID)

                        for subnode in node.getchildren():
                            #print subnode.tag, subnode.attrib, subnode.text, subnode.tail
                            if subnode.tag == "{http://www.loc.gov/METS/}mdRef" :

                                refRDF = subnode.attrib.get('{http://www.w3.org/1999/xlink}href')
                                #print "RDF File : %s"  % refRDF
                                list_amdrdf.append(refRDF)
                                list_hkeyfilename.append(refRDF)
                                list_hkeytable.append("amdsec")

                                chksumtype = subnode.attrib.get('CHECKSUMTYPE')
                                                              
                                if chksumtype is not None :
                                    list_amdchksumtype.append(chksumtype)
                                    list_hkey_chksumtype.append(chksumtype)
                                    

                                chksum = subnode.attrib.get('CHECKSUM')
                                if chksum is not None:
                                    #print "CheckSum : %s"  % chksum
                                    list_amdchksum.append(chksum)
                                    list_hkey_chksum.append(chksum)
                               

                                mimetype = subnode.attrib.get('MIMETYPE')
                                #print "MIME Type : %s"  % mimetype
                                list_amdmimetype.append(mimetype)

        #print ""
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : AMDSEC readed"
        logger.info('AMDSEC : %s - %s - %s - %s - %s' % (amdID,techMDID,refRDF,chksum,mimetype))
        # Get information of the File Section (fileSec)
        for child in root:

            if child.tag == '{http://www.loc.gov/METS/}fileSec' :

                for node in child.getchildren():

                    if node.tag == "{http://www.loc.gov/METS/}fileGrp" :

                        for subnode in node.getchildren():
                            #print subnode.tag, subnode.attrib, subnode.text, subnode.tail

                            if subnode.tag == "{http://www.loc.gov/METS/}file" :
                                fileID = subnode.attrib.get('ID')
                                #print "FILE ID : %s"  % fileID
                                list_fileid.append(fileID)

                                fchksumtype = subnode.attrib.get('checksumtype')
                                if fchksumtype is not None :
                                    #print "CheckSum type : %s"  % fchksumtype
                                    list_filechksumtype.append(fchksumtype)
                                    list_hkey_chksumtype.append(fchksumtype)
                        
                                fchksum = subnode.attrib.get('CHECKSUM')
                                if fchksum is not None :
                                    #print "CheckSum : %s"  % fchksum
                                    list_filechksum.append(fchksum)
                                    list_hkey_chksum.append(fchksum)
                             
                                fmimetype = subnode.attrib.get('MIMETYPE')
                                #print "MIME Type : %s"  % fmimetype
                                list_filemimetype.append(fmimetype)

                                for subsubnode in subnode.getchildren():
                                    #print subsubnode.tag, subsubnode.attrib, subsubnode.text, subsubnode.tail
                                    if subsubnode.tag == "{http://www.loc.gov/METS/}FLocat" :
                                        refFILE= subsubnode.attrib.get('{http://www.w3.org/1999/xlink}href')
                                        #print "File : %s"  % refFILE
                                        list_filename.append(refFILE)
                                        list_hkeyfilename.append(refFILE)
                                        list_hkeytable.append("filesec")

        #print ""
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : FILESEC readed"
        logger.info('FILESEC : %s - %s - %s ' % (refFILE,fileID,fmimetype))

        # Get information from structMap
        for child in root:
            if child.tag == '{http://www.loc.gov/METS/}structMap' :
            # WORK
                for node in child.getchildren():
                    #print node.tag, node.attrib, node.text, node.tail
                                       
                    listWork.append(node.attrib.get('CONTENTIDS'))
                    if node.tag == "{http://www.loc.gov/METS/}div" :
                        #print node.tag, node.attrib, node.text, node.tail
                        contentids_divwork = node.attrib.get('CONTENTIDS')
                        print "CONTENTIDS : %s"  % contentids_divwork
       
                    # EXPRESSION
                    for subnode in node.getchildren():
                        #print subnode.tag, subnode.attrib, subnode.text, subnode.tail
                        listExpression.append(subnode.attrib.get('CONTENTIDS'))
                        
                        # MANIFESTATION
                        for subsubnode in subnode.getchildren():
                            #print subsubnode.tag, subsubnode.attrib, subsubnode.text, subsubnode.tail 
                            for fptrnode in subsubnode.getchildren():
                                #print fptrnode.attrib
                                fileid=" fileid:"+fptrnode.attrib.get('FILEID')
                                listManifestation.append(fptrnode.attrib.get('CONTENTIDS')+fileid)
                                                                           
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : structMap (Work/Expression/Manifestation)- work readed"
        logger.info('structMap - work " : %s ' %(contentids_divwork))

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate+ " : End of the  reading %s " % xmlfile

        # Store METS INFO
        global tupMetsInfo
        tupMetsInfo = (metsDocID,profile,type,create,contentids_divwork);

        global totalFilesinMETS
        totalFilesinMETS = len(list_rdf) + len(list_amdrdf) + len(list_filename)
        return True
    except Exception, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate +' : Error %s' % e
        logger.error('Error during the reading of the METS XML %s ' % xmlfile)
        logger.error('%s' % e)
        sendEMail("Error during the reading of the METS XML :%s" %e,xmlfile)
        return False

#
# Read METS XML
#
def readMETSXML(xmlFile,sip):

    try :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Read METS XML %s " %xmlFile
        logger.info('Read METS XML %s ' %xmlFile)
        retparse = parseMetsXML(xmlFile)
        if retparse == False:
            logger.error('Error during the reading of the METS XML %s ' %xmlFile)
            return False

        serie=""
        idnum=""
        idyear=""
        idext=""
        publang=""
        pubvol=""
        typeOfcollection=""
        splitpub=""
        
        cellarId=""
        celex=""
        comnat=""
        uriserv=""
        
        global collectionTodir
        collectionTodir =""
        
        # Store XML Data in DB
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Store information (AMDSec,DMDSec ...) from METS XML %s " %xmlFile
        logger.info('Store information (AMDSec,DMDSec ...) from METS XML %s ' %xmlFile)

        # Store METS info
        global metsdocid
        metsdocid = tupMetsInfo[0]
        metsprofile = tupMetsInfo[1]
        metstype = tupMetsInfo[2]
        metscreatedate = tupMetsInfo[3]
        structmap_contentids = tupMetsInfo[4]

        print "%s - %s - %s - %s - %s " %(metsdocid,metsprofile,metstype,metscreatedate,structmap_contentids)

        dicoids = {}

        for item in (structmap_contentids).split(' '):
            #print "%s" % item
            
            if "eli" in item :
                key ="eli"
                value=item
            else :
                key,value = item.split(':',1)
                #print "%s ******* %s" % (key,value)
                dicoids[key] = value
  
        # Get information of the publication
               
        if 'oj' in dicoids :
          
            typeOfcollection = "oj"
            cellarId = dicoids.get('cellar')
            
            collection=dicoids.get('oj')
            collectionTodir = collection
                       
            splitpub = collection.split('_')
            serie = splitpub[0]
            
            if 'JO' in serie :
                idyear = splitpub[1]
                idnum = splitpub[2]
                idext = splitpub[3]
                
            if 'DD' in serie :
                uriserv = dicoids.get('uriserv')
                idyear = splitpub[1]
                idnum = splitpub[2]
                pubvol = splitpub[3]
                publang = splitpub[4]
        
        elif 'com' in dicoids:                           
       
                celex = dicoids.get('celex')
                comnat = dicoids.get('comnat')
                cellarId = dicoids.get('cellar')
               
                collection=dicoids.get('com')
                collectionTodir = collection
                       
                typeOfcollection = "com"
                splitpub = collection.split('_')
                serie = splitpub[0]
                idyear = splitpub[1]
                idnum = splitpub[2]
                        
        elif 'genpub' in dicoids:
              
            cellarId = dicoids.get('cellar')
            
            collection=dicoids.get('genpub')
            collectionTodir = collection
                                              
            typeOfcollection = "genpub"
            serie = 'genpub'
            if "." in collection :
                splitpub = collection.split('.')
                idyear = splitpub[0]
                idnum = splitpub[1]
            elif "_" in collection :
                splitpub = collection.split('_')
                idyear = splitpub[0]
                idnum = splitpub[1]
            else :
                idyear = ""
                idnum = ""

        else :
            cellarId = dicoids.get('cellar')
        
            collection="not defined"           
                       
            typeOfcollection = "other"
            celex = dicoids.get('celex')
            comnat = dicoids.get('comnat')
            uriserv = dicoids.get('uriserv')
            serie="other"
            
            if celex is not None :
                collectionTodir = celex
            elif uriserv is not None :
                collectionTodir = uriserv
            elif comnat is not None:
                collectionTodir = comnat
            elif cellarId is not None:
                collectionTodir = cellarId
            else :
                collectionTodir = "notdefined"   
                
        try :
            Query = "INSERT INTO metsinfo (metsdocid, metsprofile,pubserie,pubid_year,pubid_number,pubid_ext,pubvol,publang,"
            Query +="packagetype,createdate,infopackage_packagename,pubtype,idcellar,celexid,comnat,uriserv) "
            Query += "VALUES ('%s','%s','%s','%s','%s','%s','%s','%s', '%s', '%s', " %(metsdocid,metsprofile,serie,idyear,idnum,idext,pubvol,publang,metstype,metscreatedate)
            Query += " (select packagename from infopackage WHERE packagename='%s') ," % sip
            Query += " '%s','%s' , '%s', '%s', '%s')" %(typeOfcollection,cellarId,celex,comnat,uriserv)
            logger.info('Execute Query : %s' % Query)
            #print Query
            
            retins = insertQuery(Query)
            if retins == False :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + ' : Error during to insert of METS INFO : %s' % sip
                return False
               
        except psycopg2.DatabaseError, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + ' : %s' % e
            logger.error('%s' % e)
            sendEMail("Error during to insert of METS INFO  %s : %e "%(sip,e),sip) 
            return False
                  
                
        # Control if WORK exists
        ########################
        retcheck = checkWorkexists(cellarId,collection)
        if retcheck == True:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : WORK %s exists "%collection
            print "XML FILE %s" %xmlFile
            retmodifmets = modifMetsXML(xmlFile)
            if retmodifmets == False :
                logger.error('Error during the check of WORK')
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : Error during the check of WORK %s "  %sip
                return False
            elif retmodifmets == True :
                logger.info('Change Type of METS XML (create to update) %s' %sip)
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : Change Type of METS XML (create to update) %s" %sip
                
                try :
                    sipZip = os.path.join(workdir,sip)
                    #newZip = os.path.join(workdir,"new_"+sip)
                    newxml = os.path.join(workdir,xmlFile)
                    
                    '''
                    # create a temp copy of the archive without filename            
                    with zipfile.ZipFile(sipZip, 'r',compression=zipfile.ZIP_DEFLATED,allowZip64=True) as zin:
                        with zipfile.ZipFile(newZip, 'w',compression=zipfile.ZIP_DEFLATED,allowZip64=True) as zout:
                            zout.comment = zin.comment # preserve the comment
                            for item in zin.infolist():
                                if item.filename != xmlFile:
                                    zout.write(item, zin.read(item.filename))
                                    #zout.writestr(item, zin.read(item.filename),compress_type=zipfile.ZIP_DEFLATED)
                    
                    zout.close()
                    zin.close()
                    
 
                    try :
                        # Add a new METS in ZIP
                        zip_object = ZipFile(newZip, mode='a',compress_type=zipfile.ZIP_DEFLATED,allowZip64=True)  
                        zip_object.write(newxml, os.path.basename(xmlFile), compress_type=zipfile.ZIP_DEFLATED)
                        zip_object.close()
                    except zipfile.LargeZipFile,ze:
                        print "%s" %ze     
                
                    
                                    
                    os.remove(sipZip)
                    os.rename(newZip, sipZip)
                    
                    '''
                    # Update ZIP with sub process
                    #############################
                    
                    subprocess.check_output(["zip","-d", sipZip,xmlFile])
                    subprocess.check_output(["zip","-ju", sipZip,newxml])
                    
                    # Update METSINFO
                    updateQuery = "UPDATE metsinfo SET packagetype = 'update' "
                    updateQuery += "  where infopackage_packagename ='%s' " %sip
                    retupd=updateDB(updateQuery)
                    if retupd == False:
                        ts = time.time()
                        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                        print fdate + " : 'Error during the update in METSINFO  - %s" %sip
                        logger.error('Error during the update in METSINFO - %s' %sip)
                        return False
                                                            
                except zipfile.LargeZipFile,ze:
                    print "%s" %ze          
        
            
        elif retcheck == None :
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : WORK %s doesnt exist "%collection

        elif retcheck == False :
            logger.error('Error during the check of WORK')
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : Error during the check of WORK %s "  %sip
            return False
               
        

    except Exception, e :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + ' : %s' % e
        logger.error('%s' % e)
        sendEMail("Error during the XML parsing %s : %e "%(sip,e),sip) 
        return False
  
  
    return True

#
# Insert DB
#
def insertQuery(Query):

    # Database Paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]

    try:
        # Database Connection
        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()

        logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
        logger.info('Execute Query : %s' % Query)

        cur.execute(Query)
        con.commit()
        cur.close()
        con.close()
        return True
    except psycopg2.DatabaseError, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Error %s " % e
        logger.error('Error during a database transaction')
        logger.error('%s ' %e)
        sendEMail("Error during a database transaction %s : " %e,sip)
        #sys.exit(1)
        con.rollback()
        cur.close()
        con.close()
        return False


#
# Store data in the database
#
def storeToDB(dicToStore,tableToStore,metsdocid):

    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]

    # List used to store the data in the database
    listcolumn = []
    listvaleur = []

    columns_tostore = ""
    values_tostore = ""

    # Connection database
    # Connnection DB
    try:

        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Connect to DB - %s recording " % tableToStore
        logger.info('Connect to DB - %s recording ' % tableToStore)

        j = 0

      
        for k,v in dicToStore.iteritems():
            #print k,len(v)
            #for j in range(0,len(v)):
            if len (dicToStore.keys() ) != 0 :
                while j < len(v):
                    #print "________________________",j+1,"__________________________________"
                    for i in range(len(dicToStore.keys())):
                        #print dicToStore.keys()[i], "-", dicToStore.values()[i][j]
    
                        listcolumn.append(dicToStore.keys()[i])
                        listvaleur.append(dicToStore.values()[i][j])
    
                        table=tableToStore
                        columns_tostore= '('+','.join(listcolumn)+',metsinfo_metsdocid)'
                        values_tostore = "('"+"','".join(map(str,listvaleur))+"', (select metsdocid from metsinfo where metsdocid ='%s') )" % metsdocid
    
                        insertquery = """INSERT INTO %s %s
                        VALUES %s"""%(table,columns_tostore,values_tostore)
                        #print insertquery
    
                        logger.info('Execute Query : %s ' % insertquery)
                    #print "Store data in database"
                    #print "-------->>>" ,insertquery
                    cur.execute(insertquery)
                    con.commit()
                    
                    # Clear the lists
                    listcolumn = []
                    listvaleur = []
                    j += 1
        return True
    except psycopg2.DatabaseError, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + ' : Error %s' % e
            logger.error('Error during the insertion in the DB of the data from METS XML')
            logger.error('%s' % e)
            sendEMail("Error during the insertion in the DB of the data from METS XML: %s" %e,metsdocid)
            con.rollback()
            con.close()
            return False


#
# Store Work
def storeWorkPub(listWork):

    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]
    
    global cellarId
    cellarId=""
    global collection
    collection=""
    serie=""
    idyear= ""
    idnum=""
    idext= ""
    pubvol=""
    uriserv=""
    comnat=""
    publang=""
    contentids=""
    celex=""
    typeOfcollection=""
        

    try:

        # Insert WORK
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Connect to DB - WORKPUB recording "
        
        dicoWork = {}
                
        for item in (listWork):
            #print "-------------------------- %s " %item
            contentids=item
           
            for element in (item).split(' '):
                if "eli" in element :
                    key ="eli"
                    value=element
                else :
                    key,value = element.split(':',1)
                    dicoWork[key] = value
                    
        if 'oj' in dicoWork :
                  
            typeOfcollection = "oj"
            
            if dicoWork.has_key('cellar') is True :
                cellarId = dicoWork.get('cellar')
            
            if dicoWork.has_key('oj') is True :
                collection=dicoWork.get('oj')                             
                splitpub = collection.split('_')
                serie = splitpub[0]
            
                if 'JO' in serie :
                    idyear = splitpub[1]
                    idnum = splitpub[2]
                    idext = splitpub[3]
                
                if 'DD' in serie :
                    uriserv = dicoWork.get('uriserv')
                    idyear = splitpub[1]
                    idnum = splitpub[2]
                    pubvol = splitpub[3]
                    publang = splitpub[4]
        
        elif 'com' in dicoWork:
                           
            celex = dicoWork.get('celex')
            comnat = dicoWork.get('comnat')
            cellarId = dicoWork.get('cellar')
               
            collection=dicoWork.get('com')
            typeOfcollection = "com"
            splitpub = collection.split('_')
            serie = splitpub[0]
            idyear = splitpub[1]
            idnum = splitpub[2]
            
        elif 'genpub' in dicoWork:
            
            cellarId = dicoWork.get('cellar')           
            collection=dicoWork.get('genpub')
            typeOfcollection = "genpub"
      
            serie = "genpub"
         
            if "." in collection :
                splitpub = collection.split('.')
                idyear = splitpub[0]
                idnum = splitpub[1]
            elif "_" in collection :
                splitpub = collection.split('_')
                idyear = splitpub[0]
                idnum = splitpub[1]
            else :
                idyear = ""
                idnum = ""
        
        elif 'consil' in dicoWork:

            cellarId = dicoWork.get('cellar')
            collection = dicoWork.get('consil')
            typeOfcollection = "consil"
            serie = "consil"
            idyear = ""
            idnum = ""
        
        elif 'legissum' in dicoWork:

            cellarId = dicoWork.get('cellar')
            collection = dicoWork.get('legissum')
            typeOfcollection = "legissum"
            serie = "legissum"
            idyear = ""
            idnum = ""                 
           
        elif 'swd' in dicoWork:

            cellarId = dicoWork.get('cellar')
            collection = dicoWork.get('swd')
            typeOfcollection = "swd"
            serie = "swd"
            idyear = ""
            idnum = ""  
        
        elif 'join' in dicoWork:

            cellarId = dicoWork.get('cellar')
            collection = dicoWork.get('swd')
            typeOfcollection = "swd"
            serie = "swd"
            idyear = ""
            idnum = ""  
            
        else :
            celex = dicoWork.get('celex')
            comnat = dicoWork.get('comnat')
            cellarId = dicoWork.get('cellar')
            uriserv = dicoWork.get('uriserv')
            collection="not defined"
            typeOfcollection = "other"
            serie = "other"
                        
        
        dmdidWork=dicoWork.get('dmdid_work')
        
        global serieTodest
        serieTodest = serie
          
        # Database Connection
        con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
        cur = con.cursor()

        logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
        #print "Database    : ",db," - ",dbhost," - ",portnum," - ",usr," - ",pwd

        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate +" : ContentIDS : %s" %contentids

        # Check if SIP exists in DB
        logger.info('Verify if WORK already exists in database ')
        selectQuery= "SELECT count(contentids) from workpub "
        #selectQuery += " where contentids like '%"+contentids+"%'"
        selectQuery += " where idcellar = '"+cellarId+"'"
        logger.info('Execute Query : %s' % selectQuery)

        result=cur.execute(selectQuery)
        count_row = cur.fetchone()
        count = count_row[0]

       
        if count == 0:
            logger.info('Insert WORK in workpub %s' % contentids)
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            #print fdate + " Insert WORK in workpub %s " % cellarId
            
            insertQuery = "INSERT INTO workpub (dmdid,contentids,idcellar, celexid,collection,pubserie,pubid_year,pubid_number,pubid_ext, "
            insertQuery += "pubtype,comnat,uriserv) "
            insertQuery += "VALUES ('%s','%s','%s','%s','%s','%s','%s','%s','%s','%s','%s','%s')" % (dmdidWork,contentids,cellarId,celex,collection,serie,idyear,idnum,idext,typeOfcollection,comnat,uriserv)
            logger.info('Execute Query : %s' % insertQuery)
            #print insertQuery
            cur.execute(insertQuery)
            con.commit()
            cur.close()
            return True
        else :
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                       
            # Verify if contentids is identical
            logger.info('Verify if contentids (%s) is identical for the idcellar (%s)  '%(contentids,cellarId))
            print fdate + " : Verify if contentids (%s) is identical for the idcellar (%s) " %(contentids,cellarId)
            idsQuery= "SELECT count(contentids) from workpub "
            idsQuery += " where idcellar = '"+cellarId+"'"
            idsQuery += " and contentids = '"+contentids+"'"
            logger.info('Execute Query : %s' % idsQuery)

            resultids=cur.execute(idsQuery)
            count_row = cur.fetchone()
            countids = count_row[0]
            print countids
            
            if countids == 0:   
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : Update workpub with a new contentids %s " % contentids
                logger.info('Update workpub %s ' % contentids)
                updateQuery = "UPDATE workpub SET lastupdate = current_timestamp, contentids='%s'" %contentids
                updateQuery += "  where idcellar = '"+cellarId+"'"
                logger.info('Execute Query : %s' % updateQuery)
                cur.execute(updateQuery)
                con.commit()
                cur.close()
            else :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')                   
                print fdate + " : Update workpub  %s " % contentids
                logger.info('Update workpub %s ' % contentids)
                updateQuery = "UPDATE workpub SET lastupdate = current_timestamp"
                updateQuery += "  where idcellar = '"+cellarId+"'"
                logger.info('Execute Query : %s' % updateQuery)
                #print "Update ", updateQuery
                cur.execute(updateQuery)
                con.commit()
                cur.close()
            return True
    except psycopg2.DatabaseError, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + ' : Error %s' % e
            logger.error('Error during the insertion in the DB of the Work')
            logger.error('%s' % e)
            sendEMail("WORK insertion failed: %s" %e,sip)
            con.rollback()
            con.close()
            return False
# 
# Store Expression
#
def storeExpression(listExpression):

    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]
   
    try :
        # Insert Expression
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Connect to DB - EXPRESSION recording "
            
        cellarId = ""
        collection = ""
        idext = ""
        uriserv =""
        comnat =""
        publang =""
        celex =""
        typeOfcollection =""
        contentids=""
        dmdidExpression=""
    
        for item in (listExpression):
            print "---------------------- %s -------------" % item
            contentids=item
            
            #print "---- Contentids %s"%contentids
            dicoExpression={}
            for element in (item).split(' '):
                key,value = element.split(':',1)
                dicoExpression[key] = value
    
            if 'oj' in dicoExpression :
                    typeOfcollection = "oj"
                    
                    if dicoExpression.has_key('cellar') is True :
                        cellartmp = dicoExpression.get('cellar')            
                        splitcellar = cellartmp.split('.')
                        cellarId = splitcellar[0]
                        idext = splitcellar[1]
                        
                    if dicoExpression.has_key('oj') is True :
                        collection=dicoExpression.get('oj')
                        lglist=[]
                        for line in collection.split('.'):
                            lglist.append(line)
                            publang = lglist[-1]
                            
                    if dicoExpression.has_key('uriserv') is True :             
                        uriserv = dicoExpression.get('uriserv')
                       
            elif 'com' in dicoExpression:
                               
                    celex = dicoExpression.get('celex')
                    comnat = dicoExpression.get('comnat')
                    cellartmp = dicoExpression.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1]
               
                    collection=dicoExpression.get('com')
                    #publang = collection.split('.')[1]
                    lglist=[]
                    for line in collection.split('.'):
                        lglist.append(line)
                    publang = lglist[-1]
                    
                    #print "--------->>>>>>>>>>>>> %s" %publang
                    uriserv = dicoExpression.get('uriserv')
                    
            elif 'genpub' in dicoExpression:
                               
                    cellartmp = dicoExpression.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1]
               
                    collection=dicoExpression.get('genpub')
                                  
                    lglist=[]
                    for line in collection.split('.'):
                        lglist.append(line)
                    publang = lglist[-1]
                    
                    #print "--------->>>>>>>>>>>>> %s" %publang
                    uriserv = dicoExpression.get('uriserv')
                    
            elif 'consil' in dicoExpression:
                
                cellartmp = dicoExpression.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]

                collection = dicoExpression.get('consil')
                # publang = collection.split('.')[1]
                lglist = []
                for line in collection.split('.'):
                    lglist.append(line)
                publang = lglist[-1]

                # print "--------->>>>>>>>>>>>> %s" %publang
            
            elif 'legissum' in dicoExpression:
                
                cellartmp = dicoExpression.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]

                collection = dicoExpression.get('legissum')
                # publang = collection.split('.')[1]
                lglist = []
                for line in collection.split('.'):
                    lglist.append(line)
                publang = lglist[-1]

                #print "--------->>>>>>>>>>>>> %s" %publang
                
            elif 'swd' in dicoExpression:
                
                cellartmp = dicoExpression.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]

                collection = dicoExpression.get('swd')
                # publang = collection.split('.')[1]
                lglist = []
                for line in collection.split('.'):
                    lglist.append(line)
                publang = lglist[-1]

                #print "--------->>>>>>>>>>>>> %s" %publang
            
            elif 'join' in dicoExpression:
                
                cellartmp = dicoExpression.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]

                collection = dicoExpression.get('join')
                # publang = collection.split('.')[1]
                lglist = []
                for line in collection.split('.'):
                    lglist.append(line)
                publang = lglist[-1]

                #print "--------->>>>>>>>>>>>> %s" %publang
                

            else:
                uriserv = dicoExpression.get('uriserv')
                cellartmp = dicoExpression.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]
                collection = "not defined"
                celex = dicoExpression.get('celex')
                comnat = dicoExpression.get('comnat')

                if 'celex' in dicoExpression:
                    checkpublang = celex.split('.')[1]
                    if len(checkpublang) == 3:
                        publang = checkpublang
                    elif len(checkpublang) > 3:
                        publang = celex.split('.')[2]
                elif 'comnat' in dicoExpression:
                    checkpublang = comnat.split('.')[1]
                    if len(checkpublang) == 3:
                        publang = checkpublang
                    elif len(checkpublang) > 3:
                        publang = comnat.split('.')[2]
                else:
                    premval = list(dicoExpression.values())[0]
                    premkey = list(dicoExpression.keys())[0]
                    #print "premkey %s - premval %s"%(premkey,premval)
                    
                    collection = dicoExpression.get(premkey)
                    lglist = []
                    for line in collection.split('.'):
                        lglist.append(line)
                        publang = lglist[-1]
                        
                              
            dmdidExpression= dicoExpression.get('dmdid_expression')
            # Database Connection
            con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
            cur = con.cursor()
    
            logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
            #print "Database    : ",db," - ",dbhost," - ",portnum," - ",usr," - ",pwd
    
            # Check if SIP exists in DB
            logger.info('Verify if Expresssion already exists in database ')
            selectQuery= "SELECT count(contentids) from expression "
            selectQuery += " where idcellar = '"+cellarId+"' "
            selectQuery += " and lang = '"+publang+"' "
            logger.info('Execute Query : %s' % selectQuery)
    
            result=cur.execute(selectQuery)
            count_row = cur.fetchone()
            count = count_row[0]
    
            if count == 0:
                logger.info('Insert Expresssion %s' % cellarId)
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                #print fdate + " Insert Expression %s " % cellarId
                
                insertQuery = "INSERT INTO expression (dmdid,contentids,idcellar, idext,collection,lang,comnat,celexid,uriserv ) "
                insertQuery += "VALUES ('%s','%s','%s','%s','%s','%s','%s','%s','%s')" % (dmdidExpression,contentids,cellarId,idext,collection,publang,comnat,celex,uriserv)
                logger.info('Execute Query : %s' % insertQuery)
                #print insertQuery
                cur.execute(insertQuery)
                con.commit()
                cur.close()
                
            else :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                #print fdate + " : Update expression %s " % cellarId
                logger.info('Update expression %s ' % cellarId)
                
                updateQuery = "UPDATE expression SET lastupdate = current_timestamp "
                updateQuery += " where idcellar = '"+cellarId+"'"
                updateQuery += " and lang = '"+publang+"' "
                logger.info('Execute Query : %s' % updateQuery)
                #print "Update ", updateQuery
                cur.execute(updateQuery)
                con.commit()
                cur.close()
                
    except psycopg2.DatabaseError, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + ' : Error %s' % e
            logger.error('Error during the insertion in the DB of the Expression')
            logger.error('%s' % e)
            sendEMail("EXPRESSSION insertion failed: %s" %e,sip)
            con.rollback()
            con.close()
            return False
                              
    return True    

# Store Manifestation
def storeManifestation(listManifestation):

    # DB paramaters
    db = tupDB[0]
    dbhost = tupDB[1]
    usr = tupDB[2]
    pwd = tupDB[3]
    portnum = tupDB[4]

    try :
        # Insert Expression
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Connect to DB - MANIFESTATION recording "
            
        cellarId =""
        collection=""
        idext =""
        uriserv =""
        comnat =""
        publang =""
        celex =""
        doctype =""
        filename =""
        doctype =""
        fileid =""
        item=""      
        
        for item in (listManifestation):
            
            print "+++ %s" % item
            cellarId=""
            collection=""
            idext=""
            uriserv=""
            comnat=""
            publang=""
            celex=""
            doctype=""
            filename=""
            doctype=""
            fileid=""
            contentids=""
            
            dicoManifestation={}
                   
            for element in (item).split(' '):
                key,value = element.split(':',1)
                dicoManifestation[key] = value
            
            contentids=item
             
            if 'oj' in dicoManifestation :
                
                if dicoManifestation.has_key('cellar') is True :                
                    cellartmp = dicoManifestation.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1]+splitcellar[2]
                    
                if dicoManifestation.has_key('oj') is True :      
                    collection=dicoManifestation.get('oj')            
                    checkpublang = collection.split('.')[1]
                    if len(checkpublang)==3:
                        publang=checkpublang
                        doctype = collection.split('.')[2]  
                    elif len(checkpublang) >3:
                        publang = collection.split('.')[2]
                        doctype = collection.split('.')[3]  
    
                    seperator = ".%s." % doctype
                    filetmp =  collection.split(seperator)
                    filename = filetmp[1]
                
                if dicoManifestation.has_key('uriserv') is True :  
                    uriserv = dicoManifestation.get('uriserv')
                
                if dicoManifestation.has_key('fileid') is True : 
                    fileid = dicoManifestation.get('fileid')
                    
                #print "collection %s - cellarid %s ext %s - %s - %s - %s" % (collection,cellarId,idext,fileid,doctype,filename) 
                
            elif 'com' in dicoManifestation:
                               
                celex = dicoManifestation.get('celex')
                comnat = dicoManifestation.get('comnat')
                cellartmp = dicoManifestation.get('cellar')
                
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]+splitcellar[2]
                    
                          
                collection=dicoManifestation.get('com')
                #publang = collection.split('.')[1]
                #doctype = collection.split('.')[2]
                
                checkpublang = collection.split('.')[1]
                if len(checkpublang)==3:
                    publang=checkpublang
                    doctype = collection.split('.')[2]  
                elif len(checkpublang) >3:
                    publang = collection.split('.')[2]
                    doctype = collection.split('.')[3]  
                
                seperator = ".%s." % doctype
                filetmp =  collection.split(seperator)
                filename = filetmp[1]
                   
                uriserv = dicoManifestation.get('uriserv')
                fileid = dicoManifestation.get('fileid')
                    
                #print "collection %s - cellarid %s ext %s - %s - %s - %s" % (collection,cellarId,idext,fileid,doctype,filename) 
            
            elif 'genpub' in dicoManifestation:
                               
                cellartmp = dicoManifestation.get('cellar')            
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]+splitcellar[2]
                    
                collection=dicoManifestation.get('genpub')
                if len(collection)<25 :
                    pubidtmp = collection.replace('.', '_', 1)
                    #pubidtmp = collection.replace('.','_')
                    doctype = pubidtmp.split('_')[2]
                else :
                    doctype = collection.split('_')[2]
                    pubidtmp = collection.replace('.','_')
                #print "+++++ doctype %s " % doctype
               
                pubid =  pubidtmp.split('_')[1]
                taille=len(pubid)
                publang=pubid [taille-3:taille]
    
                #print "+++++ lang %s" % publang
                filename = dicoManifestation.get('genpub')
                fileid = dicoManifestation.get('fileid') 
                   
            elif 'consil' in dicoManifestation:
                if dicoManifestation.has_key('cellar') is True:
                    cellartmp = dicoManifestation.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1] + splitcellar[2]

                collection = dicoManifestation.get('consil')
                 
                checkpublang = collection.split('.')[1]
                if len(checkpublang) == 3:
                    publang = checkpublang
                    doctype = collection.split('.')[2]
                elif len(checkpublang) > 3:
                    publang = collection.split('.')[2]
                    doctype = collection.split('.')[3]

                seperator = ".%s." % doctype
                filetmp = collection.split(seperator)
                filename = filetmp[1]

                fileid = dicoManifestation.get('fileid')
                         
            
            elif 'legissum' in dicoManifestation:
                if dicoManifestation.has_key('cellar') is True:
                    cellartmp = dicoManifestation.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1] + splitcellar[2]

                collection = dicoManifestation.get('legissum')
                 
                checkpublang = collection.split('.')[1]
                if len(checkpublang) == 3:
                    publang = checkpublang
                    doctype = collection.split('.')[2]
                elif len(checkpublang) > 3:
                    publang = collection.split('.')[2]
                    doctype = collection.split('.')[3]

                seperator = ".%s." % doctype
                filetmp = collection.split(seperator)
                filename = filetmp[1]

                fileid = dicoManifestation.get('fileid')          
                
            elif 'swd' in dicoManifestation:
                if dicoManifestation.has_key('cellar') is True:
                    cellartmp = dicoManifestation.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1] + splitcellar[2]

                collection = dicoManifestation.get('swd')
                 
                checkpublang = collection.split('.')[1]
                if len(checkpublang) == 3:
                    publang = checkpublang
                    doctype = collection.split('.')[2]
                elif len(checkpublang) > 3:
                    publang = collection.split('.')[2]
                    doctype = collection.split('.')[3]

                seperator = ".%s." % doctype
                filetmp = collection.split(seperator)
                filename = filetmp[1]

                fileid = dicoManifestation.get('fileid')    
        
            elif 'join' in dicoManifestation:
                if dicoManifestation.has_key('cellar') is True:
                    cellartmp = dicoManifestation.get('cellar')
                    splitcellar = cellartmp.split('.')
                    cellarId = splitcellar[0]
                    idext = splitcellar[1] + splitcellar[2]

                collection = dicoManifestation.get('join')
                 
                checkpublang = collection.split('.')[1]
                if len(checkpublang) == 3:
                    publang = checkpublang
                    doctype = collection.split('.')[2]
                elif len(checkpublang) > 3:
                    publang = collection.split('.')[2]
                    doctype = collection.split('.')[3]

                seperator = ".%s." % doctype
                filetmp = collection.split(seperator)
                filename = filetmp[1]

                fileid = dicoManifestation.get('fileid')      
                
            else:
                uriserv = dicoManifestation.get('uriserv')
                cellartmp = dicoManifestation.get('cellar')
                splitcellar = cellartmp.split('.')
                cellarId = splitcellar[0]
                idext = splitcellar[1]

                fileid = dicoManifestation.get('fileid')
                collection = "not defined"
                celex = dicoManifestation.get('celex')
                comnat = dicoManifestation.get('comnat')

                if celex != None:

                    checkpublang = celex.split('.')[1]
                    if len(checkpublang) == 3:
                        publang = checkpublang
                        doctype = celex.split('.')[2]
                    elif len(checkpublang) > 3:
                        publang = celex.split('.')[2]
                        doctype = celex.split('.')[3]

                    seperator = ".%s." % doctype
                    filetmp = celex.split(seperator)
                    filename = filetmp[1]

                elif comnat != None:
                    checkpublang = comnat.split('.')[1]
                    if len(checkpublang) == 3:
                        publang = checkpublang
                        doctype = comnat.split('.')[2]
                    elif len(checkpublang) > 3:
                        publang = comnat.split('.')[2]
                        doctype = comnat.split('.')[3]

                    seperator = ".%s." % doctype
                    filetmp = comnat.split(seperator)
                    filename = filetmp[1]
                    
                else:
                    premval = list(dicoManifestation.values())[0]
                    premkey = list(dicoManifestation.keys())[0]
                    
                    print "premkey %s - premval %s"%(premkey,premval)
                    
                    collection = dicoManifestation.get(premkey)
                    
                    checkpublang = collection.split('.')[1]
                    if len(checkpublang) == 3:
                        publang = checkpublang
                        doctype = collection.split('.')[2]
                    elif len(checkpublang) > 3:
                        publang = collection.split('.')[2]
                        doctype = collection.split('.')[3]
         
                    seperator = ".%s." % doctype
                    filetmp = collection.split(seperator)
                    filename = filetmp[1]
               
                    fileid = dicoManifestation.get('fileid')
                
                
            # Database Connection
            con = psycopg2.connect(dbname=db,host=dbhost,user=usr,password=pwd,port=portnum)
            cur = con.cursor()
    
            logger.info('Connection to database %s - %s - %s ' % (db,dbhost,usr))
            #print "Database    : ",db," - ",dbhost," - ",portnum," - ",usr," - ",pwd
    
            # Check if Manifestation exists in DB
            logger.info('Verify if Manifestation already exists in database ')
            selectQuery= "SELECT count(fileid) from manifestation "
            selectQuery += " where fileid = '%s' " % fileid
            selectQuery += " and  collection = '%s' " % collection
            selectQuery += " and  filename = '%s' " % filename
            logger.info('Execute Query : %s' % selectQuery)
    
            result=cur.execute(selectQuery)
            count_row = cur.fetchone()
            count = count_row[0]
    
            if count == 0:
                logger.info('Insert Manifestation %s' % cellarId)
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                #print fdate + " Insert Manifestation %s " % cellarId
                
                insertQuery = "INSERT INTO manifestation (contentids,idcellar, idext,collection,lang,doctype,filename,fileid,comnat,celexid,uriserv ) "
                insertQuery += "VALUES ('%s','%s','%s','%s','%s','%s','%s','%s','%s','%s','%s')" % (contentids,cellarId,idext,collection,publang,doctype,filename,fileid, comnat,celex,uriserv)
                logger.info('Execute Query : %s' % insertQuery)
                #print insertQuery
                cur.execute(insertQuery)
                con.commit()
                cur.close()
                
            else :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                #print fdate + " : Update manifestation %s " % cellarId
                logger.info('Update manifestation %s ' % cellarId)
                
                updateQuery = "UPDATE manifestation SET lastupdate = current_timestamp"
                updateQuery += " where collection ='%s' and fileid = '%s' and filename ='%s' " % (collection,fileid,filename)
                logger.info('Execute Query : %s' % updateQuery)
                #print "Update ", updateQuery
                cur.execute(updateQuery)
                con.commit()
                cur.close()
                
    except psycopg2.DatabaseError, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + ' : Error %s' % e
            logger.error('Error during the insertion in the DB of the Manifestation')
            logger.error('%s' % e)
            sendEMail("MANIFESTATION insertion failed: %s" %e,sip)
            con.rollback()
            con.close()
            return False

    return True      

#
# Control SIP Package
#
def controlSIP(sip_path):

    totalFiles = ""
    sizeinbyte =""
    
    # Iniatialize Dictionnaire
    DMDdic={}
    AMDdic={}
    FILEdic={}

    # Set Dictionnaire
    DMDdic = {
            "dmdid" : list_dmdid,
            "rdfile" : list_rdf,
            "checksumtype" : list_chksumtype,
            "checksum" : list_chksum,
            "mimetype" : list_mimetype,
            }
    AMDdic={
                "mimetype" : list_amdmimetype,
                "checksumtype" : list_amdchksumtype,
                "checksum" : list_amdchksum,
                "rdfile" : list_amdrdf,
                "techmdid" : list_techmdid,
                "amdid" : list_techmdid,
            }
    FILEdic={
                 "fileid" : list_fileid,
                 "checksumtype" : list_filechksumtype,
                 "checksum" : list_filechksum,
                 "filename" : list_filename,
                 "mimetype" : list_filemimetype,
                 }
    
    sip = os.path.basename(sip_path)
    
    try:
        # Extract SIP Name from the path
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        receiptdate = fdate       
        
                     
        print fdate + " : Control of SIP ",sip
        logger.info('Control of SIP %s'  % sip)

        # Move SIP to Workdir to the different controls
        ###############################################
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Move ",sip," to Workdir ",workdir
        logger.info('Move SIP to %s' % workdir)
        sipinWorkdir=os.path.join(workdir,sip)
        shutil.move(sip_path, sipinWorkdir)
        
        # Backup of original SIP
        #################################                        
        '''
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Backup of SIP %s" %sip
                
        src = os.path.join(workdir,sip)
        dst = os.path.join(backupdir,sip)
                
        shutil.copyfile(src, dst)
        '''                
           
        # Check opening of ZIP File
        ###############################################
        retopenzfile = openingZip(sipinWorkdir)
        if retopenzfile == False :
            # Move sip to Rejected directory
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : Checking of opening SIP failed %s "  %sip
            moveSIP(workdir,rejdir,sip)
            return False
                
        # Get Information about SIP (create, size, total files ...)
        # Store SIP in DATABASE
        ###########################################################
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Get information about package %s" % sip

        # total files in SIP package
        totalFiles = 0
        zfile = zipfile.ZipFile(sipinWorkdir)
        for item in zfile.namelist():
            totalFiles= totalFiles+1
        zfile.close()

        print fdate + " : Total Files : " , totalFiles
        logger.info("Total Files %d "  % totalFiles)
                
        # Size for the package
        sizeinbyte = 0
        sizeinbyte = os.path.getsize(sipinWorkdir)
        print fdate + " : Size in bytes : ", sizeinbyte
        logger.info("Size in bytes %d  " % sizeinbyte)

        # Date of SIP (Create and Last Modfication)
        creationDate = time.ctime(os.path.getctime(sipinWorkdir))
        lastModification = time.ctime(os.path.getmtime(sipinWorkdir))
               
        print fdate + " : Created : %s" % creationDate
        print fdate + " : Last modified : %s" % lastModification
                
        # Store SIP in Database
        # Prepare Query to insert the information about the SIP package
        Query = "INSERT INTO infopackage (packagename, receipt_date,status,site,server,service,packagesize,nbfiles,creation_date,last_modification) "
        Query += "VALUES ('%s','%s','INPROGRESS','%s','%s','BACKLOG','%d','%d','%s','%s')" % (sip,receiptdate,sipsite,sipserver,sizeinbyte,totalFiles,creationDate,lastModification)
                
        retStore =storeSIPtoDB(sip, Query)
        if retStore == False:
            # Move SIP to REJECTED
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            return False
        
        # Extract only METS XML for the XSD Validation
        ###############################################
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Control the METS Schema %s " % metsSchema
        # decompress METS File
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Unzip only METS xml %s " % sip
       
        retdezipmets = dezipMETS(sip,workdir,sip)
        if retdezipmets == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            print fdate + " : Workdir Cleaning ."
            removeFiles(workdir,sip)            
            return False
        
        # Valid METS XML
        ########################
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Valid METS Schema %s " % metsSchema
                
        retvalschema = validXML(metsSchema,metsXML,sip)
                
        if retvalschema == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : Error during the METS Validation see the Logs ." 
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            print fdate + " : Workdir Cleaning ."
            removeFiles(workdir,sip)  
            return False
        
        # Parse the METS XML (extract the information needed)
        #####################################################
        retreadxml = readMETSXML(metsXML,sip)
        if retreadxml == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            processdate = fdate
            print fdate + " : Error during the METS XML Parsing %s "  %sip
                              
            # move file to rejected
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            print fdate + " : Workdir Cleaning ."
            removeFiles(workdir,sip)  
            
            # update database
            Query = "UPDATE infopackage SET status ='ERROR', description ='Error during the METS XML Parsing' "
            Query += " ,process_date ='%s' " % processdate
            Query += " where packagename ='%s' " % sip
            retupd=updateDB(Query)
            if retupd == False:
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : 'Error during to the update of theDB  - %s" %sip
                logger.error('Error during to the insertion in DB - %s' %sip)
                sys.exit(1)
             
            return False
        
        # Compare Files in METS and in SIP
        #####################################
        valOfCmp = compareTotalFiles(sip)
        if valOfCmp != 0:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            processDate = fdate
            print fdate + " : A difference of files have been detected between METS XML and %s "  %sip
            # move file to rejected
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            print fdate + " : Workdir Cleaning ."
            removeFiles(workdir,sip)  
            
            # update database
            QueryToExec = "UPDATE infopackage SET status ='ERROR', "
            QueryToExec += " description ='A difference of files have been detected between METS XML and %s (%d)' " %(sip,valOfCmp)
            QueryToExec += " ,process_date ='%s' " % processDate
            QueryToExec += " where packagename ='%s' " % sip
            retupd=updateDB(QueryToExec)
            if retupd == False:
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : 'Error during to the update of theDB  - %s" %sip
                logger.error('Error during to the insertion in DB - %s' %sip)
                sys.exit(1)
            
            return False    
         
        elif valOfCmp ==0:
            # Enregistrement du METS dans la DB (amdsec, dmdsec ..)
            # Store DMDSec            
            if len(DMDdic) !=0 :
            # Remove empty list from dictionnary (checksum,checksumtype)
                if len(list_chksumtype) == 0:
                    del DMDdic['checksumtype']
                if len(list_chksum) == 0:
                    del DMDdic['checksum']
                retstoredb = storeToDB(DMDdic,'dmdsec',metsdocid)       
                if retstoredb == False:
                    logger.error('Error during the insertion into the DMDSec ')
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    processdate = fdate
                    print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                    # move file to rejected
                    print fdate + " : Move %s to %s" %(sip,rejdir)
                    moveSIP(workdir,rejdir,sip)
                    print fdate + " : Workdir Cleaning ."
                    removeFiles(workdir,sip)  
            
                    # update database
                    Query = "UPDATE infopackage SET status ='ERROR', description ='Error during DMDsec insertion .' "
                    Query += " ,process_date ='%s' " % processdate
                    Query += " where packagename ='%s' " % sip
                    retupd=updateDB(Query)
                    if retupd == False:
                        ts = time.time()
                        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                        print fdate + " : 'Error during to the update of theDB  - %s" %sip
                        logger.error('Error during to the insertion in DB - %s' %sip)
                        sys.exit(1)
                    
                    return False
        
            # Store AMDSec
            if len(AMDdic) !=0 :
                # Remove empty list from dictionnary (checksum,checksumtype)
                if len(list_amdchksumtype) == 0:
                    del AMDdic['checksumtype']
                if len(list_amdchksum) == 0:
                    del AMDdic['checksum']
                retstoredb = storeToDB(AMDdic,'amdsec',metsdocid)
                if retstoredb == False:
                    logger.error('Error during the insertion into the AMDSec ')
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    processdate = fdate
                    print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                    # move file to rejected
                    print fdate + " : Move %s to %s" %(sip,rejdir)
                    moveSIP(workdir,rejdir,sip)
                    print fdate + " : Workdir Cleaning ."
                    removeFiles(workdir,sip)  
            
                    # update database
                    Query = "UPDATE infopackage SET status ='ERROR', description ='Error during AMDSec insertion .' "
                    Query += " ,process_date ='%s' " % processdate
                    Query += " where packagename ='%s' " % sip
                    retupd=updateDB(Query)
                    if retupd == False:
                        ts = time.time()
                        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                        print fdate + " : 'Error during to the update of theDB  - %s" %sip
                        logger.error('Error during to the insertion in DB - %s' %sip)
                        sys.exit(1)
                    return False
            # Store FileSec
            if len(FILEdic) !=0 :
            # Remove empty list from dictionnary (checksum,checksumtype)
                if len(list_filechksumtype) == 0:
                    del FILEdic['checksumtype']
                if len(list_filechksum) == 0:
                    del FILEdic['checksum']
                retstoredb = storeToDB(FILEdic,'filesec',metsdocid)
                if retstoredb == False:
                    logger.error('Error during the insertion into the FileSec ')
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    processdate = fdate
                    print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                    # move file to rejected
                    print fdate + " : Move %s to %s" %(sip,rejdir)
                    moveSIP(workdir,rejdir,sip)
                    print fdate + " : Workdir Cleaning ."
                    removeFiles(workdir,sip)  
            
                    # update database
                    Query = "UPDATE infopackage SET status ='ERROR', description ='Error during FILEsec insertion .' "
                    Query += " ,process_date ='%s' " % processdate
                    Query += " where packagename ='%s' " % sip
                    retupd=updateDB(Query)
                    if retupd == False:
                        ts = time.time()
                        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                        print fdate + " : 'Error during to the update of theDB  - %s" %sip
                        logger.error('Error during to the insertion in DB - %s' %sip)
                        sys.exit(1)
                    return False

            # Store Work, Expression, Manifestation
            retstoreWorkPub = storeWorkPub(listWork)
            if retstoreWorkPub == False:
                logger.error('Error during the insertion of the Work ')
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                # move file to rejected
                print fdate + " : Move %s to %s" %(sip,rejdir)
                moveSIP(workdir,rejdir,sip)
                print fdate + " : Workdir Cleaning ."
                removeFiles(workdir,sip)  
            
                # update database
                Query = "UPDATE infopackage SET status ='ERROR', description ='Error during WORK insertion .' "
                Query += " ,process_date ='%s' " % processdate
                Query += " where packagename ='%s' " % sip
                retupd=updateDB(Query)
                if retupd == False:
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    print fdate + " : 'Error during to the update of theDB  - %s" %sip
                    logger.error('Error during to the insertion in DB - %s' %sip)
                    sys.exit(1)
                
                return False
          
            retStoreExpression = storeExpression(listExpression)
            if retStoreExpression == False:
                logger.error('Error during the insertion of the Expression ')
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                # move file to rejected
                print fdate + " : Move %s to %s" %(sip,rejdir)
                moveSIP(workdir,rejdir,sip)
                print fdate + " : Workdir Cleaning ."
                removeFiles(workdir,sip)  
            
                # update database
                Query = "UPDATE infopackage SET status ='ERROR', description ='Error during EXPRESSION insertion .' "
                Query += " ,process_date ='%s' " % processdate
                Query += " where packagename ='%s' " % sip
                retupd=updateDB(Query)
                if retupd == False:
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    print fdate + " : 'Error during to the update of theDB  - %s" %sip
                    logger.error('Error during to the insertion in DB - %s' %sip)
                    sys.exit(1)
                
                return False
              
            retStoreManifestation = storeManifestation(listManifestation)
            if retStoreManifestation == False:
                logger.error('Error during the insertion of the Manifestation ')
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                print fdate + " : Error during the insertion into the DMDSec %s "  %sip
                # move file to rejected
                print fdate + " : Move %s to %s" %(sip,rejdir)
                moveSIP(workdir,rejdir,sip)
                print fdate + " : Workdir Cleaning ."
                removeFiles(workdir,sip)  
            
                # update database
                Query = "UPDATE infopackage SET status ='ERROR', description ='Error during MANIFESTATION insertion .' "
                Query += " ,process_date ='%s' " % processdate
                Query += " where packagename ='%s' " % sip
                retupd=updateDB(Query)
                if retupd == False:
                    ts = time.time()
                    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                    print fdate + " : 'Error during to the update of theDB  - %s" %sip
                    logger.error('Error during to the insertion in DB - %s' %sip)
                    sys.exit(1)
                                
                return False

    
        return True                                 
              
    except Exception, e:
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        processdate = fdate
        print fdate+ " : Error during to control of SIP %s : %s " %(sip,e)
        logger.error('Error during to control of SIP %s : %s' %( sip,e) )
        
        sippath = os.path.join(workdir,sip)       
        if os.path.exists(sippath):
            print fdate + " : Move %s to %s" %(sip,rejdir)
            moveSIP(workdir,rejdir,sip)
            print fdate + " : Workdir Cleaning ."
            removeFiles(workdir,sip)  
        
        # update database
        Query = "UPDATE infopackage SET status ='ERROR', description ='%s' " %e
        Query += " ,process_date ='%s' " % processdate
        Query += " where packagename ='%s' " % sip
        retupd=updateDB(Query)
        if retupd == False:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate + " : 'Error during to the update of theDB  - %s" %sip
            logger.error('Error during to the insertion in DB - %s' %sip)
            sys.exit(1)
        return False
#
# Main Program
#

continuer=True

print "----------------------------------------------"
print "        pre-Ingest BACKLOG "
print "    SIP Control - EUDOR V3 "
print "----------------------------------------------"

# Check total arguments passed
totalarg = len(sys.argv)
if totalarg < 2 :
        print ("Usage :  %s [configuration file]" % str(sys.argv[0]))
        sys.exit(2)

if sys.argv[1] == "-v":
    print " %s : Version %s" %(str(sys.argv[0]),version)
    sys.exit(0)
# Configuration file = argument passed
config = sys.argv[1]

# Check if the configuration file exists
if not os.path.exists(config):
    print ("The configuration file in argument doesn't exist !")
    sys.exit(2)

# Parse configuration file
retparse = parseConfig(config)
# Exit of the program if error during the configuration file parsing
if retparse == False :
    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
    print fdate+ " : Error during the parsing of the configuration file"
    sendEMail("Error during the parsing of the configuration file",None)
    sys.exit(2)

# Initialize the logger
retlogger=initLogger()
# Exit of the program if error during the logger configuration
if retlogger == False :
    ts = time.time()
    fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
    print fdate+ " : Error during the configuration of the Logger"
    sendEMail("Error during the configuration of the Logger",None)
    sys.exit(2)
    
# List the content in the input directory
ts = time.time()
fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
print fdate + " : Waiting of a SIP from the input directory %s " % source
#logging.info('Lecture du repertoire %s'  % source)
logger.info('Waiting of a SIP from the input directory %s '  % source)
# Search SIP in input directory
retscandir=""

while continuer:
    time.sleep(2)
    retscandir = scandir(source)
    #print retscandir

    if retscandir == False :
        ts = time.time()
        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
        print fdate + " : Error during the reading of the directory ", source
        logger.error('Error during the reading of the directory  %s'  % source)
        sendEMail("Error during the reading of the directory  %s "  % source,None)
        sys.exit(2)
    elif retscandir != None :
        
        # if "STOP" exit of the program
        if (retscandir == "STOP"):
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print "\n"+fdate +" : Demande d'arret du programme !!!!"
            sys.exit(0)
        
        sip=os.path.basename(sip_paquet)
        
        try:
            # Control SIP
            retcontrol = controlSIP(sip_paquet)
            if retcontrol == False :
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                print fdate + " : The control of SIP %s failed " % sip
                #sendEMail("The control of SIP %s failed !!!" ,sip)
                                
            elif retcontrol == True:
               
                #Control with succes move sip to output              
                ts = time.time()
                fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                processdate = fdate
                
                # Move SIP to Output
                ts = time.time()
                timestamp = datetime.datetime.fromtimestamp(ts).strftime('%Y%m%d')
               
                if (packagetype == 'create') :
                    outdir =os.path.join(destination,serieTodest)
                    print fdate +" : Move %s to %s" %(sip,outdir)
                    moveSIP(workdir,outdir,sip)
                        
                elif (packagetype == 'update') :
                    outdir =os.path.join(waitdir,serieTodest)
                    print fdate +" : Move %s to %s" %(sip,outdir)
                    moveSIP(workdir,outdir,sip)
                               
                # Clean Workdir
                removeFiles(workdir,sip)
                                
                # Update INFOPACKAGE
                ts = time.time()
                processdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')

                Query = "UPDATE INFOPACKAGE SET status ='COMPLETED', process_date='%s' " % processdate
                Query += " , description ='' "
                Query += " where packagename ='%s' " % sip
                retUpdInfo = updateDB(Query)
                if retUpdInfo == False:
                        ts = time.time()
                        fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
                        print fdate + " : 'Error during to the update of theDB  - %s" %sip
                        logger.error('Error during to the insertion in DB - %s' %sip)
                        sys.exit(1)
                    
                print fdate+ " : End of validation and control %s ." %(sip)
                logger.info("End of validation and control %s ." %(sip))
                
        except Exception, e:
            ts = time.time()
            fdate = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
            print fdate +' : A problem was encountered during the validation and the control : %s' %e
            logger.error("A problem was encountered during the validation and the control %s "%sip)
            logger.error('%s'  % e)
            sendEMail("A problem was encountered during the validation and the control %s : " %e ,sip)
        print "--------"+fdate+" %s ------------------------------" % os.path.basename(sip_paquet)
        print "---------------------------------------------------"
    elif retscandir == None:
        print ".",
        time.sleep(tempo)
