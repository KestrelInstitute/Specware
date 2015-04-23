@echo off
rem  Processes a Spec and exports it as an OMDoc XML file
rem usage: specware-xmlprint.cmd ROOTDIR UID RECURSIVE
rem where RECURSIVE = T | nil; if T, dependencies are exported as well

set CURRDIR=%cd%
rem call check-and-set-environment (this needlessly changes the working directory, which we restore afterwards) 
call Set_Environment_Vars
cd %CURRDIR%

set SWPATH=%1

"%LISP_EXECUTABLE%" --eval "(progn(XMLPrinter::printUIDtoFile-4 \"%1\" \"%2\" \"%3\" %4) (exit))"
