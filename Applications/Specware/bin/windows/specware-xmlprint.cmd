@echo off
rem  Processes a Spec and exports it

rem call check-and-set-environment
call Set_Environment_Vars

set SWPATH=%1

"%LISP_EXECUTABLE%" --eval "(progn(XMLPrinter::printUIDtoFile-3 \"%2\" T %3) (exit))"

