@echo off

set "Prior_Path=%Path%"

rem ============================== PATH ======================================
rem This could be smarter about not adding things if they are already present.
rem You (the end user) may wish to modify this for your particular situation:

rem add Cygwin to path

if exist "C:\Cygwin\bin" (
    echo augmenting PATH with C:\Cygwin\bin  
    set "PATH=%PATH%;C:\Cygwin\bin"
)

rem add Java to path

if exist "C:\Program Files\Java\jdk1.5.0_06\bin" (
    echo augmenting PATH with C:\Program Files\Java\jdk1.5.0_06\bin 
    set "PATH=%PATH%;C:\Program Files\Java\jdk1.5.0_06\bin"
)

rem ==========================================================================

echo.
echo prior Path: %Prior_Path%
echo final Path: %Path%
echo.
