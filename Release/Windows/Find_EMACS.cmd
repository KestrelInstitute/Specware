@echo off

set "Prior_EMACS=%EMACS%"

rem ============================== EMACS ===================================
rem 
rem This looks for the Emacs directory (sans spaces!), in this order:
rem
rem    %HOMEDRIVE%%HOMEPATH%\Emacs-23.5
rem    C:\Program Files\Emacs-23.5
rem    C:\Emacs-23.5
rem    C:\Emacs
rem 
rem [As of 12/19/2005 the current stable emacs is 21.4.18]
rem 
rem You (the end user) may need to modify this for your particular situation:
rem If you set EMACS as a user environment variable 
rem   (Start => Control Panel => System => Advanced => Enviroment Variables)
rem in such a way that %EMACS%\i586-pc-win32\emacs.ee is defined,
rem this file becomes largely irrelevant.
rem

set HOMEDIR=%HOMEDRIVE%%HOMEPATH%
rem E.g.  C:\Documents and Settings\Joe

rem First, look in "Emacs" subdirectory in user's home directory, if it exists.

if exist %HOMEDIR%\Emacs (
  if "%EMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\Emacs-23*') do (
      echo setting EMACS to %%HOMEDRIVE%%%%HOMEPATH%%\%%i
      set "EMACS=%HOMEDIR%\%%i"
    )
  ) else if not exist "%EMACS%\bin\emacs.exe" (
    echo Cannot find "%EMACS%\bin\emacs.exe"
    for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\Emacs-23*') do (
      echo revising EMACS to %%HOMEDRIVE%%%%HOMEPATH%%\%%i
      set "EMACS=%HOMEDIR%\%%i"
    )
  )
)

rem Second, look in user's home directory
if "%EMACS%"=="" (
  for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\Emacs-23*') do (
    echo setting EMACS to %%HOMEDRIVE%%%%HOMEPATH%%\%%i
    set "EMACS=%HOMEDIR%\%%i"
  )
) else if not exist "%EMACS%\bin\emacs.exe" (
  echo Cannot find  "%EMACS%\bin\emacs.exe"
  for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\Emacs-23*') do (
    echo revising EMACS to  %%HOMEDRIVE%%%%HOMEPATH%%\%%i
    set "EMACS=%HOMEDIR%\%%i"
  )
)


rem Third, look under C:\Program Files\Emacs-23.5, if it exists

if exist "C:\Program Files\Emacs-23.5" (
  if "%EMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B "C:\Program Files\emacs-23*"') do (
     echo setting EMACS to C:\Program Files\%%i
     set "EMACS=C:\Program Files\%%i"
    )
  ) else if not exist "%EMACS%\bin\emacs.exe" (
  echo Cannot find  "%EMACS%\bin\emacs.exe"
    for /F "tokens=*" %%i in ('dir /B "C:\Program Files\emacs-23*"') do (
     echo revising EMACS to C:\Program Files\%%i
     set "EMACS=C:\Program Files\%%i"
    )
  )
)  

rem Fourth, look under C:\Emacs-23.*, if it exists

if exist C:\Emacs-23.5 (
  if "%EMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B C:\emacs-23*') do (
      echo setting EMACS to C:\%%i
      set "EMACS=C:\%%i"
    )
  ) else if not exist  "%EMACS%\bin\emacs.exe" (
  echo Cannot find  "%EMACS%\bin\emacs.exe"
    for /F "tokens=*" %%i in ('dir /B C:\emacs-23*') do (
     echo revising EMACS to C:\%%i
     set "EMACS=C:\%%i"
    )
  )
)  


if "%EMACS%"=="" (
  echo.
  echo Could not find an emacs eecutable using pattern "emacs-2*" 
  echo under any of these directories:
  echo.
  echo *  %HOMEDIR%\Emacs
  echo *  %HOMEDIR%
  echo *  C:\Emacs
  echo *  C:\Program Files\Emacs
  echo.
  echo If Emacs is installed elsewhere, set the EMACS environment var 
  echo manually via "Start" => "Control panel" => "system" => "Advanced"
  echo.
  pause
  exit
)
  
set "EMACS_EE=%EMACS%\i586-pc-win32\emacs.ee"
if not exist "%EMACS_EE%" (
  echo.
  echo Cannot find Emacs Eecutable: "%EMACS_EE%"
  echo.
  echo If Emacs is installed elsewhere, set the EMACS environment var 
  echo manually via "Start" => "Control panel" => "system" => "Advanced"
  echo.
  pause
  exit
)

rem =========================================================================

echo.
echo prior EMACS: %Prior_EMACS%
echo final EMACS: %EMACS%
echo.

