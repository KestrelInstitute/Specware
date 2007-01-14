@echo off

set "Prior_XEMACS=%XEMACS%"

rem ============================== XEMACS ===================================
rem 
rem This looks for the XEmacs directory (sans spaces!), in this order:
rem
rem    %HOMEDRIVE%%HOMEPATH%\XEmacs\XEmacs-21.4.18
rem    %HOMEDRIVE%%HOMEPATH%\XEmacs-21.4.18
rem    C:\XEmacs\XEmacs-21.4.18
rem    C:\Program Files\XEmacs\XEmacs-21.4.18
rem 
rem [As of 12/19/2005 the current stable xemacs is 21.4.18]
rem 
rem You (the end user) may need to modify this for your particular situation:
rem If you set XEMACS as a user environment variable 
rem   (Start => Control Panel => System => Advanced => Enviroment Variables)
rem in such a way that %XEMACS%\i586-pc-win32\xemacs.exe is defined,
rem this file becomes largely irrelevant.
rem

set HOMEDIR=%HOMEDRIVE%%HOMEPATH%
rem E.g.  C:\Documents and Settings\Joe

rem First, look in "XEmacs" subdirectory in user's home directory, if it exists.

if exist %HOMEDIR%\XEmacs (
  if "%XEMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\XEmacs\XEmacs-2*') do (
      echo setting XEMACS to %%HOMEDRIVE%%%%HOMEPATH%%\XEmacs\%%i
      set "XEMACS=%HOMEDIR%\XEmacs\%%i"
    )
  ) else if not exist "%XEMACS%\i586-pc-win32\xemacs.exe" (
    echo Cannot find "%XEMACS%\i586-pc-win32\xemacs.exe"
    for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\XEmacs\XEmacs-2*') do (
      echo revising XEMACS to %%HOMEDRIVE%%%%HOMEPATH%%\XEmacs\%%i
      set "XEMACS=%HOMEDIR%\XEmacs\%%i"
    )
  )
)

rem Second, look in user's home directory
if "%XEMACS%"=="" (
  for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\XEmacs-2*') do (
    echo setting XEMACS to %%HOMEDRIVE%%%%HOMEPATH%%\%%i
    set "XEMACS=%HOMEDIR%\%%i"
  )
) else if not exist "%XEMACS%\i586-pc-win32\xemacs.exe" (
  echo Cannot find "%XEMACS%\i586-pc-win32\xemacs.exe"
  for /F "tokens=*" %%i in ('dir /B %HOMEDIR%\XEmacs-2*') do (
    echo revising XEMACS to %%HOMEDRIVE%%%%HOMEPATH%%\%%i
    set "XEMACS=%HOMEDIR%\%%i"
  )
)

rem Third, look under C:\XEmacs, if it exists

if exist C:\XEmacs (
  if "%XEMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B C:\XEmacs\xemacs-2*') do (
      echo setting XEMACS to C:\XEmacs\%%i
      set "XEMACS=C:\XEmacs\%%i"
    )
  ) else if not exist "%XEMACS%\i586-pc-win32\xemacs.exe" (
    echo Cannot find "%XEMACS%\i586-pc-win32\xemacs.exe"
    for /F "tokens=*" %%i in ('dir /B C:\XEmacs\xemacs-2*') do (
     echo revising XEMACS to C:\XEmacs\%%i
     set "XEMACS=C:\XEmacs\%%i"
    )
  )
)  

rem Fourth, look under C:\Program Files\XEmacs, if it exists

if exist "C:\Program Files\XEmacs" (
  if "%XEMACS%"=="" (
    for /F "tokens=*" %%i in ('dir /B C:\Program Files\XEmacs\xemacs-2*') do (
     echo setting XEMACS to C:\Program Files\XEmacs\%%i
     set "XEMACS=C:\Program Files\XEmacs\%%i"
    )
  ) else if not exist "%XEMACS%\i586-pc-win32\xemacs.exe" (
    echo Cannot find "%XEMACS%\i586-pc-win32\xemacs.exe"
    for /F "tokens=*" %%i in ('dir /B C:\Program Files\XEmacs\xemacs-2*') do (
     echo revising XEMACS to C:\Program Files\XEmacs\%%i
     set "XEMACS=C:\Program Files\XEmacs\%%i"
    )
  )
)  

if "%XEMACS%"=="" (
  echo.
  echo Could not find an xemacs executable using pattern "xemacs-2*" 
  echo under any of these directories:
  echo.
  echo *  %HOMEDIR%\XEmacs
  echo *  %HOMEDIR%
  echo *  C:\XEmacs
  echo *  C:\Program Files\XEmacs
  echo.
  echo If XEmacs is installed elsewhere, set the XEMACS environment var 
  echo manually via "Start" => "Control panel" => "system" => "Advanced"
  echo.
  pause
  exit
)
  
set "XEMACS_EXE=%XEMACS%\i586-pc-win32\xemacs.exe"
if not exist "%XEMACS_EXE%" (
  echo.
  echo Cannot find XEmacs Executable: "%XEMACS_EXE%"
  echo.
  echo If XEmacs is installed elsewhere, set the XEMACS environment var 
  echo manually via "Start" => "Control panel" => "system" => "Advanced"
  echo.
  pause
  exit
)

rem =========================================================================

echo.
echo prior XEMACS: %Prior_XEMACS%
echo final XEMACS: %XEMACS%
echo.

