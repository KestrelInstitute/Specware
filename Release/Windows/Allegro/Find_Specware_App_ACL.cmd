@echo off

rem ==================== Specware image and directory ========================

rem Set additional environment variables that depend on previous ones.
rem The following environment variables are used within the emacs
rem interface to find the executable and the Specware world to run.
rem
rem The direction of each slash is important. Within Emacs Lisp,
rem these environment variables are bound to strings and the backslashes
rem (\) in Windows style paths are treated as special characters. Emacs Lisp
rem will do the right thing with these paths and translate them as needed.
rem 
rem Do not omit the .exe suffix when the application is called Specware. 
rem On Windows, searching for names of files or folders is case insensitive.
rem If you call it Specware and omit the suffix, then the Emacs Lisp 
rem Interface fails to find the executable. Instead, it may find a directory 
rem named "specware".

set "LISP_DIRECTORY=%SPECWARE4%/"
set "LISP_EXECUTABLE=%SPECWARE4%/Specware4.exe"
set "LISP_HEAP_IMAGE=%SPECWARE4%/Specware4.dxl"

if not exist "%LISP_EXECUTABLE%" (
  echo Cannot find Specware4 executable: %LISP_EXECUTABLE%
  pause
  exit
)

rem ==========================================================================

echo.
echo final LISP_DIRECTORY:  %LISP_DIRECTORY%
echo final LISP_EXECUTABLE: %LISP_EXECUTABLE%
echo final LISP_HEAP_IMAGE: %LISP_HEAP_IMAGE%
echo.

rem ==========================================================================

rem You (the end user) may wish to modify the initial connected directory
rem to suit your particular situation:

echo Connecting to %LISP_DIRECTORY%
cd "%LISP_DIRECTORY%"



