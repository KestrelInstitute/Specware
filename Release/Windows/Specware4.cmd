echo off

set SPECWARE4=%CD%
echo SPECWARE4=%SPECWARE4%
IF NOT EXIST "%SPECWARE4%\Specware4.exe" (
  echo Cannot find Specware Executable %SPECWARE4%\Specware4.exe
  Pause
  Exit
)

set SWPATH=C:/

rem This looks for XEmacs current directory in c:\progra~1\XEmacs\.
rem If it is somewhere else you can set it explicitly.

rem set XEMACS=...

IF "%XEMACS%"=="" (
   FOR /F "tokens=*" %%i IN ('dir /B c:\progra~1\XEmacs\xemacs-2*') DO set XEMACS=c:\progra~1\XEmacs\%%i
) ELSE (
IF NOT EXIST %XEMACS%\i586-pc-win32\xemacs.exe (
   FOR /F "tokens=*" %%i IN ('dir /B c:\progra~1\XEmacs\xemacs-2*') DO set XEMACS=c:\progra~1\XEmacs\%%i
)
)

IF "%XEMACS%"=="" (
  echo Cannot find XEmacs in C:\Program Files\XEmacs
  echo Set XEMACS explicitly if it is installed elsewhere.
  Pause
  Exit
)

echo XEMACS=%XEMACS%

set XEMACS_EXE=%XEMACS%\i586-pc-win32\xemacs.exe
IF NOT EXIST %XEMACS_EXE% (
  echo Cannot find XEmacs Executable: %XEMACS_EXE%
  Pause
  Exit
)

rem The following environment variables are used within the emacs
rem interface to find the executable and the Specware world to run. Note
rem the direction of the slashes. This is important. Within Emacs Lisp,
rem these environment variables are bound to strings and the backslashes
rem (\) in Windows style paths are treated as special characters. Emacs Lisp
rem will do the right thing with these paths and translate them as needed.
rem 
rem Do not omit the .exe suffix if the application is called Specware. On
rem Windows, searching for names of files or folders is case insensitive. If
rem you call it Specware and omit the suffix, then the Emacs Lisp Interface
rem fails to find the executable. Instead, it finds the directory called
rem specware.

set "LISP_EXECUTABLE=%SPECWARE4%\Specware4.exe"
set "LISP_HEAP_IMAGE=%SPECWARE4%\Specware4.dxl"
set LISP_DIRECTORY="%Specware4%/"
cd "%Specware4%"

start "ignore" "%XEMACS_EXE%" -l "%SPECWARE4%\Library\IO\Emacs\xeli\fi-site-init" -l "%SPECWARE4%\Library\IO\Emacs\load" -f run-specware4
