echo off
rem These paths are set by the Specware installer.  SWPATH may be changed if your project necessitates it.
set SPECWARE4=
set ACCORD=
set SWPATH=
set XEMACS_EXE=

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

set "LISP_EXECUTABLE=%SPECWARE4%\Specware-Accord.exe"
set "LISP_HEAP_IMAGE=%SPECWARE4%\Specware-Accord.dxl"
set LISP_DIRECTORY=%SPECWARE4%/
cd "%SPECWARE4%"

start "ignore" "%XEMACS_EXE%" -l "%SPECWARE4%\Library\IO\Emacs\xeli\fi-site-init" -l "%SPECWARE4%\Library\IO\Emacs\load" -f "run-specware4"
