echo off
rem This starts Specware within an Xemacs window (plus a Allegro Lisp Console)
set SPECWARE4=\Progra~1\Specware4
rem SWPATH needs /s rather than \s so URI parsing works
set SWPATH=/Progra~1/Specware4:/
set XEMACS=C:\Progra~1\XEmacs\XEmacs-21.4.6

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
set LISP_DIRECTORY=%Specware4%/
cd "%Specware4%"

%XEMACS%\i586-pc-win32\xemacs.exe -l "%SPECWARE4%\Library\IO\Emacs\xeli\fi-site-init" -l "%SPECWARE4%\Library\IO\Emacs\load" -f run-lisp-application
