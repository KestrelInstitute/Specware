echo off
rem This starts Specware within an Xemacs window (plus a Allegro Lisp Console)

set SPECWARE4=\Progra~1\Specware4
set ALLEGRO=C:\Progra~1\acl61

set SWPATH=/Proga~1/Specware4

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

set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_HEAP_IMAGE=%Specware4%/Specware4.world
set LISP_DIRECTORY=%Specware4%/
cd "%Specware4%"

%LISP_EXECUTABLE% -I %LISP_HEAP_IMAGE%
