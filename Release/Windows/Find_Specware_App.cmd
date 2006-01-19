@echo off

call Find_Specware4

rem Set additional environment variables that depend on the previous ones.
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
set "LISP_HEAP_IMAGE=%SPECWARE4%\Specware4.dxl"


