@echo off

if "%1" == "/wait" (
 set MAYBE_WAIT=/wait
 shift
) else (
 set MAYBE_WAIT=
)

call Set_Environment_Vars

rem If the lisp files used to build specware are missing, recover them.
if not exist "%SPECWARE4%/Applications/Specware/lisp/Specware4.lisp" (
 cd "%SPECWARE4%/Applications/Specware/"
 tar -xvf SpecwareLispFiles.tgz  
 cd "%SPECWARE4%"
)

rem  Start Emacs or XEmacs, loading various files and performing the action given as argument (i.e. '%1'):

echo start "ignore, do not kill" %MAYBE_WAIT% "%EMACS_EXECUTABLE%" %EMACS_INIT% -f %1

start "ignore, do not kill" %MAYBE_WAIT% "%EMACS_EXECUTABLE%" %EMACS_INIT% -f %1



