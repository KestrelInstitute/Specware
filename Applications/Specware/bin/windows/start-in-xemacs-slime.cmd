@echo off

if "%1"=="/wait" (
 set MAYBE_WAIT=/wait
 shift
) else (
 set MAYBE_WAIT=
)

call check-and-set-environment

rem  Start XEmacs loading various files and performing the action given as argument (i.e. %1):

rem following attempt to use ilisp interface doesn't work, for some mysterious reason:
rem start "ignore" "%XEMACS%\i586-pc-win32\xemacs.exe" -debug-init -l "%SPECWARE4%/Library/IO/Emacs/load-ilisp" -f "%1" &

start "ignore" %MAYBE_WAIT% "%XEMACS%\i586-pc-win32\xemacs.exe" -l "%SPECWARE4%/Library/IO/Emacs/load-slime" -f "%1"
