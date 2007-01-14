@echo off

if "%1"=="/wait" (
 set MAYBE_WAIT=/wait
 shift
) else (
 set MAYBE_WAIT=
)

@echo off

rem Run Specware under XEmacs as a standalone application built using ACL
rem To run this, the user does not need an ACL license,  but
rem must meet criteria set forth in Kestrel's agreeement with Franz.

rem A hack to try to ensure we connect to the proper directory,
rem so the calls to Find_xxx will succeed.
rem The proper alternative is probably to parse %CMDCMDLINE%,
rem but that is dreadful to contemplate.

if exist Specware-4-2 ( cd Specware-4-2 )

call Find_XEMACS
call Find_SPECWARE4
call Update_Path
call Update_SWPATH
call Find_Specware_App_ACL

start "ignore" %MAYBE_WAIT% "%XEMACS_EXE%" -l "%SPECWARE4%/Library/IO/Emacs/load-slime" -f "%1"
