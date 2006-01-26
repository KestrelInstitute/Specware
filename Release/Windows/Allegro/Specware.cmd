@echo off

rem Run Specware under XEmacs as a standalone application built using ACL
rem To run this, the user does not need an ACL license,  but
rem must meet criteria set forth in Kestrel's agreeement with Franz.

rem A hack to try to ensure we connect to the proper directory,
rem so the calls to Find_xxx will succeed.
rem The proper alternative is probably to parse %CMDCMDLINE%,
rem but that is dreadful to contemplate.

if exist Specware-4-1-4 ( cd Specware-4-1-4 )

call Find_XEMACS
call Find_SPECWARE4
call Update_Path
call Update_SWPATH
call Find_Specware_App_ACL

start "ignore" "%XEMACS_EXE%" -l "%SPECWARE4%\Library\IO\Emacs\Preface" -l "%SPECWARE4%\Library\IO\Emacs\xeli\fi-site-init" -l "%SPECWARE4%\Library\IO\Emacs\load" -f run-specware4

rem  The following pause is just to keep the window that this 
rem  script runs in from disappearing while debugging this script.
rem  You can comment it in or out as you please.

rem pause
