@echo off

rem Run Specware directly as a standalone application built using ACL
rem To run this, the user does not need an ACL license,  but
rem must meet criteria set forth in Kestrel's agreeement with Franz.

rem A hack to try to ensure we connect to the proper directory,
rem so the call to CheckSpecwareVars will succeed.
rem The proper alternative is probably to parse %CMDCMDLINE%,
rem but that is dreadful to contemplate.

if exist Specware-4-1-5 ( cd Specware-4-1-5 )


call Find_SPECWARE4
call Update_Path
call Update_SWPATH
call Find_Specware_App_ACL

start "ignore" "%LISP_EXECUTABLE%"  +t "Specware Shell" +s "%SPECWARE4%\StartSpecwareShell.lisp" -I "%LISP_HEAP_IMAGE%" -e "(setq emacs::*use-emacs-interface?* nil)"

rem  The following pause is just to keep the window that this 
rem  script runs in from disappearing while debugging this script.
rem  You can comment it in or out as you please.

rem pause
