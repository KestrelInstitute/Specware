@echo off

rem  Start Specware shell within Lisp shell, no emacs

rem Run Specware under XEmacs as a standalone application built using ACL
rem To run this, the user does not need an ACL license,  but
rem must meet criteria set forth in Kestrel's agreeement with Franz.

rem A hack to try to ensure we connect to the proper directory,
rem so the calls to Find_xxx will succeed.
rem The proper alternative is probably to parse %CMDCMDLINE%,
rem but that is dreadful to contemplate.

if exist Specware-4-2-5 ( cd Specware-4-2-5 )

call Find_SPECWARE4
call Update_Path
call Update_SWPATH
call Find_Specware_App_SBCL

start "Specware Shell" "%LISP_EXECUTABLE%"  --eval "(setq Emacs::*use-emacs-interface?* nil)" --load "%SPECWARE4%\StartSpecwareShell.lisp"

