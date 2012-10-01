@echo off


rem call check-and-set-environment
call Set_Environment_Vars


rem  Start Specware shell within Lisp shell:

start "ignore" "%LISP_EXECUTABLE%" +t "Specware Shell" +s "%SPECWARE4%\Applications\Specware\Handwritten\Lisp\StartShell.lisp" -I "%LISP_HEAP_IMAGE%" -e "(setq Emacs::*use-emacs-interface?* nil)"

