@echo off


call check-and-set-environment


rem  Start Specware shell within Lisp shell:

start "ignore" "%LISP_EXECUTABLE%" +t "Specware Shell" +s "%SPECWARE4%\Applications\Specware\Handwritten\Lisp\StartShell.lisp" -I "%LISP_HEAP_IMAGE%" -e "(setq emacs::*use-emacs-interface?* nil)"

