@echo off


call check-and-set-environment


rem  Start Specware shell within Lisp shell:

%LISP_EXECUTABLE%  +t "Specware Shell" -I "%LISP_HEAP_IMAGE%" -e "(progn (setq emacs::*use-emacs-interface?* nil ) (SWShell::specware-shell t) (exit))"&
