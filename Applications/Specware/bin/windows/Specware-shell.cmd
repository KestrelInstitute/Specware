@echo off


call check-and-set-environment


rem  Start Specware shell within Lisp shell:

"%LISP_EXECUTABLE%"  +t "Specware Shell" -I "%LISP_HEAP_IMAGE%" -e "(progn (Specware::initializeSpecware-0)(SWShell::sw-shell-0))"&

