echo off
rem These paths are set by the Specware installer.  SWPATH may be changed if your project necessitates it.
set SPECWARE4=
set SWPATH=

set "LISP_EXECUTABLE=%SPECWARE4%\Specware4.exe"
set "LISP_HEAP_IMAGE=%SPECWARE4%\Specware4.dxl"
set LISP_DIRECTORY=%Specware4%/
cd "%Specware4%"

%LISP_EXECUTABLE%  +t "Specware Shell" -I "%LISP_HEAP_IMAGE%" -e "(progn (Specware::initializeSpecware-0) (setq emacs::*use-emacs-interface?* nil)(SWShell::specware-shell t) (exit))"&
