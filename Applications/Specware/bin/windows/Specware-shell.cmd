set SPECWARE4=C:\Progra~1\Specware4
rem SWPATH needs /s rather than \s so URI parsing works
set SWPATH=/Progra~1/Specware4;/
set XEMACS=C:\Progra~1\XEmacs\XEmacs-21.4.6
rem Set allegro to the version you have
set ALLEGRO=C:\Progra~1\acl62
rem set ALLEGRO=C:\Progra~1\acl61

set SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows

set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.dxl
set LISP_DIRECTORY=%Specware4%/
cd "%Specware4%"

%LISP_EXECUTABLE%  +t "Specware Shell" -I "%LISP_HEAP_IMAGE%" -e "(progn (setq emacs::*use-emacs-interface?* nil ) (SWShell::specware-shell t) (exit))"&
