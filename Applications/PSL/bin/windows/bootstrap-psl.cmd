set SPECWARE4=\Progra~1\Specware4
rem SWPATH needs /s rather than \s so URI parsing works
set SWPATH=/Progra~1/Specware4;/
set XEMACS=C:\Progra~1\XEmacs\XEmacs-21.4.10
rem set XEMACS=C:\Progra~1\XEmacs\XEmacs-21.4.6
rem Set allegro to the version you have
rem set ALLEGRO=C:\Progra~1\acl62
set ALLEGRO=C:\Progra~1\acl61

set SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows

set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.dxl
set LISP_DIRECTORY=%Specware4%/
cd "%Specware4%"

%XEMACS%\i586-pc-win32\xemacs.exe -debug-init -l "%SPECWARE4%/Library/IO/Emacs/load-ilisp"  -l "%SPECWARE4%/Applications/PSL/bin/windows/psl-init" -f "bootstrap-psl" &
