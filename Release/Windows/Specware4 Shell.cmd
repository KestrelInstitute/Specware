echo off

set SPECWARE4=%CD%
echo SPECWARE4=%SPECWARE4%
IF NOT EXIST "%SPECWARE4%\Specware4.exe" (
  echo Cannot find Specware Executable %SPECWARE4%\Specware4.exe
  Pause
  Exit
)

set SWPATH=C:/

echo SPECWARE4=%SPECWARE4%

set "LISP_EXECUTABLE=%SPECWARE4%\Specware4.exe"
set "LISP_HEAP_IMAGE=%SPECWARE4%\Specware4.dxl"
set LISP_DIRECTORY="%Specware4%/"
cd "%Specware4%"

start "ignore" "%LISP_EXECUTABLE%"  +t "Specware Shell" +s "%SPECWARE4%\StartShell.lisp" -I "%LISP_HEAP_IMAGE%" -e "(setq emacs::*use-emacs-interface?* nil)"