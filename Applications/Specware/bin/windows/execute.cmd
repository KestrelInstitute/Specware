@echo off


rem  This is a parameterized .cmd script that starts XEmacs and performs a certain action.
rem  The action is passed as argument to this script (the argument is referred to as %1).


rem  Check that the needed environment variables are set:

if "%SPECWARE4%"=="" (
  echo Error: environment variable SPECWARE4 not set.
  pause
  exit
)

if "%SWPATH%"=="" (
  echo Error: environment variable SWPATH not set.
  pause
  exit
)

if "%XEMACS%"=="" (
  echo Error: environment variable XEMACS not set.
  pause
  exit
)

if "%ALLEGRO%"=="" (
  echo Error: environment variable ALLEGRO not set.
  pause
  exit
)


rem  Set additional environment variables that depend on the previous ones:

set SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows
set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.dxl
set LISP_DIRECTORY=%Specware4%/


rem  Move to Specware 4 main directory:

cd "%Specware4%"


rem  Start XEmacs loading various files and performing the action given as argument:

%XEMACS%\i586-pc-win32\xemacs.exe -debug-init -l "%ALLEGRO%/xeli/fi-site-init" -l "%SPECWARE4%/Library/IO/Emacs/load" -f "%1" &
