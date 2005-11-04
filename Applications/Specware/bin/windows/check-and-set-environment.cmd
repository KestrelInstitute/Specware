@echo off


rem  Check that the needed environment variables are set:

if "%SPECWARE4%"=="" (
  echo Error: environment variable SPECWARE4 not set.
  echo SPECWARE4 must be set to the path of the Specware 4 tree,
  echo e.g. c:\users\me\specware4.
  pause
  exit
)

if "%XEMACS%"=="" (
  echo Error: environment variable XEMACS not set.
  echo XEMACS must be set to the path of the XEmacs tree,
  echo e.g. c:\progra~1\xemacs\xemacs-21.4.11.
  pause
  exit
)

if "%ALLEGRO%"=="" (
  echo Error: environment variable ALLEGRO not set.
  echo ALLEGRO must be set to the path of the Allegro Common Lisp tree,
  echo e.g. c:\progra~1\acl70.
  pause
  exit
)


rem  Set additional environment variables that depend on the previous ones:

if "%SWPATH%"=="" set SWPATH=C:/
  rem set SWPATH only if unset
set SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows
set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.dxl
set LISP_DIRECTORY=%Specware4%/


rem  Move to Specware 4 main directory:

cd "%SPECWARE4%"
