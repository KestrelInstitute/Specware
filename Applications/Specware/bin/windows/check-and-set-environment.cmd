@echo off

echo "pre XEMACS:       %XEMACS%"
echo "pre BOOTSTRAP:    %BOOTSTRAP%"
echo "pre SPECWARE4:    %SPECWARE4%"
echo "pre ALLEGRO:      %ALLEGRO%"
echo "pre SWPATH:       %SWPATH%"

rem  Check that the needed environment variables are set:

if "%ALLEGRO%"=="" (
  set ALLEGRO=C:\Progra~1\acl62
)

if "%XEMACS%"=="" (
  set XEMACS=C:\Progra~1\XEmacs\XEmacs-21.4.13
)

if "%BOOTSTRAP%"=="" (
  set BOOTSTRAP=C:\Specware4
)

if "%SPECWARE4%"=="" (
  set SPECWARE4=C:\Specware4
)

rem  Set additional environment variables that depend on the previous ones:

if "%SWPATH%"=="" (
  set SWPATH=C:/
) else (
  set SWPATH=%SWPATH%;C:/
)

set LISP_EXECUTABLE=%ALLEGRO%\alisp.exe
set LISP_DIRECTORY=%Specware4%/
set SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows
set LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.dxl

echo "post ALLEGRO:         %ALLEGRO%"
echo "post XEMACS:          %XEMACS%"
echo "post BOOTSTRAP:       %BOOTSTRAP%"
echo "post SPECWARE4:       %SPECWARE4%"
echo "post SWPATH:          %SWPATH%"
echo "post LISP_EXECUTABLE: %LISP_EXECUTABLE%"
echo "post LISP_DIRECTORY:  %LISP_DIRECTORY%"

rem  Move to Specware4 main directory:

cd "%SPECWARE4%"
