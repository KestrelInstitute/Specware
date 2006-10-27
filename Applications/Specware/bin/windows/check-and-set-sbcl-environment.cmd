@echo off

rem  =============================================================
rem  Check that the needed environment variables are set.
rem
rem  In general, we need to enclose filenames in double-quotes, 
rem  since enviroment variables could expand to directories 
rem  containing spaces, periods, and other nasty characters.
rem
rem  However, the exact format is crucial.
rem  This format leads to disaster:  set FOO="%ABC%/xyz.lisp"  
rem  This format works as expected:  set "FOO=%ABC%/xyz.lisp"  
rem  =============================================================

if "%SPECWARE4%"=="" (
  echo  Error: environment variable SPECWARE4 not set.
  echo  SPECWARE4 must be set to the path of the Specware tree,
  echo  e.g. C:\Specware4.
  pause
  exit
)

if "%XEMACS%"=="" (
  echo  Error: environment variable XEMACS not set.
  echo  XEMACS must be set to the path of the XEmacs tree,
  echo  e.g. C:\Progra~1\xemacs\xemacs-21.4.18.
  pause
  exit
)

rem  Set additional environment variables that depend on the previous ones:

if "%SWPATH%"=="" set "SWPATH=C:/"
rem set SWPATH only if unset

set "SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows"
set "LISP_EXECUTABLE=c:\Progra~1\SBCL\0.9.17\sbcl.exe"
set "LISP_HEAP_IMAGE=%SPECWARE_BIN%\Specware4.sbclimage"
set "LISP_DIRECTORY=%Specware4%/"

rem  Move to Specware4 main directory:

cd "%SPECWARE4%"
