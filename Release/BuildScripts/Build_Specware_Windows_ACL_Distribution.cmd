@echo off

set "FLAGS=%1"

if "%SPECWARE4%"=="" (
  set "SPECWARE4=C:\Specware4"
)

if "%DISTRIBUTION%"=="" (
  set "DISTRIBUTION=C:\Distribution"
)

if not exist "%SPECWARE4%" (
  echo Cannot find Specware4 directory: %SPECWARE4%
  exit -1
)

if not exist "%DISTRIBUTION%" (
  echo Cannot find distribution directory: %DISTRIBUTION%
  exit -1
)

set VERBOSE=t

set "LISP_EXECUTABLE=%Allegro%\alisp.exe"
set "LISP_HEAP_IMAGE=%Allegro%\alisp.dxl"

cd "%SPECWARE4%\Release\BuildScripts\"

start "ignore" %FLAGS% "%LISP_EXECUTABLE%"  +t "Build Specware Distribution" -L "BuildSpecwareDistribution.lisp" -e '(progn (user::build-specware-release 4 1 5 %VERBOSE%) (sleep 9) (exit 0))' -I "%LISP_HEAP_IMAGE%" 







