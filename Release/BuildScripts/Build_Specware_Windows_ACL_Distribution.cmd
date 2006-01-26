echo off

if "%SPECWARE4%"=="" (
  set "SPECWARE4=C:/Specware4"
)

if "%DISTRIBUTION%"=="" (
  set "DISTRIBUTION=C:/Distribution"
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

set "LISP_EXECUTABLE=c:\Program Files\acl70\alisp.exe"
set "LISP_HEAP_IMAGE=c:\Program Files\acl70\alisp.dxl"

rem %SPECWARE4% may have forward slash (e.g. "C:/") where cd demands backslash
rem cd "%SPECWARE4%\Release\BuildScripts\"

start "ignore" "%LISP_EXECUTABLE%"  +t "Build Specware Distribution" -L "BuildSpecwareDistribution.lisp" -e '(progn (user::build-specware-release 4 1 4 "%SPECWARE4%/" "%DISTRIBUTION%/" %VERBOSE%) (sleep 10) (exit 0))' -I "%LISP_HEAP_IMAGE%" 






