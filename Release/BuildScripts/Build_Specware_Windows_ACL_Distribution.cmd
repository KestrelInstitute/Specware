echo off

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

set "LISP_EXECUTABLE=c:\Program Files\acl70\alisp.exe"
set "LISP_HEAP_IMAGE=c:\Program Files\acl70\alisp.dxl"

cd "%SPECWARE4%\Release\BuildScripts\"

start "ignore" "%LISP_EXECUTABLE%"  +t "Build Specware Distribution" +s "BuildSpecwareDistribution.lisp" -e "(build-specware-release 4 1 4 \"%SPECWARE4%/\" \"%DISTRIBUTION%/\" \"%VERBOSE%\")" -I "%LISP_HEAP_IMAGE%" 





