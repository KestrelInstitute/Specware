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

rem  These variables are tested and set here...
rem    USING_CYGWIN
rem    SPECWARE4
rem    SPECWARE_BIN
rem    SPECWARE_EXECUTABLE
rem    SPECWARE_INIT_FORM
rem    SWPATH
rem    EMACS_DIR
rem    EMACS_EXECUTABLE
rem    EMACS_INIT

rem  =============================================================
rem  SET CYGWIN STATUS VARS
rem  =============================================================
echo.

rem To force a choice, pick one...

rem set "USING_CYGWIN=FALSE"
rem set "USING_CYGWIN=TRUE"

if "%USING_CYGWIN%" == "" (

  if exist C:\cygwin (

    echo USING_CYGWIN not set, but found C:\cygwin
    echo set "USING_CYGWIN=TRUE"
         set "USING_CYGWIN=TRUE"

  ) else (

    echo USING_CYGWIN not set, and could not find C:\cygwin
    echo set "USING_CYGWIN=FALSE"
         set "USING_CYGWIN=FALSE"
  )
)

if "%USING_CYGWIN%" == "TRUE" (
    echo.
) else if "%USING_CYGWIN%" == "FALSE" (
    echo.
) else (
    echo.
    echo In Set_Environment_Vars.cmd,
    echo  USING_CYGWIN should be "TRUE" or "FALSE", but is "%USING_CYGWIN%"
    echo.
    pause
    exit 1
)

rem  =============================================================
rem  SET SPECWARE VARS
rem  =============================================================
echo.

if "%SPECWARE4%"=="" (

  echo  Environment variable SPECWARE4 not set.
  echo  SPECWARE4 must be set to the path of the Specware tree, in a format
  echo  appropriate to the environment being used: native vs. cygwin. 

  if "%USING_CYGWIN%"=="TRUE" (

  echo TODO: If we use C:\Specware4,          what happens ??
  echo TODO: If we use /cygdrive/c/Specware4, what happens ??
  echo.
  echo Using cygwin, not native:

  echo set "SPECWARE4=C:/Specware4"
       set "SPECWARE4=C:/Specware4"

  ) else (

  echo Native, not using cygwin:
  echo set "SPECWARE4=C:\Specware4"
       set "SPECWARE4=C:\Specware4"

  )

  echo.
)

if "%SPECWARE_BIN%" == "" (
  echo set "SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows"
       set "SPECWARE_BIN=%SPECWARE4%\Applications\Specware\bin\windows"
)

if "%SPECWARE_EXECUTABLE%" == "" (
  echo  set "SPECWARE_EXECUTABLE=%SPECWARE_BIN%\Specware4.exe"
        set "SPECWARE_EXECUTABLE=%SPECWARE_BIN%\Specware4.exe"
)

if "%SPECWARE_INIT_FORM%" == "" (
  echo set "SPECWARE_INIT_FORM=NIL"
       set "SPECWARE_INIT_FORM=NIL"
)

rem set SWPATH only if unset

if "%SWPATH%" == "" (
 echo set "SWPATH=C:/"
      set "SWPATH=C:/"
)

rem  ============================================================
rem  SET EMACS VARS
rem  ============================================================
echo.

rem Pick a version of emacs to use:

if "%EMACS_EXECUTABLE%" == "" (
  echo.
  echo  Environment variable EMACS_EXECUTABLE not set.
  echo.

  if "%USING_CYGWIN%" == "TRUE" (

    echo Using Cygwin...
    echo Set EMACS_EXECUTABLE to point at a cygwin emacs executable, but 
    echo in a format that can be interpreted by a native windows cmd script.
    echo "(I.e., not as /usr/bin/emacs)"
    echo.
    echo set "EMACS_EXECUTABLE=C:/cygwin/bin/emacs"
         set "EMACS_EXECUTABLE=C:/cygwin/bin/emacs"

  ) else (

    if "%EMACS_DIR%" == "" (
      echo "EMACS_EXECUTABLE=%EMACS_EXECUTABLE%"

      echo Not using Cygwin...
      echo.
      echo Environment variable EMACS_EXECUTABLE not set.
      echo.
      echo Either set EMACS_DIR to the root of the shared emacs directory
      echo or set EMACS_EXECUTABLE to a native emacs executable
      echo.
      pause
      exit 1
    )

    echo Not using Cygwin...
    echo Set EMACS_EXECUTABLE to point at a native emacs executable,
    echo.
    echo set "EMACS_EXECUTABLE=%EMACS_DIR%\bin\emacs.exe"
         set "EMACS_EXECUTABLE=%EMACS_DIR%\bin\emacs.exe"

  )
  echo.
)

if not exist "%EMACS_EXECUTABLE%" (
  echo.
  echo  Set_Environment_Vars.cmd could not find an emacs executable
  echo  at %EMACS_EXECUTABLE%
  echo.
  pause
  exit 1
)

echo.

if "%EMACS_INIT%" == "" (
  rem Or perhaps ilisp?
  echo set "EMACS_INIT=-l %SPECWARE4%/Library/IO/Emacs/load-slime"
       set "EMACS_INIT=-l %SPECWARE4%/Library/IO/Emacs/load-slime"
)

rem if not exist "%EMACS_INIT%.el" (
rem   echo.
rem   echo  Set_Environment_Vars.cmd could not find emacs init file
rem   echo.
rem   pause
rem   exit 1
rem )

rem  =============================================================
rem  LISP VARS
rem  =============================================================
echo.

if "%LISP%" == "" (
  echo set "LISP=sbcl.exe"
       set "LISP=sbcl.exe"
)

if "%LISP_EXECUTABLE%" == "" (
  echo set "LISP_EXECUTABLE=%SPECWARE_BIN%\Specware4.exe"
       set "LISP_EXECUTABLE=%SPECWARE_BIN%\Specware4.exe"
)

if "%LISP_HEAP_IMAGE%" == "" (
  echo set "LISP_HEAP_IMAGE=NONE"
       set "LISP_HEAP_IMAGE=NONE"
)

if "%LISP_DIRECTORY%" == "" (
  echo set "LISP_DIRECTORY=%SPECWARE4%/"
       set "LISP_DIRECTORY=%SPECWARE4%/"
)

rem  =============================================================
rem  ECHO VALUES
echo ============================================================
echo.

echo USING_CYGWIN         = %USING_CYGWIN%

echo EMACS                = %EMACS%
echo EMACS_DIR            = %EMACS_DIR%
echo EMACS_EXECUTABLE     = %EMACS_EXECUTABLE%
echo EMACS_INIT           = %EMACS_INIT%

echo LISP                 = %LISP%
echo LISP_EXECUTABLE      = %LISP_EXECUTABLE%
echo LISP_HEAP_IMAGE      = %LISP_HEAP_IMAGE%
echo LISP_DIRECTORY       = %LISP_DIRECTORY%

echo SPECWARE4            = %SPECWARE4%
echo SPECWARE_BIN         = %SPECWARE_BIN%
echo SPECWARE_EXECUTABLE  = %SPECWARE_EXECUTABLE%
echo SPECWARE_INIT_FORM   = %SPECWARE_INIT_FORM%

echo SWPATH               = %SWPATH%

echo ============================================================

rem  Move to Specware4 main directory:
echo cd "%SPECWARE4%"

cd "%SPECWARE4%"

