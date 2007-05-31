@echo off

set "Prior_SPECWARE4=%SPECWARE4%"

rem ============================== SPECWARE4 ================================
rem
rem Spaces in the expansion of the SPECWARE4 environment variable seem to
rem create confusion in bash scripts, so we fix the canonical culprit.
rem
rem You (the end user) may need to modify this for your particular situation.
rem
rem Note: The peculiar arrangement of slashes in some pathnames is delicate.
rem       There is one backward slash after "C:", which the Windows shell
rem        under XEmacs seems to need, and which the bash shell can tolerate.
rem       The remaining separators are all forward slashes, which the 
rem        bash shell needs and which the Windows shell seems to tolerate.
rem       Insanity.

set SW_VERSION=Specware-4-2-2

if "%SPECWARE4%"=="" (

    echo undefined SPECWARE4
    if exist C:\Progra~1/Kestrel/%SW_VERSION% (
        echo setting SPECWARE4 to C:\Progra~1/Kestrel/%SW_VERSION%
        set "SPECWARE4=C:\Progra~1/Kestrel/%SW_VERSION%"
    ) else if exist C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION% (
        echo setting SPECWARE4 to: C:\Docume~1/%%USERNAME%%/Kestrel/%SW_VERSION%
        set "SPECWARE4=C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION%"
    )

) else if "%SPECWARE4%"=="C:\Program Files\Kestrel\%SW_VERSION%" (

    echo Problematic space and backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Progra~1/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Progra~1/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="c:\Program Files\Kestrel\%SW_VERSION%" (

    echo Problematic space and backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Progra~1/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Progra~1/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="C:\Progra~1\Kestrel\%SW_VERSION%" (

    echo Problematic backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Progra~1/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Progra~1/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="c:\Progra~1\Kestrel\%SW_VERSION%" (

    echo Problematic backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Progra~1/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Progra~1/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="C:\Documents and Settings\%USERNAME%\Kestrel\%SW_VERSION%" (

    echo Problematic space and backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Docume~1/%%USERNAME%%/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="c:\Documents and Settings\%USERNAME%\Kestrel\%SW_VERSION%" (

    echo Problematic space and backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Docume~1/%%USERNAME%%/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="C:\Docume~1\%USERNAME%\Kestrel\%SW_VERSION%" (

    echo Problematic backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Docume~1/%%USERNAME%%/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION%"

) else if "%SPECWARE4%"=="c:\Docume~1\%USERNAME%\Kestrel\%SW_VERSION%" (

    echo Problematic backslashes in: "%SPECWARE4%"
    echo revising SPECWARE4 to: C:\Docume~1/%%USERNAME%%/Kestrel/%SW_VERSION%
    set "SPECWARE4=C:\Docume~1/%USERNAME%/Kestrel/%SW_VERSION%"
)

rem ==========================================================================

echo.
echo prior SPECWARE4: %Prior_SPECWARE4%
echo final SPECWARE4: %SPECWARE4%
echo.


