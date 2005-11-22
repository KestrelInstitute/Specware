@echo off

echo This script runs two installations in sequence:
echo First XEmacs 21.4.10, then Specware 4.1.4
echo.
echo Preparing to offer to install xemacs 21.4.10 ...
echo.
echo When prompted with a choice of places to install from,
echo you should choose to install from "Local Disk".
echo.
echo For all other xemacs installation questions, you should press "Next".
echo.
echo NOTE:
echo.
echo If you already have XEmacs, you should be able to skip re-loading it
echo by pressing "Cancel" when prompted.  This intallation script should 
echo then proceed to offer to load Specware.
echo.
echo In particular, if you have a newer version (e.g. 21.4.17, etc.), you
echo probably SHOULD skip loading this (somewhat dated) version of XEmacs.
echo.
pause

XEmacs\setup.exe

echo.
echo Preparing to offer to install Specware 4.1.4 ...
echo.
echo Once InstallShield starts (which can take awhile, so be patient),
echo you should press "Next", "Next", "Next", "Install", "Finish".
echo.
echo (To do so, you will need to accept the click-thru license terms.)
echo. 

Windows\setup.jar

echo.
echo Assuming you chose to install them, both XEmacs 21.4.10 and 
echo Specware 4.1.4 should now be available.
echo.
echo Unless you chose elsewhere, Specware 4.1.4 lives at 
echo.
echo   C:\Program Files\Kestrel\Specware-4-1-4
echo.
echo There should be two desktop icons to run Specware:
echo.
echo  one that runs with    XEMacs (normal usage)
echo  one that runs without XEmacs
echo.

pause