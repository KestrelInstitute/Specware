@echo off


call check-and-set-environment


rem  Start XEmacs loading various files and performing the action given as argument (i.e. %1):

start "ignore" "%XEMACS%\i586-pc-win32\xemacs.exe" -debug-init -l "%SPECWARE4%/Library/IO/Emacs/load-ilisp" -f "%1" &
