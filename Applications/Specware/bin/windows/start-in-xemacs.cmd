@echo off


call check-and-set-environment


rem  Start XEmacs loading various files and performing the action given as argument (i.e. %1):

%XEMACS%\i586-pc-win32\xemacs.exe -debug-init -l "%ALLEGRO%/xeli/fi-site-init" -l "%SPECWARE4%/Library/IO/Emacs/load" -f "%1" &
