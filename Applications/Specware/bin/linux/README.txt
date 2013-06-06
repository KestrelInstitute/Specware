This directory contains a variety of scripts and needs to be cleaned
up.  (This directory is also where executable images currently get put.)

Here is a start at figuring out the status of each script (I don't
list all the callers of each script, if there is any caller script
that we have to keep, the callee script must also be kept -- unless we
can refactor or unify scripts somehow):

Specware-gnu - Preferred way on Linux to run Specware within emacs
Specware4-shell-sbcl - Preferred way on Linux to run Specware in a terminal

Isabelle_Specware - Preferred way to run Isabelle with Specware? (doesn't seem to work on Linux for Eric)
Emacs_Specware - used by Isabelle_Specware script (unify with Specware-gnu?)
Isabelle_Specware_gnu - ???

SpecwareMac - Alessandro uses this on the Mac
Specware4Mac - identical to SpecwareMac (delete one of them!)

bootstrap - main script for building Specware on Mac and Linux
Bootstrap_Specware - called by bootstrap
Prepare_Bootstrap_Image - called by Bootstrap_Specware
Generate_Specware_Lisp - called by Bootstrap_Specware
Compile_Specware_Lisp - called by Bootstrap_Specware
Build_Specware_Dev - called by Bootstrap_Specware
Verify_Specware_Variables - called by Prepare_Bootstrap_Image

Scripts of unknown status (can we delete these?):

XEmacs_Specware - Didn't we stop supporting xemacs (we only support Gnu Emacs now)?
Specware4 - seems to run xemacs
Test_Specware4_Subdir
Test_Specware4_Bugs
Test_Specware4_Bug
Test_Specware4
Specware-slime-xmlrpc-server
Specware-slime
Specware-shell-sbcl
Specware-sbcl-slime
Specware-sbcl
Specware-cmulisp-slime
Specware-cmulisp
Specware4-xmlrpc-server-openmcl
Specware4-xmlrpc-server
Specware4-text-sbcl
Specware4-text-acl
Specware4-text
Specware4-shell-openmcl
Specware4-shell-clisp
Specware4-shell
Specware4-openmcl
Specware4-emacs-xmlrpc-server-openmcl
Specware4-emacs-xmlrpc-server
SpecBeans-text
SnapshotSpecwareLispFiles
Init-ilisp-for-xemacs-cmucl
Init-ilisp-for-xemacs-acl
Init-ilisp-for-xemacs
build-with-cache
Build_Specware_Dev_With_Cache
bootstrap-acl

