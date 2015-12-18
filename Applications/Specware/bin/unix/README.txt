This directory contains a variety of scripts and needs to be cleaned
up.  (This directory is also where executable images currently get
put, but perhaps that should change.)

Naming style:
- underscores preferred to dashes or camel case
- "Specware" preferred over "Specware4"
- Jim suggests the format "command_application_language"

TODO: Consider doing much of this scripting in Emacs.  Would then work
on Windows too.

Here is a start at figuring out the status of each script (I don't
list all the callers of each script, if there is any caller script
that we have to keep, the callee script must also be kept -- unless we
can refactor or unify scripts somehow):

Specware-gnu - TODO: Deprecate this (just use bin/specware-emacs).

TODO: Consider deprecating these:
Isabelle_Specware - Preferred way to run Isabelle with Specware? (doesn't seem to work on Linux for Eric)
Emacs_Specware - used by Isabelle_Specware script (unify with Specware-gnu? - no, not meant to be called directly)

SpecwareMac - TODO: Deprecate this (just use bin/specware-emacs).

bootstrap - main script for building Specware on Mac and Linux (SW builds Specware from emacs, runs elisp code, see the Windows scripts - these scripts possibly allow other lisps, uses more non-hardwired variables, could mimic what Windows does, e.g., with Set_Environment_Vars.cmd)
Bootstrap_Specware - called by bootstrap
Prepare_Bootstrap_Image - called by Bootstrap_Specware
Generate_Specware_Lisp - called by Bootstrap_Specware
Compile_Specware_Lisp - called by Bootstrap_Specware
Build_Specware_Dev - called by Bootstrap_Specware
Verify_Specware_Variables - called by Prepare_Bootstrap_Image - finds Specware, emacs, etc.  lots of scripts call this, to get a uniform environment.

SnapshotSpecwareLispFiles - created March, 2012?  Used when you make an incompatible change, keep a snapshot, need to keep this script

Jim uses to run the Specware test suite (TODO: integrate into Bamboo tests):
 (subdir handling broken on Mac?)
Test_Specware4_Subdir - test a subdir of the bugs dir
Test_Specware4_Bugs - just test the bugs
Test_Specware4_Bug - takes an arg, which is a specific bug to test
Test_Specware4 - Jim changed in Nov. 2012


