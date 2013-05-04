This directory contains the following top-level scripts:

. run scripts

    specware.cmd               -- run Specware within Gnu Emacs
    specware-shell.cmd         -- run Specware without Gnu Emacs

. build scripts

    bootstrap-specware.cmd     -- bootstrap Specware within Gnu Emacs
                                  (generate Specware Lisp, compile Specware Lisp, build Specware executable, and run Specware within Gnu Emacs)
    build-specware.cmd         -- build Specware within Gnu Emacs
                                  (compile Specware Lisp, build Specware executable, and run Specware within Gnu Emacs)

. single-step scripts might be useful during debugging

    generate-specware-lisp.cmd -- just generate Specware Lisp within Gnu Emacs
    compile-specware-lisp.cmd  -- just compile Specware Lisp within Gnu Emacs


The following scripts are used by the top-level ones and should not be called directly:

    Set_Environment_Vars.cmd
    Run_Emacs.cmd
