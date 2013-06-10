Welcome to Specware!

Specware runs on top of SBCL (Steel Bank Common Lisp).  To build
Specware, first install SBCL (available from http://www.sbcl.org/).
Specware has been successfully built with SBCL 1.1.7, and later
versions should also work.

Specware also requires Gnu Emacs (we no longer support xemacs).  GNU
Emacs 23.1.1 on Linux is known to work, and later versions should also
work.

To build Specware on Linux or MacOS:

1.  Set your SPECWARE4 environment variable to point to your copy of
the main Specware/ directory.

2.  Run the script Specware/Applications/Specware/bin/linux/bootstrap

TODO: Add instructions for building on Windows.

Optional: For proof support, install Isabelle2013 (available from
http://www.cl.cam.ac.uk/research/hvg/Isabelle/).  Older versions of
Isabelle will not work.

To run Specware on Linux (within emacs), execute:
Specware/Applications/Specware/bin/linux/Specware-gnu

To run Specware on MacOS (within emacs), execute:
Specware/Applications/Specware/bin/linux/SpecwareMac

TODO: Add Windows instructions.

To learn about Specware, see the documentation in Specware/UserDoc/.

To see a list of available commands, type "help" at the Specware shell.




