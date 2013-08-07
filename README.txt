Welcome to Specware!

Specware runs on Linux, Mac OS X, and Windows.

It requires a machine with about 2800MB of memory or more (should not
be an issue on physical machines; on virtual machines, be sure to
provision the machine with enough memory).

Specware runs on top of SBCL (Steel Bank Common Lisp).  To build
Specware, first install SBCL (available from http://www.sbcl.org/).
Specware has been successfully built with SBCL 1.1.7, and later
versions should also work.

Specware also requires Gnu Emacs (we no longer support xemacs).  GNU
Emacs 23.1.1 on Linux is known to work, and later versions should also
work.  (Note: Emacs may be already installed on your system.)

To build Specware on Linux or MacOS:

1.  Set your SPECWARE4 environment variable to point to your copy of
the main Specware/ directory.

2.  Run the script Specware/Applications/Specware/bin/linux/bootstrap

3a. On Linux, to start a new emacs with Specware running in it, execute:
Specware/Applications/Specware/bin/linux/Specware-gnu

3b. On Mac OS X, to start a new emacs with Specware running in it, execute:
Specware/Applications/Specware/bin/linux/SpecwareMac

TODO: Add instructions for building on Windows.

Notes:

Errors in launching Specware may be displayed in the "mini-buffer" in
Emacs.

You should not need to install Specware as 'root' if you install it in
your home directory.

Optional: For proof support, install Isabelle2013 (available from
http://www.cl.cam.ac.uk/research/hvg/Isabelle/).  Older versions of
Isabelle will not work.

To learn about Specware, see the documentation in Specware/UserDoc/.

To see a list of available commands, type "help" at the Specware shell.




