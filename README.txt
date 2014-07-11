Specware README.txt file (updated July, 2014).

Welcome to Specware!

(NOTE: By using Specware, you agree to the license in SpecwareLicense.txt.)

Specware runs on Linux, Mac OS X, and Windows.  (Windows support is
experimental.  These instructions only cover the Linux and Mac
versions.)

Specware requires a machine with about 2800MB of memory or more. (If
using a virtual machine, be sure to provision the machine with enough
memory.)

Specware also requires GNU Emacs (we no longer support XEmacs).  GNU
Emacs 23.1.1 on Linux is known to work, and later versions should also
work.  (Note: Emacs may be already installed on your system.)

Optional: For proof support, install the Isabelle/HOL theorem prover
(available from http://www.cl.cam.ac.uk/research/hvg/Isabelle/).  The
required version of Isabelle is Isabelle2013-2.  Older versions of
Isabelle (including Isabelle2013 without the "-2") will not work.

If this is a pre-built copy of Specware, you can just run Specware by
executing the script bin/specware-emacs.  This will start a new Emacs
with Specware running in it.

If this is a source code vesion of Specware, you will need to build
Specware before running it.  To do so, follow these steps:

1. Specware runs on top of SBCL (Steel Bank Common Lisp).  To build
Specware, first install SBCL (available from http://www.sbcl.org/).
Specifically, we suggest using SBCL version 1.1.13.

2. Set your SPECWARE4 environment variable to point to your Specware
directory. TODO: Is this still needed?

3.  Run the script Specware/Applications/Specware/bin/linux/bootstrap
(despite the 'linux' in the name, this script should work on MacOS as
well).

TODO: Add instructions for building on Windows.

Notes:

Errors in launching Specware may be displayed in the "mini-buffer" in
Emacs.

You should not need to install Specware as 'root' if you install it in
your home directory.

To learn about Specware, see the documentation in UserDoc/.

To see a list of available commands, type "help" at the Specware shell.

Questions about Specware can be emailed to support@specware.org.

