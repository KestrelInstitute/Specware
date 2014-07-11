Specware README.txt file (updated January, 2014).

Welcome to Specware!

(NOTE: By using Specware, you agree to the license in SpecwareLicense.txt.)

Specware runs on Linux, Mac OS X, and Windows.  (The Linux and Mac
versions may be more robust.)

Specware requires a machine with about 2800MB of memory or more (if
using a virtual machine, be sure to provision the machine with enough
memory).

Specware runs on top of SBCL (Steel Bank Common Lisp).  To build
Specware, first install SBCL (available from http://www.sbcl.org/).
Specifically, we suggest using SBCL version 1.1.13.

Specware also requires GNU Emacs (we no longer support XEmacs).  GNU
Emacs 23.1.1 on Linux is known to work, and later versions should also
work.  (Note: Emacs may be already installed on your system.)

Optional: For proof support, install the Isabelle/HOL theorem prover
(available from http://www.cl.cam.ac.uk/research/hvg/Isabelle/).  The
required version of Isabelle is Isabelle2013-2.  Older versions of
Isabelle (including Isabelle2013 without the "-2") will not work.

To build Specware on Linux or MacOS:

1. Check out or untar/unzip Specware into a directory called Specware/.

2. Set your SPECWARE4 environment variable to point to your Specware/
directory.

3.  Run the script Specware/Applications/Specware/bin/linux/bootstrap
(despite the 'linux' in the name, this script should work on MacOS as
well).

4. On Linux or Mac OS X, to start a new emacs with Specware running
in it, execute: Specware/bin/specware-emacs

TODO: Add instructions for building on Windows.

Notes:

Errors in launching Specware may be displayed in the "mini-buffer" in
Emacs.

You should not need to install Specware as 'root' if you install it in
your home directory.

To learn about Specware, see the documentation in UserDoc/.

To see a list of available commands, type "help" at the Specware shell.

Questions about Specware can be emailed to support@specware.org.

