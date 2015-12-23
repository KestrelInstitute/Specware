Specware README.txt file (updated January, 2015).

Welcome to Specware!

(NOTE: By using Specware, you agree to the license in LICENSE.)

Specware runs on Linux and Mac OS X. (It is possible to run Specware
on Windows, but this is not being actively supported.  These
instructions only cover the Linux and Mac versions.)

Specware requires a machine with about 2800MB of memory or more. (If
using a virtual machine, be sure to provision the machine with enough
memory.)

Specware also requires GNU Emacs.  GNU Emacs 23.1.1 on Linux is known
to work, and later versions should also work.  (Note: Emacs may be
already installed on your system.)

Optional: For proof support, install the Isabelle/HOL theorem prover
(available from http://www.cl.cam.ac.uk/research/hvg/Isabelle/).  The
required version of Isabelle is Isabelle2015.  Older versions of
Isabelle will not work.

If this is a source code version of Specware, you will need to build
Specware before running it.  To do so, follow these steps:

1. Specware runs on top of SBCL (Steel Bank Common Lisp).  To build Specware, 
first install SBCL (available from http://sbcl.org/platform-table.html).

2. Run make in the Specware directory

To run Specware execute the script bin/specware-emacs.  This will start
a new Emacs with Specware running in it.  Alternatively, on Mac OS X
you can double click on bin/Specware.app. You can drag this to the
dock or create an alias to it, to make it more accessible.  You can
use bin/specware-shell to run Specware without Emacs support.

Notes:

You may need to set an Isabelle environment variable so that Isabelle
understands references to $SPECWARE4.  You can put something like this line:
export SPECWARE4=$HOME/Specware 
into the file:
~/.isabelle/Isabelle2015/etc/settings
in your home directory.

Errors in launching Specware may be displayed in the "mini-buffer" in
Emacs.

You should not need to install Specware as 'root' if you install it in
your home directory.

To learn about Specware, see the documentation in UserDoc/.

To see a list of available commands, type "help" at the Specware shell.

Questions about Specware can be emailed to support@specware.org.

