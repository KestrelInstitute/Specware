This directory contains the sources and tools needed to build the
Specware documentation.  The build process currently (Oct. 5, 2012)
works on Linux and Mac OSX. 

Required programs include:

python
pdflatex

Additionally, the python 'sphinx' and 'docutils' packages are
required. Assuming that you have a working python installation, it
should be possible to install these two packages with the command:

sudo easy_install sphinx

In addition, you need the pdflatex program.  Generally this is a symlink
to pdftex.  On the Mac, you can get this from http://www.tug.org/mactex/

For more details on the required programs as well as
instructions on editing and building the manuals, please read the
'Manual Writers Guide', located in 'ManualWritersGuide.pdf'.

There are six main documents that get built, each with its own directory under sources:
 language-manual
 user-manual
 tutorial
 xform-manual
 isabelle-interface
 quick-reference

Building the writers-guide is mentioned further below.

To build all the manuals  (in PDF form) except the writers-guide, 
cd to 'sources' and type 'make'. This will build a pdf version of 
each manual.  The manuals will be generated in the _build/latex/ 
subdirectory of each manual's source directory, for example:
./sources/language-manual/_build/latex/SpecwareLanguageManual.pdf

[If you want to build just a single document, cd to the document's
directory under 'sources' and do 'make latexpdf'.]

This UserDoc/ directory also contains a snapshot copy of all of the
manuals (these files are checked in to SVN).  To update these
snapshots when the manuals are improved, run the refresh-docs.bash
script to copy over the updated PDFs from the _build/latex/
subdirectories.  (This Makefile used to do this, but that led SVN to
always think the manuals were updated, even when no substantive change
was made.)

To build an HTML version, execute 'make html'. See the manual writers
guide for more information on the various makefile targets.

In addition, the writers-guide is in its own directory under sources,
but if you want to build it, you need to cd to its directory and
do 'make latexpdf' separately.  It is not mentioned in the general Makefile.

This file was written by Eric Smith, based on information from Lambert
Meertens, and modified by Garrin Kimmell to reflect updates of the
manual format to restructuredtext. For more information, see
README-MANUAL-WRITERS.txt.
