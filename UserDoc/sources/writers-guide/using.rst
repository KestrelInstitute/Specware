===============================
 Using the documentation tools
===============================




Prerequisites
#############


To build the manuals, you need python and the ``sphinx`` package
installed. Assuming that you've installed a recent version of python
that includes the ``setuptools`` package (which it probably does), you
can install ``sphinx`` with::
    
    sudo easy_install sphinx


Building Documentation
######################

Each manual is in its own directory. To build a particular manual, you
change to the directory associated with the manual, then use the
included ``Makefile``, which in turn invokes the ``sphinx``
tools. There are a number of output formats supported, as well as a
few utilities. To view a list of all targets, simply invoke ``make``
without an argument::

  > make

There are a few targets of particular interest.

``html``
    Build the ``html`` version of the documentation.

``latexpdf`` 
    Generate latex, then build the resulting latex with ``pdflatex``.

``epub``
    Generate an EPUB version of the manual.

``linkcheck``
    Run the tools on the input files to check for correctness in
    links.

In each case, the makefile will generate output in a subdirectory of
a top-level ``_build`` directory. The subdirectory name will be
associated with the makefile target (e.g. ``html`` for the ``html``
target, ``latex`` for the ``pdflatex`` target). 


The directory contains two important files that dictate the structure
of the manual. First, ``index.rst`` defines the files that will be
included in the manual. Second ``conf.py`` defines configuration
variables for the documentation. Editing the ``index.rst`` file is
described in :ref:`Writing Documentation with reStructuredText`, while
documentation for editing the ``conf.py`` file is available on the
`Sphinx website`_.

.. _`Sphinx website`: http://sphinx.pocoo.org/contents.html
