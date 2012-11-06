

=====================
Installing |Specware|
=====================

Contents of Distribution Package
################################

The following programs and documents are included on the |SpecwareV|
installation CD:

``setup.exe`` 
  This program in the root directory of the CD is the
  |SpecwareV| installer for Windows. It should be launched automatically
  when the CD is inserted into the CD-ROM drive.

``XEmacs``
  This folder contains the XEmacs ``setup.exe`` installer
  for Windows, as well as the packages necessary to install the program.
  XEmacs is the environment within which |SpecwareV| is designed to run.

``SNARK``
  This folder contains the license agreement and modified
  source code for the theorem prover SNARK, which is built into
  |SpecwareV|.

 

.. COMMENT:  CD contents 

The following documentation is included with the distribution package:

|SpecwareV| Quick Reference
  The Quick Reference gives an overview
  of processing commands and |Metaslang| language constructs.

|SpecwareV| User Manual (this document)
  The User Manual serves as a quick guide to basic usage and concepts of
  |Specware|. After reading this, you should feel comfortable with the
  mechanics of running and using |Specware|.

|SpecwareV| Tutorial
  The Tutorial will guide you through the process of specifying,
  refining and generating code in |Specware|. A comprehensive example
  provides step-by-step instructions for this development process.

|SpecwareV| Language Manual
  The Language Manual discusses the |Metaslang| specification language
  and gives the grammar rules and meaning for each |Metaslang|
  language construct.

 

.. COMMENT:  documentation 

 

.. COMMENT:  distribution package contents 

System Requirements
###################

Hardware
========

|Specware| has relatively modest system requirements for simple
projects. Of course, as with any development tool, as your projects
being developed become more complex, you may wish to work on a more
powerful machine. For average use, however, the following basic
hardware configuration is recommended:

- CPU: 250 Mhz

- RAM: 128 MB total, at least 64 MB free for applications

- Disk space: 15 MB for base system, 10-50 MB for user projects

  

.. COMMENT:  hardware 

Operating system
================

This version of |SpecwareV| has been tested to work with Windows XP,
Windows 2000 and Windows NT 4.0.

  

.. COMMENT:  operating system 

  

.. COMMENT:  system requirements  

Installation Instructions
#########################

#. Insert the installation CD into your CD-ROM drive; the |SpecwareV|
   ``setup.exe`` installer wizard will be automatically launched.

#. After accepting the license agreement, the installer will try to find
   the path to the XEmacs ``xemacs.exe`` startup file under the ``Program
   Files`` directory. If the path is found, the installer continues.
   Otherwise, you will have the option to either install XEmacs from the
   distribution CD (click ``Yes``) or to manually type in the full path
   to ``xemacs.exe``, if it is installed elsewhere on your machine (click
   ``No``). Clicking ``Yes`` will launch the XEmacs installer wizard.
   Select the "Install from Local Directory" option for quickest
   installation, specify ``[CD-ROM drive]:\XEmacs\packages\`` as the
   directory from which to install the packages, and click ``Next``
   through the remaining steps in the wizard to accept the default
   configuration. After XEmacs has been installed, you will return to the
   |Specware| installer wizard.

#. Select the directory where you would like |Specware| to be installed
   (the default is ``C:\Program Files\Specware4.2``), and click ``Next``
   to complete the installation. A shortcut to |Specware| will be placed
   on your Desktop as well as in the Program Files folder in the Start
   menu. Documentation, libraries and example code will be placed in the
   installation directory you selected.

 

.. COMMENT:  installation instructions 

Uninstalling
############

To uninstall |SpecwareV|, run the installer on the CD again and select
the "Remove" option in the wizard, or use the ``Add/Remove Programs``
setting in the Control Panel.

 

.. COMMENT:  uninstalling 

