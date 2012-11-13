

===============
Getting Started
===============

|Specware| is a development environment that runs on top of Lisp. The
following sections describe the |Specware| environment and the basic
mechanisms for running |Specware|.

Starting |Specware|
###################

The user interacts with |Specware| through the "|SShell|", with the
choice of running the latter in an XEmacs buffer or in a Lisp window.
XEmacs users will almost certainly be more comfortable with the first
choice, while the second choice may be preferable for users unfamiliar
with Xemacs.

To start |Specware|, double-click either the :guilabel:`Specware4 XEmacs`
shortcut or the :guilabel:`Specware4` shortcut on your Desktop, or select one
of the two from the :guilabel:`Start Menu -> Program Files -> Specware`` menu.

.. todo:: Remove XEmacs reference?
  
When |Specware| is launched through the :guilabel:`Specware4 XEmacs` shortcut,
a couple of things happen: an Allegro Common Lisp Console window
appears (which may be ignored but should not be closed), XEmacs is
started, and a Lisp image containing the |SShell| is started inside an
XEmacs buffer entitled ``Specware Shell``.

When |Specware| is launched through the :guilabel:`Specware4` shortcut, a Lisp
window entitled ``Specware Shell`` appears in which the |SShell| is
running.

In either case, the |SShell| starts with issuing a prompt (an asterisk
"\ ``*``\ "), prompting the user to issue a |SShell| command. All of
the user interaction (see the next chapter) with |Specware| occurs at
the |SShell| prompt: the user issues a command; Specware processes it
and shows any results or error messages, insofar as applicable; then
prompts the user; and so on, until the end of the session.

Processing errors may cause the execution of the |SShell| to be
interrupted, throwing interaction into a Lisp shell. To return to the
|SShell|, issue the Lisp command :command:`:sw-shell`. Alternatively,
select an appropriate restart action if one is offered by Lisp.

  

.. COMMENT:  starting specware 

Exiting |Specware|
##################

To exit |Specware|, type :command:`exit` or :command:`quit` at the Specware prompt.
This will terminate the |Specware| session.

.. COMMENT: as well as Lisp.
            To exit |Specware| while remaining inside Lisp, give the
            command ``ok``\ .

An existing XEmacs window remains open and needs to be closed separately.

  

.. COMMENT:  exiting specware 

