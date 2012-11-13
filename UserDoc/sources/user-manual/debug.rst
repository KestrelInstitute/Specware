

==============================
Debugging Generated Lisp Files
==============================

Tracing
#######

If you need to debug your application, there a number of useful Lisp
facilities you should be aware of. The simplest trick is to trace some
functions you care about to see what they are doing.

::

   (trace foo)

This will display the arguments to foo each time it is 
called, and will display the results each time it returns.
  
::
 
   (untrace foo)

This will turn off any tracing on foo.

:: 
   
   (untrace)      

Untrace all functions.
   

Breaking
########

If you need a more detail view of runtime behavior, you might want to
BREAK some functions you care about.

.. code-block:: specware

   (trace foo :break-all t)  
   
This will invoke the debugger each time foo is called,                   
and upon each exit from foo.
   

Once you arrive in the debugger, you can use commands in the SLDB
menu, and typing ``h`` will give a more comprehensive list of
commands. Note, if you are in a break at the return of a function you
can see the return value by evaluating ``sb-debug:*trace-values*``.

SBCL's trace function is documented at
http://www.sbcl.org/manual/#Function-Tracing.

Timing
######

If you are curious about the overall performance of your application,
the ``time`` macro will provide some quick information::

   (time (foo nil))  
     This will report the time and space used by foo, e.g.:
   
    * (time (list 1 2 3))
   Evaluation took:
     0.000 seconds of real time
     0.000006 seconds of total run time (0.000004 user, 0.000002 system)
     100.00% CPU
     2,481 processor cycles
     0 bytes consed
   
    (1 2 3)
   

Note that the number of bytes consed has the granularity of full
pages, hence the ``0 bytes consed`` in this small example. ``time`` is
transparent, i.e., it returns whatever its argument would return,
including multiple values, etc., so it is safe to intersperse it
nearly anywhere.

.. todo::
   Kestrel Technolog*ies* or Kestrel Technology?

Common Lisp has more facilities for rolling your own timers: see the
generic Common Lisp documentation, or contact Kestrel Technologies.

Interrupting
############

Finally, note that a useful trick in Lisp is to start your
application, e.g. ``(foo nil)``, then at an appropriate time type
:kbd:`Ctrl\-C` twice. This will interrupt your application and put your into
the debugger where you can examine the state of the execution stack.

