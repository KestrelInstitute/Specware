Specware 4.0 README - November 2002
===================================

This file contains information about the differences between version
4.0 of Specware and versions 3.x.  Please see the product website

http://www.specware.org

for updates and development news.  In addition, we would appreciate
any feedback from users on the Specware language, environment,
interface with the SNARK theorem prover, and other issues so that we
may incorporate this information into the next release.  The product
website will also provide a means for submitting this feedback.

Please refer to the documentation included with the distribution
package for details on using Specware 4.0.


=============================================
DIFFERENCES BETWEEN SPECWARE 4 AND SPECWARE 3
=============================================


File extensions
---------------

The file extension for Specware 3 files is .sl.

The file extension for Specware 4 files is .sw (derived from the first
and fifth letter of "Specware").


Name spaces
-----------

In Specware 3, the top level construct of MetaSlang is "module". A
file contains one or more modules. A module contains definitions of
specs, morphisms, and other entities. Each module defines a separate
name space. Since the name space of modules is flat, the names of
specs, morphisms, etc. only consist of two levels (module name and
spec/morphism/etc. name).

In Specware 4, there are no modules. Instead, specs, morphisms, etc.,
collectively called "units", live in hierarchical name spaces that
have a tree structure. A unit name may have an arbitrary number of
levels. Instead of having a module-like construct in the language to
delimit units belonging to a certain name space, the hierarchical
structure of the underlying file system is used to organize units in
the name space, by placing files defining units in appropriate places
of the file system.


Qualified sort and op names
---------------------------

In Specware 3, the names of sorts and ops inside specs belong to flat
name spaces (modules divide the name space of specs and other units,
not of sorts and ops, which live inside specs).

In Specware 4, each sort or op name has a (possibly empty) qualifier.
Qualifiers serve to structure the name space of sorts and ops (the
hierarchical name space for units only applies to units, not to spec
contents).


Only one "import" construct
---------------------------

In Specware 3, there are two "import" constructs. One is used to
import modules; it appears inside modules but outside the specs
defined inside modules. The other is used to import specs; it appears
inside specs (which are inside modules). Despite their identical
appearance, module-level and spec-level "import" have different
semantics: the former merely makes the units defined in a module
accessible to another module without having to prepend the module name
to them; the latter uses all the sorts, ops, and axioms of the
imported spec as a base to construct a new spec.

In Specware 4, there is only one "import" construct, the one for specs
(there are no modules in Specware 4). Its semantics is as in Specware
3.


Specialized syntax for non-spec units
-------------------------------------

In Specware 3, only specs had a specialized syntax ("spec ... end").
All other kinds of units (morphisms, etc.), are defined inside modules
with the same syntax used to define constant ops inside specs (i.e.,
"def M = ..."). In particular, unit-building operators such as colimit
are used in the same way as ops are used inside specs (e.g.,
diagramColimit(...)).

In Specware 4, there is specialized syntax for all kinds of units.
This specialized syntax is more readable and intuitive than the
general syntax used inside specs for op application.


Diagrams and colimits
---------------------

In Specware 3, only limited support for diagrams and colimits is
provided. In particular, there is no way to define a diagram with two
distinct nodes labeled by the same spec.

In Specware 4, there is full support for diagrams and colimits. The
syntax allows an explicit definition of the underlying graph of a
diagram (with explicit names for nodes and edges) and an explicit
labeling of nodes and edges with specs and morphisms.


More direct and specialized interaction with the system
-------------------------------------------------------

In Specware 3, the interaction with the system is rather indirect. In
order to have the system process some units, it is necessary to create
a suitable load.lisp file with a list of the names of the files
containing the modules where the units to be processed are defined.
The list must be ordered according to the dependencies among the
modules.  Besides the list of file names, the load.lisp must contain
some esoteric information (the system exposes its internals more than
needed); the usual approach is to copy and modify an existing
load.lisp file.

In Specware 4, units are processed by typing simple commands into the
Lisp shell. There is no need to create .lisp files or to worry about
the order in which files must be processed. The system automatically
finds and processed the needed files; all the user has to provide is
the name of the unit that must be processed.


Prover interface
----------------

In Specware 3, only limited support for theorem provers is
provided. In particular, provers could be only accessed via an
XEmacs-based GUI. There was no easy way to save the results of
invoking the provers for later "replay".

In Specware 4, a new kind of unit, the "proof unit", has been added.
MetaSlang includes syntax to construct proof units. When proof units
are processed by Specware, provers are invoked. The syntax for proof
units includes various prover-independent and prover-dependent
parameters that influence the provers' attempts to find proofs.

Even though Specware 4's prover interface is still rather limited and
experimental, it is built upon a simple and sound conceptual model.
In particular, since all the information about the invocation of the
provers is part of the syntax for proof units, the system
automatically and implicitly provides a way to "replay" calls to
provers.
