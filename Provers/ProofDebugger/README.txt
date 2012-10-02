This directory contains a proof debugger for the Metaslang logic, i.e. an
extension of the Metaslang proof checker with utilities to "debug" Metaslang
proofs.

This proof debugger should be used according to the same API conventions
described in the README.txt file of the proof checker. The only public spec in
this directory is spec Spec, and the only public morphism in this directory is
morphism Refinement. Morphism refinement can be applied to spec Spec to obtain
an executable implementation. The public/private status of the types and ops
in the specs in this directory are indicated via the same kind of comments
used in the proof checker.

Since the proof debugger extends (by importing) the proof checker, importing
the proof debugger into external code automatically also imports the proof
checker. The public types and ops of the proof checker remain of course public
through this indirect importing.
