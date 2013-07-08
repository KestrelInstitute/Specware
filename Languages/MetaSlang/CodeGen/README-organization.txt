This is just a rough sketch, but provides some guidelines for generating code 
files for language "Foo".  

The ops shown here are simply notional, and will be tailored for each language.

A MetaSlang spec should be the first argument to each op.  Ellipses (...) 
indicate additional arguments appropriate for generating Foo files.

================================================================================

The Specware shell command 'gen-Foo ...' will (directly or indirectly) invoke 
SpecTransform.generateFooCode on the full spec.

If appropriate, 'lgen-Foo ...' will produce code for just the ops in the top 
level of the selected spec, ignoring imports (except insofar as imports may be
relevant to processing the toplevel ops).
 
================================================================================

SpecTransform.generateFooFiles is available as a user-invocable identity 
transformation on specs that has the side-effect of producing Foo files:

 <spec> {generateFooFiles (<filename> ...)}

Users may break that process down into smaller transformations, e.g.:

 <spec> {transformSpecTowardsFoo;
         emitFooFiles (<filename>)}


SpecTransform.transformSpecTowardsFoo (see below) is a transform that produces 
a new MetaSlang spec suitable for immediate translation into Foo specs, from
which Foo files can be produced directly.

SpecTransform.transformSpecTowardsFoo is written as nothing more than a series 
of simpler transforms that may be invoked directly by users, to the same effect.

SpecTransform.emitFoofiles (see below) is an identity transform on MetaSlang 
specs, with the side-effect of possibly outputting Foo files directly from the 
provided MetaSlang spec.  It should be as simple and direct as possible, and 
might emit no files if the provided MetaSlang spec fails to obey various 
restrictions.

================================================================================

In file MetaSlang/CodeGen/Foo/GenFoo.sw
---------------------------------------

op SpecTransform.generateFooFiles (ms_spec : Spec, ...) : Spec =

 %% generateFooFiles is a side-effecting transformation used to produce Foo
 %% files from (in principle) arbitrary metaslang specs.  
 %% It may fail to do anything for problematic specs, and always returns the 
 %% original unaltered spec.

 let new_ms_spec = transformSpecTowardsFoo (ms_spec,     ...) in
 let _           = emitFooFiles            (new_ms_spec, ...) in
 ms_spec


op SpecTransform.transformSpecTowardsFoo (ms_spec : Spec, ...) : Spec =

 %% transformSpecTowardsFoo performs a series of spec transforms with the 
 %% intention of producing a a MetaSlang spec suitable for immediate 
 %% production of Foo files.

 %% The transforms within transformSpecTowardsFoo should all be individually
 %% invocable, allowing users to replicate this functionality step-by-step.

 %% Any problems encountered along the way may be indicated via warning 
 %% messages, but this transform always returns a spec (possibly the 
 %% original one).

 %% There is no guarantee that the resulting spec will be suitable for 
 %% code production, so any SpecToFoo translator which follows this must 
 %% anticipate that contigency.

 ...

 transformed_ms_spec


op SpecTransform.emitFooFiles (ms_spec : Spec, ...) : Spec =

 %% emitFoofiles is an identity transform on MetaSlang specs with theside-effect
 %% of possibly outputting Foo files directly from the provided MetaSlang spec.  

 %% The provided MetaSlang spec might have been produced manually, or by an 
 %% invocation of transformSpecTowardsFoo, or by a series of more detailed 
 %% transformations.  

 %% emitFooFiles should be as simple and direct as possible, and might emit no
 %% files if the provided metaslang spec fails to obey appropriate restrictions.

 %% The motivation for having this as a distinct transform is that we may wish
 %% to first transform the MetaSlang spec, then print it out for examination,
 %% then generate Foo files.

 let _ = 
     case generateFooSpecFromTransformedSpec (ms_spec, ...) of
       | Some foo_spec ->
         printFooSpec (foo_spec, opt_filename, ...) 
       | _ ->
         %% warning might be under control of various flags
         let _ = writeLine ("Unable to emit foo files for ...") in
         false
 in             
 ms_spec

================================================================================

In file MetaSlang/CodeGen/Foo/SpecToFooSpec.sw
----------------------------------------------

op generateFooSpecFromTransformedSpec (ms_spec : Spec, ...) : Option Foo_Spec =

 %% Produce a foo_spec from an ms_spec.

 %% This should be as simple and direct as possible -- nothing at all tricky.
 %% It may assume the spec obeys numerous restrictions, and may return None
 %% if those restriction are not met.

 %% If a Foo spec is produced, the expectation is that we can then directly 
 %% generate all appropriate target files from that Foo spec, without fail.

 ...

 Some foo_spec

================================================================================

In file /Specware4/Languages/Foo/PrintFooSpec.sw
------------------------------------------------

op printFooSpec (foo_spec : Foo_Spec, opt_filename : Option String, ...) : Bool

%% This routine prints a FooSpec to appropriate files, and returns true if
%% successful, false if not.
%% Some errors are possible In the event that the filename is illegal, etc., 
%% but there should never be errors associated with the translation itelf.

================================================================================
