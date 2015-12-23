(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% Simple transformations written by Eric starting in March, 2013.
%% Ground rules:
%%   * Transformations should be amenable to proof.
%%   * Transformations should only add new spec elements (ops, types, theorems), not change existing elements.
%%     (Should the result of transforming a spec be a new spec that imports the old one and then adds some new stuff?  Or simply an extension of the old spec?  I am trying the first approach (lets us just import the Isabelle definitions proofs for the original spec.)
%%   * Transformations should generate proof obligations (if not proofs yet).
%%   * Transformations should be built up from separate, small, reusable pieces.

%% TODO If a transformation builds a new spec, what about the qualifier of the new spec?  Let's say that
%% every op in the new spec is explicitly qualified with the same
%% qualifiers as the original op.

Simple qualifying
spec

%% TODO: Include less:
import ../Specs/AnnSpec
import ../Specs/MSTerm
import ../Specs/Position
import ../Specs/QualifierMap
import ../AbstractSyntax/QualifiedId
%import /Library/Structures/Data/Monad/State#State % This seems to cause problems.
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import /Languages/SpecCalculus/AbstractSyntax/UnitId

% Trying to declare this because the import of /Library/Structures/Data/Monad/State caused problems.
%op MonadicStateInternal.readGlobalVar : [a] String -> Option.Option a


%% This is a trivial transformation that simply "copies" a spec (we
%% could also have called it Identity or Noop).  It is included to
%% illustrate the general pattern of how to add a transformation to
%% Specware.  In particular, it suffices to define and op that takes a
%% Spec and returns a Spec and whose qualifier is SpecTransform (such
%% as op SpecTransform.copySpec).  Also, I guess one must cause the
%% new op to be imported in the Specware build (I added to:
%%
%% Languages/SpecCalculus/Semantics/Evaluate/Transform.sw
%%
%% the following import statement: 
%%
%% import /Languages/MetaSlang/Transformations/Simple
%%
%% to cause this file to be included.  I believe ops such as
%% SpecTransform.copySpec can include additional arguments, and for
%% simple types, Specware will correctly parse them and pass them in.
%% However, I have not yet tested this. -Eric

%% TODO just write spc here?
%% TODO Try the Env monad here?
%% Rebuild the hash tables?

op SpecTransform.copySpec (spc : Spec) : Spec =
  AnnSpec.copySpec spc

%% Extends the given spec by adding to it a new op.
%% One must supply the new op's name, qualifier, fixity, and body.
%% See also addOp in AddSpecElements.sw, but those functions are much more complicated than what is needed here.
%% TODO ensure no name clash with existing op.
%% TODO test that the fixity is either Nonfix or Infix (and infix for only binary ops).
%% TODO Check well-formedness of body (this same check can be used in the "lint" checker).
%% TODO Think about the use of StandardAnnotation here:


%% Make a nonsense spec containing a single op that returns an error message.
op errorSpec (message : String) : Spec =
  let spc = emptySpec in
  %addNewOp("ERROR", "ERROR", Nonfix, mkTypedTerm(mkString "msg", Base("String.String", [])), Base("String.String", []), spc)
  spc


%% Trivial transformation that makes a new spec that simply imports
%% spc.  To make the import, we need to know the unit ID of the spec
%% we are importing, so we look it up in the cache.

%% TODO how to signal an error from a transform function like this?  See Garrin's monadic spec transformers.
op SpecTransform.makeImportingSpec (spc : Spec) : Spec =
  case MonadicStateInternal.readGlobalVar "GlobalContext" of
    | None -> errorSpec "Cannot access global context."
    | Some global_context ->
       % case findUnitIdForUnit(Spec spc, global_context) of
       %   | None -> errorSpec "Cannot find unit ID for spec."  %TODO Why must import take a relative UID?
       %   | Some {path=path, hashSuffix=hashSuffix} ->
       %     let path = "/" :: path in %% TODO There must be a better way of handling this.  We'd like the imported UID to not be essentiall an absolute path.
       %     let uid = {path=path,hashSuffix=hashSuffix} in
       % let relUID = UnitId_Relative uid in
       case findRelativeUIDforValue(Spec spc) of
         | None -> errorSpec "Cannot find unit ID for spec."
         | Some relUID ->
           spc << {%% Okay to just use spc.elements here because we know that no redundant imports need to be removed from spc.elements (because the new import is the first element of the new spec).
                     elements = [Import ((UnitId(relUID),noPos),
                                         spc, 
                                         spc.elements, 
                                         noPos)
                                 ],  %%TODO, Why does import take both a spec and some spec elements (presumably the elements of that spec)? SW says that the separate elements have redundant imports removed.
                     qualifier=None}
           
 

op SpecTransform.copyOp (%op_to_copy_base_name : Id,
                         %op_to_copy_qualifier : Qualifier,
                         qid : QualifiedId,
                         spc : Spec) : Spec =
  let Qualified(q,id) = qid in
  let new_spec = SpecTransform.makeImportingSpec spc in
  case (findAQualifierMap(spc.ops, q, id)) of
    | None -> errorSpec ("Can't find op " ^ show qid)
    | Some (op_info : OpInfo) ->
      addNewOp(Qualified(id ^ "NEW", q),  %TODO Generate a unique name!
               op_info.fixity,
               op_info.dfn,
               spc)
  

% What name should we use for the new op?
  

%% What should be the signature of this?:  I want it to take a constant of arbitrary type.  Maybe the constant should be a metaslang term (is that supported?).
% op specialize(fn..., constant..., spec...)
%% AC suggests something like: translate A by {specialize (foo, {constantop1, constantop2, ...})} where the constantops are ops with no args (not even unit) that return the right types.
%how to indicate which params should be specialized?
    
  %% TODO: What kinds of constants can I pass into a transform command?  What about constants whose types are defined in the spec itself?
%  op SpecTransform.specializeOp(qid: QualifiedId

%% TODO: How do I recognize a constant of some as-yet unknown type?  I guess it contains only constructor applications and primitive constants.

%% TODO Add a function to create a new spec that imports the old one an adds some ops.
%% TODO We also need a function to add a set of new ops to a spec.    

%% When re-building dependers (better name for these?), there are two layers: immediate dependers (e.g., callers), which must be changed in a transformation-specific way (their bodies change but not their signatures) and, and indirect dependers, which must simply have a renaming applied to the names they reference.  I guess a function may be both an immediate and indirect depender.
%since we have to do a topoligal sort on the callers, maybe the layers don't matter.  we process all dependers in topo order, replacing calls of f as appropriate (e.g., swap the args) and calls of dependers with the new dependers

end-spec
