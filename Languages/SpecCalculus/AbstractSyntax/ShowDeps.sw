(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% TODO: Maybe this file should be called ShowDeps.sw since showdeps is the command to invoke it.

%% This file contains a utility to print the "dependencies" in a spec.  For each
%% type or op, it prints the list of types and ops it refers to.  The output
%% goes to a file in the deps/ subdirectory of the directory that contains the
%% spec.  Each line of the output lists a type or op, followed by a colon and a
%% space-separated list of all the types or ops it refers to.

%% This file might be similar to some of the operations done by Languages/MetaSlang/Transformations/SliceSpec.sw

%% The top level function to call is showdepsForSpec.  Example call (from the Specware shell):
%%   showdeps /usr/home/kestrel/ewsmith/Dropbox/vTPM/vTPM/Examples/Arrays_1#Imp

ShowDeps qualifying spec 

import Types
import ShowUtils
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Monad

% prints <unqualified> if no qualifier
op printQualifiedIdFull (Qualified (q, id) : QualifiedId) : String =
  q ^ "." ^ id

type QIDSet = List QualifiedId %FIXME which set library should I use?

op printQIDSet (set : QIDSet) : String =
  foldl (fn (str, qid) -> " "^(printQualifiedIdFull qid)^str) "" set

% maps each op or type name (fully qualified) to the list of ops and types (all fully qualified) to which it refers
type DepsMap = STHMap.Map(QualifiedId,QIDSet)

op lookupDeps (caller:QualifiedId) (deps:DepsMap) : QIDSet =
  case STH_apply(deps,caller) of
  | None -> []
  | Some set -> set

op insertIntoSet (callee:QualifiedId) (deps:QIDSet) : QIDSet =
  if callee in? deps then deps else callee::deps

op insertDepIntoMap (caller:QualifiedId) (callee:QualifiedId) (map:DepsMap) : DepsMap =
  let currentDeps = lookupDeps caller map in
  let newDeps = insertIntoSet callee currentDeps in
  let newMap = STH_update(map, caller, newDeps) in
    newMap

type Deps = DepsMap
  
type SpecElem = SpecElemTerm
  
  %% --------------------------------------------------------------------------------
  %% Give the signature of utilities so we don't have to import them

% type SpecCalc.GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
%op  Specware.evaluateUnitId: String -> Option Value


  %op  SpecCalc.uidToFullPath: UnitId -> String
%op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo

% op uidToDepsName ({path,hashSuffix=_}: UnitId) : String =
%   let device? = deviceString? (head path) in
%   let main_name = last path in
%   let path_dir = butLast path in 
%   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
%                             ["/deps/",main_name]
%                             (if device? then tail path_dir else path_dir))
%   in if device?
%        then (head path) ^ mainPath
%      else mainPath

% op uidStringPairForValue (val: Value) : Option (UnitId * String * String) =
%   case MonadicStateInternal.readGlobalVar "GlobalContext" of
%   | None -> None
%   | Some global_context ->
%     case findUnitIdForUnit(val,global_context) of
%     | None -> None
%     | Some uid ->
%       Some (uid,
%             fileNameInSubDir(uid, "deps"),
%             case uid.hashSuffix of
%             | Some loc_nm -> numberSignString ^ loc_nm
%             | _ -> "")

% op uidStringForValue (val:Value) : Option String =
%   case uidStringPairForValue val of
%   | None -> None
%   | Some(_,filnm,hash) -> Some(filnm ^ hash)
    
%% Extend deps to indicate that name depends on all the things in ty.
op addDepsForType (name : QualifiedId) (deps: Deps) (ty: MSType): Deps =
  case ty of
  | Arrow (ty1,ty2,_) -> (addDepsForType name (addDepsForType name deps ty1) ty2)
  | Product (fields,_) -> (foldl (fn (deps, (_, ty)) -> addDepsForType name deps ty) deps fields)
  | CoProduct (taggedTypes,_) ->
    let def addDepsForTaggedType (deps, (id, optTy)) =
      case optTy of
      | None -> deps
      | Some ty -> addDepsForType name deps ty
    in foldl addDepsForTaggedType deps taggedTypes
  | Quotient (ty,term,_) -> (addDepsForTerm name (addDepsForType name deps ty) term)
  | Subtype (ty,term,_) ->  (addDepsForTerm name (addDepsForType name deps ty) term)
  | Base (qid,tys,_) ->  (foldl (fn (deps, ty) -> addDepsForType name deps ty)
                                (insertDepIntoMap name qid deps)
                                tys)
  | Boolean _ -> deps
  | TyVar (tyVar,_) -> deps
  | Pi(tvs,ty,_) ->  (addDepsForType name deps ty)
    %Can this occur?  I am leaving this out, so that an error will be triggered if this ever occurs.
  % | And(types,_) -> (foldl (fn (deps, ty) -> addDepsForType name deps ty)
  %                          deps
  %                          types)
  | Any(_) -> deps
  | mystery -> fail ("No match in addDepsForType with: '" ^ (anyToString mystery) ^ "'")
        
op addDepsForFun (name : QualifiedId) (fun:MSFun) (deps:Deps) : Deps =
  case fun of
  | Not       -> deps
  | And       -> deps
  | Or        -> deps
  | Implies   -> deps
  | Iff       -> deps
  | Equals    -> deps
  | NotEquals -> deps
  | Quotient typename -> (insertDepIntoMap name typename deps)
  | Choose typename   -> (insertDepIntoMap name typename deps)
  | Restrict -> deps %what is this?
  | Relax -> deps %what is this?
  | PQuotient typename -> (insertDepIntoMap name typename deps) % what is this?
  | PChoose typename   -> (insertDepIntoMap name typename deps) % what is this?
  | Op (qid,fixity) ->    (insertDepIntoMap name qid deps)
  | Project id -> deps
  | RecordMerge -> deps
  | Embed (id,b) -> deps
  | Embedded id  -> deps
  | Select id -> deps %FIXME what is this?
  | Nat nat -> deps
  | Char char -> deps
  | String string -> deps
  | Bool bool -> deps
    %      | OneName (id,fxty) -> ppString id
    %      | TwoNames (id1,id2,fxty) -> ppQualifiedId (Qualified (id1,id2))
  | mystery -> fail ("No match in addDepsForFun with: '" ^ (anyToString mystery) ^ "'")

op addDepsForMatchCase (name : QualifiedId) (deps : Deps, triple : (APattern Position * ATerm Position * ATerm Position)) : Deps =
  let (pattern, guard, term) = triple in
    addDepsForTerm name deps term
    
op addDepsForMatch (name : QualifiedId) (cases:MSMatch) (deps:Deps) : Deps =
  List.foldl (addDepsForMatchCase name) deps cases

% Walk through term and, for each thing mentioned, record the fact that name depends on that thing.
op addDepsForTerm (name : QualifiedId) (deps: Deps) (term: MSTerm): Deps =
  case term of
  | Apply (term1, term2, _) -> (addDepsForTerm name (addDepsForTerm name deps term1) term2)
    % think about tuples vs records:
  | Record (fields,_) -> (foldl (fn (deps, (_, term)) -> addDepsForTerm name deps term) deps fields)
  | Bind (binder,vars,term,_) -> addDepsForTerm name deps term
  | The (var,term,_) -> addDepsForTerm name deps term
  | Let (decls,term,_)    -> foldl (fn (deps, (_, term)) -> addDepsForTerm name deps term) (addDepsForTerm name deps term) decls
  | LetRec (decls,term,_) -> foldl (fn (deps, (_, term)) -> addDepsForTerm name deps term) (addDepsForTerm name deps term) decls
  | Var (v,_) -> deps
  | Fun (fun,ty,_) -> (addDepsForType name (addDepsForFun name fun deps) ty) %should we include the deps from ty or not?
  | Lambda (match,_) -> addDepsForMatch name match deps
  | IfThenElse (pred,term1,term2,_) -> (addDepsForTerm name (addDepsForTerm name (addDepsForTerm name deps pred) term1) term2)
  | Seq (terms,_) -> foldl (fn (deps, term) -> addDepsForTerm name deps term) deps terms
  | TypedTerm (term,ty,_) -> (addDepsForType name (addDepsForTerm name deps term) ty)
    %% what about Transform?
  | Pi(tvs,term,_) -> addDepsForTerm name deps term
  | And(terms,_) -> foldl (fn (deps, term) -> addDepsForTerm name deps term) deps terms
  | Any(_) -> deps
  | mystery -> fail ("No match in addDepsForTerm with: '" ^ (anyToString mystery) ^ "'")

op addDepsForAOpInfo (aopinfo : AOpInfo StandardAnnotation) (deps:Deps) : Deps = 
  let {names, fixity, dfn, fullyQualified?} = aopinfo in
  let name = head names in
    addDepsForTerm name deps dfn

op addDepsForMapLMapFromStringsToAOpInfos (m:MapL.Map(String, (AOpInfo StandardAnnotation))) (deps:Deps) : Deps =
  foldi (fn (key, val, deps) -> (addDepsForAOpInfo val deps))
        deps
        m
   
%% Each val in the map is itself a map.
op addDepsForAOpMapEntry (key : String, val : (MapL.Map(String, (AOpInfo StandardAnnotation))), deps: Deps) : Deps =
  addDepsForMapLMapFromStringsToAOpInfos val deps
              
%% This is a map from op names to (maps from qualifiers to opinfos).
op addDepsForAOpMap (m:(AOpMap StandardAnnotation), deps : Deps) : Deps =
  MapSTHashtable.STH_foldi(addDepsForAOpMapEntry, deps, m)


op addDepsForATypeInfo (atypeinfo : ATypeInfo StandardAnnotation) (deps:Deps) : Deps = 
  let {names, dfn} = atypeinfo in
  let name = head names in
    addDepsForType name deps dfn

op addDepsForMapLMapFromStringsToATypeInfos (m:MapL.Map(String, (ATypeInfo StandardAnnotation))) (deps:Deps) : Deps =
  foldi (fn (key, val, deps) -> (addDepsForATypeInfo val deps))
        deps
        m
   
%% Each val in the map is itself a map.
op addDepsForATypeMapEntry (key : String, val : (MapL.Map(String, (ATypeInfo StandardAnnotation))), deps: Deps) : Deps =
  addDepsForMapLMapFromStringsToATypeInfos val deps
              
%% This is a map from type names to (maps from qualifiers to typeinfos).
op addDepsForATypeMap (m:(ATypeMap StandardAnnotation), deps : Deps) : Deps =
  MapSTHashtable.STH_foldi(addDepsForATypeMapEntry, deps, m)

%FIXME fill this in!
op addDepsForSpecElement (elem : SpecElement, deps : Deps) : Deps =
  case elem of
  %% Skipping the scterm for now.  Skipping spc because we have specelems
  | Import (scterm, spc, specelems, _) -> addDepsForSpecElements(specelems, deps)
  | Type (_,_) -> deps % nothing really to do here
  | TypeDef (_,_) -> deps % nothing really to do here
  | Op (_,_,_) -> deps % nothing really to do here
  | OpDef (_,_,_,_) -> deps % nothing really to do here %TODO use the transform history?
  | Property (proptype, propname, tyvars, term, _) -> addDepsForTerm propname deps term
  | Comment (str, _) -> deps
  | Pragma (_, _, _, _) -> deps %anything to do here?

op addDepsForSpecElements (elems : SpecElements, deps : Deps) : Deps =
  case elems of
  | [] -> deps
  | elem :: rest -> addDepsForSpecElements(rest, addDepsForSpecElement(elem, deps))

%% First we build a map that captures the dependency information.  Then we turn the map into a string for printing.
op getDepsForSpec (spc : Spec) : String =
  let deps = MapSTHashtable.STH_empty_map in
  let deps = addDepsForAOpMap(spc.ops, deps) in 
  let deps = addDepsForATypeMap(spc.types, deps) in
  let deps = addDepsForSpecElements(spc.elements, deps) in
    %%FIXME count mentions in theorems (claims).  what else?
     MapSTHashtable.STH_foldi ((fn (key, val, string) -> ((printQualifiedIdFull key)^":"^(printQIDSet val)^"\n"^string)), 
                               "", 
                               deps)

%% Evaluate the given unit and print its deps.
%% Returns a flag indicating whether the operation succeeded (failure may happen if the spec fails to be processed).
op showDepsForSpec (uid_str : String) : Bool =
  let _ = writeLine ("Printing deps for unit: "^uid_str) in
    %% Evaluate the unit (if necessary):
    case evaluateUnitId uid_str of
    | None -> let _ = writeLine ("ERROR: Could not evaluate UID: " ^ uid_str) in false
    | Some val ->
      (case val of
       | Spec spc ->
         (case uidForValue val of
          | None -> let _ = writeLine "ERROR: Can't get UID string from value" in false
          | Some uid ->
            let uidstr = fileNameInSubDir(uid, "deps") in
            let file_name = uidstr ^ ".deps" in
            let _ = ensureDirectoriesExist file_name in
            let deps = getDepsForSpec(spc) in
	    let _ = writeLine("Writing deps to: "^file_name^"\n") in
            let _ = writeStringToFile(deps,file_name) in
              true)
       | _ -> let _ = writeLine "ERROR: The unit evaluated to something other than a spec." in false)

%% This is the top level Metaslang function for the 'showdeps' command.  It
%% is called by the hand-written Lisp function showdeps in toplevel.lisp.
%% The optional_argstring is the entire argument string passed to showdeps, or None.
%% FIXME add more processing of the argument string:
%%   strip leading spaces
%%   handle Windows path names (driver letter plus colon, backslashes instead of slashes).
%% Then get rid of the awkward call to uidStringForValue?
%% The return value is an optional string to make the new value of *last-unit-Id-_loaded*.
%% FIXME can the previous unit loaded be something unexpected, like a spec transform term?

op evaluateShowDeps (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String = 
  let _ = writeLine "Calling evaluateShowDeps." in
  let _ = writeLine ("The user's home directory: "^homedir) in
  let _ = writeLine ("arg string: "^(case optional_argstring of Some str -> ("\""^str^"\"") | None -> "No arg string supplied.")) in
  %FIXME handle the case when this is a qid?
  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  %% Get the unit ID to process:
  let opt_uid_str =
    (case optional_argstring of
       %% No arguments given at all, so use the last unit loaded, if there is one.
     | None -> (case lastUnitIdLoaded of
                | None -> let _ = writeLine("ERROR: No unit given and no previous unit loaded.") in None
                | Some uid_str -> lastUnitIdLoaded)
       %% Otherwise, the argument string is the unit ID to process:
     | Some argstring -> optional_argstring) in
    (case opt_uid_str of
     | None -> None %% fail and don't change *last-unit-Id-_loaded*
     | Some uid_str -> 
       let uid_str = substHomeDir(uid_str, homedir) in
       %% Print the deps to the file and return a new value for *last-unit-Id-_loaded* if the operation succeeded.
       let success? = showDepsForSpec uid_str in
       if success? then Some uid_str else None)

end-spec
