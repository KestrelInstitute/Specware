%% TODO: Maybe this file should be called ShowDeps.sw since showdeps is the command to invoke it.

%% This file contains a utility to print the "dependencies" in a spec.  For each
%% type or op, it prints the list of types and ops it refers to.  The output
%% goes to a file in the deps/ subdirectory of the directory that contains the
%% spec.  Each line of the output lists a type or op, followed by a colon and a
%% space-separated list of all the types or ops it refers to.

%% This file might be similar to some of the operations done by Languages/MetaSlang/Transformations/SliceSpec.sw

%% The top level function to call is printDepsForSpec.  To call this:
%%   gen-lisp /Languages/SpecCalculus/AbstractSyntax/PrintDeps.sw
%%   cl ~/Dropbox/Specware/Languages/SpecCalculus/AbstractSyntax/lisp/PrintDeps.lisp
%%   lisp (PRINTDEPS::printDepsForSpec "/usr/home/kestrel/ewsmith/Dropbox/vTPM/vTPM/Examples/Arrays_1#Imp")
%% Note that this last step takes advantage of the ability of the Specware shell
%% to execute Lisp commands.

%% TODO: Print to the screen instead of a file?
%% TODO: Make this command available directly in the Specware shell.

PrintDeps qualifying spec 

import Types
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Languages/MetaSlang/Transformations/NormalizeTypes
import /Library/PrettyPrinter/WadlerLindig
import /Languages/MetaSlang/Specs/Printer
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Monad

% prints <unqualified> is no qualifier
op printQualifiedIdFull (Qualified (q, id) : QualifiedId) : String =
  q ^ "." ^ id

type QIDSet = List QualifiedId %FIXME which set library should I use?

op printQIDSet (set : QIDSet) : String =
  foldl (fn (str, qid) -> " "^(printQualifiedIdFull qid)^str) "" set

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

%type Dep = String % for now
type Deps = DepsMap
  
type SpecElem = SpecElemTerm
  
  %% --------------------------------------------------------------------------------
  %% Give the signature of utilities so we don't have to import them

  type GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
  op  Specware.evaluateUnitId: String -> Option Value
  op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId

  %op  SpecCalc.uidToFullPath: UnitId -> String
  op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo

  op uidToDepsName ({path,hashSuffix=_}: UnitId) : String =
   let device? = deviceString? (head path) in
   let main_name = last path in
   let path_dir = butLast path in 
   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             ["/deps/",main_name]
                             (if device? then tail path_dir else path_dir))
   in if device?
	then (head path) ^ mainPath
	else mainPath

  %% Used because the use of "#" causes problems with syntax coloring.
  op numberSignString : String = implode [##]

  op uidStringPairForValue (val: Value) : Option (UnitId * String * String) =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
    case findUnitIdForUnit(val,global_context) of
      | None -> None
      | Some uid ->
        Some (uid,
	      uidToDepsName uid,
	      case uid.hashSuffix of
		| Some loc_nm -> numberSignString ^ loc_nm
		| _ -> "")

  op uidStringForValue (val:Value) : Option String =
    case uidStringPairForValue val of
      | None -> None
      | Some(_,filnm,hash) -> Some(filnm ^ hash)

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
%       | And(types,_) ->
% 	ppGrConcat[ppString "and ",
% 		   ppString "[",
% 		   ppSep (ppBreak) %(ppString ", ")
%                          (map addDepsForType types),
% 		   ppString "]"]
       | Any(_) -> deps
       | mystery -> fail ("No match in addDepsForType with: '" ^ (anyToString mystery) ^ "'")

  op addDepsForFun (name : QualifiedId) (fun:Fun) (deps:Deps) : Deps =
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
    
  op addDepsForMatch (name : QualifiedId) (cases:Match) (deps:Deps) : Deps =
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
   foldi
   (fn (key, val, deps) -> (addDepsForAOpInfo val deps))
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
   foldi
   (fn (key, val, deps) -> (addDepsForATypeInfo val deps))
   deps
   m
   
   %% Each val in the map is itself a map.
   op addDepsForATypeMapEntry (key : String, val : (MapL.Map(String, (ATypeInfo StandardAnnotation))), deps: Deps) : Deps =
    addDepsForMapLMapFromStringsToATypeInfos val deps
              
  %% This is a map from type names to (maps from qualifiers to typeinfos).
  op addDepsForATypeMap (m:(ATypeMap StandardAnnotation), deps : Deps) : Deps =
    MapSTHashtable.STH_foldi(addDepsForATypeMapEntry, deps, m)

  %% First we build a map that captures the dependency information.  Then we turn the map into a string for printing.
  op getDepsForSpec (value : Value) : String =
    case value of
      | Spec spc -> (let deps = MapSTHashtable.STH_empty_map in
                    let deps = addDepsForAOpMap(spc.ops, deps) in 
                    let deps = addDepsForATypeMap(spc.types, deps) in
                    %%FIXME count mentions in theorems (claims).  what else?
                    MapSTHashtable.STH_foldi ((fn (key, val, string) -> ((printQualifiedIdFull key)^":"^(printQIDSet val)^"\n"^string)), "", deps))
      | _        -> "Unrecognized value.  It should be a spec."

  %% Evaluate the given unit and print its deps.
  %% Returns a flag indicating whether the operation succeeded (failure may happen if the spec fails to be processed).
  op printDepsForSpec (uid_str : String) : Bool =
  let _ = writeLine ("Printing deps for spec: "^uid_str) in
  case evaluateUnitId uid_str of
    | Some val ->
      (case uidStringForValue val of
         | None -> let _ = writeLine "Error: Can't get UID string from value" in false
         | Some uidstr ->
           let file_name = uidstr ^ ".deps" in
           let _ = ensureDirectoriesExist file_name in
           let deps = getDepsForSpec(val) in
	   let _ = writeLine("Writing deps to to: "^file_name^"\n") in
           let _ = writeStringToFile(deps,file_name) in
           true
           )
    | _ -> let _ = writeLine ("Error: Could not evaluate UID: " ^ uid_str) in false

endspec
