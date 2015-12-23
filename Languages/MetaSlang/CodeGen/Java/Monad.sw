(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


JGen qualifying spec

%import translate (translate /Library/Structures/Data/Monad/Base
%		  by {Monad +-> Env})
%                  by {Monad._ +-> Env._}

%import Monad qualifying /Library/Structures/Data/Monad/Base
%import JGen qualifying /Languages/MetaSlang/Specs/Categories/Specs       % AnnSpec.Spec
import /Languages/MetaSlang/Specs/AnnSpec
import /Languages/Java/Java

import Errors
%import IJavaCodeGen
import /Languages/SpecCalculus/Semantics/Wizard       % op specwareWizard? : Bool
import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
import /Library/Legacy/DataStructures/StringMapSplay

type JGenEnv a = State -> (Result a) * State

type Result a =
  | Ok a
  | Exception JGenException

type SpecialFunType = StringMap.Map JavaExpr * MSTerm * Nat * Nat -> JGenEnv (Option (JavaBlock * JavaExpr * Nat * Nat))

type State = {
	      envSpec            : Spec,
	      packageName        : Option JavaName,
	      imports            : List JavaName,
	      clsDecls           : List ClsDecl,
	      interfDecls        : List InterfDecl,
	      arrowclasses       : List Java.ClsDecl,
	      productTypes       : MSTypes,
	      typeAliases        : List (String * String), % a list of type aliases for recording type definitions of the form "type t1 = t2" where t2 is either a base type or boolean
	      primitiveClassName : String,
	      ignoreSubtypes     : Bool,
	      verbose            : Bool,
	      sep                : String, % the string used for Java class name generation, default "_"
	      transformSpecFun   : Spec -> Spec,              % Accord
	      localVarToJExpr    : String -> Option JavaExpr, % Accord: return some java expression if the string is a local parameter
	      definedOps         : List QualifiedId,                % Accord: list of ops defined across many specs
	      specialFun         : SpecialFunType,
              createFieldFun     : MSTerm -> Bool,
	      ignoreTypeDefFun   : String -> Bool, % returns true, if the code generation should ignore the type definition for 
		                                   % the given string, used to prevent code generation for the type definition
		                                   % generated for the accord classes
              isClassNameFun     : String -> Bool, % returns true if the given ident is a currently visible classname
	      cresCounter        : Nat
	     }

%% same as NamedSpec in Accord/Sources/Semantics
%% but it's not clear what that file and this one import in common...
type AccordNamedSpec = {term : SCTerm,
			spc  : Spec}

op initialState : State
def initialState = {
		    envSpec            = emptySpec,
		    packageName        = None,
		    imports            = [],
		    clsDecls           = [],
		    interfDecls        = [],
		    arrowclasses       = [],
		    productTypes       = [],
		    typeAliases        = [],
		    primitiveClassName = "Primitive",
		    ignoreSubtypes     = false,
		    verbose            = true,
		    sep                = "_",
		    transformSpecFun   = (fn spc -> spc),
		    localVarToJExpr    = (fn _ -> None),
		    definedOps         = [],
		    specialFun         = (fn _ -> return None),
		    createFieldFun     = (fn tm -> 
                                            %% Suppress field declarations for undefined functions
                                            let (tvs, typ, tm) = unpackFirstTerm tm in
                                            ~(anyTerm? tm && embed? Arrow typ)),
                    ignoreTypeDefFun   = fn _ -> false,
		    isClassNameFun     = fn _ -> false,
		    cresCounter        = 0
		   }


%% --------------------------------------------------------------------------------
%% State ops

op get: JGenEnv State
def get =
  fn state -> (Ok state,state)

op put: State -> JGenEnv ()
def put s = fn _ -> (Ok (), s)


%% --------------------------------------------------------------------------------

op setPackageName: Option JavaName -> JGenEnv ()
def setPackageName optname =
  fn state ->
  (Ok (), state << { packageName = optname })

op getPackageName: JGenEnv (Option JavaName)
def getPackageName =
  fn state ->
  (Ok state.packageName, state)

op setImports: List JavaName -> JGenEnv ()
def setImports imports =
  fn state ->
  (Ok (), state << { imports = imports })

op addImports: List JavaName -> JGenEnv ()
def addImports imports =
  fn state ->
  (Ok (), state << { imports = state.imports ++ imports })

op getImports: JGenEnv (List JavaName)
def getImports =
  fn state ->
  (Ok state.imports, state)

op addClsDecl: ClsDecl -> JGenEnv ()
def addClsDecl decl =
  fn state ->
  (Ok (), maybeAddClsDecl (state, decl))

op  maybeAddClsDecl : State * ClsDecl -> State
def maybeAddClsDecl (state, decl) =
  let old_decls = state.clsDecls in
  if decl in? old_decls then
    state
  else
    case findLeftmost (fn old_decl -> old_decl.2.1 = decl.2.1) old_decls of
      | Some old_decl ->
        % This can happen in two cases -- 
        % We might be revising names, e.g. "BitString" => "int", in which case the old and
        % new decls would have the old and new names, respectively.
        % Or we might be merging two independently generated versions of the class.
        % To cover both cases, we merge, but prefer new to old.
        let merged_decl = mergeClsDecls old_decl decl in
	let new_decls = map (fn old_decl -> 
			     if old_decl.2.1 = decl.2.1 then 
			       merged_decl 
			     else
			       old_decl)
	                    old_decls
	in
	  state << { clsDecls = new_decls }
      | _ ->
	state << { clsDecls = state.clsDecls ++ [decl] }

 op  mergeClsDecls : ClsDecl -> ClsDecl -> ClsDecl
 def mergeClsDecls (decl_a as (mods_a, (id_a, super_class_a, super_interf_a), body_a)) 
                   (decl_b as (mods_b, (id_b, super_class_b, super_interf_b), body_b))
   =
   %% id_a must equal id_b for us to get here	      
   let new_super_class =
       case (super_class_a, super_class_b) of
	 | (None, _)        -> super_class_b
	 | (_,    None)     -> super_class_a  
	 | (Some a, Some b) -> 
	   if a = b then
	     Some a
	   else
	     let _ = writeLine("Two different super classes for class " ^ id_a ^ " : " ^ anyToString a ^ " and " ^ anyToString b) in
	     let _ = writeLine("Using first...") in
	     Some a
   in
   let new_super_interf = listUnion (super_interf_a, super_interf_b) in
   let new_hdr  = (id_a, new_super_class, new_super_interf) in
   let new_mods = listUnion (mods_a, mods_b) in
   %% The result for each merging of lists is almost  list_a ++ list_b, 
   %% except that anything from list_a with the same name as something from 
   %% list_b is suppressed.
   %% Unfortunately, the location of the names to compare is different for 
   %% each list, so this is verbose:
   let new_fields = foldl (fn (fields, a) ->
			   if exists? (fn b -> b.3.1 = a.3.1) body_b.flds then
			     fields
			   else
			     [a] ++ fields)
			  body_b.flds
			  body_a.flds
   in
   let new_methods = foldl (fn (methods, a) ->
			    if exists? (fn b -> b.1.3 = a.1.3) body_b.meths then
			      methods
			    else
			      [a] ++ methods)
                           body_b.meths
			   body_a.meths
   in
   let new_constrs = foldl (fn (constrs, a) ->
			    if exists? (fn b -> b.2 = a.2) body_b.constrs then
			      constrs
			    else
			      [a] ++ constrs)
                           body_b.constrs
			   body_a.constrs
   in
   let new_body = {
		   handwritten = listUnion (body_a.handwritten, body_b.handwritten),
		   staticInits = listUnion (body_a.staticInits, body_b.staticInits),
		   flds        = new_fields,
		   meths       = new_methods,
		   constrs     = new_constrs,
		   clss        = listUnion (body_a.clss,        body_b.clss),
		   interfs     = listUnion (body_a.interfs,     body_b.interfs)
		  }
   in
     (new_mods, new_hdr, new_body)
     
	    
	    
op addClsDecls: List ClsDecl -> JGenEnv ()
def addClsDecls decls =
  fn state ->
  (Ok (), foldl maybeAddClsDecl state decls) 

op addInterfDecl: InterfDecl -> JGenEnv ()
def addInterfDecl decl =
  fn state ->
  (Ok (), state << { interfDecls = state.interfDecls ++ [decl] })

op putClsDecls: List ClsDecl -> JGenEnv ()
def putClsDecls decls =
  fn state ->
  (Ok (), state << { clsDecls = decls })

op putInterfDecls: List InterfDecl -> JGenEnv ()
def putInterfDecls decls =
  fn state ->
  (Ok (), state << { interfDecls = decls })

op getClsDecls: JGenEnv (List ClsDecl)
def getClsDecls =
  fn state ->
  (Ok (state.clsDecls), state)

op addProductType: MSType -> JGenEnv ()
def addProductType srt =
  fn state ->
  (Ok (), state << { productTypes = state.productTypes ++ [srt] })

op addArrowClass: ClsDecl -> JGenEnv ()
def addArrowClass clsDecl =
  fn state ->
  (Ok (), state << { arrowclasses = state.arrowclasses ++ [clsDecl] })

op putProductTypes: MSTypes -> JGenEnv ()
def putProductTypes srts =
  fn state ->
  (Ok (), state << { productTypes = srts })

op putArrowClasses: List ClsDecl -> JGenEnv ()
def putArrowClasses clsDecls =
  fn state ->
  (Ok (), state << { arrowclasses = clsDecls })

op getProductTypes: JGenEnv MSTypes
def getProductTypes =
  fn state ->
  (Ok state.productTypes, state)

op getArrowClasses: JGenEnv (List ClsDecl)
def getArrowClasses =
  fn state ->
  (Ok state.arrowclasses, state)

op putEnvSpec: Spec -> JGenEnv ()
def putEnvSpec spc =
  fn state ->
  (Ok (), state << { envSpec = spc })

op getEnvSpec: JGenEnv Spec
def getEnvSpec =
  fn state ->
  (Ok state.envSpec, state)

% --------------------------------------------------------------------------------

op addTypeAlias: String * String -> JGenEnv ()
def addTypeAlias(lhs,rhs) =
  fn state -> 
  (Ok (), state << { typeAliases = state.typeAliases ++ [(lhs,rhs)] })

op getTypeAliases: JGenEnv (List(String * String))
def getTypeAliases =
  fn state ->
  (Ok state.typeAliases, state)

op getTypeAlias: String -> JGenEnv (Option String)
def getTypeAlias id =
  fn state ->
  let def getTypeAlias(l) =
       case l of
	 | [] -> None
	 | (x,id1)::l -> if x = id then Some id1 else getTypeAlias l
  in
    (Ok (getTypeAlias state.typeAliases),state)

% --------------------------------------------------------------------------------

op getPrimitiveClassName: JGenEnv String
def getPrimitiveClassName =
  fn state ->
  (Ok state.primitiveClassName, state)

op setPrimitiveClassName: String -> JGenEnv ()
def setPrimitiveClassName s =
  fn state ->
  (Ok (), state << { primitiveClassName = s })

op isIgnoreSubtypes: JGenEnv Bool
def isIgnoreSubtypes =
  fn state ->
  (Ok state.ignoreSubtypes, state)

op setIgnoreSubtypes: Bool -> JGenEnv ()
def setIgnoreSubtypes b =
  fn state ->
  (Ok (), state << { ignoreSubtypes = b })

op isVerbose: JGenEnv Bool
def isVerbose =
  fn state ->
  (Ok state.verbose, state)

op setVerbose: Bool -> JGenEnv ()
def setVerbose b =
  fn state ->
  (Ok (), state << { verbose = b })

op getSep: JGenEnv String
def getSep =
  fn state ->
  (Ok state.sep,state)

op setSep: String -> JGenEnv ()
def setSep sep =
  fn state ->
  (Ok (), state << { sep = sep })

op getTransformSpecFun: JGenEnv (Spec -> Spec)
def getTransformSpecFun =
  fn state ->
  (Ok state.transformSpecFun, state)

op setTransformSpecFun: (Spec -> Spec) -> JGenEnv ()
def setTransformSpecFun tfun =
  fn state ->
  (Ok (), state << { transformSpecFun = tfun })

op getLocalVarToJExprFun: JGenEnv (String -> Option JavaExpr)
def getLocalVarToJExprFun =
  fn state ->
  (Ok state.localVarToJExpr, state)

op setLocalVarToJExprFun: (String -> Option JavaExpr) -> JGenEnv ()
def setLocalVarToJExprFun tfun =
  fn state ->
  (Ok (), state << { localVarToJExpr = tfun })

op  getDefinedOps: JGenEnv (List QualifiedId)
def getDefinedOps =
  fn state ->
  (Ok state.definedOps, state)

op  setDefinedOps: List QualifiedId -> JGenEnv ()
def setDefinedOps qids =
  fn state ->
  (Ok (), state << { definedOps = qids })

op getSpecialFun: JGenEnv SpecialFunType
def getSpecialFun =
  fn state ->
  (Ok state.specialFun, state)

op setSpecialFun: SpecialFunType -> JGenEnv ()
def setSpecialFun sfun =
  fn state ->
  (Ok (), state << { specialFun = sfun })

op getCreateFieldFun: JGenEnv (MSTerm -> Bool)
def getCreateFieldFun =
  fn state ->
  (Ok state.createFieldFun, state)

op setCreateFieldFun: (MSTerm -> Bool) -> JGenEnv ()
def setCreateFieldFun cfun =
  fn state ->
  (Ok (), state << { createFieldFun = cfun })

op getIgnoreTypeDefFun: JGenEnv (String -> Bool)
def getIgnoreTypeDefFun =
  fn state ->
  (Ok state.ignoreTypeDefFun, state)

op setIgnoreTypeDefFun: (String -> Bool) -> JGenEnv ()
def setIgnoreTypeDefFun ifun =
  fn state ->
  (Ok (), state << { ignoreTypeDefFun = ifun })

op getIsClassNameFun: JGenEnv (String -> Bool)
def getIsClassNameFun =
  fn state ->
  (Ok state.isClassNameFun, state)

op setIsClassNameFun: (String -> Bool) -> JGenEnv ()
def setIsClassNameFun ifun =
  fn state ->
  (Ok (), state << { isClassNameFun = ifun })

op  setCresCounter : Nat -> JGenEnv ()
def setCresCounter n =
  fn state ->
  (Ok (), state << { cresCounter = n })

op  getCresCounter : JGenEnv Nat
def getCresCounter =
  fn state ->
  (Ok state.cresCounter, state)

%%  ================================================================================
%%  monadBind and monadSeq expressions are generated by the MetaSlang parser
%%  for the "<-" and ";" in forms such as { y <- f x ; z <- g y ; return z }
%%  ================================================================================

op monadBind : [a,b] (JGenEnv a) * (a -> JGenEnv b) -> JGenEnv b
def monadBind (f, g1) =
    fn state ->
      case (f state) of

        %% In the normal case, y is the value that would have been returned
        %%  by f if it had not been written monadically but rather dealt with
        %%  exceptions via side effects or a non-local flow of control.
        %% g accepts that obvious value and produces a new JGenEnv (see above),
	%%  which is applied to the hidden state created by the monadic f,
	%%  to produce a new value and state...
	| (Ok        y,      newState) -> (g1 y newState)

        %%
        %% In the exceptional case, f is not returning a normal value,
        %%  so we stop processing and simply return the exception, along
	%%  with its associated state, without ever looking at g.
        %%
	%% We can't do obvious optimization of | x -> x
        %%  because lhs is JGenEnv a and rhs is JGenEnv b
	| (Exception except, newState) -> (Exception except, newState)

op monadSeq : [a,b] (JGenEnv a) * (JGenEnv b) -> JGenEnv b
def monadSeq (f, g2) =   % monadBind (f, (fn _ -> g2))
    %% Unfolded is more efficient
    fn state ->
      case (f state) of
        | (Ok        _,      newState) -> (g2 newState)
        | (Exception except, newState) -> (Exception except, newState)

%% ================================================================================
%%  catch is used at outer levels to process exceptions.
%%  so that processing can resume normally after the catch.
%% ================================================================================

op catch : [a] JGenEnv a -> (JGenException -> JGenEnv a) -> JGenEnv a
def catch f handler =
    fn state ->
      (case (f state) of

        %% For the normal csses, catch is a no-op
        | (Ok        x, newState) -> (Ok x, newState)

	%% In exceptional cases, the handler might be a no-op,
	%% might generate an 'Ok' value with associatd state,
        %% or might return a completely new exception.
        | (Exception x, newState) -> handler x newState)

% tries a list of things and calls the handler only if all have failed
op catchL : [a] List(JGenEnv a) -> (JGenException -> JGenEnv a) -> JGenEnv a
def catchL flist handler =
  case flist of
    | [f] -> catch f handler
    | f::flist -> catch f (fn _ -> catchL flist handler)

% transform an exception an Option parameter, useful for
% try-catch situations
op try : [a] JGenEnv a -> JGenEnv (Option a)
def try f =
  fn state ->
  (case (f state) of
     | (Ok x,newState) -> (Ok(Some x),newState)
     | (Exception _,newState) -> (Ok None,newState)
    )

%% Normal control flow -- proceed to next application

op return : [a] a -> JGenEnv a
def return x = fn state -> (Ok x, state)

op when : Bool -> JGenEnv () -> JGenEnv ()
def when p command = if p then (fn s -> (command s)) else return ()

op foldM : [a,b] (a -> b -> JGenEnv a) -> a -> List b -> JGenEnv a
def foldM f a l =
    case l of
      | [] -> return a
      | x::xs -> {
            y <- f a x;
            foldM f y xs
          }

(**
 * seqM has the effect the f is called on each element of the list l
 * whereby the state of the previous execution is not lost (as it is
 * in mapM
 *)
op seqM : [a,b] (a -> JGenEnv b) -> List a -> JGenEnv ()
def seqM f l =
  case l of
    | [] -> return ()
    | x::xs -> {
		f x;
		seqM f xs
	       }

op mapM : [a,b] (a -> JGenEnv b) -> (List a) -> JGenEnv (List b)
def mapM f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- mapM f xs;
            return (Cons (xNew,xsNew))
          }

op appM : [a] (a -> JGenEnv ()) -> (List a) -> JGenEnv ()
def appM f l =
  case l of
    | [] -> return ()
    | x::xs -> {
		f x;
		appM f xs
	       }

op mapOptionM: [a,b] (a -> JGenEnv b) -> Option a -> JGenEnv (Option b)
def mapOptionM f x =
  case x of
    | None -> return None
    | Some x -> {
		 res <- f x;
		 return (Some res)
		}

op require: Bool -> JGenException -> JGenEnv ()
def require check except =
  if check then return ()
  else raise except

op checkSupported: Bool -> String * Pos -> JGenEnv ()
def checkSupported check (msg,pos) =
  if check then return ()
  else raise(NotSupported(msg),pos)

op ifM: Bool -> JGenEnv () -> JGenEnv ()
def ifM check f =
  if check then f else return ()

%% --------------------------------------------------------------------------------
%%  Exception handling -- do not process following applications

op raise : [a] JGenException -> JGenEnv a
def raise except = 
  fn state -> 
  let _ = if specwareWizard? then
             %% This allows us to examine the stack at the time of the error
             fail (anyToString except) % under specwareWizard?
	  else
	    ()
  in
  (Exception except, state)

% conditional exception handling
op checkraise: JGenException -> JGenEnv ()
def checkraise except =
  case except of
    | (NoError,_) -> (fn state -> (Ok (), state))
    | _ -> (fn state -> 
	    let _ = if specwareWizard? then
	              %% This allows us to examine the stack at the time of the error
	              fail (anyToString except) % under specwareWizard?
		    else
		      ()
	    in
	      (Exception except, state))

%% --------------------------------------------------------------------------------
%%  Debugging -- normal control flow, but print message as immediate side effect

op print : String -> JGenEnv ()
def print str =
  fn state ->
    let _ = toScreen str in
    (Ok (), state)

op println : String -> JGenEnv ()
def println s = print (s^"\n")

op vprintln : String -> JGenEnv ()
def vprintln s =
  {
   verbose <- isVerbose;
   if verbose then
     println s
   else return ()
  }

op printI: Int -> JGenEnv ()
def printI n = print (Integer.show n)

op debug?: Bool
def debug? = true

op dbg: String -> JGenEnv ()
def dbg s = if debug? then println s else return ()

%This runs a monadic program and lifts the result out of the monad.
%op run : [a] JGenEnv a -> a
op run : [a] JGenEnv a -> State -> a
def run f s = 
  case f s of
    | (Ok x, _) -> x
    | (Exception exception, _) -> 
    fail ("run: uncaught exception:\n  ") % ^ (printException exception))


%% --------------------------------------------------------------------------------
%% handler op that shows the exception and returns a default value
(*
op showAndContinue: [a] a -> JGenException  -> JGenEnv a
def showAndContinue defaultvalue except =
  {
   println ("*** Error: "^(errToString except));
   return defaultvalue
  }
*)

endspec
