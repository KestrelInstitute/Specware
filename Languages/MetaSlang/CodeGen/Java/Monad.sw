
JGen qualifying spec

%import translate (translate /Library/Structures/Data/Monad/Base
%		  by {Monad +-> Env})
%                  by {Monad._ +-> Env._}

%import Monad qualifying /Library/Structures/Data/Monad/Base
import /Languages/MetaSlang/Specs/Categories/Specs       % AnnSpec.Spec
import Java qualifying /Languages/Java/Java

import Errors
%import IJavaCodeGen

sort JGenEnv a = State -> (Result a) * State

sort Result a =
  | Ok a
  | Exception JGenException

type SpecialFunType = StringMap.Map Java.Expr * MS.Term * Nat * Nat -> JGenEnv (Option (Block * Java.Expr * Nat * Nat))

type State = {
	      envSpec : Spec,
	      packageName : Option Name,
	      imports : List Name,
	      clsDecls : List ClsDecl,
	      interfDecls : List InterfDecl,
	      arrowclasses : List Java.ClsDecl,
	      productSorts : List Sort,
	      typeAliases : List(String * String), % a list of type aliases for recording type definitions of the form "type t1 = t2" where t2 is either a base type or boolean
	      primitiveClassName : String,
	      ignoreSubsorts : Boolean,
	      verbose : Boolean,
	      sep : String, % the string used for Java class name generation, default "$"
	      transformSpecFun : Spec -> Spec,
	      localVarToJExpr : String -> Option Java.Expr, % return some java expression if the string is a local parameter
	      specialFun: SpecialFunType,
              createFieldFun : MS.Term -> Boolean,
	      ignoreTypeDefFun : String -> Boolean, % returns true, if the code generation should ignore the type definition for 
		                                    % the given string, used to prevent code generation for the type definition
		                                    % generated for the accord classes
              isClassNameFun : String -> Boolean % returns true if the given ident is a currently visible classname
	     }

op initialState : State
def initialState = {
		    envSpec = emptySpec,
		    packageName = None,
		    imports = [],
		    clsDecls = [],
		    interfDecls = [],
		    arrowclasses = [],
		    productSorts = [],
		    typeAliases = [],
		    primitiveClassName = "Primitive",
		    ignoreSubsorts = false,
		    verbose = true,
		    sep = "$",
		    transformSpecFun = (fn spc -> spc),
		    localVarToJExpr = (fn _ -> None),
		    specialFun = (fn _ -> return None),
		    createFieldFun = (fn tm -> 
				      %% Suppress field declarations for undefined functions
				      let (tvs, typ, tm) = unpackTerm tm in
				      case tm of
					| Any _ -> 
				          (case typ of
					     | Arrow _ -> false
					     | _ -> true)
					| _ -> true),
		    ignoreTypeDefFun = fn _ -> false,
		    isClassNameFun = fn _ -> false
		   }


%% --------------------------------------------------------------------------------
%% State ops

op get: JGenEnv State
def get =
  fn state -> (Ok state,state)

op put: State -> JGenEnv ()
def put s = fn _ -> (Ok (), s)


%% --------------------------------------------------------------------------------

op setPackageName: Option Name -> JGenEnv ()
def setPackageName optname =
  fn state ->
  (Ok (), state << { packageName = optname })

op getPackageName: JGenEnv (Option Name)
def getPackageName =
  fn state ->
  (Ok state.packageName, state)

op setImports: List Name -> JGenEnv ()
def setImports imports =
  fn state ->
  (Ok (), state << { imports = imports })

op addImports: List Name -> JGenEnv ()
def addImports imports =
  fn state ->
  (Ok (), state << { imports = state.imports ++ imports })

op getImports: JGenEnv (List Name)
def getImports =
  fn state ->
  (Ok state.imports, state)


op addClsDecl: ClsDecl -> JGenEnv ()
def addClsDecl decl =
  fn state ->
  (Ok (), state << { clsDecls = state.clsDecls ++ [decl] })

op addClsDecls: List ClsDecl -> JGenEnv ()
def addClsDecls decls =
  fn state ->
  (Ok (), state << { clsDecls = state.clsDecls ++ decls })

op addInterfDecl: InterfDecl -> JGenEnv ()
def addInterfDecl decl =
  fn state ->
  (Ok (), state << { interfDecls = state.interfDecls ++ [decl] })

op putClsDecls: List ClsDecl -> JGenEnv ()
def putClsDecls clsDecls =
  fn state ->
  (Ok (), state << { clsDecls = clsDecls })

op getClsDecls: JGenEnv (List ClsDecl)
def getClsDecls =
  fn state ->
  (Ok (state.clsDecls), state)

op addProductSort: Sort -> JGenEnv ()
def addProductSort srt =
  fn state ->
  (Ok (), state << { productSorts = state.productSorts ++ [srt] })

op addArrowClass: ClsDecl -> JGenEnv ()
def addArrowClass clsDecl =
  fn state ->
  (Ok (), state << { arrowclasses = state.arrowclasses ++ [clsDecl] })

op putProductSorts: List Sort -> JGenEnv ()
def putProductSorts srts =
  fn state ->
  (Ok (), state << { productSorts = srts })

op putArrowClasses: List ClsDecl -> JGenEnv ()
def putArrowClasses clsDecls =
  fn state ->
  (Ok (), state << { arrowclasses = clsDecls })

op getProductSorts: JGenEnv (List Sort)
def getProductSorts =
  fn state ->
  (Ok state.productSorts, state)

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

op isIgnoreSubsorts: JGenEnv Boolean
def isIgnoreSubsorts =
  fn state ->
  (Ok state.ignoreSubsorts, state)

op setIgnoreSubsorts: Boolean -> JGenEnv ()
def setIgnoreSubsorts b =
  fn state ->
  (Ok (), state << { ignoreSubsorts = b })

op isVerbose: JGenEnv Boolean
def isVerbose =
  fn state ->
  (Ok state.verbose, state)

op setVerbose: Boolean -> JGenEnv ()
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

op getLocalVarToJExprFun: JGenEnv (String -> Option Java.Expr)
def getLocalVarToJExprFun =
  fn state ->
  (Ok state.localVarToJExpr, state)

op setLocalVarToJExprFun: (String -> Option Java.Expr) -> JGenEnv ()
def setLocalVarToJExprFun tfun =
  fn state ->
  (Ok (), state << { localVarToJExpr = tfun })

op getSpecialFun: JGenEnv SpecialFunType
def getSpecialFun =
  fn state ->
  (Ok state.specialFun, state)

op setSpecialFun: SpecialFunType -> JGenEnv ()
def setSpecialFun sfun =
  fn state ->
  (Ok (), state << { specialFun = sfun })

op getCreateFieldFun: JGenEnv (MS.Term -> Boolean)
def getCreateFieldFun =
  fn state ->
  (Ok state.createFieldFun, state)

op setCreateFieldFun: (MS.Term -> Boolean) -> JGenEnv ()
def setCreateFieldFun cfun =
  fn state ->
  (Ok (), state << { createFieldFun = cfun })

op getIgnoreTypeDefFun: JGenEnv (String -> Boolean)
def getIgnoreTypeDefFun =
  fn state ->
  (Ok state.ignoreTypeDefFun, state)

op setIgnoreTypeDefFun: (String -> Boolean) -> JGenEnv ()
def setIgnoreTypeDefFun ifun =
  fn state ->
  (Ok (), state << { ignoreTypeDefFun = ifun })

op getIsClassNameFun: JGenEnv (String -> Boolean)
def getIsClassNameFun =
  fn state ->
  (Ok state.isClassNameFun, state)

op setIsClassNameFun: (String -> Boolean) -> JGenEnv ()
def setIsClassNameFun ifun =
  fn state ->
  (Ok (), state << { isClassNameFun = ifun })

%%  ================================================================================
%%  monadBind and monadSeq expressions are generated by the MetaSlang parser
%%  for the "<-" and ";" in forms such as { y <- f x ; z <- g y ; return z }
%%  ================================================================================

op monadBind : fa (a,b) (JGenEnv a) * (a -> JGenEnv b) -> JGenEnv b
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

op monadSeq : fa (a,b) (JGenEnv a) * (JGenEnv b) -> JGenEnv b
def monadSeq (f, g2) = monadBind (f, (fn _ -> g2))

%% ================================================================================
%%  catch is used at outer levels to process exceptions.
%%  so that processing can resume normally after the catch.
%% ================================================================================

op catch : fa (a) JGenEnv a -> (JGenException -> JGenEnv a) -> JGenEnv a
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
op catchL : fa(a) List(JGenEnv a) -> (JGenException -> JGenEnv a) -> JGenEnv a
def catchL flist handler =
  case flist of
    | [f] -> catch f handler
    | f::flist -> catch f (fn _ -> catchL flist handler)

% transform an exception an Option parameter, useful for
% try-catch situations
op try : fa (a) JGenEnv a -> JGenEnv (Option a)
def try f =
  fn state ->
  (case (f state) of
     | (Ok x,newState) -> (Ok(Some x),newState)
     | (Exception _,newState) -> (Ok None,newState)
    )

%% Normal control flow -- proceed to next application

op return : fa (a) a -> JGenEnv a
def return x = fn state -> (Ok x, state)

op when : Boolean -> JGenEnv () -> JGenEnv ()
def when p command = if p then (fn s -> (command s)) else return ()

op foldM : fa (a,b) (a -> b -> JGenEnv a) -> a -> List b -> JGenEnv a
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
op seqM : fa(a,b) (a -> JGenEnv b) -> List a -> JGenEnv ()
def seqM f l =
  case l of
    | [] -> return ()
    | x::xs -> {
		f x;
		seqM f xs
	       }

op mapM : fa (a,b) (a -> JGenEnv b) -> (List a) -> JGenEnv (List b)
def mapM f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- mapM f xs;
            return (Cons (xNew,xsNew))
          }

op appM : fa(a) (a -> JGenEnv ()) -> (List a) -> JGenEnv ()
def appM f l =
  case l of
    | [] -> return ()
    | x::xs -> {
		f x;
		appM f xs
	       }

op mapOptionM: fa(a,b) (a -> JGenEnv b) -> Option a -> JGenEnv (Option b)
def mapOptionM f x =
  case x of
    | None -> return None
    | Some x -> {
		 res <- f x;
		 return (Some res)
		}

op require: Boolean -> JGenException -> JGenEnv ()
def require check except =
  if check then return ()
  else raise except

op checkSupported: Boolean -> String * Pos -> JGenEnv ()
def checkSupported check (msg,pos) =
  if check then return ()
  else raise(NotSupported(msg),pos)

op ifM: Boolean -> JGenEnv () -> JGenEnv ()
def ifM check f =
  if check then f else return ()

%% --------------------------------------------------------------------------------
%%  Exception handling -- do not process following applications

op raise : fa(a) JGenException -> JGenEnv a
def raise except = 
  fn state -> (Exception except, state)

% conditional exception handling
op checkraise: JGenException -> JGenEnv ()
def checkraise except =
  case except of
    | (NoError,_) -> (fn state -> (Ok (), state))
    | _ -> (fn state -> (Exception except, state))

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

op printI: Integer -> JGenEnv ()
def printI n = print (Integer.toString n)

op debug?: Boolean
def debug? = true

op dbg: String -> JGenEnv ()
def dbg s = if debug? then println s else return ()

%This runs a monadic program and lifts the result out of the monad.
%op run : fa (a) JGenEnv a -> a
op run : fa (a) JGenEnv a -> State -> a
def run f s = 
  case f s of
    | (Ok x, _) -> x
    | (Exception exception, _) -> 
    fail ("run: uncaught exception:\n  ") % ^ (printException exception))


%% --------------------------------------------------------------------------------
%% handler op that shows the exception and returns a default value
(*
op showAndContinue: fa(a) a -> JGenException  -> JGenEnv a
def showAndContinue defaultvalue except =
  {
   println ("*** Error: "^(errToString except));
   return defaultvalue
  }
*)

endspec
