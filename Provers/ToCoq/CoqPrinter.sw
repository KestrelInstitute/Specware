(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CoqTermPrinter qualifying spec

import /Library/PrettyPrinter/BjornerEspinosa
import translate /Library/Structures/Data/Monad by {Monad._ +-> CoqTermPrinter._}
import /Library/Structures/Data/Monad/State

(* specs, terms, etc. *)
% import /Languages/SpecCalculus/Semantics/Bootstrap
import /Languages/MetaSlang/Specs/MSTerm
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import /Languages/SpecCalculus/AbstractSyntax/UnitId


(***
 *** customizations and flags
 ***)

(* the format width for producing Coq files *)
def formatWidth = 75


(***
 *** utility types and defs
 ***)

(* the Either type (from Haskell) *)
type Either (a, b) =
| Left a
| Right b

(* add an element to an alist, with no dups of keys *)
op addToAlist : [a,b] a * b * List (a * b) -> List (a * b)
def addToAlist (k, v, al) =
  case findLeftmost (fn (k', _) -> k = k') al of
    | Some _ -> al
    | Non -> (k, v) :: al

(* map a function of type A -> Option B over a list and then filter
   out only the "Some"'s returned by that function *)
op [a,b] filterMap (f : a -> Option b) (l : List a) : List b =
  case l of
    | [] -> []
    | x::l' ->
      case f x of
        | None -> filterMap f l'
        | Some x_out -> x_out :: filterMap f l'

(* map a function of type A -> Monad (Option B) over a list and then
   filter out only the "Some"'s returned by that function *)
op [a,b] filterMapM (f : a -> Monad (Option b)) (l : List a) : Monad (List b) =
  case l of
    | [] -> return []
    | x::l' ->
      { x_out_opt <- f x;
        l'_out <- filterMapM f l';
        case x_out_opt of
          | None -> return l'_out
          | Some x_out -> return (x_out :: l'_out) }

(* This is like filterMapM but with a (left) fold. That is, for each
   element x of l in turn, we apply f to (x, acc); if this returns
   Some (x',acc'), then we recurse, using acc' as the new accumulator,
   and prepend x' to the result list; otherwise, we recurse and use
   the old value of the accumulator. *)
op [a,b,c] filterFoldM (f : (a * c) -> Monad (Option (b * c))) (acc:c) (l : List a) : Monad (List b * c) =
  case l of
    | [] -> return ([], acc)
    | x::l' ->
      { x_out_opt <- f (x,acc);
        case x_out_opt of
          | None -> filterFoldM f acc l'
          | Some (x_out, next) -> {
              (l'_out,acc') <- filterFoldM f next l';
              return (x_out :: l'_out, acc')}
            }

(* version of foldr that assumes a non-empty list, so does not need a
   base case *)
(*
op [a] foldr1 (f: a * a -> b) (l: List a) : a =
  case l of
  | [x] -> x
  | hd::tl -> f (hd, foldr f base tl)
*)

(* separate a string into a list of the strings between a separator *)
def separateString (sep : Char) (str : String) : List String =
  let def helper strList =
    case splitAtLeftmost (fn c -> c = sep) strList of
      | Some (pre, _, post) -> implode pre :: helper post
      | None -> [implode strList]
  in
  helper (explode str)

(* concatenate a list of strings with a separator; inverse of above *)
def concatenate (sep : Char) (strs : List String) : String =
  case strs of
    | [] -> ""
    | [str] -> str
    | str :: strs' -> str ^ (implode [sep]) ^ concatenate sep strs'


op [a,b] mapM (f : a -> Monad b) (l : List a) : Monad (List b) =
  case l of
    | [] -> return []
    | x::l' ->
      { x_ret <- f x ;
        l_ret <- mapM f l' ;
        return (x_ret :: l_ret) }
(*
def mapM (f, l) =
  List.foldl
  ((fn (m, x) ->
      { x' <- f x ; l' <- m ; return (x'::l') }),
   return [], l)
*)

(* remove duplicates with a user-defined equality predicate *)
op [a] removeDups (eq : a -> a -> Bool) (l : List a) : List a =
  case l of
    | [] -> []
    | x :: l' ->
      (case findLeftmost (eq x) l' of
         | Some _ -> removeDups eq l'
         | None -> x :: (removeDups eq l'))

(* convert a Spec path into a triple (path, name, suffix_opt) *)
op specPathToRelUID : String -> Option RelativeUID
def specPathToRelUID spath =
  let spath_elems = separateString #/ spath in
  let (path, ctorfun) =
    % If spath starts with "/" then it is "SpecPath-Relative"
    if head spath_elems = "" then
      (butLast (tail spath_elems), (fn p -> SpecPath_Relative p))
    else (butLast spath_elems, (fn p -> UnitId_Relative p))
  in
  let base = last spath_elems in
  let hash_elems = separateString ## base in
  case hash_elems of
    | [filename] ->
      Some (ctorfun { path = path ++ [filename], hashSuffix = None })
    | [filename, suffix] ->
      Some (ctorfun { path = path ++ [filename], hashSuffix = Some suffix })
    | _ -> None


op relUIDToString(r:RelativeUID):String =
  case r of
    | UnitId_Relative u -> last (u.path)
    | SpecPath_Relative u ->  last (u.path)

(* declare this here so we don't have to import Bootstrap above *)
op  Specware.evaluateUnitId: String -> Option Value

(***
 *** converting Specware names to Coq names
 ***)

def qidToCoqName (q, id) =
  if q = "" || q = "<unqualified>" then id else q ^ "__" ^ id

def ppQid qid : Pretty = string (qidToCoqName qid)

type CoqModName = List String

def coqModNameToString (coq_mod : CoqModName) : String =
  concatenate #. coq_mod

def relUIDToCoqModuleName (ruid : RelativeUID) : CoqModName =
  let (uid, specpath?) =
    case ruid of
      | SpecPath_Relative uid -> (uid, true)
      | UnitId_Relative uid -> (uid, false)
  in
  (if specpath? then "Specware" :: uid.path else uid.path)
  ++ (case uid.hashSuffix of
        | Some suffix -> [suffix]
        | None -> [])

def relUIDToCoqNameString (ruid : RelativeUID) : String =
  coqModNameToString (relUIDToCoqModuleName ruid)

def specPathToCoqModule (spath : String) : Option CoqModName =
  case specPathToRelUID spath of
    | Some ruid -> Some (relUIDToCoqModuleName ruid)
    | None -> None

def meta_mod_name = "Meta"

(* add "Meta" to the end of a Coq module name *)
def coqModNameAddMeta (coq_mod : CoqModName) : CoqModName =
  coq_mod ++ [meta_mod_name]

(*
def relUIDToCoqMetaModuleName (ruid : RelativeUID) : String =
  coqModNameToString (coqModNameAddMeta (relUIDToCoqModuleName ruid))
*)

(* README: we do not want to deal with absolute paths, which are
   mostly what Specware seems to put out... *)
(* convert a uid to a Coq module name *)
(*
def uidToCoqModule (uid : UnitId) : Pretty =
  let suffixList =
    case uid.hashSuffix of
      | Some suf -> [suf]
      | None -> []
  in
  string (concatenate (intersperse "." (uid.path ++ suffixList)))
*)

(* muck around with Specware internal state to get a name for a Value;
   code taken from IsaPrinter.sw *)
(*
op uidForValue: Value -> Option UnitId
def uidForValue val =
  case MonadicStateInternal.readGlobalVar "GlobalContext" of
    | None -> None
    | Some global_context -> findUnitIdForUnit(val, global_context)

def uidToCoqName (uid : UnitId) =
  foldr (fn (str, rest) -> str ^ "." ^ rest) "" uid.path
  ^ (case uid.hashSuffix of
       | Some suffix -> "." ^ suffix
       | None -> "")

def valueToCoqName v =
  case uidForValue v of
    | Some uid -> Some (uidToCoqName uid)
    | None -> None
*)

(* convert a QualifierMap b to a list of ((q, id), b) *)
op listOfAQualifierMap : [a] AQualifierMap a -> List (String * String * a)
def listOfAQualifierMap m =
  foldriAQualifierMap (fn (q, id, elem, rest) -> (q, id, elem) :: rest) [] m

(* like the above, but apply f to each elem as well *)
op [a,b] mappedListOfAQualifierMap
  (f : a -> b) (m : AQualifierMap a) : List (String * String * b)
  = foldriAQualifierMap (fn (q, id, elem, rest) -> (q, id, f elem) :: rest) [] m

(* return true iff a type is well-defined, i.e., not "Any" *)
def typeIsDefined? (t : MSType) : Bool =
  case t of
    | Any _ -> false
    | _ -> true

(* return true iff a term is well-defined, i.e., not "Any" *)
def termIsDefined? (t : MSTerm) : Bool =
  case t of
    | Any _ -> false
    | TypedTerm (t', _, _) -> termIsDefined? t'
    | Lambda (matches, _) ->
      forall? (fn (_, _, body) -> termIsDefined? body) matches
    | _ -> true


(***
 *** The monad for translating to Coq
 ***)

(* Translation to Coq takes place in a monad, which is a state monad
   for a "current context" combined with an error monad *)

type Context =
  {
   freshNatCounter : Nat, % for making fresh names
   topPrettys : List Pretty, % out-of-band extras printed at top-level
   specName : String,
   prop : Bool, % If in `prop`, then Specware logical connectives will
               % be rendered using their Coq Prop forms, rather than
               % the decidable boolean forms (e.g. forall vs.
               % forallb).
   prec : Nat
   }

def mkContext (sn:String) =
  {
   specName = sn,
   freshNatCounter = 0,
   topPrettys = [],
   prop = false,
   prec = 0
   }

type Monad a = Context -> Either (String, Context * a)

% op monadBind: [a,b] (Monad a) * (a -> Monad b) -> Monad b
def monadBind (m, f) =
  fn ctx ->
  case m ctx of
    | Right (ctx', res) -> f res ctx'
    | Left str -> Left str

% op monadSeq : [a,b] (Monad a) * (Monad b) -> Monad b
def monadSeq (m1, m2) = monadBind (m1, (fn _ -> m2))

% op return : [a] a -> Monad a
def return x = fn ctx -> Right (ctx, x)

op err : [a] String -> Monad a
def err str = fn _ -> Left str

op getCtx : Monad Context
def getCtx = fn ctx -> Right (ctx, ctx)

op putCtx : Context -> Monad ()
def putCtx ctx = fn _ -> Right (ctx, ())

op freshNat : Monad Nat
def freshNat =
  { ctx <- getCtx;
    () <- putCtx (ctx<<{ freshNatCounter = ctx.freshNatCounter + 1 });
    return ctx.freshNatCounter }

op ppFreshVar : Monad Pretty
def ppFreshVar =
  { var_nat <- freshNat;
    return (string ("__fresh_" ^ intToString var_nat)) }

op appendTopPretty (p : Pretty) : Monad () =
  fn ctx -> Right (ctx << { topPrettys = ctx.topPrettys ++ [p] }, ())

op prependTopPretty (p : Pretty) : Monad () =
  fn ctx -> Right (ctx << { topPrettys = p :: ctx.topPrettys }, ())

op getSpecName : Monad String =
  { ctx <- getCtx;
    return ctx.specName
   }

(* Read the value of the prop flag *)
op getProp : Monad Bool =
  {
   ctx <- getCtx;
   return ctx.prop
  }

(* Execute m with the prop flag set *)
op [a] withProp(m:Monad a):Monad a =
  {
   ctx <- getCtx;
   putCtx (ctx << { prop = true });
   v <- m;
   ctx' <- getCtx;
   putCtx (ctx' << { prop = ctx.prop});
   return v
  }

(* Execute m with the prop flag cleared, in "bool" mode *)
op [a] withBool(m:Monad a):Monad a =
  {
   ctx <- getCtx;
   putCtx (ctx << { prop = false });
   v <- m;
   ctx' <- getCtx;
   putCtx (ctx' << { prop = ctx.prop});
   return v
   }

(* Execute m with the given precedence, p *)
op [a] withPrec(p:Precedence)(m:Monad a):Monad a =
  {
   ctx <- getCtx;
   putCtx (ctx << { prec = p });
   v <- m;
   ctx' <- getCtx;
   putCtx (ctx' << { prec = ctx.prec});
   return v
   }

(* Run mt if the prop flag is set, or mf otherwise *)
op [a] ifProp(mt:Monad a)(mf:Monad a):Monad a =
  {
   prop <- getProp;
   if prop then mt else mf
  }


(* Run operation for our monad: use a computation to write a Pretty to
   a file, returning an error string on error *)
op writingToFile : String * Context * Monad Pretty -> Option String
def writingToFile (filename, ctx, m) =
  case m ctx of
    | Right (ctx, pp) ->
      let combined_pp = prLines 0 (ctx.topPrettys ++ [pp]) in
      (toFile (filename, format (formatWidth, combined_pp)) ; None)
    | Left str -> Some str


(***
 *** pretty-printer helper functions
 ***)

op retString (str : String) : Monad Pretty =
  return (string str)

(* combination of return and blockFill *)
op retFill (elems : List (Nat * Pretty)) : Monad Pretty =
  return (blockFill (0, elems))

(* pretty-print p1 followed by p2 with a string separator *)
op ppSeparator (sep : String) (p1 : Pretty) (p2 : Pretty) : Pretty =
  blockFill (0, [(0, p1), (0, string (" " ^ sep ^ " ")), (0, p2)])

(* pretty-print p1 and p2 with a separator and a terminator *)
op ppSeparatorTerm : Pretty -> String -> Pretty -> String -> Pretty
def ppSeparatorTerm p1 sep p2 term =
  blockFill
  (0,
   [(0, p1),
    (1, string (" " ^ sep ^ " ")),
    (4, p2),
    (1, string (term ^ " "))])

(* pretty-print something like begin { middle } end, where either the
   whole thing is on one line on three with the middle indented *)
op ppIndentMiddle : Pretty -> Pretty -> Pretty -> Pretty
def ppIndentMiddle p1 p2 p3 =
  blockLinear (0, [(0, p1),(2, p2),(0, p3)])

def ppColon = ppSeparator ":"
def ppSemi = ppSeparator ";"
def ppColonEq = ppSeparator ":="

(* pretty-print parens around a Pretty *)
op ppParens (pp : Pretty) : Pretty =
  blockFill (0, [(0, string " ("), (1, pp), (0, string ") ")])

(* pretty-print curly brackets around a Pretty *)
op ppCurlies (pp : Pretty) : Pretty =
  blockFill (0, [(0, string " {"), (1, pp), (0, string "} ")])


(* pretty-print parens, but only if the given precedence is less than (or equal) to the enclosing term precedence *)
op ppPrecParens (prec:Precedence) (mpp : Monad Pretty) : Monad Pretty =
  {
   ctx <- getCtx;
   if (prec <= ctx.prec)
     then {
       pp <-  mpp;
       return (blockFill (0, [(0, string "("), (1, pp), (0, string ")")]))
      }
   else
     mpp
  }  

(***
 *** Coq-specific pretty-printing functions
 ***)

(* pretty-print a Coq application *)
op coqApply : Pretty -> Pretty -> Pretty
def coqApply f_pp a_pp =
  blockFill (0, [(0, prConcat [f_pp, string " "]), (2, a_pp)])

(* pretty-print a Coq application, using monads *)
op coqApplyM : Monad Pretty -> Monad Pretty -> Monad Pretty
def coqApplyM mf ma =
  { f_pp <- mf; a_pp <- ma; return (coqApply f_pp a_pp) }

op coqApplyMulti : Pretty -> List Pretty -> Pretty
def coqApplyMulti f args =
  foldl (fn (f', a') -> coqApply f' a') f args

op coqApplyMultiM : Monad Pretty -> List (Monad Pretty) -> Monad Pretty
def coqApplyMultiM mf mas =
  foldl (fn (m1, m2) -> coqApplyM m1 m2) mf mas

(* pretty-print a Coq fun from a pretty-printed variable (either in
    the form "x" or the form "(x:A)") and a pretty-printed body *)
op ppCoqFun : Pretty -> Pretty -> Pretty
def ppCoqFun var_pp body_pp =
  (blockFill
     (0, [(0, string " fun "),
          (2, var_pp),
          (0, string " => "),
          (2, body_pp)]))

(* pretty-print a Coq parameter *)
op ppCoqParam : (String * String * Pretty) -> Pretty
def ppCoqParam (q, id, tp_pp) =
  blockFill (0, [(0, string "Parameter "),
                      (2, string (qidToCoqName (q,id))),
                      (0, string " : "),
                      (2, tp_pp),
                      (0, string ".")])


(* pretty-print a Coq Class *)
op ppCoqClass(className:Pretty, params:Pretty, classSort:Pretty, fieldAlist:List (String * Pretty)): Pretty =
  blockFill
  (0,
   [(0, string "Class "),
    (2, className),
    (4, prConcat [params, string " "]),
    (0, string ": "),
    (2, prConcat [classSort, string " "]),
    (0, string ":= "),
    (2,
     (ppIndentMiddle
        (string "{")
        (prPostSep 0 blockFill (string ";")
           (map (fn (fnm, ftp_pp) ->
                   (blockFill
                      (0, [(0,string fnm), (0, string ":"), (0, string " "), (2,ftp_pp)])))
              fieldAlist))
        (string "}"))
     ),
    (0, string ".")
    ])

op ppCoqOperationalClass(sn, q, id, prev, tp_pp):(Pretty * Option String) =
  let params = (case prev of
                  | None -> string ""
                  | Some q -> string (" `{" ^ q ^ " } ")) in
  let className = prConcat [string sn, string "_", string (qidToCoqName (q,id))] in
  let fieldAList = [(qidToCoqName (q,id), tp_pp)] in
  let doc =  ppCoqClass(className, params, string "Type", fieldAList) in
  (doc, Some (sn ^ "_" ^ id))


(* FIXME: Change this to use ppCoqClass *)
op ppCoqPredicateClass : (String * String * List (String * Pretty)) -> Pretty
def ppCoqPredicateClass (nm, final, fieldAlist) =
  ppCoqClass(string nm, string (" `{" ^ final ^ "} "), string "Prop", fieldAlist)
  

(* pretty-print a Coq definition, which takes in a (pretty-printed)
   Coq type and Coq value of that type *)
op ppCoqDef : (String * Pretty * Pretty) -> Pretty
def ppCoqDef (nm, tp_pp, def_pp) =
  blockFill (0, [(0, string "Program Definition "),
                      (2, string nm),
                      (0, string " : "),
                      (2, tp_pp),
                      (0, string " := "),
                      (2, def_pp),
                      (0, string ".")])

(* pretty-print a Coq definition, which takes in a (pretty-printed)
   Coq type and Coq value of that type *)
op ppCoqPgmDef : (String * Pretty * Pretty) -> Pretty
def ppCoqPgmDef (nm, tp_pp, def_pp) =
  blockFill (0, [(0, string "Program Definition "),
                      (2, string nm),
                      (0, string " : "),
                      (2, tp_pp),
                      (0, string " := "),
                      (2, def_pp),
                      (0, string ".")])

(* pretty-print a Coq definition without a type *)
op ppCoqDefNoT : (String * Pretty) -> Pretty
def ppCoqDefNoT (nm, def_pp) =
  blockFill (0, [(0, string "Definition "),
                      (2, string nm),
                      (0, string " := "),
                      (2, def_pp),
                      (0, string ".")])

(* pretty-print a Coq record type *)
op ppCoqRecordDef : (String * String * List (String * Pretty)) -> Pretty
def ppCoqRecordDef (nm, ctor, fieldAlist) =
  ppIndentMiddle
    (blockFill
       (0,
        [(0, string "Record "),
         (4, string nm),
         (2, string " := "),
         (2, string ctor),
         (2, string " {")]))
    (prLinear 0
       (intersperse
          (string "; ")
          (map (fn (fnm, ftp_pp) ->
                  ppColon (string fnm) ftp_pp) fieldAlist)))
    (string " }.")

(* pretty-print an element of a Coq record type *)
op ppCoqRecordElem : (List (String * Pretty)) -> Pretty
def ppCoqRecordElem (fields) =
  blockFill
    (0,
     [(0, string "{| ")]
     ++
     intersperse
       (2, (string "; "))
       (map (fn (fname, fval_pp) ->
            (2, ppColonEq (string fname) fval_pp)) fields)
     ++
     [(0, string " |}")])

def ppTuple (l : List Pretty) : Pretty =
  ppParens (prBreak 0 (intersperse (string ", ") l))



     
(* pretty-print an element of a Specware record type, which is a tuple
   if the fields are all natural numbers in ascending order from 1 *)
op ppCoqRecordElemOrTuple : (List (String * Pretty)) -> Pretty
def ppCoqRecordElemOrTuple fields =
  if foralli? (fn (i, (fld, _)) -> intToString (i+1) = fld) fields then
    ppTuple (map (fn (_, val) -> val) fields)
  else
    ppCoqRecordElem fields

(* pretty-print a Coq Inductive declaration *)
op ppCoqInductive : (String * String * TyVars * List (Id * Option Pretty)) -> Pretty
def ppCoqInductive (q, id, tyvars, id_tps) =
  let tpName = qidToCoqName (q, id) in
  prLines 0
  ([blockFill
      (0,
       [(0, string "Inductive"),
        (2, string tpName),
        (4, ppParens (ppColon (prBreak 0 (map string tyvars)) (string "Set"))),
        (2, string ":"),
        (4, string "Set"),
        (2, string ":=")
        ])]
   ++
   (map
      (fn (ctor, tp_pp_opt) ->
         blockFill
         (2,
          [(0, string "|"),
           (2, string ctor),
           (2, string ":"),
           (4,
            case tp_pp_opt of
              | Some tp_pp -> ppSeparator "->" tp_pp (string tpName)
              | None -> string tpName)]))
      id_tps)
   ++
   [string "."])


(* pretty-print a Coq module *)
op ppCoqModule : (String * List Pretty) -> Pretty
def ppCoqModule (mod_name, pps) =
  prLines 0
    ([string ("Module " ^ mod_name ^ ".\n")]
     ++ (intersperse (string "") pps)
     ++ [string ("End " ^ mod_name ^ ".\n")])

(* pretty-print a Coq module type *)
op ppCoqModuleType : (String * List Pretty) -> Pretty
def ppCoqModuleType (mod_name, pps) =
  prLines 0
    ([string ("Module Type " ^ mod_name ^ ".\n")]
     ++ (intersperse (string "") pps)
     ++ [string ("End " ^ mod_name ^ ".\n")])


(***
 *** pretty-printers for term constructs (everything but specs)
 ***)

op unhandled : String * String * String -> Monad Pretty
def unhandled (fun, construct, obj_str) =
  % err (fun ^ ": unhandled construct " ^ construct ^ " in: " ^ obj_str)
  let _ = System.writeLine (fun ^ ": unhandled construct " ^ construct ^ " in: " ^ obj_str) in
  return (string ("##unknown construct " ^ construct ^ "##"))

def unhandledTerm (str : String) (tm : MSTerm) : Monad Pretty =
  unhandled ("ppTerm", str, anyToString tm)

(* pretty-print an MSTerm into a Coq term *)
op ppTerm : MSTerm -> Monad Pretty
def ppTerm tm =
  case tm of
    | t as Apply (f, a, _) ->
         let (fun,args) = unpackApplication t 
         in ppApplication (fun, args)
    | ApplyN (ts, _) -> unhandledTerm "ApplyN" tm
    | Record (elems, _) ->
      { elems_pp
         <- mapM (fn (id, tm) ->
                    { tm_pp <- ppTerm tm; return (id, tm_pp) }) elems;
        return (ppCoqRecordElemOrTuple elems_pp) }
    | Bind (Forall, vars, body, _) ->
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        ppForallTerm vars_pp body_pp
      }
    | Bind (Exists, vars, body, _) ->
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        ppExistsTerm vars_pp body_pp }
    | Bind (Exists1, vars, body, _) ->
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        return (ppExistsB1 vars_pp body_pp) }
    | The (var, body, _) ->
      { body_pp <- ppTerm body;
        var_pp <- ppVarBinding var;
        return (coqApply (string "the") (ppCoqFun var_pp body_pp)) }
    | Let (bindings, body, _) -> unhandledTerm "Let" tm
    | LetRec (bindings, body, _) -> unhandledTerm "LetRec" tm
    | Var ((str, tp), _) ->
      (* FIXME: add type annotation? *)
      return (string str)
    | Fun (f, tp, _) ->
      (* FIXME: add type annotation? *)
      ppFun (f, tp)
    | Lambda ([(VarPat (v, _), Fun (Bool true, Boolean _, _), body)], _) ->
      (* the above matches simple lambdas with no pattern-matching *)
      { var_pp <- ppVarBinding v ;
        body_pp <- ppTerm body ;
        return
         (ppParens (ppCoqFun var_pp body_pp)) }
    | Lambda (matches, _) ->
      { var_pp <- ppFreshVar;
        body_pp <- ppCaseExpr var_pp matches;
        return (ppParens (ppCoqFun var_pp body_pp)) }
    | IfThenElse (t1, t2, t3, _) ->
      { t1_pp <- ppTerm t1 ;
        t2_pp <- ppTerm t2 ;
        t3_pp <- ppTerm t3 ;
        return 
         (ppParens
            (blockFill (0, [(0, string "if"),
                                 (2, t1_pp),
                                 (0, string "then"),
                                 (2, t2_pp),
                                 (0, string "else"),
                                 (2, t3_pp)]))) }
    | Seq (ts, _) -> unhandledTerm "Seq" tm
    | TypedTerm (tm, tp, _) ->
      { tm_pp <- ppTerm tm ;
        tp_pp <- ppType tp ;
        return (ppParens (ppColon tm_pp tp_pp)) }
    | Transform (transforms, _) -> unhandledTerm "Transform" tm
    | Pi (tyvars, body, _) ->
      let tyvars_pp = map (fn (pp : Pretty) -> (0, pp)) (ppTyVarBindings tyvars) in
      { body_pp <- ppTerm body;
        return (ppCoqFun (blockFill (0, tyvars_pp)) body_pp) }
    | And (ts, _) -> unhandledTerm "And" tm
    | Any _ -> unhandledTerm "Any" tm


(* pretty-print an application to n-arguments. *)
op ppApplication(f:MSTerm, args:List MSTerm):Monad Pretty =
{
   fixity <- termFixity f;
   fDoc <- ppTerm f;
   case (fixity, args) of
     | (Infix (assoc, prec), [ Record ([("1",tm1), ("2",tm2)], _) ]) ->
        {
         doc1 <- withPrec prec (ppTerm tm1);
         doc2 <- withPrec prec (ppTerm tm2);
         let doc = blockFill (0,[(0,doc1), (0,fDoc), (0,doc2)]) in
         ppPrecParens prec (return doc)
        }
     | _ -> ppPrecParens appPrecedence (withPrec appPrecedence (coqApplyMultiM (return fDoc) (map ppTerm args)))
}


(* pretty-print a pattern-match over a scrutinee, where the latter has
   already been pretty-printed *)
(* NOTE: we do not handle guards *)
(* FIXME: print the whole term being printed when reporting errors *)
op ppCaseExpr : Pretty -> MSMatch -> Monad Pretty
def ppCaseExpr scrut_pp pats =
  { pat_pps <- mapM ppBranch pats;
    return
     (ppIndentMiddle
        (blockFill
           (0, [(0, string "match "), (4, scrut_pp), (1, string " with")]))
        (prLinear 0 pat_pps)
        (string "end")) }

(* pretty-print a pattern-matching branch, i.e., a pattern + body *)
op ppBranch : (MSPattern * MSTerm * MSTerm) -> Monad Pretty
def ppBranch (pat, gd, body) =
  case gd of
    | Fun (Bool true, Boolean _, _) ->
      { pat_pp <- ppPat pat;
        body_pp <- ppTerm body;
        retFill
         [(0, string "| "), (2, pat_pp), (1, string " => "), (4, body_pp)]}
    | _ ->
      err "ppBranch: cannot handle pattern guards!"

op unhandledPat (str : String) (p : MSPattern) : Monad Pretty =
  unhandled ("ppPat", str, anyToString p)

(* pretty-print the actual pattern itself *)
op ppPat : MSPattern -> Monad Pretty
def ppPat pat =
  case pat of
    | AliasPat (p, VarPat ((v, _), _), _) ->
      { p_pp <- ppPat p;
        retFill [(0, ppParens p_pp), (0, string "as"), (0, string v)] }
    | VarPat ((v, _), _) -> retString v
    | EmbedPat (Qualified(_, ctor), None, _, _) -> retString ctor
    | EmbedPat (Qualified(_, ctor), Some arg_pat, _, _) ->
      { arg_pp <- ppPat arg_pat;
        retFill [(0, string ctor), (2, arg_pp)] }
    | RecordPat (id_pats, _) ->
      { fld_pats_pp
         <- mapM (fn (fname, fpat) ->
                    { fpat_pp <- ppPat fpat;
                     return (fname, fpat_pp) }) id_pats;
        return
          (ppCoqRecordElemOrTuple fld_pats_pp) }
    | WildPat (_, _) -> retString "_"
    | BoolPat (b, _) ->
         if b then retString "true" else retString "false"
    | NatPat (n, _) -> retString (intToString n)
    | StringPat (str, _) -> retString ("\"" ^ str ^ "\"%string")
    | CharPat (c, _) -> retString ("\"" ^ implode [c] ^ "\"%char")
    | QuotientPat (_, _, _, _) ->
         unhandledPat "QuotientPat" pat
    | RestrictedPat (_, _, _) ->
         unhandledPat "RestrictedPat" pat
    | TypedPat (pat', _, _) -> ppPat pat'


op ppVarBinding : MSVar -> Monad Pretty
def ppVarBinding (str, tp) =
  { tp_pp <- ppType tp ;
    return (ppParens (ppColon (string str) tp_pp)) }

op ppVarBindings (vs : List MSVar) : Monad Pretty =
  { pps <- mapM ppVarBinding vs ;
    retFill (List.map (fn pp -> (0, pp)) pps) }

op unhandledFun (str : String) (f : MSFun) : Monad Pretty =
  unhandled ("ppFun", str, anyToString f)


op termFixity(f:MSTerm):Monad Fixity =
  case f of
  | Fun (f, tp, _) -> funFixity f
  | _ -> return Nonfix


(* Given a function, return its fixity. For boolean operations, the
   result will differ depending on whether we're printing in Prop or
   Boolean context. Prop connectives are printed to match coq's
   syntax, while bool connections are infix.
 *)
op funFixity(f:MSFun):Monad Fixity =
  case f of
    | Not -> ifProp (return Nonfix) (return Nonfix)
    | And -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | Or -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | Implies -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | Iff -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | Equals -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | NotEquals -> ifProp (return (Infix (Left, 5))) (return Nonfix)
    | _  -> return Nonfix

op appPrecedence:Nat = 10      
  
  
op ppFun : MSFun * MSType -> Monad Pretty
def ppFun (f, tp) =
  case f of
    | Not -> ifProp (retString " ~") (retString "notb")
    | And -> ifProp (retString " /\\ ") (retString "andb_pair")
    | Or -> ifProp (retString " \\/ ") (retString "orb_pair")
    | Implies -> ifProp (retString " -> ") (retString "implb_pair")
    | Iff -> ifProp (retString " <-> ") (retString "iffb_pair")
    | Equals -> ifProp (retString " = ") (retString "dec_eq_b_pair")
    | NotEquals -> ifProp (retString " != ") (retString "dec_neq_b_pair")

    | Quotient tp -> unhandledFun "Quotient" f
    | Choose tp -> unhandledFun "Choose" f
    | Restrict -> unhandledFun "Restrict" f
    | Relax -> unhandledFun "Relax" f

    | PQuotient tp -> unhandledFun "PQuotient" f
    | PChoose tp -> unhandledFun "PChoose" f

    | Op (Qualified qid, fixity) -> return (ppQid qid)
    | Project id -> unhandledFun "Project" f
    | RecordMerge -> unhandledFun "RecordMerge" f
    | Embed (Qualified(_, id), flag) -> retString id
    | Embedded (Qualified(_, id)) -> unhandledFun "Embedded" f
    | Select (Qualified(_, id)) -> unhandledFun "Select" f
    | Nat n -> retString (show n)
    | Char c -> retString ("\"" ^ implode [c] ^ "\"%char")
    | String str -> retString ("\"" ^ str ^ "\"%string")
    | Bool b -> retString (show b)

    | OneName (id, fixity) -> unhandledFun "OneName" f
    | TwoNames (id1, id2, fixity) -> unhandledFun "TwoNames" f


def unhandledType (construct : String) (tp : MSType): Monad Pretty =
  unhandled ("ppType", construct, anyToString tp)

op ppTyVarBinding : TyVar -> Pretty
def ppTyVarBinding str =
  ppParens (ppColon (string str) (string "Set"))

op ppTyVarBindings : TyVars -> List Pretty
def ppTyVarBindings tyvars =
  map ppTyVarBinding tyvars


op ppForallTerm(vs_pp : List Pretty) (body_pp : Pretty) : Monad Pretty =
  ifProp (return (ppForall vs_pp body_pp)) (return (ppForallB vs_pp body_pp))


(* pretty-print a forall type, assuming all the variables have been
   pretty-printed as "(name : tp)" and that body_pp is a
   pretty-printed Coq type *)
def ppForall (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    blockFill
    (0, [(0, string "forall")]
       ++ [(2, prLinear 2 vs_pp)]
       ++ [(2, string ","), (4, body_pp)])

(* pretty-print a forall proposition converted to a bool, assuming all
   the variables have been pretty-printed as "(name : tp)" and that
   body_pp is a pretty-printed Coq term of type bool *)
def ppForallB (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    (blockFill
       (0, [(0, string "forallB")]
          ++ (map (fn (v_pp : Pretty) -> (2, v_pp)) vs_pp)
          ++ [(0, string ","), (0, body_pp)]))

(* Same as ppForall, but with existential terms *)
op ppExistsTerm(vs_pp : List Pretty) (body_pp : Pretty) : Monad Pretty =
  ifProp (return (ppExists vs_pp body_pp)) (return (ppExistsB vs_pp body_pp))

(* pretty-print an exists proposition, assuming all the variables have
   been pretty-printed as "(name : tp)" and that body_pp is a
   pretty-printed Coq term of type Prop *)
def ppExists (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    (blockFill
       (0, [(0, string "exists")]
          ++ (map (fn (v_pp : Pretty) -> (2, v_pp)) vs_pp)
          ++ [(0, string ","), (0, body_pp)]))

(* pretty-print an exists proposition converted to a bool, assuming
   all the variables have been pretty-printed as "(name : tp)" and
   that body_pp is a pretty-printed Coq term of type bool *)
def ppExistsB (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    (blockFill
       (0, [(0, string "existsB")]
          ++ (map (fn (v_pp : Pretty) -> (2, v_pp)) vs_pp)
          ++ [(0, string ","), (0, body_pp)]))

(* pretty-print an exists! proposition converted to a bool, assuming
   all the variables have been pretty-printed as "(name : tp)" and
   that body_pp is a pretty-printed Coq term of type bool *)
def ppExistsB1 (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    (blockFill
       (0, [(0, string "existsB!")]
          ++ (map (fn (v_pp : Pretty) -> (2, v_pp)) vs_pp)
          ++ [(0, string ","), (0, body_pp)]))


(* Pretty-print a Specware type to a Coq type *)
op ppType : MSType -> Monad Pretty
def ppType tp =
  case tp of
    | Arrow (t1, t2, _) ->
      { t1_pp <- ppType t1 ;
        t2_pp <- ppType t2 ;
        retFill [(0, t1_pp), (0, string "->"), (0, t2_pp)] }
  | Product (id_tps, _) ->
    let def helper i (id_tps') =
      case id_tps' of
        | [] -> err ("Unexpected empty type list in Product type: "
                       ^ anyToString tp)
        | [(proj,tp)] ->
          if proj = intToString i then ppType tp else
            err ("Unexpected projection function " ^ proj
                   ^ " in product type: " ^ anyToString tp)
        | (proj,tp1)::rest ->
          if proj = intToString i then
            coqApplyM
              (coqApplyM (return (string "prod")) (ppType tp1))
              (helper (i+1) rest)
          else
            err ("Unexpected projection function " ^ proj
                   ^ " in product type: " ^ anyToString tp)
    in
    helper 1 id_tps
  | CoProduct (id_tps, _) -> unhandledType "CoProduct" tp
  | Quotient (base_tp, tm, _) -> unhandledType "Quotient" tp
  | Subtype (base_tp, pred, _) ->
    { base_tp_pp <- ppType base_tp;
      pred_pp <- ppTerm pred;
      return
       (ppCurlies
          (ppSeparator "|"
             (ppColon (string "x") base_tp_pp)
             (coqApply pred_pp (string "x")))) }
  | Base (Qualified qid, params, _) ->
    coqApplyMultiM (return (string (qidToCoqName qid)))
      (map ppType params)
  | Boolean _ -> retString "bool"
  | TyVar (str, _) -> retString str
  | MetaTyVar (_, _) -> unhandledType "MetaTyVar" tp
  | Pi (tyvars, body, _) ->
    { body_pp <- ppType body ;
      return (ppForall (ppTyVarBindings tyvars) body_pp) }
  | And (ts, _) -> unhandledType "And" tp
  | Any _ -> unhandledType "Any" tp

(* remove all leading Pis, returning a pair of (tyvars, body) *)
def unzipPis (tp : MSType) : TyVars * MSType =
  case tp of
    | Pi (tyvars, body, _) ->
      let (tyvars', body') = unzipPis body in
      (tyvars ++ tyvars', body')
    | _ -> ([], tp)

(* pretty-print a type definition, where we know the name of the type;
   this is the only way we can, for example, pretty-print coproduct
   types (at least, for now...). Note that by "definition" we also
   include a Coq Parameter declaration when the type is "Any" *)
op ppTypeDef : (String * String * MSType) -> Monad Pretty
def ppTypeDef (q,id, tp) =
  let (tyvars, body) = unzipPis tp in
  case body of
    | Any _ -> return (ppCoqParam (q, id, string "Set"))
    | CoProduct (id_tps, _) ->
      { id_tps_pp
         <- (mapM
               (fn (Qualified(_, ctor), tp_opt) ->
                  case tp_opt of
                    | None -> return (ctor, None)
                    | Some tp ->
                      { tp_pp <- ppType tp ; return (ctor, Some tp_pp) })
               id_tps) ;
        return (ppCoqInductive (q, id, tyvars, id_tps_pp)) }
    | _ ->
         { tp_pp <- ppType tp ;
           return (ppCoqPgmDef (qidToCoqName (q, id), string "Set", tp_pp)) }

(***
 *** importing a spec
 ***)

(* This does two things:

   1. Load the required Coq file using a Coq "Require"; and

   2. If the current spec adds definitions 

*)

op importSpec (cur_spec : Spec) (ruid : RelativeUID) : Monad (Option Pretty) =
  {
   appendTopPretty (string ("Require " ^ relUIDToCoqNameString ruid));
   return (Some (string ("Include " ^ relUIDToCoqNameString ruid ^ ".Spec.")))
  }  

(***
 *** pretty-printer for specs
 ***)

(* The basic idea is that a spec is translated into two Coq
   type-classes, one for the types and ops of the spec and one for the
   axioms and proofs. We call the first one the "ops type-class" for
   the spec; the second is just referred to as the type-class for the
   spec, since it contains the ops type-class as well, but we
   sometimes call it the "axioms type-class" to be more specific.  If
   a spec is named Foo, then its ops type-class is named "Foo__ops",
   and its axioms type-class is called "Foo".

   The ops type-class is defined as a sequence of operational
   type-classes (type-classes with a single element), one for each
   type, op, or import statement of the spec. Each of these imports
   the previous operational type-class, using the Coq backtick
   notation `{Class} in the parameters of the type-class. For ops, the
   type-class contains a single field whose type is the pretty-printed
   Coq version of the Specware type of the op; for types, it contains
   a single field of type Set; and for imports, the type-class
   contains no fields, but has an additional import, again using the
   `{Class} notation, of the operational type-class for the imported
   spec. For example, the following is a spec and its sequence of
   definitions that give its ops type-class:

   Monoid = spec
     type A
     op zero : A
     op plus (x:A) (y:A) : A
     axiom unit_left is fa (x) plus zero x = x
     axiom unit_right is fa (x) plus x zero = x
     axiom assoc is fa (x,y,z) plus (plus x y) z = plus x (plus y z)
   end-spec

   -->

   Class Monoid__A : Type := { A : Set }.
   Class Monoid__zero `{Monoid__A} : Type := { zero : A }.
   Class Monoid__plus `{Monoid__zero} : Type := { plus : A -> A -> A }.
   Class Monoid__ops `{Monoid__plus} : Type.

   The axioms type-class is a single type-class of sort Prop
   containing a field for each of the axioms of the spec. It imports
   the ops type-class, so that it can refer to the ops and types of
   the spec. For example, the Monoid spec above would be translated to
   the following type-class:

   Class Monoid `{Monoid__ops} : Prop :=
   {
     unit_left : forall x, plus zero x = x;
     unit_right : forall x, plus x zero = x;
     assoc : forall x y z, plus (plus x y) z = plus x (plus y z)
   }.

   FIXME HERE: how to handle imports

*)

def tp_elem_name = "__type"
def pinst_elem_name = "__pinst"



(* pretty-print the (operational) parts of a spec as a sequence of unbundled classes *)
op ppOperationalSpecElem : Spec -> (SpecElement * Option String) -> Monad (Option (Pretty * Option String))
def ppOperationalSpecElem s (elem, prev) = {
   sn <- getSpecName
                                            ;
   let def ppTypeSpecElem (q, id) : Monad (Option (Pretty * Option String)) =
    (case findAQualifierMap (s.types, q, id) of
       | Some tp_info ->
         if typeIsDefined? tp_info.dfn then
           { tp_pp <- ppType tp_info.dfn;
            let next = Some (sn ^ "_" ^ id) in                                                          
             return
              (Some
                 (ppCoqPgmDef (qidToCoqName (q, id), string "Set", tp_pp), next)) }
         else
           return (Some (ppCoqOperationalClass (sn, q, id, prev, string "Set")))
       | None -> err ("ppOpSpecElem: could not find type " ^ id ^ " in spec!"))
  in
    let def ppOpSpecElem (q, id) : Monad (Option (Pretty * Option String)) =
     (case findAQualifierMap (s.ops, q, id) of
       | Some op_info ->
         if termIsDefined? op_info.dfn then
           { def_pp <- ppTerm op_info.dfn;
             tp_pp <- ppType (termType op_info.dfn);
            return (Some (ppCoqPgmDef (qidToCoqName (q, id), tp_pp, def_pp),prev)) }
         else
           { tp_pp <- ppType (termType op_info.dfn);
             return (Some (ppCoqOperationalClass (sn, q, id, prev,  tp_pp))) }
       | None -> err ("ppOpSpecElem: could not find op " ^ id ^ " in spec!"))
  in
  case elem of
   % | Import ((UnitId ruid, _), _, _, _) -> importSpec s ruid
   | Type (Qualified qid, _) -> ppTypeSpecElem qid
   | TypeDef (Qualified qid, _) -> ppTypeSpecElem qid
   | Op (Qualified qid, _, _) -> ppOpSpecElem qid
   | OpDef (Qualified qid, _, _, _) -> ppOpSpecElem qid
   | Comment (str, _) ->
     (* FIXME *)
     return (Some (string ("(* Comment: " ^ str ^ " *)"), prev))
   | Pragma (str1, str2, str3, _) ->
     (* FIXME *)
     return
       (Some
          (string ("(* pragma: (" ^ str1 ^ "," ^ str2 ^ "," ^ str3 ^ ") *)"), prev))
   % | Property (Axiom, Qualified (q, id), tyvars, tm, _) -> return None
     % (* FIXME: search for a proof *)
     % { tm_pp <- ppTerm tm;
     %   return
     %    (Some
     %       (ppCoqParam
     %          (q, id,
     %           ppForall (ppTyVarBindings tyvars) tm_pp))) }
   | _ -> return None
 }

op ppPredicateSpecElem : Spec -> SpecElement -> Monad (Option (String * Pretty))
def ppPredicateSpecElem s elem = {
   sn <- getSpecName;
   case elem of
     | Property (Axiom, Qualified (q, id), tyvars, tm, _) ->
       withProp 
     ({ tm_pp <- ppTerm tm;
       return
        (Some
           (id, ppForall (ppTyVarBindings tyvars) tm_pp)) })
   | _ -> return None
 }

  
  
(* top-level entry point for pretty-printing specs *)
op ppSpec : CoqModName -> Spec -> Monad Pretty
def ppSpec coq_mod s =
  
  (* first get the spec elements, ensuring that we don't have both a
     decl and def of the same type or op *)
  let def spec_elem_same_qid elem1 elem2 =
    case (elem1, elem2) of
      | (Op (qid1, _, _), Op (qid2, _, _)) -> qid1 = qid2
      | (Op (qid1, _, _), OpDef (qid2, _, _, _)) -> qid1 = qid2
      | (OpDef (qid1, _, _, _), Op (qid2, _, _)) -> qid1 = qid2
      | (OpDef (qid1, _, _, _), OpDef (qid2, _, _, _)) -> qid1 = qid2
      | (Type (qid1, _), Type (qid2, _)) -> qid1 = qid2
      | _ -> false
  in
  let spec_elems = removeDups spec_elem_same_qid s.elements in

  {

   appendTopPretty (string ("Add LoadPath \"$SPECWARE4/Provers/ToCoq/\"."));
   appendTopPretty (string ("Require Import MetaSlang."));

   (* next, pretty-print the operational spec elements *)
   (spec_operational_elems_pp, final) <- filterFoldM (ppOperationalSpecElem s) None spec_elems;


   sn <- getSpecName;
   last_class_name <- return (case final of
                         | None -> "FIXME: Should have a class name here."
                         | Some nm -> nm);

   (* Create a 'terminal' class called 'sn_ops' -- it doesn't seem that we can define class aliases *)
   op_class_name <- return (sn ^ "_ops");
   ops_class <- return (ppCoqClass(string op_class_name, string (" `{" ^ last_class_name ^ "} "), string "Type", [(sn ^ "_triv", string "true")]));

   (* pretty-print the elements of the predicate class *) 
   spec_predicate_elems_pp <- filterMapM (ppPredicateSpecElem s) spec_elems;
   pred_class <- return (ppCoqPredicateClass (sn, op_class_name, spec_predicate_elems_pp));
   
   (* Now, build the Coq module! *)
   return (ppCoqModule ("Spec", spec_operational_elems_pp ++ [ops_class, pred_class]))
  }


(***
 *** the top-level entrypoint
 **)

(* adapted from IsaPrinter.sw *)
op printUIDToCoqFile : String -> String
def printUIDToCoqFile spath =

  case specPathToCoqModule spath of
    | None -> "Error: Malformed spec path: " ^ spath
    | Some mod_path ->
      (case Specware.evaluateUnitId spath of
         | None -> "Error: Unknown UID " ^ spath
         | Some (Spec s) ->
          (case specPathToRelUID spath of
             | None -> "Error: Could not convert spec path " ^ spath ^ " to Relative UUID"
             | Some relpath ->
                 let context = mkContext (relUIDToString relpath) in
                 let filepath =
                   if head mod_path = "Specware" then tail mod_path
                   else mod_path
                 in
                 let filename = concatenate #/ filepath ^ ".v" in
                 let _ = ensureDirectoriesExist filename in
                 let m = ppSpec mod_path s in
                (case writingToFile (filename, context, m) of
                  | None -> filename
                  | Some err_str -> "Error: " ^ err_str)))
      | _ -> "Error: currently only support converting Specs to Coq"

end-spec
