
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

(* add an element in between every existing element of a list *)
op [a] intersperse (x : a) (l : List a) : List a =
  case l of
    | [] -> []
    | y::[] -> [y]
    | y::l' -> y :: x :: intersperse x l'

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
    | _ -> true


(***
 *** The monad for translating to Coq
 ***)

(* Translation to Coq takes place in a monad, which is a state monad
   for a "current context" combined with an error monad *)

type Context =
  {
   freshNatCounter : Nat
   }

def mkContext () =
  { freshNatCounter = 0 }

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
    () <- putCtx { freshNatCounter = ctx.freshNatCounter + 1 };
    return ctx.freshNatCounter }

op ppFreshVar : Monad Pretty
def ppFreshVar =
  { var_nat <- freshNat;
    return (string ("__fresh_" ^ intToString var_nat)) }

(* Run operation for our monad: use a computation to write a Pretty to
   a file, returning an error string on error *)
op writingToFile : String * Context * Monad Pretty -> Option String
def writingToFile (filename, ctx, m) =
  case m ctx of
    | Right (_, pp) -> (toFile (filename, format (formatWidth, pp)) ; None)
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


(***
 *** Coq-specific pretty-printing functions
 ***)

(* pretty-print a Coq application *)
op coqApply : Pretty -> Pretty -> Pretty
def coqApply f_pp a_pp =
  blockFill (0, [(0, ppParens f_pp), (2, ppParens a_pp)])

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
    | Apply (f, a, _) -> coqApplyM (ppTerm f) (ppTerm a)
    | ApplyN (ts, _) -> unhandledTerm "ApplyN" tm
    | Record (elems, _) ->
      { elems_pp
         <- mapM (fn (id, tm) ->
                    { tm_pp <- ppTerm tm; return (id, tm_pp) }) elems;
        return (ppCoqRecordElemOrTuple elems_pp) }
    | Bind (Forall, vars, body, _) ->
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        return (ppForallB vars_pp body_pp) }
    | Bind (Exists, vars, body, _) ->
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        return (ppExistsB vars_pp body_pp) }
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
    | EmbedPat (ctor, None, _, _) -> retString ctor
    | EmbedPat (ctor, Some arg_pat, _, _) ->
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
    | QuotientPat (_, _, _) ->
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

op ppFun : MSFun * MSType -> Monad Pretty
def ppFun (f, tp) =
  case f of
    | Not -> retString "negb"
    | And -> retString "andb_pair"
    | Or -> retString "orb_pair"
    | Implies -> retString "implb_pair"
    | Iff -> retString "iffb_pair"
    | Equals -> retString "dec_eq_b_pair"
    | NotEquals -> retString "dec_neq_b_pair"

    | Quotient tp -> unhandledFun "Quotient" f
    | Choose tp -> unhandledFun "Choose" f
    | Restrict -> unhandledFun "Restrict" f
    | Relax -> unhandledFun "Relax" f

    | PQuotient tp -> unhandledFun "PQuotient" f
    | PChoose tp -> unhandledFun "PChoose" f

    | Op (Qualified qid, fixity) -> return (ppQid qid)
    | Project id -> unhandledFun "Project" f
    | RecordMerge -> unhandledFun "RecordMerge" f
    | Embed (id, flag) -> retString id
    | Embedded id -> unhandledFun "Embedded" f
    | Select id -> unhandledFun "Select" f
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

(* pretty-print a forall type, assuming all the variables have been
   pretty-printed as "(name : tp)" and that body_pp is a
   pretty-printed Coq type *)
def ppForall (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    blockFill
    (0, [(0, string "forall")]
       ++ (map (fn (v_pp : Pretty) -> (2, v_pp)) vs_pp)
       ++ [(0, string ","), (0, body_pp)])

(* pretty-print a forall proposition converted to a bool, assuming all
   the variables have been pretty-printed as "(name : tp)" and that
   body_pp is a pretty-printed Coq term of type bool *)
def ppForallB (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  if vs_pp = [] then body_pp else
    (blockFill
       (0, [(0, string "forallB")]
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
               (fn (ctor, tp_opt) ->
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
 *** pretty-printer for specs
 ***)

(* The basic idea is that a spec is translated into two Coq objects:

    1. A record type, whose elements are the types (in Set),
    operators, and proofs of the axioms declared in the spec; AND

    2. A "partial instance" of this record type, i.e., a function that
    takes in all the "holes" of a spec -- the undefined types,
    operators, and proofs -- and builds an element of the given record
    type.

    Note that a Specware "axiom" is represented in a way similar to
    the types and ops that are declared but not defined, as a proof
    element of the record type that is not defined in the partial
    instance, i.e., that is a "hole".

    To make the above easier to work with in Coq, these are defined in
    a Coq module, of the same name as the spec, that contains:

    * A Coq parameter for each "hole" in the spec;

    * A Coq definition for each type, op, and proof (given with
      specware pragmas) in the spec;

    * A Coq Export statement for each imported spec (FIXME: this is
      not yet supported); and

    * A sub-module "Meta" that contains:

      - An element "__type" equal to the record type of the spec;

      - An element "__pinst" that gives the partial instance, i.e.,
         where each type, op, and proof is bound to either its
         parameter or its definition given in the module.

*)

def tp_elem_name = "__type"
def pinst_elem_name = "__pinst"


(* pretty-print a spec element as an element of a Coq module *)
op ppSpecElem : Spec -> SpecElement -> Monad (Option Pretty)
def ppSpecElem s elem =
  let def ppTypeSpecElem (q, id) : Monad (Option Pretty) =
    (case findAQualifierMap (s.types, q, id) of
       | Some tp_info ->
         if typeIsDefined? tp_info.dfn then
           { tp_pp <- ppType tp_info.dfn;
            return
              (Some
                 (ppCoqPgmDef (qidToCoqName (q, id), string "Set", tp_pp))) }
         else
           return (Some (ppCoqParam (q, id, string "Set")))
       | None -> err ("ppSpecElem: could not find type " ^ id ^ " in spec!"))
  in
  let def ppOpSpecElem (q, id) : Monad (Option Pretty) =
    (case findAQualifierMap (s.ops, q, id) of
       | Some op_info ->
         if termIsDefined? op_info.dfn then
           { def_pp <- ppTerm op_info.dfn;
             tp_pp <- ppType (termType op_info.dfn);
            return (Some (ppCoqPgmDef (qidToCoqName (q, id), tp_pp, def_pp))) }
         else
           { tp_pp <- ppType (termType op_info.dfn);
             return (Some (ppCoqParam (q, id, tp_pp))) }
       | None -> err ("ppSpecElem: could not find op " ^ id ^ " in spec!"))
  in
  case elem of
   | Import ((UnitId ruid, _), _, _, _) ->
     return
     (Some
        (string ("Require Import " ^ relUIDToCoqNameString ruid ^ ".")))
   | Type (Qualified qid, _) -> ppTypeSpecElem qid
   | TypeDef (Qualified qid, _) -> ppTypeSpecElem qid
   | Op (Qualified qid, _, _) -> ppOpSpecElem qid
   | OpDef (Qualified qid, _, _, _) -> ppOpSpecElem qid
   | Property (Axiom, Qualified (q, id), tyvars, tm, _) ->
     (* FIXME: search for a proof *)
     { tm_pp <- ppTerm tm;
       return
        (Some
           (ppCoqParam
              (q, id,
               ppForall (ppTyVarBindings tyvars) tm_pp))) }
   | Property prop -> (* FIXME *) return (Some (string "(* property *)"))
   | Comment (str, _) ->
     (* FIXME *)
     return (Some (string ("(* Comment: " ^ str ^ " *)")))
   | Pragma (str1, str2, str3, _) ->
     (* FIXME *)
     return
       (Some
          (string ("(* pragma: (" ^ str1 ^ "," ^ str2 ^ "," ^ str3 ^ ") *)")))


(* return a tuple of a pretty-printed (name, type, value) for a spec
   element as an element of a Coq record. The "value" here for
   types, ops, and axioms is just the name of the variable in the
   current module (introduced by Definition or Parameter)
   corresponding to the particular element; for imports, it is
   the "__pinst" value for the module being imported *)
op ppSpecElemInRecord
  : Spec -> SpecElement -> Monad (Option (String * Pretty * Pretty))
def ppSpecElemInRecord s elem =
  let def opHelper (q, id) =
    (case findAQualifierMap (s.ops, q, id) of
       | Some op_info ->
         { tp_pp <- ppType (termType op_info.dfn);
           return (Some ("__" ^ qidToCoqName (q, id), tp_pp, ppQid (q, id))) }
       | None -> err ("ppSpecElem: could not find op " ^ id ^ " in spec!"))  in
  case elem of
   | Import ((UnitId ruid, _), _, _, _) ->
     (* for an import,  *)
     let modName = relUIDToCoqModuleName ruid in
     let metaModStr = coqModNameToString (coqModNameAddMeta modName) in
     let modField = last modName in
     (* README: we are using the last element of the module name as
        the name of the field in the __pinst record. Hopefully this
        will not cause name clashes. If it does, maybe we can allow
        user control with pragmas? *)
     return
     (Some
        (modField,
         string (metaModStr ^ "." ^ tp_elem_name),
         string (metaModStr ^ "." ^ pinst_elem_name)))
   | Type (Qualified qid, _) ->
     return (Some ("__" ^ qidToCoqName qid, string "Set", ppQid qid))
   | TypeDef (Qualified qid, _) ->
     return (Some ("__" ^ qidToCoqName qid, string "Set", ppQid qid))
   | Op (Qualified qid, _, _) -> opHelper qid
   | OpDef (Qualified qid, _, _, _) -> opHelper qid
   | Property (Axiom, Qualified qid, tyvars, tm, _) ->
     (* FIXME: search for a proof *)
     { tm_pp <- ppTerm tm;
       return
        (Some
           ("__" ^ qidToCoqName qid,
            ppForall (ppTyVarBindings tyvars) tm_pp,
            ppQid qid)) }
   | Property prop -> (* FIXME *) return None
   | Comment (str, _) -> return None
   | Pragma (str1, str2, str3, _) ->
     (* FIXME *)
     return None


(* FIXME HERE: use "Variable" instead of "Parameter"; add Sections
   inside our modules *)

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
   (* next, pretty-print the spec elements *)
   spec_elems_pp <- filterMapM (ppSpecElem s) spec_elems;

   (* pretty-print spec elems to Coq record elems *)
   spec_record_elems_pp <- filterMapM (ppSpecElemInRecord s) spec_elems;

   (* Now, build the Coq module! *)
   return
   (
    prLines 0
    (intersperse (string "")
       (spec_elems_pp
          ++
          (* build the "Meta" module *)
          [ppCoqModule
             (meta_mod_name,
              [
               (* build the "__type" component *)
               ppCoqRecordDef
               (tp_elem_name, "mk" ^ tp_elem_name,
                map (fn (nm, tp_pp, _) -> (nm, tp_pp)) spec_record_elems_pp)
               ,

               (* build the "__pinst" component *)
               ppCoqDefNoT
                 (pinst_elem_name,
                  ppCoqRecordElem
                    (map (fn (nm, _, val_pp) -> (nm, val_pp)) spec_record_elems_pp))
               ])]
          ))
    )}


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
           let context = mkContext () in
           let filepath =
             if head mod_path = "Specware" then tail mod_path
             else mod_path
           in
           let filename = concatenate #/ filepath ^ ".v" in
           let _ = ensureDirectoriesExist filename in
           let m = ppSpec mod_path s in
           (case writingToFile (filename, context, m) of
              | None -> filename
              | Some err_str -> "Error: " ^ err_str))
    | _ -> "Error: currently only support converting Specs to Coq"

end-spec
