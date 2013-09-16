
CoqTermPrinter qualifying spec

import /Library/PrettyPrinter/BjornerEspinosa
import /Library/Structures/Data/Monad
import /Library/Base/List

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

(* declare this here so we don't have to import Bootstrap above *)
op  Specware.evaluateUnitId: String -> Option Value


(***
 *** converting Specware names to Coq names
 ***)

(* muck around with Specware internal state to get a name for a Value;
   code taken from IsaPrinter.sw *)
op uidForValue: Value -> Option UnitId
def uidForValue val =
  case MonadicStateInternal.readGlobalVar "GlobalContext" of
    | None -> None
    | Some global_context -> findUnitIdForUnit(val, global_context)

def uidToCoqName (uid : UnitId) =
  foldr (fn (str, rest) -> str ^ "__" ^ rest) "" uid.path
  ^ (case uid.hashSuffix of
       | Some suffix -> "__" ^ suffix
       | None -> "")

def qidToCoqName (q, id) =
  if q = "" then id else q ^ "." ^ id

def valueToCoqName v =
  case uidForValue v of
    | Some uid -> Some (uidToCoqName uid)
    | None -> None

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
    | _ -> true


(***
 *** The monad for translating to Coq
 ***)

(* Translation to Coq takes place in a monad, which (so far!) is just
   a reader monad for Contexts combined with an error monad *)

type Context = { }

type Monad a = Context -> Either (String, a)

op monadBind: [a,b] (Monad a) * (a -> Monad b) -> Monad b
def monadBind (m, f) =
  fn ctx ->
  case m ctx of
    | Right res -> f res ctx
    | Left str -> Left str

op monadSeq : [a,b] (Monad a) * (Monad b) -> Monad b
def monadSeq (m1, m2) = monadBind (m1, (fn _ -> m2))

op return : [a] a -> Monad a
def return x = fn ctx -> Right x

op err : [a] String -> Monad a
def err str = fn _ -> Left str

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

(* Use a computation to write a Pretty to a file, returning an error
   string on error *)
op writingToFile : String * Context * Monad Pretty -> Option String
def writingToFile (filename, ctx, m) =
  case m ctx of
    | Right pp -> (toFile (filename, format (formatWidth, pp)) ; None)
    | Left str -> Some str


(***
 *** pretty-printer helper functions
 ***)

op retString (str : String) : Monad Pretty =
  return (string str)

(* combination of return and blockFill *)
op retFill (elems : List (Nat * Pretty)) : Monad Pretty =
  return (blockFill (0, elems))

(* pretty-print a Coq application *)
op coqApply : Monad Pretty * Monad Pretty -> Monad Pretty
def coqApply (mf, ma) =
  { f_pp <- mf; a_pp <- ma;
    retFill [(0, f_pp), (2, a_pp)] }

(* pretty-print p1 followed by p2 with a string separator *)
op ppSeparator (sep : String) (p1 : Pretty) (p2 : Pretty) : Pretty =
  blockFill (0, [(0, p1), (0, string sep), (0, p2)])

def ppColon = ppSeparator ":"
def ppSemi = ppSeparator ";"

(* pretty-print parens around a Pretty *)
op ppParens (pp : Pretty) : Pretty =
  blockFill (0, [(0, string "("), (1, pp), (0, string ")")])

(* pretty-print curly brackets around a Pretty *)
op ppCurlies (pp : Pretty) : Pretty =
  blockFill (0, [(0, string "{"), (1, pp), (0, string "}")])


(***
 *** Coq-specific pretty-printing functions
 ***)

(* convert a Coq Prop to a bool, in a monad *)
op prop2bool : Monad Pretty -> Monad Pretty
def prop2bool m = coqApply ((return (string "prop2bool")), m)

(* pretty-print a Coq parameter *)
op ppCoqParam : (String * String * Pretty) -> Pretty
def ppCoqParam (q, id, tp_pp) =
  blockFill (0, [(0, string "Parameter"),
                      (2, string (qidToCoqName (q,id))),
                      (0, string ":"),
                      (2, tp_pp)])

(* pretty-print a Coq definition, which takes in a (pretty-printed)
   Coq type and Coq value of that type *)
op ppCoqDef : (String * String * Pretty * Pretty) -> Pretty
def ppCoqDef (q, id, tp_pp, def_pp) =
  blockFill (0, [(0, string "Program Definition"),
                      (2, string (qidToCoqName (q,id))),
                      (0, string ":"),
                      (2, tp_pp),
                      (0, string "="),
                      (2, def_pp)])

(* pretty-print a Coq definition without a type *)
op ppCoqDefNoT : (String * String * Pretty) -> Pretty
def ppCoqDefNoT (q, id, def_pp) =
  blockFill (0, [(0, string "Definition"),
                      (2, string (qidToCoqName (q,id))),
                      (0, string "="),
                      (2, def_pp)])

(* pretty-print a Coq record type *)
op ppCoqRecordDef : (String * String * List (String * Pretty)) -> Pretty
def ppCoqRecordDef (nm, ctor, fieldAlist) =
  blockFill
  (0,
   [(0, string "Record"),
    (4, string nm),
    (2, string ":="),
    (2, string ctor),
    (2, string "{"),
    (4,
     prLines 0 (map (fn (fnm, ftp_pp) ->
                       ppColon (string fnm) ftp_pp) fieldAlist)),
    (0, string "}.")])

(* pretty-print an element of a Coq record type *)
op ppCoqRecordElem : (String * List (String * Pretty)) -> Pretty
def ppCoqRecordElem (ctor, fields) =
  blockFill
    (0,
     [(0, string ctor),
      (0, string "{|")]
     ++
     map (fn (fname, fval_pp) ->
            (2, ppSeparator "=" (string fname) fval_pp)) fields
     ++
     [(0, string "|}")])

(* pretty-print a Coq module *)
op ppCoqModule : (String * List Pretty) -> Pretty
def ppCoqModule (mod_name, pps) =
  prLines 0
    ([string ("Module " ^ mod_name ^ ".")]
     ++ pps
     ++ [string ("End " ^ mod_name ^ ".")])


(***
 *** pretty-printers for term constructs (everything but specs)
 ***)

op unhandled : String * String -> Monad Pretty
def unhandled (fun, construct) =
  err (fun ^ ": unhandled construct " ^ construct)

def unhandledTerm (str : String) : Monad Pretty =
  unhandled ("ppTerm", str)

(* pretty-print a qualified id *)
op ppQid : QualifiedId -> Monad Pretty
def ppQid qid =
  case qid of
    | Qualified (q, id) -> retString (q ^ "." ^ id)

(* pretty-print an MSTerm into a Coq term *)
op ppTerm : MSTerm -> Monad Pretty
def ppTerm tm =
  case tm of
    | Apply (f, a, _) -> coqApply (ppTerm f, ppTerm a)
    | ApplyN (ts, _) -> unhandledTerm "ApplyN"
    | Record (elems, _) -> unhandledTerm "Record"
    | Bind (Forall, vars, body, _) ->
      prop2bool
      { vars_pp <- mapM ppVarBinding vars ;
        body_pp <- ppTerm body ;
        return (ppForall vars_pp body_pp) }
    | Bind (Exists, vars, body, _) -> unhandledTerm "Bind (Exists)"
    | Bind (Exists1, vars, body, _) -> unhandledTerm "Bind (Exists1)"
    | The (var, body, _) -> unhandledTerm "The"
    | Let (bindings, body, _) -> unhandledTerm "Let"
    | LetRec (bindings, body, _) -> unhandledTerm "LetRec"
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
         (ppParens
            (blockFill
               (0, [(0, string "fun"),
                     (2, var_pp),
                     (0, string "=>"),
                     (2, body_pp)]))) }
    | Lambda (matches, _) ->
      err "ppTerm: pattern-matching lambdas currently unhandled"
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
    | Seq (ts, _) -> unhandledTerm "Seq"
    | TypedTerm (tm, tp, _) ->
      { tm_pp <- ppTerm tm ;
        tp_pp <- ppType tp ;
        return (ppParens (ppColon tm_pp tp_pp)) }
    | Transform (transforms, _) -> unhandledTerm "Transform"
    | Pi (tyvars, body, _) -> unhandledTerm "Pi"
    | And (ts, _) -> unhandledTerm "And"
    | Any _ -> unhandledTerm "Any"

op ppVarBinding : MSVar -> Monad Pretty
def ppVarBinding (str, tp) =
  { tp_pp <- ppType tp ;
    return (ppParens (ppColon (string str) tp_pp)) }

op ppVarBindings (vs : List MSVar) : Monad Pretty =
  { pps <- mapM ppVarBinding vs ;
    retFill (List.map (fn pp -> (0, pp)) pps) }

op unhandledFun (str : String) : Monad Pretty =
  unhandled ("ppFun", str)

op ppFun : MSFun * MSType -> Monad Pretty
def ppFun (f, tp) =
  case f of
    | Not -> retString "negb"
    | And -> retString "andb_pair"
    | Or -> retString "orb_pair"
    | Implies -> retString "implb_pair"
    | Iff -> retString "iffb_pair"
    | Equals -> retString "dec_eq_pair"
    | NotEquals -> retString "dec_neq_pair"

    | Quotient tp -> unhandledFun "Quotient"
    | Choose tp -> unhandledFun "Choose"
    | Restrict -> unhandledFun "Restrict"
    | Relax -> unhandledFun "Relax"

    | PQuotient tp -> unhandledFun "PQuotient"
    | PChoose tp -> unhandledFun "PChoose"

    | Op (qid, fixity) -> ppQid qid
    | Project id -> unhandledFun "Project"
    | RecordMerge -> unhandledFun "RecordMerge"
    | Embed (id, flag) -> unhandledFun "Embed"
    | Embedded id -> unhandledFun "Embedded"
    | Select id -> unhandledFun "Select"
    | Nat n -> retString (show n)
    | Char c -> unhandledFun "Char"
    | String str -> unhandledFun "String"
    | Bool b -> retString (show b)

    | OneName (id, fixity) -> unhandledFun "OneName"
    | TwoNames (id1, id2, fixity) -> unhandledFun "TwoNames"


def unhandledType (construct : String) : Monad Pretty =
  unhandled ("ppType", construct)

op ppTyVarBinding : TyVar -> Pretty
def ppTyVarBinding str =
  ppParens (ppColon (string str) (string "Set"))

op ppTyVarBindings : TyVars -> List Pretty
def ppTyVarBindings tyvars =
  map ppTyVarBinding tyvars

(* pretty-print a forall, assuming all the variables have been
   pretty-printed as name : tp pairs*)
def ppForall (vs_pp : List Pretty) (body_pp : Pretty) : Pretty =
  blockFill
  (0, [(0, string "forall")]
     ++ (map (fn v_pp -> (0, ppParens v_pp)) vs_pp)
     ++ [(0, string ","), (0, body_pp)])

op ppType : MSType -> Monad Pretty
def ppType tp =
  case tp of
    | Arrow (t1, t2, _) ->
      { t1_pp <- ppType t1 ;
        t2_pp <- ppType t2 ;
        retFill [(0, t1_pp), (0, string "->"), (0, t2_pp)] }
  | Product (id_tps, _) -> unhandledType "Product"
  | CoProduct (id_tps, _) -> unhandledFun "CoProduct"
  | Quotient (tp, tm, _) -> unhandledFun "Quotient"
  | Subtype (tp, pred, _) -> unhandledFun "Subtype"
  | Base (id, params, _) -> unhandledFun "Base"
  | Boolean _ -> retString "bool"
  | TyVar (str, _) -> retString str
  | MetaTyVar (_, _) -> unhandledType "MetaTyVar"
  | Pi (tyvars, body, _) ->
    { body_pp <- ppType body ;
      return (ppForall (ppTyVarBindings tyvars) body_pp) }
  | And (ts, _) -> unhandledFun "And"
  | Any _ -> unhandledFun "Any"


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

    * An element "__type" equal to the record type of the spec;

    * A Coq Export statement for each imported spec (FIXME: this is
      not yet supported);

    * A Coq parameter for each "hole" in the spec;

    * A Coq definition for each type, op, and proof (given with
      specware pragmas) in the spec; and

    * An element __pinst that gives the partial instance, i.e., where
      each type, op, and proof is bound to either its parameter or
      its definition given in the module.

*)

op ppSpec : Spec -> Monad Pretty
def ppSpec s =

  (* first get all the types, ops, and axioms with (optional) defs *)
  let types_with_defs =
    mappedListOfAQualifierMap (fn tinfo -> tinfo.dfn) s.types
  (*
   foldr (fn (elem, rest) ->
            case elem of
              | Type (Qualified (q, id), _) ->
                addToAlist ((q, id), findAQualifierMap (types s, q, id))
              | TypeDef (qid, _) ->
                addToAlist ((q, id), findAQualifierMap (types s, q, id))
              | _ -> rest) [] (elements s)
     *)
  in
  let ops_with_defs_tps =
    mappedListOfAQualifierMap
      (fn op_info -> (op_info.dfn, termType op_info.dfn))
      s.ops
  (*
  let ops_with_defs =
   foldr (fn (elem, rest) ->
            case elem of
              | Op (qid, _, _) ->
                addToAlist ((q, id), findAQualifierMap (ops s, q, id))
              | OpDef (qid, _, _, _) ->
                addToAlist ((q, id), findAQualifierMap (ops s, q, id))
              | _ -> rest) [] (elements s)
   *)
  in
  let axioms_with_pfs =
   foldr (fn (elem, rest) ->
            case elem of
              | Property (Axiom, Qualified (q, id), tyvars, pred, _) ->
                (* FIXME: look for proofs given as pragmas...? *)
                (q, id, tyvars, pred, None) :: rest
              | _ -> rest) [] s.elements
  in

  {
   (* form the Coq name for the Spec *)
   specName <-
     (case valueToCoqName (Spec s) of
        | Some nm -> return nm
        | None -> err "Could not look up name of this Spec!!") ;

   (* form a list of type names with pp-ed defs *)
   tps_list
   <- (mapM
         (fn (q, id, tp) ->
            if typeIsDefined? tp then
              { tp_pp <- ppType tp ;
               return (q, id, string "Set", Some tp_pp)}
            else return (q, id, string "Set", None))
         types_with_defs) ;

   (* form a list of op names with pp-ed defs and types *)
   ops_list
   <- (mapM (fn (q, id, (op_def, op_tp)) ->
               if termIsDefined? op_def then
                 { def_pp <- ppTerm op_def ;
                   tp_pp <- ppType op_tp ;
                   return (q, id, tp_pp, Some def_pp) }
               else if typeIsDefined? op_tp then
                 { tp_pp <- ppType op_tp ;
                   return (q, id, tp_pp, None) }
               else
                 err ("Could not get type for op: " ^ q ^ "." ^ id))
         ops_with_defs_tps) ;

   (* form a list of axiom names with pp-ed props and proofs *)
   axioms_list
   <- (mapM (fn (q, id, tyvars, ax, pf_opt) ->
               case pf_opt of
                 | None ->
                   { ax_term_pp <- ppTerm ax ;
                     ax_pp <-
                      (prop2bool
                         (return
                            (ppForall (ppTyVarBindings tyvars)
                               (ppSeparator "=" ax_term_pp (string "true"))))) ;
                     return (q, id, ax_pp, None) }
                 | Some _ ->
                   err "Cannot yet handle axioms with proofs!")
         axioms_with_pfs) ;

   (* Now, build the Coq module! *)
   return
   (
    let elems_list = tps_list ++ ops_list ++ axioms_list in

    (* first build the Pretty for the __type module element *)
    let rt_pp =
      ppCoqRecordDef
        (specName, "mk_" ^ specName,
         (map (fn (q, id, tp_pp, _) ->
                 (qidToCoqName (q, id), string "Set")) elems_list))
    in 

    (* next build Prettys for type, op, and axiom module elements *)
    let defs_pps =
      map (fn (q, id, tp_pp, def_pp_opt) ->
             case def_pp_opt of
               | Some def_pp -> ppCoqDef (q, id, tp_pp, def_pp)
               | None -> ppCoqParam (q, id, tp_pp)) elems_list
    in

    (* now build the __pinst module element *)
    let pinst_pp =
      ppCoqDefNoT
        ("", "__pinst",
         ppCoqRecordElem
           ("mk_" ^ specName,
            map
              (fn (q, id, _, _) ->
                 (qidToCoqName (q, id), string (qidToCoqName (q, id))))
              elems_list))
    in

    (* Finally, build the Module! *)
    ppCoqModule
      (specName, [rt_pp] ++ defs_pps ++ [pinst_pp])
    )}


(***
 *** the top-level entrypoint
 **)

(* adapted from IsaPrinter.sw *)
op printUIDToCoqFile : String -> String
def printUIDToCoqFile uid_str =
  case Specware.evaluateUnitId uid_str of
    | None -> "Error: Unknown UID " ^ uid_str
    | Some (Spec s) ->
      (case valueToCoqName (Spec s) of
         | None -> "Error: Can't get UID string from value"
         | Some nm ->
           let context = { } in
           let filename = "Coq/" ^ nm ^ ".v" in
           let _ = ensureDirectoriesExist filename in
           (case writingToFile (filename, context, ppSpec s) of
              | None -> filename
              | Some err_str -> "Error: " ^ err_str))
    | _ -> "Error: currently only support converting Specs to Coq"

end-spec
