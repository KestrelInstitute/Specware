
CoqTermPrinter qualifying spec

import /Library/PrettyPrinter/BjornerEspinosa
import /Library/Structures/Data/Monad
import /Library/Base/List

(* specs, terms, etc. *)
import /Languages/MetaSlang/Specs/MSTerm


(* the Either type (from Haskell) *)
type Either (a, b) =
| Left a
| Right b

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

op mapM : [a,b] (a -> Monad b) * List a -> Monad (List b)
def mapM (f, l) =
  case l of
    | [] -> return []
    | x::l' ->
      { x_ret <- f x ;
        l_ret <- mapM (f, l') ;
        return (x_ret :: l_ret) }
(*
def mapM (f, l) =
  List.foldl
  ((fn (m, x) ->
      { x' <- f x ; l' <- m ; return (x'::l') }),
   return [], l)
*)


(*** pretty-printer helper functions ***)
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

(* convert a Coq Prop to a bool *)
op prop2bool : Monad Pretty -> Monad Pretty
def prop2bool m = coqApply ((return (string "prop2bool")), m)

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
      { vars_pp <- ppVarBindings vars ;
        body_pp <- ppTerm body ;
        retFill ([(0, string "forall"),
                  (2, vars_pp),(0, string ","), (0, body_pp)]) }
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
         (blockNone
            (0, [(0, string "(fun"),
                  (2, var_pp),
                  (0, string "=>"),
                  (2, body_pp),
                  (0, string ")")]))
        }
    | Lambda (matches, _) ->
      err "ppTerm: pattern-matching lambdas currently unhandled"
    | IfThenElse (t1, t2, t3, _) ->
      { t1_pp <- ppTerm t1 ;
        t2_pp <- ppTerm t2 ;
        t3_pp <- ppTerm t3 ;
        retFill [(0, string "(if"),
                 (2, t1_pp),
                 (0, string "then"),
                 (2, t2_pp),
                 (0, string "else"),
                 (2, t3_pp),
                 (0, string ")")] }
    | Seq (ts, _) -> unhandledTerm "Seq"
    | TypedTerm (tm, tp, _) ->
      { tm_pp <- ppTerm tm ;
        tp_pp <- ppType tp ;
        retFill [(0, string "("),
                 (1, tm_pp),
                 (1, string ":"),
                 (1, tp_pp),
                 (0, string ")")] }
    | Transform (transforms, _) -> unhandledTerm "Transform"
    | Pi (tyvars, body, _) -> unhandledTerm "Transform"
    | And (ts, _) -> unhandledTerm "And"
    | Any _ -> unhandledTerm "Any"

op ppVarBinding (v : MSVar) : Monad Pretty
def ppVarBinding (str, tp) =
  { tp_pp <- ppType tp ;
   retFill [(0, string ("(" ^ str)),
            (0, string ":"),
            (0, tp_pp)] }

op ppVarBindings (vs : List MSVar) : Monad Pretty =
  { pps <- mapM (ppVarBinding, vs) ;
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
  | Pi (tyvars, body, _) -> unhandledFun "Pi"
  | And (ts, _) -> unhandledFun "And"
  | Any _ -> unhandledFun "Any"

end-spec
