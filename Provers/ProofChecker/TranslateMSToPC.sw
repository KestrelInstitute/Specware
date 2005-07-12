% Translation from MetaSlang abstract syntax to proof checker abstract syntax.

% There are some outstanding issues. First, in AC's abstract syntax, an
% instance of an operator is accompanied by instantiations for any type
% variables for that operator. The code below, does not try to recover what
% those instantiations are.

% A number of functions have been left unspecified. This includes functions
% for converting identifiers (strings) in MetaSlang to identifiers in the
% proof checker abstract syntax. It also includes a monadic function
% for generating fresh variable names.

Translate qualifying spec
  import BasicAbbreviations
  import OtherAbbreviations
  import /Languages/MetaSlang/AbstractSyntax/AnnTerm
  import /Languages/MetaSlang/Specs/Environment
  import /Languages/SpecCalculus/Semantics/Environment  % for the Specware monad

  op Term.msToPC : Spec -> MS.Term -> Env Expression
  def Term.msToPC spc trm =
    case trm of
      | Apply (Fun (And,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            t1PC <- msToPC spc t1;
            t2PC <- msToPC spc t2;
            return (t1PC &&& t2PC)
          }
      | Apply (Fun (Or,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            t1PC <- msToPC spc t1;
            t2PC <- msToPC spc t2;
            return (t1PC ||| t2PC)
          }
      | Apply (Fun (Implies,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            t1PC <- msToPC spc t1;
            t2PC <- msToPC spc t2;
            return (t1PC ==> t2PC)
          }
      | Apply (Fun (Equals,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            t1PC <- msToPC spc t1;
            t2PC <- msToPC spc t2;
            return (t1PC == t2PC)
          }
      | Apply (Fun (NotEquals,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            t1PC <- msToPC spc t1;
            t2PC <- msToPC spc t2;
            return (t1PC ~== t2PC)
          }
      % | Apply (Fun (RecordMerge,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
            % t1PC <- msToPC spc t1;
            % t2PC <- msToPC spc t2;
            % return (t1PC <<< t2PC)
          % }
      | Apply (Fun (Project id,srt,_),term,_) -> {
            termPC <- msToPC spc term;
            typePC <- msToPC spc (inferType (spc,term));
            if posNat? id then
              return (DOT (termPC, typePC, prod (toPosNat id)))
            else
              return (DOT (termPC, typePC, user (idToUserField id)))
          }
      % | Apply (Quotient,arg,pos) -> return (nullary truE)   % ???
      | Apply(Fun (Embed(id,b),srt,_),arg,_) -> {
            newType <- Type.msToPC spc srt;
            argExpr <- Term.msToPC spc arg;
            return ((EMBED (newType, idToConstructor id)) @ argExpr)
          }
      | Apply (f,a,pos) -> {
            fPC <- msToPC spc f;
            aPC <- msToPC spc a;
            return (fPC @ aPC)
          }
      | ApplyN (terms,pos) -> raise (Fail "trying to translate MetaSlang ApplyN for proof checker")
      | Record (pairs as (("1",_)::_),pos) -> {
            elems <- mapListToFSeq (fn pair -> msToPC spc pair.2) pairs;
            types <- mapListToFSeq (fn pair -> msToPC spc (inferType (spc,pair.2))) pairs;
            return (TUPLE (types,elems))
          }
      | Record (pairs,pos) -> {
            fields <- mapListToFSeq (fn pair -> return (user (idToUserField pair.1))) pairs;
            types <- mapListToFSeq (fn pair -> msToPC spc (inferType (spc,pair.2))) pairs;
            exprs <- mapListToFSeq (fn pair -> msToPC spc pair.2) pairs;
            return (REC (fields,types,exprs))
          }
      | Bind (Forall,vars,term,pos) -> {
            vs <- mapListToFSeq (fn aVar -> return (idToVariable aVar.1)) vars;
            types <- mapListToFSeq (fn aVar -> msToPC spc aVar.2) vars;
            newTerm <- msToPC spc term;
            return (FAA (vs,types,newTerm))
          }
      | Bind (Exists,vars,term,pos) -> {
            vs <- mapListToFSeq (fn aVar -> return (idToVariable aVar.1)) vars;
            types <- mapListToFSeq (fn aVar -> msToPC spc aVar.2) vars;
            newTerm <- msToPC spc term;
            return (EXX (vs,types,newTerm))
          }
      | Let ((lhs,rhs)::rest,term,pos) -> {
            newRhs <- msToPC spc rhs;
            (vars,types,newGuard) <- Pattern.msToPC spc newRhs lhs;
            newType <- Type.msToPC spc (inferType (spc,term));
            if rest = [] then {
              newTerm <- Term.msToPC spc term;
              return (COND (newType, single (vars,types,newGuard,newTerm)))
            }
            else {
              newTerm <- Term.msToPC spc (Let (rest,term,pos));
              return (COND (newType, single (vars,types,newGuard,newTerm)))
            }
          }
      | Let ([],term,pos) -> Term.msToPC spc term
      | LetRec (bindings,term,pos) -> {
            vs <- mapListToFSeq (fn (var,rhs) -> return (idToVariable var.1)) bindings;
            types <- mapListToFSeq (fn (var,rhs) -> Type.msToPC spc var.2) bindings;
            exprs <- mapListToFSeq (fn (var,rhs) -> Term.msToPC spc rhs) bindings;
            expr <- Term.msToPC spc term;
            typ <- Type.msToPC spc (inferType (spc,term));
            return (LETDEF (typ,vs,types,exprs,expr))
          }
      | IfThenElse (pred,yes,no,pos) -> {
            newPred <- msToPC spc pred;
            newYes <- msToPC spc yes;
            newNo <- msToPC spc no;
            return (IF (newPred,newYes,newNo))
          }
      | Fun (Op(id,fxty),typ,_) -> {
            newType <- Type.msToPC spc typ; 
            return (OPI (qidToOperation id,empty))         % ???
          }
      | Fun (Embed(id,b),srt,_) ->  {
            newType <- Type.msToPC spc srt;
            return ((EMBED (newType, idToConstructor id)) @ MTREC)
          }
      | Lambda ([],pos) ->
          raise (Fail "trying to translate empty MetaSlang match for proof checker")
      | Lambda ((match as ((pat,guard,rhs)::_)),pos) -> {
            var <- newVar;
            branches <- mapListToFSeq (GuardedExpr.msToPC spc (VAR var)) match;
            lhsType <- Type.msToPC spc (patternSort pat);
            rhsType <- Type.msToPC spc (inferType (spc,rhs));
            return (FN (var, lhsType, COND (rhsType,branches)))
          }
      | Seq (term::rest,pos) ->
          if rest = [] then 
            Term.msToPC spc term
          else
            Term.msToPC spc (Let ([(WildPat (inferType (spc,term),pos),term)], Seq (rest,pos),pos))
      | Seq ([],pos) -> 
          raise (Fail "trying to translate empty MetaSlang Seq for proof checker")
      | SortedTerm  (term,typ,pos) -> msToPC spc term
      | Pi (tyVars,term,pos) -> msToPC spc term
      | And (terms,pos) -> 
          raise (Fail "trying to translate MetaSlang join operation on terms for proof checker")
      | Fun (Nat n,srt,pos) -> return (primNat n)
      | Fun (Char c,srt,pos) -> return (primChar c)
      | Fun (String s,srt,pos) -> return (primString s)
      | Fun (Bool true,srt,pos) -> return TRUE
      | Fun (Bool false,srt,pos) -> return FALSE
      | Fun (Quotient,srt,pos) -> {
            newType <- Type.msToPC spc srt;
            return (QUOT newType)
          }
      | Var ((id,srt),pos) -> return (VAR (idToVariable id))

  op OptType.msToPC : Spec -> Option MS.Sort -> Env Type
  def OptType.msToPC spc typ? =
    case typ? of
      | None -> return UNIT
      | Some typ -> msToPC spc typ

  op Type.msToPC : Spec -> MS.Sort -> Env Type
  def Type.msToPC spc typ =
    case typ of
      | Arrow (ty1,ty2,_) -> {
           newTy1 <- msToPC spc ty1;
           newTy2 <- msToPC spc ty2;
           return (newTy1 --> newTy2)
          }
      | Product (fields as (("1",_)::_),_) -> {
           types <- mapListToFSeq (fn (id,typ) -> msToPC spc typ) fields;
           return (PRODUCT types)
         }
      | Product (fields,_) -> {
           newFields <- mapListToFSeq (fn (id,typ) -> return (user (idToUserField id))) fields;
           types <- mapListToFSeq (fn (id,typ) -> msToPC spc typ) fields;
           return (RECORD (newFields, types))
         }
      | CoProduct (sums,_) -> {
           constructors <- mapListToFSeq (fn (id,typ?) -> return (idToConstructor id)) sums;
           types <- mapListToFSeq (fn (id,typ?) -> OptType.msToPC spc typ?) sums;
           return (SUM (constructors, types))
         }
      | Quotient (typ,term,_) -> {
           newType <- Type.msToPC spc typ;
           newTerm <- Term.msToPC spc term;
           return (QUOT (newType,newTerm))
          }
      | Subsort (typ,term,_) -> {
           newType <- Type.msToPC spc typ;
           newTerm <- Term.msToPC spc term;
           return (RESTR (newType,newTerm))
          }
      | Base (id,types,_) -> {
           newTypes <- mapListToFSeq (Type.msToPC spc) types;
           return (TYPE (qidToTypeName id, newTypes))
          }
      | Boolean _ -> return BOOL
      | TyVar (id,_) -> return (VAR (idToTypeVariable id))
      | MetaTyVar _ ->
           raise (Fail "trying to translate MetaSlang meta type variable for proof checker")
      | Pi (typeVars,types,_) ->
           raise (Fail "trying to translate MetaSlang type scheme for proof checker")
      | And (types,_) -> 
           raise (Fail "trying to translate MetaSlang join type for proof checker")
      | Any _ ->
           raise (Fail "trying to translate MetaSlang any type for proof checker")

  % The second argument is the expression to which we will identify (equate) with all patterns.
  op GuardedExpr.msToPC : Spec -> Expression -> (MS.Pattern * MS.Term * MS.Term) -> Env BindingBranch
  def GuardedExpr.msToPC spc expr (pattern,guard,term) = {
      (vars,types,lhs) <- Pattern.msToPC spc expr pattern; 
      rhs <- msToPC spc term; 
      return (vars,types,lhs,rhs)
    }

  % As above, the second argument is the expression to which we will identify (equate) with the pattern.
  % In many cases it is just a variable. The function computes a list of variables that
  % are bound by the match, the types of the variables and a boolean valued expression (a guard)
  % that represents the pattern.
  op Pattern.msToPC : Spec -> Expression -> MS.Pattern -> Env (Variables * Types * Expression)
  def Pattern.msToPC spc expr pattern = 
    case pattern of
      | AliasPat (pat1,pat2,_) -> {
          (vars1,types1,expr1) <- Pattern.msToPC spc expr pat1;
          (vars2,types2,expr2) <- Pattern.msToPC spc expr pat2;
          return (vars1++vars2, types1++types2, expr1 &&& expr2)
        }
      | VarPat ((id,typ), b) -> {
          newType <- Type.msToPC spc typ;
          return (single (idToVariable id), single newType, (VAR (idToVariable id)) == expr)
        }
      | EmbedPat (id,None,typ,_) -> {
          newType <- Type.msToPC spc typ;
          return (empty, empty, ((EMBED (newType, idToConstructor id)) @ MTREC) == expr)
        }
      | EmbedPat (id,Some pat,typ,_) -> {
          var <- newVar;
          newType <- Type.msToPC spc typ;
          (vars,types,boolExpr) <- Pattern.msToPC spc (VAR var) pat;
          return (var |> vars,newType |> types, ((EMBED (newType, idToConstructor id)) @ (VAR var)) == expr)
        }
      | RecordPat (fields as (("1",_)::_),_) ->
           foldM (fn (vars,types,newExpr) -> fn (n,pat) -> {
              fieldType <- Type.msToPC spc (patternSort pat);
              (fVars,fType,fExpr) <- Pattern.msToPC spc (DOT (expr, fieldType, prod (toPosNat n))) pat;
              return (vars++fVars,types++fType,newExpr &&& fExpr)
            }) (empty,empty,TRUE) fields
      | RecordPat (fields,_) -> 
           foldM (fn (vars,types,newExpr) -> fn (id,pat) -> {
              fieldType <- Type.msToPC spc (patternSort pat);
              (fVars,fType,fExpr) <- Pattern.msToPC spc (DOT (expr, fieldType, user (idToUserField id))) pat;
              return (vars++fVars,types++fType,newExpr &&& fExpr)
            }) (empty,empty,TRUE) fields
      | StringPat (string, b) -> return (empty,empty,(primString string) == expr)
      | BoolPat (bool, b) -> return (empty,empty,expr)
      | CharPat (char, b) -> return (empty,empty,(primChar char) == expr)
      | NatPat (nat, b) -> return (empty,empty,(primNat nat) == expr)
      | WildPat (srt, _) -> return (empty,empty,TRUE)

  op idToUserField : String -> UserField
  op idToVariable : String -> Variable
  op idToConstructor : String -> Constructor
  op idToTypeVariable : String -> TypeVariable

  op qidToTypeName : QualifiedId -> TypeName
  op qidToOperation : QualifiedId -> Operation

  op newVar : Env Variable

  op posNat? : String -> Boolean
  op toPosNat : (String | posNat?) -> PosNat

  op mapListToFSeq : fa(a,b) (a -> b) -> List a -> FSeq b
  def mapListToFSeq f list = foldl (fn (x,fSeq) -> (f x) |> fSeq) empty list

  op MonadFSeq.map : fa(a,b) (a -> Env b) -> FSeq a -> Env (FSeq b)

  op MSToPCTranslateMonad.mapListToFSeq : fa(a,b) (a -> Env b) -> List a -> Env (FSeq b)
  def MSToPCTranslateMonad.mapListToFSeq f list =
    case list of
      | [] -> return empty
      | x::xs -> {
          xNew <- f x;
          xsNew <- mapListToFSeq f xs;
          return (xNew |> xsNew)
        }

  op primNat : Nat -> Expression
  def primNat n =
    if n = 0 then
      OPI (qidToOperation (Qualified ("Nat","zero")),empty)
    else
      (OPI (qidToOperation (Qualified ("Nat","succ")),empty)) @ (primNat (n - 1))

  op primString : String -> Expression
  def primString str =
    (OPI (qidToOperation (Qualified ("String","implode")),empty)) @ (primList charType (map primChar (explode str)))

  op charType : Type
  def charType = TYPE (qidToTypeName (Qualified ("Char","Char")),empty)

  op primChar : Char -> Expression
  def primChar c = (OPI (qidToOperation (Qualified ("Char","chr")),empty)) @ (primNat (ord c))

  op primList : Type -> List Expression -> Expression
  def primList typ l =
    let nil = (EMBED (listType typ, idToConstructor "Nil")) @ MTREC in
    let def cons (a, l) =
      let p = PAIR (typ, listType typ, a, l) in
      (EMBED (listType typ, idToConstructor "Cons")) @ p
    in
      foldr cons nil l

  op listType : Type -> Type
  def listType typ = TYPE (qidToTypeName (Qualified ("List","List")), single typ)
endspec
