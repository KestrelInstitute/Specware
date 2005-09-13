% Translation from MetaSlang abstract syntax to proof checker abstract syntax.

% This file will be moved.

Translate qualifying
spec
  import Spec
  import /Languages/MetaSlang/AbstractSyntax/AnnTerm
  import /Languages/MetaSlang/Specs/Environment
  import /Languages/SpecCalculus/Semantics/Environment  % for the Specware monad

  type Subst = List (Constructor * Operation)

%%   op applyConstructorSubst : Subst -> Expression -> Expression
%%   def applyConstructorSubst subst expr =
%%     case expr of
%%       | EMBED (typ,constr) = 
%%           let
%%             def lookup l =
%%               case l of
%%                 | [] -> expr
%%                 | (constructor,opr)::rest ->
%%                    if constructor = constr then
%%                      OPI (opr,empty)     % !!!???
%%                    else
%%                      lookup rest
%%           in
%%             lookup subst
%%       | _ -> expr
   
  op specToContext : Spec -> SpecCalc.Env Context
  def specToContext spc =
    let
      def specElemToContextElems fSeq elem = 
        case elem of
            % We recursively process all the elements in the imports as well. It is here
            % that a single spec element can give rise to many context elements
            % and consequently why we are using foldM, rather than the mapListToFSeq function
            % defined later.
          | Import (specTerm,spc,elements) -> {
              otherCtxt <- specToContext spc;
              return (fSeq ++ otherCtxt)
            }
          | Sort qid -> {
              typeInfo <- findInMap spc.sorts qid;
              case typeInfo.dfn of
                | Pi (tyVars,typ,_) -> return (fSeq <| (typeDeclaration (qidToTypeName qid, length tyVars)))
                | typ -> return (fSeq <| (typeDeclaration (qidToTypeName qid, 0)))
            }
          | SortDef qid -> {
              typeInfo <- findInMap spc.sorts qid;
              case typeInfo.dfn of
                | Pi (tyVars,typ as (CoProduct (sums,_)),_) -> {
                     newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
                     test? <- recursiveSumOfProducts? spc qid;
                     if test? then
                       let
                         def idToOperation str = qidToOperation (mkUnQualifiedId str) (embed prefix)
                         def summandToOp summand =
                           case summand of
                             | (name, None) -> {
                                 newOpName <- return ((printQualifiedId qid) ^ "$" ^ name);
                                 newOperator <- return (idToOperation newOpName);
                                 typeVarTypes <- mapListToFSeq (fn tyVar -> return (VAR (idToTypeVariable tyVar))) tyVars;
                                 newType <- return (TYPE (qidToTypeName qid, typeVarTypes));
                                 % return (opDeclaration (newOpName,newTyVars,newType)) % ,(idToConstructor name,newOperator))
                                 return (newOpName,newOperator,newTyVars,newType) % ,(idToConstructor name,newOperator))
                                }
                             | (name, Some typ) -> {
                                 newOpName <- return ((printQualifiedId qid) ^ "$" ^ name);
                                 newOperator <- return (idToOperation newOpName);
                                 typeVarTypes <- mapListToFSeq (fn tyVar -> return (VAR (idToTypeVariable tyVar))) tyVars;
                                 srcType <- Type.msToPC spc typ;
                                 newType <- return (srcType --> (TYPE (qidToTypeName qid, typeVarTypes)));
                                 % return (opDeclaration (newOpName,newTyVars,newType)) % ,(idToConstructor name,newOpName))
                                 return (newOpName,newOperator,newTyVars,newType) % ,(idToConstructor name,newOpName))
                                }
                          def injectiveAxiom axms (opName,oper,typeVars,typ) =
                            case typ of
                              | ARROW (srcType,tar) -> {
                                    lVar <- newVar;
                                    rVar <- newVar;
                                    newTerm <- return (FA2 (lVar,srcType,rVar,srcType,
                                                   (EQ (APPLY (OPI (oper,empty),VAR lVar),APPLY (OPI (oper,empty),VAR rVar)))
                                               ==> (EQ (VAR lVar,VAR rVar))));
                                    return (axms <| (axioM ("injective$" ^ opName,typeVars,newTerm)))
                                  }
                              | _ -> return axms
                          def disjointFrom op1 operators =
                            case operators of
                              | [] -> return empty
                              | op2::rest ->
                                 (case (op1,op2) of
                                   | ((name1,oper1,tyVars1,ARROW (src1,tar1)),(name2,oper2,tyVars2,ARROW (src2,tar2))) -> {
                                       var1 <- newVar;
                                       var2 <- newVar;
                                       newTerm <- return (FA2 (var1,src1,var2,src2,
                                               ~~ (EQ (APPLY (OPI (oper1,empty),VAR var1),APPLY (OPI (oper2,empty),VAR var2)))));
                                       newAxiom <- return (axioM ("disjoint$" ^ name1 ^ "$" ^ name2,tyVars1,newTerm));
                                       moreAxioms <- disjointFrom op1 rest;
                                       return (newAxiom |> moreAxioms) 
                                     }
                                   | ((name1,oper1,tyVars1,typ1),(name2,oper2,tyVars2,ARROW (src2,tar2))) -> {
                                       var2 <- newVar;
                                       newTerm <- return (FA (var2,src2,
                                               ~~ (EQ (OPI (oper1,empty),APPLY (OPI (oper2,empty),VAR var2)))));
                                       newAxiom <- return (axioM ("disjoint$" ^ name1 ^ "$" ^ name2,tyVars1,newTerm));
                                       moreAxioms <- disjointFrom op1 rest;
                                       return (newAxiom |> moreAxioms) 
                                     }
                                   | ((name1,oper1,tyVars1,ARROW (src1,tar1)),(name2,oper2,tyVars2,typ2)) -> {
                                       var1 <- newVar;
                                       newTerm <- return (FA (var1,src1,
                                               ~~ (EQ (APPLY (OPI (oper1,empty),VAR var1),OPI (oper2,empty)))));
                                       newAxiom <- return (axioM ("disjoint$" ^ name1 ^ "$" ^ name2,tyVars1,newTerm));
                                       moreAxioms <- disjointFrom op1 rest;
                                       return (newAxiom |> moreAxioms) 
                                     }
                                   | ((name1,oper1,tyVars1,typ1),(name2,oper2,tyVars2,typ2)) -> {
                                       newTerm <- return (~~ (EQ (OPI (oper1,empty),OPI (oper2,empty))));
                                       newAxiom <- return (axioM ("disjoint$" ^ name1 ^ "$" ^ name2,tyVars1,newTerm));
                                       moreAxioms <- disjointFrom op1 rest;
                                       return (newAxiom |> moreAxioms)
                                     })
                          def disjointAxioms operators =
                            case operators of
                              | op1::rest -> {
                                  op1Axioms <- disjointFrom op1 rest;
                                  restAxioms <- disjointAxioms rest;
                                  return (op1Axioms ++ restAxioms)
                                }
                              | _ -> return empty
                       in {
                         print ("Recursive sum of products " ^ (printQualifiedId qid) ^ "\n");
                         newOperators <- mapM summandToOp sums;
                         decls <- mapListToFSeq (fn opr -> return (opDeclaration (opr.2,opr.3,opr.4))) newOperators;
                         injAxioms <- foldM injectiveAxiom FSeq.empty newOperators;
                         disjAxioms <- disjointAxioms newOperators;
                         return ((fSeq <| (typeDeclaration (qidToTypeName qid, length tyVars))) ++ decls ++ injAxioms ++ disjAxioms)
                       }
                     else {
                       print ("Not recursive sum of products " ^ (printQualifiedId qid) ^ "\n");
                       newType <- Type.msToPC spc typeInfo.dfn;
                       return (fSeq <| (typeDefinition (qidToTypeName qid, newTyVars, newType)))
                     }
                  }
                | typ -> {
                     newType <- Type.msToPC spc typeInfo.dfn;
                     return (fSeq <| (typeDefinition (qidToTypeName qid, empty, newType)))
                  }
             }
          | Op qid -> {
              % print ("Op:" ^ (printQualifiedId qid) ^ "\n");
              opInfo <- findInMap spc.ops qid;
              case opInfo.dfn of
                | Pi (tyVars,SortedTerm (_,typ,_),_) -> {
                       newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
                       newType <- Type.msToPC spc typ;
                       return (fSeq <| (opDeclaration (qidToOperation qid (convertFixity opInfo.fixity), newTyVars, newType)))
                    }
%%                 | Pi (tyVars,SortedTerm (term,typ,_),_) -> {
%%                        newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
%%                        newTerm <- msToPC spc term;
%%                        return (fSeq <| (opDefinition (qidToOperation qid (convertFixity opInfo.fixity), newTyVars, newTerm)))
%%                     }
%%                 | SortedTerm (_,Pi (tyVars,typ,pos),_) -> {
%%                       newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
%%                       newType <- Type.msToPC spc typ;
%%                       return (fSeq <| (opDeclaration (qidToOperation qid (convertFixity opInfo.fixity), newTyVars, newType)))
%%                     }
                 | SortedTerm (_,typ,_) -> {
                       newType <- Type.msToPC spc typ;
                       return (fSeq <| (opDeclaration (qidToOperation qid (convertFixity opInfo.fixity), empty, newType)))
                     }
                | _ -> raise (Fail ("translateMSToPC: specToContext: ill-formed declaration for op " ^ (printQualifiedId qid) ^ " term = " ^ (System.anyToString opInfo.dfn)))
             }
           | OpDef qid -> {
              % print ("OpDef:" ^ (printQualifiedId qid) ^ "\n");
               opInfo <- findInMap spc.ops qid;
               case opInfo.dfn of
                 | Pi (tyVars,SortedTerm (term,typ,_),_) -> {
                       newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
                       newTerm <- msToPC spc term;
                       return (fSeq <| (opDefinition (qidToOperation qid (convertFixity opInfo.fixity), newTyVars, newTerm)))
                     }
                 | SortedTerm (term,Pi (tyVars,typ,pos),_) -> {
                       newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
                       newTerm <- msToPC spc term;
                       return (fSeq <| (opDefinition (qidToOperation qid (convertFixity opInfo.fixity), newTyVars, newTerm)))
                     }
                 | SortedTerm (term,typ,_) -> {
                       newTerm <- msToPC spc term;
                       return (fSeq <| (opDefinition (qidToOperation qid (convertFixity opInfo.fixity), empty, newTerm)))
                     }
                 | _ -> raise (Fail ("translateMSToPC: specToContext: ill-formed definition for op " ^ (printQualifiedId qid) ^ " term = " ^ (System.anyToString opInfo.dfn)))
             }
           | Property (Axiom,propName,tyVars,term) -> {
               newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
               newTerm <- msToPC spc term;
               return (fSeq <| (axioM (propNameToAxiomName propName, newTyVars,newTerm)))
             }
               
           | Property (Theorem,propName,tyVars,term) -> {
               newTyVars <- mapListToFSeq (fn tyVar -> return (idToTypeVariable tyVar)) tyVars;
               newTerm <- msToPC spc term;
               return (fSeq <| (axioM (propNameToAxiomName propName, newTyVars,newTerm)))
             }
               
          % | Comment str ->
    in
      foldM specElemToContextElems empty spc.elements
      
  % Convert a term in MetaSlang abstract syntax to a term in the proof checker's abstract syntax.
  op Term.msToPC : Spec -> MS.Term -> SpecCalc.Env Expression
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
      | Apply (Fun (Iff,srt,_),Record ([("1",t1),("2",t2)],_),_) -> {
          t1PC <- msToPC spc t1;
          t2PC <- msToPC spc t2;
          return (t1PC <==> t2PC)
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
          if natConvertible id then
            return (DOT (termPC, typePC, prod (stringToNat id)))
          else
            return (DOT (termPC, typePC, user (idToUserField id)))
        }
      % | Apply (Quotient,arg,pos) -> return (nullary truE)   % ???
      | Apply(Fun (Embed(id,b),srt,_),arg,_) -> {
          newType <- Type.msToPC spc srt;
          argExpr <- Term.msToPC spc arg;
          return ((EMBED (newType, idToConstructor id)) @ argExpr)
        }
      | Apply (Fun (Not,srt,_),t,_) -> {
          tPC <- msToPC spc t;
          return (~~ tPC)
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
      | Fun (Op(id,fxty),typ,_) ->
          let
            def lookup l id =
              case l of
                | [] -> raise (Fail ("matchType: failed to find instance for type variable: " ^ id))
                | (name,typ)::rest ->
                    if id = name then
                      return typ
                    else
                      lookup rest id
          in {
            % print ("msToPC: term=" ^ (printTerm trm) ^ " type=" ^ (printSort typ) ^ "\n");
            opInfo <- findInMap spc.ops id;
            case opInfo.dfn of
              | Pi (tyVars,SortedTerm (_,abstTyp,_),_) -> {
                  % print ("msToPC: abstract type=" ^ (printSort abstTyp) ^ "\n");
                  subs <- catch (matchType spc abstTyp typ)
                     (fn (Fail str) -> raise (Fail (str ^ "\nTerm.msToPC: abstTyp=" ^ (printSort abstTyp) ^ " typ=" ^ (printSort typ))));
                  types <- mapListToFSeq (fn tyVar -> lookup subs tyVar) tyVars;
                  return (OPI (qidToOperation id (convertFixity fxty),types)) 
                }
              | SortedTerm (_,typ,_) -> return (OPI (qidToOperation id (convertFixity fxty),empty)) 
              | _ -> raise (Fail "trying to translate empty MetaSlang match for proof checker")
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
      | _ -> {
         print ("Term.msToPC: no match\n");
         % print (printTerm trm);
         print (System.anyToString trm);
         print ("term = " ^ (printTerm trm) ^ "\n");
         raise (Fail "no match in Term.msToPC")
       }

  op zip : [a,b] List a -> List b -> List (a * b)
  def zip l1 l2 =
    case (l1,l2) of
      | ([],_) -> []
      | (_,[]) -> []
      | (x::xs,y::ys) -> Cons ((x,y),zip xs ys)

  % Operator references that appear in a proof checker abstract syntax
  % tree are accompanied by a sequence of types. These types are the
  % instantiations of the type variables (if any) associated with the
  % declaration of the type of the op. This information is not directly
  % recorded in the Metaslang abstract syntax. The function below recovers
  % this information, in the form of a substitution, by matching a
  % particular type instance (t2) with the abstract type declaration (t1).
  % The latter is assumed to be free of type variables.

  op matchType : Spec -> MS.Sort -> MS.Sort -> Env (List (TyVar * Type))
  def matchType spc t1 t2 =
    % case (unfoldBase (spc,t1),unfoldBase (spc,t2)) of
    case (t1,t2) of
      | (Arrow (l1,l2,_), Arrow (r1,r2,_)) -> {
           sub1 <- matchType spc l1 r1;
           sub2 <- matchType spc l2 r2;
           return (sub1 List.++ sub2)
         }
      | (Product (lFlds,_), Product (rFlds,_)) -> {
           subs <- mapListToFSeq (fn ((_,l),(_,r)) -> matchType spc l r) (zip lFlds rFlds);
           return (foldl List.concat [] subs)
         }
      | (CoProduct (lSums,_), CoProduct (rSums,_)) ->
         let
           def f pair =
             case pair of
               | ((_,None),(_,None)) -> return []
               | ((_,Some lTyp),(_,Some rTyp)) -> matchType spc lTyp rTyp
               | _ -> raise (Fail "bad")
         in {
           subs <- mapListToFSeq f (zip lSums rSums);
           return (foldl List.concat [] subs)
         }
      | (Quotient (lTyp,lTerm,_), Quotient (rTyp,rTerm,_)) -> matchType spc lTyp rTyp
      | (Subsort (lTyp,lTerm,_), Subsort (rTyp,rTerm,_)) -> matchType spc lTyp rTyp
      | (Base (qid1,types1,_),Base (qid,types2,_)) ->
           foldM (fn subs1 -> fn (t1,t2) -> {
             subs2 <- matchType spc t1 t2;
             return (subs1 List.++ subs2)
           }) [] (zip types1 types2)
%%       | (_,Base (qid,[],_)) -> {
%%            typeInfo <- findInMap spc.sorts qid;
%%            matchType spc t1 typeInfo.dfn
%%          }
%%       | (Base (qid,types,_),_) -> {
%%            typeInfo <- findInMap spc.sorts qid; case typeInfo.dfn of
%%              | Pi (tyVars,typ,_) -> {
%%                   newType <- return (substSort (zip tyVars types, typ));
%%                   matchType spc newType t2
%%                 }
%%              | _ -> raise (Fail "matchType: mismatch of ")
%%           }
%%       | (_,Base (qid,types,_)) -> {
%%            typeInfo <- findInMap spc.sorts qid; case typeInfo.dfn of
%%              | Pi (tyVars,typ,_) -> {
%%                   newType <- return (substSort (zip tyVars types, typ));
%%                   matchType spc t1 newType
%%                 }
%%              | _ -> raise (Fail "matchType: mismatch of ")
%%           }
%%       | (TyVar _,TyVar _) -> raise (Fail "matchType: type instance contains type variables")
      | (TyVar (id,_),_) -> {
            newType <- catch (msToPC spc t2)
               (fn (Fail str) -> raise (Fail (str ^ "\nmatchType: matching type var " ^ id ^ " with type: " ^ (printSort t2))));
            return [(id, newType)]
          }
      | (_, TyVar _) -> raise (Fail "matchType: type instance contains type variables")
      | (_, _) -> return []

  op OptType.msToPC : Spec -> Option MS.Sort -> SpecCalc.Env Type
  def OptType.msToPC spc typ? =
    case typ? of
      | None -> return UNIT
      | Some typ -> msToPC spc typ

  % Convert a type in MetaSlang abstract syntax to a type in the proof checker's abstract syntax.
  op Type.msToPC : Spec -> MS.Sort -> SpecCalc.Env Type
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
      | _ -> {
          print ("Type.msToPC: no match\n");
          print ("type = " ^ (printSort typ) ^ "\n");
          raise (Fail "no match in Type.msToPC")
        }

  % The second argument is the expression to which we will identify (equate) with all patterns.
  op GuardedExpr.msToPC : Spec -> Expression -> (MS.Pattern * MS.Term * MS.Term) -> SpecCalc.Env BindingBranch
  def GuardedExpr.msToPC spc expr (pattern,guard,term) = {
      (vars,types,lhs) <- Pattern.msToPC spc expr pattern; 
      rhs <- msToPC spc term; 
      return (vars,types,lhs,rhs)
    }

  % As above, the second argument is the expression to which we will identify (equate) with the pattern.
  % In many cases it is just a variable. The function computes a list of variables that
  % are bound by the match, the types of the variables and a boolean valued expression (a guard)
  % that represents the pattern.
  op Pattern.msToPC : Spec -> Expression -> MS.Pattern -> SpecCalc.Env (Variables * Types * Expression)
  def Pattern.msToPC spc expr pattern = 
    case pattern of
      | AliasPat (pat1,pat2,_) -> {
          (vars1,types1,expr1) <- Pattern.msToPC spc expr pat1;
          (vars2,types2,expr2) <- Pattern.msToPC spc expr pat2;
          return (vars1 ++ vars2, types1 ++ types2, expr1 &&& expr2)
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
              (fVars,fType,fExpr) <- Pattern.msToPC spc (DOT (expr, fieldType, prod (stringToNat n))) pat;
              return (vars ++ fVars,types ++ fType,newExpr &&& fExpr)
            }) (empty,empty,TRUE) fields
      | RecordPat (fields,_) -> 
           foldM (fn (vars,types,newExpr) -> fn (id,pat) -> {
              fieldType <- Type.msToPC spc (patternSort pat);
              (fVars,fType,fExpr) <- Pattern.msToPC spc (DOT (expr, fieldType, user (idToUserField id))) pat;
              return (vars ++ fVars,types ++ fType,newExpr &&& fExpr)
            }) (empty,empty,TRUE) fields
      | StringPat (string, b) -> return (empty,empty,(primString string) == expr)
      | BoolPat (bool, b) -> return (empty,empty,expr)
      | CharPat (char, b) -> return (empty,empty,(primChar char) == expr)
      | NatPat (nat, b) -> return (empty,empty,(primNat nat) == expr)
      | WildPat (srt, _) -> return (empty,empty,TRUE)

  op idToUserField : String -> UserField
  def idToUserField s = s

  op idToVariable : String -> Variable
  def idToVariable s = user s

  op idToConstructor : String -> Constructor
  def idToConstructor s = s

  op idToTypeVariable : String -> TypeVariable
  def idToTypeVariable s = s

  op propNameToAxiomName : PropertyName -> AxiomName
  def propNameToAxiomName qid = printQualifiedId qid

  op qidToTypeName : QualifiedId -> TypeName
  def qidToTypeName qid = printQualifiedId qid

  op qidToOperation : QualifiedId -> MetaslangProofChecker.Fixity -> Operation
  def qidToOperation qid fxty = (printQualifiedId qid,fxty)

  op newVar : SpecCalc.Env Variable
  def newVar = {
    n <- freshNat;   % in the Specware monad
    return (abbr n)
  }

  op mapListToFSeq : fa(a,b) (a -> b) -> List a -> FSeq b
  def mapListToFSeq f list = foldl (fn (x,fSeq) -> (f x) |> fSeq) empty list

  op MSToPCTranslateMonad.mapListToFSeq : fa(a,b) (a -> SpecCalc.Env b) -> List a -> SpecCalc.Env (FSeq b)
  def MSToPCTranslateMonad.mapListToFSeq f list =
    case list of
      | [] -> return empty
      | x::xs -> {
          xNew <- f x;
          xsNew <- mapListToFSeq f xs;
          return (xNew |> xsNew)
        }

  op MSToPCTranslateMonad.mapQualifierMapToFSeq : fa(a,b) (Qualifier * Id * a -> SpecCalc.Env b) -> AQualifierMap a -> SpecCalc.Env (FSeq b)
  def MSToPCTranslateMonad.mapQualifierMapToFSeq f qMap =
    let
      def newF (qual,id,a,rest) = {
        xNew <- f (qual,id,a); 
        return (xNew |> rest)
      }
    in
      foldOverQualifierMap newF empty qMap

  op primNat : Nat -> Expression
  def primNat n =
    if n = 0 then
      OPI (qidToOperation (Qualified ("Nat","zero")) (embed prefix),empty)
    else
      (OPI (qidToOperation (Qualified ("Nat","succ")) (embed prefix),empty)) @ (primNat (n - 1))

  % Construct an expression in the proof checker's abstract syntax that encodes the given string.
  op primString : String -> Expression
  def primString str =
    (OPI (qidToOperation (Qualified ("String","implode")) (embed prefix),empty)) @ (primList charType (List.map primChar (explode str)))

  op charType : Type
  def charType = TYPE (qidToTypeName (Qualified ("Char","Char")),empty)

  % Construct a expression in the proof checker's abstract syntax that encodes the given char.
  op primChar : Char -> Expression
  def primChar c = (OPI (qidToOperation (Qualified ("Char","chr")) (embed prefix),empty)) @ (primNat (ord c))

  % Construct a expression in the proof checker's abstract syntax that encodes the given
  % list of elements of the given type.
  op primList : Type -> List Expression -> Expression
  def primList typ l =
    let nil = (EMBED (listType typ, idToConstructor "Nil")) @ MTREC in
    let def cons (a, l) =
      let p = PAIR (typ, listType typ, a, l) in
      (EMBED (listType typ, idToConstructor "Cons")) @ p
    in
      List.foldr cons nil l

  op listType : Type -> Type
  def listType typ = TYPE (qidToTypeName (Qualified ("List","List")), single typ)

  op findInMap : [a] AQualifierMap a -> QualifiedId -> SpecCalc.Env a
  def findInMap map (qid as (Qualified (qualifier,id))) =
    case findAQualifierMap (map,qualifier,id) of
      | None -> raise (Fail ("translateMSToPC: failed to find qualified id: " ^ (printQualifiedId qid)))
      | Some x -> return x

  % Simple test to see if a type is a recursive sum of products.  The test returns
  % true if the type is a coproduct and if each summand is a recursive reference
  % to the same type, or a product were each field is either a type variable
  % or a recursive reference to the same type. This will, for example, handle, 
  % polymorphic lists but not monomorphic lists as there can be only recursive references
  % to the same type.
  %
  % A more comprehensive scheme would need handle mutually recursive type definitions
  % presumably using some sort of toplogical sort.
 
  op recursiveSumOfProducts? : Spec -> QualifiedId -> SpecCalc.Env Boolean
  def recursiveSumOfProducts? spc qid = {
    typeInfo <- findInMap spc.sorts qid;
    case typeInfo.dfn of
      | Pi (tyVars,CoProduct (pairs,_),_) -> 
          let
            def checkSums sums =
              case sums of
                | [] -> true
                | (name, None)::rest -> checkSums rest
                | (name, Some (TyVar (tVar,_)))::rest -> checkSums rest
                | (name, Some (Base (otherQid,typs,_)))::rest ->
                    if (qid = otherQid) then
                      checkSums rest
                    else
                      false
                | (name, Some (Product (fields,_)))::rest -> 
                    if checkFields fields then
                      checkSums rest
                    else
                      false
            def checkFields fields =
              case fields of
                | [] -> true
                | (name, TyVar (tVar,_))::rest -> checkFields rest
                | (name, Base (otherQid,typs,_))::rest ->
                    if (qid = otherQid) then
                      checkFields rest
                    else
                      false
          in
            return (checkSums pairs)
      | _ -> return false
    }

  op convertFixity : MetaSlang.Fixity ->  MetaslangProofChecker.Fixity
  def convertFixity fxty =
    case fxty of
      | Nonfix -> embed prefix
      | Infix _ -> infix
      | Unspecified -> embed prefix

    % computeUpperMatrix pairs =
      % case pairs of
        % | [] -> []
        % | sumTerm::rest -> (map (fn x -> (sumTerm,x)) rest)  List.++  (computeUpperMatrix rest)
            %  
    % (a::l)  zip a with l and then do the same to l
endspec
