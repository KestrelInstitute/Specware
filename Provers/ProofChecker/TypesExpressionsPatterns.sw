spec

  (* Here we put types, expressions, and patterns together. *)

  import Types, Expressions, Patterns

  type TypeOrExprOrPatt =
    | typ(*e*) Type
    | expr     Expression
    | patt     Pattern

  (* The (meta) type definitions only express fixpoints, not necessarily least
  ones. We enforce least ones by means of a (quite verbose) induction axiom on
  types, expressions, and patterns. *)

  axiom inductionTypesExpressionsPatterns is
    fa (pred : Predicate TypeOrExprOrPatt)
  %%%%% types:
      pred (typ boolean)
   && (fa (tv:TypeVariable) pred (typ (variable tv)))
   && (fa (t1:Type, t2:Type)
         pred (typ t1) && pred (typ t2)
      => pred (typ (arrow (t1, t2))))
   && (fa (cS:FSeqNE Constructor, tS?:FSeqNE(Option Type))
         (fa(t) Some t in? tS? => pred (typ t))
      => pred (typ (sum (cS, tS?))))
   && (fa (tc:NaryTypeConstruct, tS:FSeq Type)
         (fa(t) t in? tS => pred (typ t))
      => pred (typ (nary (tc, tS))))
   && (fa (tc:SubOrQuotientTypeConstruct, t:Type, e:Expression)
         pred (typ t) && pred (expr e)
      => pred (typ (subQuot (tc, t, e))))
  %%%%% expressions:
   && (fa (eo:NullaryExprOperator)
         pred (expr (nullary eo)))
   && (fa (eo:UnaryExprOperator, e:Expression)
         pred (expr e)
      => pred (expr (unary(eo, e))))
   && (fa (eo:BinaryExprOperator, e1:Expression, e2:Expression)
         pred (expr e1) && pred (expr e2)
      => pred (expr (binary (eo, e1, e2))))
   && (fa (e0:Expression, e1:Expression, e2:Expression)
         pred (expr e0) && pred (expr e1) && pred (expr e2)
      => pred (expr (ifThenElse (e0, e1, e2))))
   && (fa (eo:NaryExprOperator, eS:FSeq Expression)
         (fa(e) e in? eS => pred (expr e))
      => pred (expr (nary (eo, eS))))
   && (fa (eo:BindingExprOperator,
           vS:FSeqNE Variable, tS:FSeqNE Type, e:Expression)
         (fa(t) t in? tS => pred (typ t))
      && pred (expr e)
      => pred (expr (binding (eo, zip (vS, tS), e))))
   && (fa (o:Operation, tS:FSeq Type)
         (fa(t) t in? tS => pred (typ t))
      => pred (expr (opInstance (o, tS))))
   && (fa (t:Type, c:Constructor)
         pred (typ t)
      => pred (expr (embedder (t, c))))
   && (fa (e:Expression, pS:FSeqNE Pattern, eS:FSeqNE Expression)
         length pS = length eS
      && (fa(p) p in? pS => pred (patt p))
      && (fa(e1) e1 in? eS => pred (expr e1))
      => pred (expr (cas (e, zip (pS, eS)))))
   && (fa (vS:FSeqNE Variable, tS:FSeqNE Type, eS:FSeq Expression,
           e:Expression)
         length vS  = length tS
      && length tS = length eS
      && (fa(t) t in? tS => pred (typ t))
      && (fa(e1) e1 in? eS => pred (expr e1))
      && pred (expr e)
      => pred (expr (recursiveLet (zip (zip (vS, tS), eS), e))))
   && (fa (p:Pattern, e:Expression, e1:Expression)
         pred (patt p)
      && pred (expr e)
      && pred (expr e1)
      => pred (expr (nonRecursiveLet (p, e, e1))))
  %%%%% patterns:
   && (fa (v:Variable, t:Type)
         pred (typ t)
      => pred (patt (variable (v, t))))
   && (fa (t:Type, c:Constructor, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (embedding (t, c, p))))
   && (fa (fS:FSeq Field, pS:FSeq Pattern)
         (fa(p) p in? pS => pred (patt p))
      => pred (patt (record (fS, pS))))
   && (fa (v:Variable, t:Type, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (alias (v, t, p))))

endspec
