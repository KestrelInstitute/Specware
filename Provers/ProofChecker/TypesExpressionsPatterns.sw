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
   && (fa (tVar:TypeVariable) pred (typ (variable tVar)))
   && (fa (t1:Type, t2:Type)
         pred (typ t1) && pred (typ t2)
      => pred (typ (arrow (t1, t2))))
   && (fa (constrs:FSeqNE Constructor, types?:FSeqNE(Option Type))
         (fa(t) Some t in? types? => pred (typ t))
      => pred (typ (sum (constrs, types?))))
   && (fa (ntc:NaryTypeConstruct, types:FSeq Type)
         (fa(t) t in? types => pred (typ t))
      => pred (typ (nary (ntc, types))))
   && (fa (sqtc:SubOrQuotientTypeConstruct, t:Type, e:Expression)
         pred (typ t) && pred (expr e)
      => pred (typ (subQuot (sqtc, t, e))))
  %%%%% expressions:
   && (fa (neo:NullaryExprOperator)
         pred (expr (nullary neo)))
   && (fa (uep:UnaryExprOperator, e:Expression)
         pred (expr e)
      => pred (expr (unary(uep, e))))
   && (fa (beo:BinaryExprOperator, e1:Expression, e2:Expression)
         pred (expr e1) && pred (expr e2)
      => pred (expr (binary (beo, e1, e2))))
   && (fa (e0:Expression, e1:Expression, e2:Expression)
         pred (expr e0) && pred (expr e1) && pred (expr e2)
      => pred (expr (ifThenElse (e0, e1, e2))))
   && (fa (neo:NaryExprOperator, exprs:FSeq Expression)
         (fa(e) e in? exprs => pred (expr e))
      => pred (expr (nary (neo, exprs))))
   && (fa (beo:BindingExprOperator, var:Variable, t:Type, e:Expression)
         pred (typ t) && pred (expr e)
      => pred (expr (binding (beo, (var, t), e))))
   && (fa (meo:MultiBindingExprOperator,
           vars:FSeqNE Variable, types:FSeqNE Type, e:Expression)
         (fa(t) t in? types => pred (typ t))
      && pred (expr e)
      => pred (expr (multiBinding (meo, zip (vars, types), e))))
   && (fa (opp:Operation, types:FSeq Type)
         (fa(t) t in? types => pred (typ t))
      => pred (expr (opInstance (opp, types))))
   && (fa (t:Type, constr:Constructor)
         pred (typ t)
      => pred (expr (embedder (t, constr))))
   && (fa (e:Expression, patts:FSeqNE Pattern, exprs:FSeqNE Expression)
         length patts = length exprs
      && (fa(p) p in? patts => pred (patt p))
      && (fa(e1) e1 in? exprs => pred (expr e1))
      => pred (expr (cas (e, zip (patts, exprs)))))
   && (fa (vars:FSeqNE Variable, types:FSeqNE Type, exprs:FSeq Expression,
           e:Expression)
         length vars  = length types
      && length types = length exprs
      && (fa(t) t in? types => pred (typ t))
      && (fa(e1) e1 in? exprs => pred (expr e1))
      && pred (expr e)
      => pred (expr (recursiveLet (zip (zip (vars, types), exprs), e))))
   && (fa (p:Pattern, e:Expression, e1:Expression)
         pred (patt p)
      && pred (expr e)
      && pred (expr e1)
      => pred (expr (nonRecursiveLet (p, e, e1))))
  %%%%% patterns:
   && (fa (var:Variable, t:Type)
         pred (typ t)
      => pred (patt (variable (var, t))))
   && (fa (t:Type, constr:Constructor, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (embedding (t, constr, p))))
   && (fa (fields:FSeq Field, patts:FSeq Pattern)
         (fa(p) p in? patts => pred (patt p))
      => pred (patt (record (zip (fields, patts)))))
   && (fa (var:Variable, t:Type, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (alias ((var, t), p))))

endspec
