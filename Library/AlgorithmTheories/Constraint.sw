(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
          Abstract Constraint Theory

Notes: the representation and processing of constraints as objects depends on
the operations we need to perform.  Here are the basic operations that require
no internal structure to Constraints:

 - satisfies: Constraint -> Valuation -> Bool
 - Simplify : Constraint -> Valuation -> Constraint  (aka interpret, eval, PE)

These ops require that Constraints have Vars and Terms:
 - varsOf: Constraint -> Set Var
 - subst: Var -> Term -> Constraint -> Constraint

Inference rules require yet more structure:
 - resolve requires vars, and, exists
 - formArcConsistencyInstances requires forall/exists, implies, var membership in set

For constraint solvers we need to formulate formulas over the extended
vocabulary of the concrete domain (valuations, Constraint) and abstract domain
(partial valuations/maps and propagation rules and pruning tests,...)

 - pruning requires vars, and, exists, concrete&abstract valuation vars&ops

For Definite Constraints we need a semilattice structure and mono/anti-tone
predicates.

*)

Valuation = spec
  import /Library/DataStructures/StructuredTypes
         %../Library/StructuredTypes   % not using Specware library (maps problem)
  type Variable
  type Value
  type Valuation = Map(Variable, Value)
  op   valuationVars (v:Valuation): Set Variable = domain(v)
end-spec


(* ---------------- Syntax:  Constraints -----------------------------

   We define an abstract syntax for first-order constraints.
   Specialized structure can be obtained by subtracting and extending.
   Semantics of constraints builds on this spec.

  Issues:
   - to formalize substitution requires var, term, and Map(var,term)
     i.e. the generic structure of constraints
   - we could restrict to first-order structure and logic
   - we avoid the elaboration of type structure of terms ...

*)

Constraint = spec
  import Valuation

  type Constraint
  op varsOf: Constraint -> Set Variable

% these are needed to specify resolution
  % op mkConjunction: Constraint -> Constraint -> Constraint
  % op mkExistential: Variable   -> Constraint -> Constraint

(* Constructors of constraint terms: try letting codomain define these
  type TermOp
  type Atom = | const Value | var Variable  % should this be a subtype of Term?
  type Term = | const Value | var Variable | trmop TermOp
  op varsOfT: Term -> Set Variable

  op mkTrue : Constraint
  op mkFalse: Constraint
  op isTrue (c:Constraint): Bool = (c = mkTrue)
  op isFalse(c:Constraint): Bool = (c = mkFalse)

  op mkNegation:    Constraint -> Constraint -> Constraint
  op mkConjunction: Constraint -> Constraint -> Constraint
  op mkDisjunction: Constraint -> Constraint -> Constraint
  op mkExistential: Variable   -> Constraint -> Constraint
  op mkUniversal:   Variable   -> Constraint -> Constraint

% probably need to ensure well-typed substitutivity here
  op substC(v:Variable)(trm:Term)(C:Constraint): Constraint
  op substT(v:Variable)(val:Value)(trm:Term)   : Term

  axiom varsOf_SubstC is
    fa(C:Constraint,v:Variable,trm:Term)
      (varsOf(substC v trm C) = set_delete(v,varsOf(C)))

  axiom varsOf_SubstT is
    fa(C:Constraint,v:Variable,val:Value,trm:Term)
      (varsOfT(substT v val trm) = set_delete(v,varsOfT(trm)))
*)

end-spec


(* ---------------------- Constraint Semantics  ----------------------

The essence of constraint logic is the satisfaction relation between
valuation (model) and constraint (sentence).  

The following ops could be specified, but they do not seem to be
needed formally - useful in papers and maybe in spec predicates?

  op satisfiable : Constraint -> Bool
  op satisfiableCs: Set Constraint -> Bool
  op valid : Constraint -> Bool
  op subsumes: Constraint -> Constraint -> Bool
*)

Logic_param = spec
  import Constraint %, Valuation

%  op evalT: Term -> Valuation -> Value
  op satisfiesC(c:Constraint)(v:Valuation | (varsOf c) subset (valuationVars v)):Bool

  op satisfiableCs: Set Constraint -> Bool
  axiom def_of_satisfiableCs is
    fa(Cs:Set Constraint) satisfiableCs Cs = 
      (ex(vm:Valuation)fa(c:Constraint)(c in? Cs && varsOf c = domain vm
                                        => satisfiesC c vm))
end-spec

Logic = spec
  import Logic_param

  op satisfiesCs(Cs:Set Constraint)(v:Valuation):Bool =
      set_fold true
               (fn(b:Bool,c:Constraint) -> b && (satisfiesC c v))
               Cs
  op entails(c1:Constraint)(c2:Constraint):
            {b:Bool | fa(v:Valuation)(satisfiesC c1 v => satisfiesC c2 v)}

  op entailsCs(cs1:Set Constraint)(c2:Constraint):
            {b:Bool | fa(v:Valuation)
                           ((fa(c1:Constraint)(c1 in? cs1 => satisfiesC c1 v)) 
                              => satisfiesC c2 v)}

  op equivalentC(c1:Constraint)(c2:Constraint):
                {b:Bool | b = (entails c1 c2) && (entails c2 c1)}
end-spec  % Logic
     

(* ------------------- Inference mechanisms ----------------------------- 
We could define cases based on the constructors for Constraints,
to the extent they exist:  e.g.
 simplify (mkAnd C mkTrue) = C
 simplify (mkAnd mkTrue C) = C
 simplify (mkAnd C mkFalse) = mkFalse
 simplify (mkAnd mkFalse C) = mkFalse
*)

Inference = spec
  import Logic

  op simplify(c:Constraint):  % how to specify the optimization aspect?
             {simp:Constraint | equivalentC c simp}
  op resolve(c1:Constraint)(c2:Constraint)   % logic-independent spec for resolution
            (v:Variable | v in? (varsOf c1)  && v in? (varsOf c2)):Constraint
%            {c0:Constraint | equivalentC c0 (mkExistential v (mkConjunction c1 c2))}

(* a pure functional spec for a Constraint Solver
  op Solve (Cs: Set Constraint): 
          {ov: Option Valuation |
             case ov of
               | None -> ~(satisfiableCs(Cs))
               | Some vm -> satisfiesCs Cs vm}
*)

end-spec  % Inference

