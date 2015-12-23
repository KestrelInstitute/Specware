(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* 

       Galois Connections for Global Search/CBDL
  
  This file includes an abstract spec for a Galois Connection that is
  renamed to be suitable as an overapproximating abstract domain for
  search and propagation in GS_CDB.  That is, GS_CDB is parametric on
  GS_GC.   The concrete domain is fixed as (Set Valuation).

  The other specs in this file provide alternative interpretations of
  this overapproximating abstract domain.

  We shouldn't ever need to supply definitions for concretize and
  abstract - they are useful in specifications (e.g. in
  pre/post-conditions and axioms) but aren't used in actual
  computation.

*)

% GS_GC = 
spec
   import Constraint#Valuation
   import translate /Library/Math/Semilattice#BoundedJoinSemilattice by  
      {A      +-> Rhat,                        
       <=     +-> RefinesTo,
       bot    +-> RhatBot,
       join   +-> RhatJoin}

  op concretize: Rhat -> Set Valuation                 % gamma
  op abstract  : Set Valuation -> Rhat                 % alpha
  op beta      : Valuation     -> Rhat                 % beta
  axiom Overapprox_Galois_Connection_C is
     fa(S:Set Valuation) S subset (concretize (abstract S))
  axiom Overapprox_Galois_Connection_A is   % typically this is equality
     fa(rhat:Rhat) rhat RefinesTo (abstract (concretize rhat))

  axiom RhatBot_is_comprehensive is    % i.e. R = concretize RhatBot
    fa(z:Valuation)( z in? concretize RhatBot )
  axiom beta_isomorphism is     %  gamma beta z = {z}
    fa(z:Valuation,y:Valuation)( y in? (concretize (beta z)) = (y=z) )

end-spec 


