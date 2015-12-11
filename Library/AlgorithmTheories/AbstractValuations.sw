(*  

     This file contains several specs for abstract domains over the
     concrete domain of Valuations = Map(Variable,Value).   They
     serve as alternative codomains for the GS_Galois_Connection spec.

*)


(* -------------------------------------------------------------------
     Spec for maps into the 4-valued boolean lattice, which represents
     partial maps.
*)

Valuation4 = spec
  import ../Math/Logic4, Constraint#Valuation

  type Value = Bool                            % concrete Valuations
  type Valuation4 = Map(Variable, Logic4)        % abstract Valuations

  op V4le (val1:Valuation4, val2:Valuation4) infixl 20 : Bool =
    set_fold (true)
             (fn (b:Bool, var:Variable) ->
               (case (apply val2 var) of
                  | Some v -> Logic4Le(TMApply(val1,var), v)   && b
                  | None   -> Logic4Le(TMApply(val1,var), Bot) && b))
             (domain(val1))

  op V4bot: Valuation4   % can't give def until we know the given variables
        % set_fold empty_map
        %     (fn (vm:VarMap, var:Variable) 
        %      -> update vm var ((TMApply(vm1,var)) \/ (TMApply(vm2,var))))
        %     (domain(vm1))

  op V4join(val1:Valuation4, val2:Valuation4): Valuation4 =
     set_fold (val1)
              (fn(newval:Valuation4, v:Variable) ->
	         (case (apply val1 v) of
                   | Some b4 -> (update newval v (Join4(b4,TMApply(val2,v))))
                   | None    -> (update newval v (TMApply(val2,v)))))
	      (domain(val2))

  op V4gamma: Valuation4 -> Set Valuation
  op V4alpha: Set Valuation -> Valuation4

  axiom V4gamma_def is
     fa(pv:Valuation4, m:Valuation) 
       (m in? (V4gamma pv)) = (pv V4le (V4beta m))

  def V4beta(val: Valuation): Valuation4 = ValtoVal4 val

  def ValtoVal4(val: Valuation): Valuation4 =
    set_fold (empty_map)
             (fn (val4:Valuation4, var:Variable) 
              -> let newval:Logic4 = BooltoLogic4(TMApply(val, var)) in
                update val4 var newval)
             (domain(val))

  def Val4toVal(val4:Valuation4): Valuation =   % was Val4toVal
    set_fold (empty_map)
             (fn (val:Valuation, var:Variable) 
              -> let newval:Bool = logic4toBool(TMApply(val4, var)) in
                update val var newval)
             (domain(val4))
             
  op convertExternalValuation4 (sol:List Integer) : Map(Integer, Logic4) =
    if empty?(sol)
      then empty_map
    else update (convertExternalValuation4(tail(sol))) 
                (abs(head(sol))) 
                (if head(sol)>0 then True else False)

end-spec

GC_to_Valuation4 = morphism GS_Galois_Connection -> Valuation4
              { Rhat         +-> Valuation4                        
              , RefinesTo    +-> V4le
              , RhatBot      +-> V4bot
              , RhatJoin     +-> V4join
              , concretize   +-> V4gamma
              , abstract     +-> V4alpha
              , beta         +-> V4beta
              } 


(* --------- OverApproximating Valuations via Partial Valuations ------------ 
This is for flat domains; i.e. with no intrinsic order other than equality.

Issue:  How do we express a polymorphic semilattice?
   e.g. the le order requires the underlying order as a (2nd-order) parameter ...

  op [a] ScottLe (sv1:Scott a)(sv2:Scott a):Bool =
      case sv1 of
        | Bottom -> true
        | ok sv -> 
        | Top -> (sv2 = Top)

  import translate /Library/Math/Semilattice#BoundedJoinSemilattice 
         by {A    +-> Scott a, 
             <=   +-> Scottle, 
             join +-> Scottjoin, 
             bot  +-> Bottom}
*)

PartialValuation = spec
  import Constraint#Valuation

  type Scott a = (| Bottom | Ok a | Top)

% a Scott domain forms a lattice, here's the partial order (over Value):
  op SValueLe infixl 20: Scott Value * Scott Value -> Bool

  op SValueLe (sv1:Scott Value,sv2:Scott Value): Bool =
     (case sv1 of
       | Bottom -> true
       | Ok val1 -> (case sv2 of
                      | Bottom -> false
                      | Ok val2 -> if val1=val2 then true else false
                      | Top -> true)
       | Top -> (sv2=Top))

% ... and here's the join/lub:
  op SValueJoin infixl 20 :Scott Value * Scott Value -> Scott Value
  op SValueJoin (sv1:Scott Value,sv2:Scott Value): Scott Value =
     (case sv1 of
       | Bottom -> sv2
       | Ok val1 -> (case sv2 of
                      | Bottom -> Bottom
                      | Ok val2 -> if val1=val2 then Ok val1 else Top
                      | Top -> Top)
       | Top -> Top)

  type PartialValuation = Map(Variable, Scott Value)
  op PVVars (pv:PartialValuation): Set Variable = domain(pv)

  op PVbot:PartialValuation = empty_map

% lift the value partial order to PV's
  op PVle infixl 20:PartialValuation * PartialValuation -> Bool

  op PVle (pv1:PartialValuation,pv2:PartialValuation): Bool =
   set_fold true
            (fn (b:Bool, var:Variable) 
             -> b && ((TMApply(pv1, var)) SValueLe (TMApply(pv2,var))))
            (domain(pv1))

  op PVjoin infixl 20:PartialValuation * PartialValuation -> PartialValuation

  op PVjoin (pv1:PartialValuation, pv2:PartialValuation): PartialValuation =
   set_fold empty_map
            (fn (pv:PartialValuation, var:Variable) 
             -> update pv var ((TMApply(pv1,var)) SValueJoin (TMApply(pv2,var))))
            (domain(pv1))
       
% The Galois Connection between Valuation and PartialValuation:

  op PVgamma: PartialValuation -> Set Valuation
  op PValpha: Set Valuation -> PartialValuation
  op PVbeta : Valuation -> PartialValuation
  axiom PVgamma_def is
     fa(pv:PartialValuation, m:Valuation) 
       (m in? (PVgamma pv)) = (pv PVle (PVbeta m))
(* to finish:
  axiom PValpha_def is
     fa(pv:PartialValuation, ms:Set Valuation, var:Variable) 
        TMApply(pv,var) = join {TMApply(m,var) | m in ms}
  axiom PVbeta_def is
     fa(pv:PartialValuation, m:Valuation, var:Variable) 
        TMApply(pv,var) = ok (TMApply(m,var))
  GC axioms ...
*)

end-spec   % PartialValuation  Scott domains

GC_to_PV = morphism GS_Galois_Connection -> PartialValuation
              {Rhat         +-> PartialValuation,                        
               RefinesTo    +-> PVle,
               RhatBot      +-> PVbot,
               RhatJoin     +-> PVjoin,
               concretize   +-> PVgamma,
               abstract     +-> PValpha,
               beta         +-> PVbeta
               } 

(* ------ OverApproximating Valuations via Value sets for each variable ------- 

We overapproximate valuations by means of maps from each variable to its
current set/domain of candidate values.

*)

VarMap = spec
  import Constraint#Valuation

  type VarMap = Map(Variable, Set Value)
%  op VarMapVars (v:VarMap): Set Variable = domain(v)

% The join semilattice structure on (Set Value) lifts to VarMaps
  op VMle infixl 20:VarMap * VarMap -> Bool
  op VMle (vm1:VarMap,vm2:VarMap): Bool =
   set_fold true
            (fn (b:Bool, var:Variable) 
             -> b && ((TMApply(vm1, var)) subset (TMApply(vm2,var))))
            (domain(vm1))

  op VMjoin infixl 20:VarMap * VarMap -> VarMap
  op VMjoin (vm1:VarMap, vm2:VarMap): VarMap =
   set_fold empty_map
            (fn (vm:VarMap, var:Variable) 
             -> update vm var ((TMApply(vm1,var)) \/ (TMApply(vm2,var))))
            (domain(vm1))

  op VMbot:VarMap  % can't give def until we know the given variables
       
% The Galois Connection between Valuation and VarMap:

  op VMgamma: VarMap -> Set Valuation
  op VMalpha: Set Valuation -> VarMap
  op VMbeta : Valuation -> VarMap
  axiom VMgamma_def is
     fa(vm:VarMap, m:Valuation) 
       (m in? (VMgamma vm)) = ((VMbeta m) VMle vm)
  axiom VMbeta_def is
     fa(vm:VarMap, m:Valuation, var:Variable) 
        TMApply(vm,var) = set_insert(TMApply(m,var),empty_set)

(* to finish:
  axiom VMalpha_def is
     fa(vm:VarMap, ms:Set Valuation, var:Variable) 
        TMApply(vm,var) = join {TMApply(m,var) | m in ms}
  GC axioms as theorems
*)

end-spec   % VarMap

GC_to_VM = morphism GS_Galois_Connection -> VarMap
              {Rhat         +-> VarMap,                        
               RefinesTo    +-> VMle,
               RhatBot      +-> VMbot,
               RhatJoin     +-> VMjoin,
               concretize   +-> VMgamma,
               abstract     +-> VMalpha,
               beta         +-> VMbeta
               } 
