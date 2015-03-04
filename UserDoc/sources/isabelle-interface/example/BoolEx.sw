spec 
type boolex = 
  | Const Bool
  | Var Nat
  | Neg boolex
  | And (boolex * boolex)

op bvalue:
  boolex -> (Nat -> Bool) -> Bool
def bvalue be env =
  case be of
    | Const b  -> b
    | Var x    -> env x
    | Neg b    -> ~ (bvalue b env)
    | And(b,c) -> bvalue b env
                 && bvalue c env

type ifex = | CIF Bool | VIF Nat | IF (ifex * ifex * ifex)

op valif : ifex -> (Nat -> Bool) -> Bool
def valif be env =
  case be of
    | CIF b    -> b
    | VIF x    -> env x
    | IF(b,t,e) -> if valif b env then valif t env
		     else valif e env

op bool2if : boolex -> ifex
def bool2if be =
  case be of
    | Const b   -> CIF b
    | Var x     -> VIF x
    | Neg b     -> IF (bool2if b, CIF false, CIF true)
    | And (b,c) -> IF (bool2if b, bool2if c, CIF false)

theorem valif is
  fa(b,env) valif (bool2if b) env = bvalue b env
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof


op normif : ifex -> ifex -> ifex -> ifex
def normif ie t e =
  case ie of
    | CIF b  -> IF (CIF b, t, e)
    | VIF x  -> IF (VIF x, t, e)
    | IF( b, e1, e2) -> normif b (normif e1 t e) (normif e2 t e)

op norm : ifex -> ifex
def norm ie =
  case ie of
    | CIF b    -> (CIF b)
    | VIF x    -> (VIF x)
    | IF(b, t, e) -> normif b (norm t) (norm e)

theorem Simplify_valif_normif is
  fa(b,env,t,e) valif (normif b t e) env = valif (IF(b, t, e)) env
  proof Isa [simp] fa t e.
    apply(induct_tac b)
    apply(auto)
  end-proof

theorem  valif_main is
  fa(b,env) valif (norm b) env = valif b env
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof

op normal: ifex -> Bool
def normal ie =
  case ie of
    | CIF b    -> true
    | VIF x    -> true
    | IF(b, t, e) -> (normal t && normal e
		   && (case b
			of CIF v -> true
			 | VIF v -> true
			 | IF(x, y, z) -> false))


theorem Simplify_normal_normif is 
  fa (b, t, e) normal(normif b t e) = (normal t && normal e)
  proof Isa [simp] fa t e.
    apply(induct_tac b)
    apply(auto)
  end-proof

theorem normal_norm is
  fa(b) normal (norm b)
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof

end-spec
