spec 
type boolex = 
  | Const Boolean
  | Var Nat
  | Neg boolex
  | And (boolex \_times boolex)

op bvalue:
  boolex \_rightarrow (Nat \_rightarrow Boolean) \_rightarrow Boolean
def bvalue be env =
  case be of
    | Const b  \_rightarrow b
    | Var x    \_rightarrow env x
    | Neg b    \_rightarrow \_not (bvalue b env)
    | And(b,c) \_rightarrow bvalue b env
                 \_and bvalue c env

type ifex = | CIF Boolean | VIF Nat | IF (ifex \_times ifex \_times ifex)

op valif : ifex \_rightarrow (Nat \_rightarrow Boolean) \_rightarrow Boolean
def valif be env =
  case be of
    | CIF b    \_rightarrow b
    | VIF x    \_rightarrow env x
    | IF(b,t,e) \_rightarrow if valif b env then valif t env
		     else valif e env

op bool2if : boolex \_rightarrow ifex
def bool2if be =
  case be of
    | Const b   \_rightarrow CIF b
    | Var x     \_rightarrow VIF x
    | Neg b     \_rightarrow IF (bool2if b, CIF false, CIF true)
    | And (b,c) \_rightarrow IF (bool2if b, bool2if c, CIF false)

theorem valif is
  \_forall(b,env) valif (bool2if b) env = bvalue b env
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof


op normif : ifex \_rightarrow ifex \_rightarrow ifex \_rightarrow ifex
def normif ie t e =
  case ie of
    | CIF b  \_rightarrow IF (CIF b, t, e)
    | VIF x  \_rightarrow IF (VIF x, t, e)
    | IF( b, e1, e2) \_rightarrow normif b (normif e1 t e) (normif e2 t e)

op norm : ifex \_rightarrow ifex
def norm ie =
  case ie of
    | CIF b    \_rightarrow (CIF b)
    | VIF x    \_rightarrow (VIF x)
    | IF(b, t, e) \_rightarrow normif b (norm t) (norm e)

proof Simplification end-proof
theorem Simplify_valif_normif is  %[simp]:
  \_forall(b,env,t,e) valif (normif b t e) env = valif (IF(b, t, e)) env
  proof Isa \_forallt e.
    apply(induct_tac b)
    apply(auto)
  end-proof

theorem  valif_main is
  \_forall(b,env) valif (norm b) env = valif b env
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof

op normal: ifex \_rightarrow Boolean
def normal ie =
  case ie of
    | CIF b    \_rightarrow true
    | VIF x    \_rightarrow true
    | IF(b, t, e) \_rightarrow (normal t \_and normal e
		   \_and (case b
			of CIF v \_rightarrow true
			 | VIF v \_rightarrow true
			 | IF(x, y, z) \_rightarrow false))


proof Simplification end-proof
theorem Simplify_normal_normif is  % [simp]
  \_forall (b, t, e) normal(normif b t e) = (normal t \_and normal e)
  proof Isa \_forallt e.
    apply(induct_tac b)
    apply(auto)
  end-proof

theorem normal_norm is
  \_forall(b) normal (norm b)
  proof Isa
    apply(induct_tac b)
    apply(auto)
  end-proof

endspec
