(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

import CTarget

%% Injectivity theorems (rewrite versions)
theorem  scharOfMathInt_inject is fa(x:Int, y:Int) (x in? rangeOfSchar  && y in? rangeOfSchar ) => ( scharOfMathInt x =  scharOfMathInt y) = (x = y)
theorem sshortOfMathInt_inject is fa(x:Int, y:Int) (x in? rangeOfSshort && y in? rangeOfSshort) => (sshortOfMathInt x = sshortOfMathInt y) = (x = y)
theorem   sintOfMathInt_inject is fa(x:Int, y:Int) (x in? rangeOfSint   && y in? rangeOfSint  ) => (  sintOfMathInt x =   sintOfMathInt y) = (x = y)
theorem  slongOfMathInt_inject is fa(x:Int, y:Int) (x in? rangeOfSlong  && y in? rangeOfSlong ) => ( slongOfMathInt x =  slongOfMathInt y) = (x = y)
theorem sllongOfMathInt_inject is fa(x:Int, y:Int) (x in? rangeOfSllong && y in? rangeOfSllong) => (sllongOfMathInt x = sllongOfMathInt y) = (x = y)

%% Injectivity theorems ("rule" versions)
theorem  scharOfMathInt_inject_fw is fa(x:Int, y:Int) (x in? rangeOfSchar  && y in? rangeOfSchar ) => ( scharOfMathInt x =  scharOfMathInt y) => (x = y)
theorem sshortOfMathInt_inject_fw is fa(x:Int, y:Int) (x in? rangeOfSshort && y in? rangeOfSshort) => (sshortOfMathInt x = sshortOfMathInt y) => (x = y)
theorem   sintOfMathInt_inject_fw is fa(x:Int, y:Int) (x in? rangeOfSint   && y in? rangeOfSint  ) => (  sintOfMathInt x =   sintOfMathInt y) => (x = y)
theorem  slongOfMathInt_inject_fw is fa(x:Int, y:Int) (x in? rangeOfSlong  && y in? rangeOfSlong ) => ( slongOfMathInt x =  slongOfMathInt y) => (x = y)
theorem sllongOfMathInt_inject_fw is fa(x:Int, y:Int) (x in? rangeOfSllong && y in? rangeOfSllong) => (sllongOfMathInt x = sllongOfMathInt y) => (x = y)

%% Injectivity theorems (rewrite versions)
theorem  ucharOfMathInt_inject is fa(x:{i:Int | i in? rangeOfUchar }, y:{i:Int | i in? rangeOfUchar }) ( ucharOfMathInt x =  ucharOfMathInt y) = (x = y)
theorem ushortOfMathInt_inject is fa(x:{i:Int | i in? rangeOfUshort}, y:{i:Int | i in? rangeOfUshort}) (ushortOfMathInt x = ushortOfMathInt y) = (x = y)
theorem   uintOfMathInt_inject is fa(x:{i:Int | i in? rangeOfUint  }, y:{i:Int | i in? rangeOfUint  }) (  uintOfMathInt x =   uintOfMathInt y) = (x = y)
theorem  ulongOfMathInt_inject is fa(x:{i:Int | i in? rangeOfUlong }, y:{i:Int | i in? rangeOfUlong }) ( ulongOfMathInt x =  ulongOfMathInt y) = (x = y)
theorem ullongOfMathInt_inject is fa(x:{i:Int | i in? rangeOfUllong}, y:{i:Int | i in? rangeOfUllong}) (ullongOfMathInt x = ullongOfMathInt y) = (x = y)

%% Injectivity theorems ("rule" versions)
theorem  ucharOfMathInt_inject_fw is fa(x:{i:Int | i in? rangeOfUchar }, y:{i:Int | i in? rangeOfUchar }) ( ucharOfMathInt x =  ucharOfMathInt y) => (x = y)
theorem ushortOfMathInt_inject_fw is fa(x:{i:Int | i in? rangeOfUshort}, y:{i:Int | i in? rangeOfUshort}) (ushortOfMathInt x = ushortOfMathInt y) => (x = y)
theorem   uintOfMathInt_inject_fw is fa(x:{i:Int | i in? rangeOfUint  }, y:{i:Int | i in? rangeOfUint  }) (  uintOfMathInt x =   uintOfMathInt y) => (x = y)
theorem  ulongOfMathInt_inject_fw is fa(x:{i:Int | i in? rangeOfUlong }, y:{i:Int | i in? rangeOfUlong }) ( ulongOfMathInt x =  ulongOfMathInt y) => (x = y)
theorem ullongOfMathInt_inject_fw is fa(x:{i:Int | i in? rangeOfUllong}, y:{i:Int | i in? rangeOfUllong}) (ullongOfMathInt x = ullongOfMathInt y) => (x = y)




%% The use of :Nat in these causes the Isabelle theorem to have the most convenient form.
%%TODO ask for a way to omit the unnecessary subtype hypotheses from the translation of this.  then, kill mathIntOfUint_minus_alt below.
%%would like to be able to use this syntax: proof Isa -nosubtypes x y end-proof

theorem mathIntOfUint_minus is fa(x:Uint, y:Uint) mathIntOfUint (x -_uint y) = ((((mathIntOfUint x) - (mathIntOfUint y)) modF (2 *** int_bits)):Nat)
theorem mathIntOfUint_plus  is fa(x:Uint, y:Uint) mathIntOfUint (x +_uint y) = ((((mathIntOfUint x) + (mathIntOfUint y)) modF (2 *** int_bits)):Nat)
theorem mathIntOfUint_times is fa(x:Uint, y:Uint) mathIntOfUint (x *_uint y) = ((((mathIntOfUint x) * (mathIntOfUint y)) modF (2 *** int_bits)):Nat)

proof isa -verbatim
theorem Uint__subtype_pred_uintOfMathInt_plus1 [simp]:
  "\<lbrakk>n \<ge> 0 ;  ((n::int) < ((2::int) ^ C__int_bits) - 1 )\<rbrakk> \<Longrightarrow>
  ((C__Uint__subtype_pred (C__uintOfMathInt (1 + n))))"
  apply(rule C__Uint__subtype_pred_uintOfMathInt)
  apply(simp)
  done
end-proof

%% TODO How to restrict this to only apply only when n is a constant?
%% TODO Do we need the hypothesis?
theorem introduce_uintConstant   is fa(i:Int) (i in? rangeOfUint  ) => (  uintOfMathInt i) = (  uintConstant i dec)
theorem introduce_ulongConstant  is fa(i:Int) (i in? rangeOfUlong ) => ( ulongOfMathInt i) = ( ulongConstant i dec)
theorem introduce_ullongConstant is fa(i:Int) (i in? rangeOfUllong) => (ullongOfMathInt i) = (ullongConstant i dec)



(******************************** The Proofs ********************************)

proof isa scharOfMathInt_inject [simp]
  apply(simp add: C__scharOfMathInt__1_def C__scharOfMathInt__1__obligation_refine_def)
end-proof
proof isa sintOfMathInt_inject [simp]
  apply(simp add: C__sintOfMathInt__1_def C__sintOfMathInt__1__obligation_refine_def)
end-proof
proof isa sshortOfMathInt_inject [simp]
  apply(simp add: C__sshortOfMathInt__1_def C__sshortOfMathInt__1__obligation_refine_def)
end-proof
proof isa slongOfMathInt_inject [simp]
  apply(simp add: C__slongOfMathInt__1_def C__slongOfMathInt__1__obligation_refine_def)
end-proof
proof isa sllongOfMathInt_inject [simp]
  apply(simp add: C__sllongOfMathInt__1_def C__sllongOfMathInt__1__obligation_refine_def)
end-proof

proof isa mathIntOfUint_minus
  apply(simp add:  C__e_dsh_uint_def C__applyUint_def)
end-proof

proof isa mathIntOfUint_plus
  apply(simp add:  C__e_pls_uint_def C__applyUint_def)
end-proof

proof isa mathIntOfUint_times
  apply(simp add:  C__e_ast_uint_def C__applyUint_def)
end-proof



proof isa ucharOfMathInt_inject [simp]
  apply(cut_tac x="C__ucharOfMathInt x" and y="C__ucharOfMathInt y" in C__mathIntOfUchar_injective, force, force)
  apply(simp del: C__mathIntOfUchar_injective add: C__mathIntOfUchar_ucharOfMathInt_2 nat_injective)
  apply(auto)
end-proof

proof isa ushortOfMathInt_inject [simp]
  apply(cut_tac x="C__ushortOfMathInt x" and y="C__ushortOfMathInt y" in C__mathIntOfUshort_injective, force, force)
  apply(simp del: C__mathIntOfUshort_injective add: C__mathIntOfUshort_ushortOfMathInt_2 nat_injective)
end-proof

proof isa uintOfMathInt_inject [simp]
  apply(cut_tac x="C__uintOfMathInt x" and y="C__uintOfMathInt y" in C__mathIntOfUint_injective, force, force)
  apply(simp del: C__mathIntOfUint_injective add: C__mathIntOfUint_uintOfMathInt_2 nat_injective)
end-proof

proof isa ulongOfMathInt_inject [simp]
  apply(cut_tac x="C__ulongOfMathInt x" and y="C__ulongOfMathInt y" in C__mathIntOfUlong_injective, force, force)
  apply(simp del: C__mathIntOfUlong_injective add: C__mathIntOfUlong_ulongOfMathInt_2 nat_injective)
end-proof

proof isa ullongOfMathInt_inject [simp]
  apply(cut_tac x="C__ullongOfMathInt x" and y="C__ullongOfMathInt y" in C__mathIntOfUllong_injective, force, force)
  apply(simp del: C__mathIntOfUllong_injective add: C__mathIntOfUllong_ullongOfMathInt_2 nat_injective)
end-proof

proof isa introduce_uintConstant
  apply(simp add: C__uintConstant_def)
end-proof

proof isa introduce_ulongConstant
  apply(simp add: C__ulongConstant_def)
end-proof

proof isa introduce_ullongConstant
  apply(simp add: C__ullongConstant_def)
end-proof



end-spec
