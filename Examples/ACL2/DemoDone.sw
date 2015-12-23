(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

type IList =
  | INil
  | ICons Int * IList

op IAppend (a:IList, b:IList) : IList = 
  case a of
  | INil -> b
  | ICons (x,xs) -> ICons (x, (IAppend (xs,b)))

op IRev (a:IList) : IList =
  case a of
  | INil -> a
  | ICons (x,xs) -> IAppend (IRev xs, ICons (x,INil))

theorem IRev_of_INil is
  (IRev INil) = INil

theorem IAppend_of_INil_1 is
  fa (a:IList) IAppend(INil,a) = a

theorem IAppend_of_INil_2 is
  fa (a:IList) IAppend(a,INil) = a

theorem IAppend_Associative is
  fa (a:IList, b:IList, c:IList) IAppend(IAppend(a,b),c) = IAppend(a,IAppend(b,c))

theorem IRev_of_IAppend is
  fa (a:IList, b:IList) IRev (IAppend(a,b)) = IAppend(IRev b, IRev a)

theorem IAppend_singleton is
  fa (a:IList, b:Int) IAppend(ICons(b,INil),a) = ICons(b,a)

theorem IRev_of_IRev is
  fa (a:IList) (IRev (IRev a)) = a

proof ACL2 IAppend_singleton :enable (IAppend) end-proof
proof ACL2 IAppend_Associative :enable (IAppend) end-proof
proof ACL2 IAppend_of_INil_1 :enable (IAppend) end-proof
proof ACL2 IAppend_of_INil_2 :enable (IAppend) end-proof
proof ACL2 IRev_of_INil :enable (IRev) end-proof
proof ACL2 IRev_of_IAppend :enable (IRev IAppend) end-proof
proof ACL2 IRev_of_IRev :enable (IRev) end-proof

end-spec
