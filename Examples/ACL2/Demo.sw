(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

type IList =
  | INil
  | ICons Int * IList

op app (a:IList, b:IList) : IList = 
  case a of
  | INil -> b
  | ICons (x,xs) -> ICons (x, (app (xs,b)))

op rev (a:IList) : IList =
  case a of
  | INil -> a
  | ICons (x,xs) -> app (rev xs, ICons (x,INil))

theorem app_of_nil is
  fa (a:IList) app(a,INil) = a

theorem app_of_nil_2 is
  fa (a:IList) app(INil,a) = a

theorem app_assoc is
  fa (a:IList, b:IList, c:IList) app(app(a,b),c) = app(a,app(b,c))

theorem app_singleton is
  fa (a:IList, x:Int) app(ICons(x,INil),a) = ICons(x,a)

theorem rev_of_app is
  fa (a:IList, b:IList) rev (app(a,b)) = app(rev b, rev a)

theorem rev_of_rev is
  fa (a:IList) rev (rev a) = a

proof ACL2 rev_of_rev :enable (rev) end-proof
proof ACL2 rev_of_app :enable (rev app) end-proof
proof ACL2 app_of_nil :enable (app) end-proof
proof ACL2 app_of_nil_2 :enable (app) end-proof
proof ACL2 app_assoc :enable (app) end-proof
proof ACL2 app_singleton :enable (app) end-proof

end-spec
