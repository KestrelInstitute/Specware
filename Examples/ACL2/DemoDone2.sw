(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

theorem append_of_INil is
  fa(a:IList) app(a,INil) = a

theorem append_of_INil2 is
  fa(a:IList) app(INil,a) = a

theorem append_assoc is
  fa(a:IList, b:IList, c:IList) app(app(a,b),c) = app(a, app(b,c))

theorem rev_of_append is
  fa(a:IList, b:IList) rev(app(a,b)) = app(rev b, rev a)

% theorem append_singleton is
%   fa(a:IList, x:Int) app(ICons(x,INil),a)) = ICons(x,a)

theorem rev_of_rev is
  fa (a:IList) rev (rev a) = a

proof ACL2 rev_of_rev :enable (rev app) end-proof
proof ACL2 rev_of_append :enable (app rev) end-proof
proof ACL2 append_of_INil :enable (app) end-proof
proof ACL2 append_of_INil2 :enable (app) end-proof
proof ACL2 append_assoc :enable (app) end-proof
%proof ACL2 append_singleton :enable (app) end-proof

end-spec
