List = spec

  import /Library/Base/Empty

  type BList =
    | BNil
    | BCons Boolean * BList

(*
  op Bappend (a:BList) (b:BList) : BList =
    case a of
      | BNil -> b
      | BCons (x,xs) -> BCons (x,Bappend xs b)
*)

end-spec

(*

(in-package "ACL2")
(include-book "~/Specware/Languages/ACL2/specware-book")

(defcoproduct BList
  (BNil)
  (BCons BCons-arg1 :type booleanp
         BCons-arg2 :type BListp))

*)