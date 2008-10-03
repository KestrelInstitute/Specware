Bool qualifying spec

  import IsabelleExtensions

  (* Specware has a built-in type Boolean, which will be renamed to Bool at some
  point in the future. Meanwhile, we introduce Bool as a synonym for Boolean, in
  order to enable the use of Bool immediately and to facilitate the migration
  from Boolean to Bool in existing specs. When we change Boolean to Bool in the
  Specware implementation, the following type definition will be removed. *)

  type Bool.Bool = Boolean

endspec
