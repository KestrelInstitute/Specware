(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec {
  import ../SplayMap
  import /Library/Structures/Data/Monad

  % The first is derived from foldriAp. I suspect this should not
  % be exported.
  op foldMapAp : fa(key,a,b)
       (key * a * b -> Monad b)
    -> Splay(key * a) * b
    -> Monad b 
  def foldMapAp abf (sp,b) = 
    case sp of
      | SplayNil -> return b
      | SplayObj {value = (k,a),left,right} -> {
            rightResult <- foldMapAp abf (right,b);
            rootResult <- abf (k,a,rightResult);
            foldMapAp abf (left,rootResult)
          }
          % foldriAp abf (left,abf(k,a,foldriAp abf (right,b)))

  op foldMap : fa(key,a,b)
       (key * a * b -> Monad b)
     -> b
     -> Map(key,a)
     -> Monad b
  def foldMap abf b map = 
    case map of
      | EMPTY _ -> return b
      | MAP {root,comp,nobj} -> foldMapAp abf (! root,b)

  op foldDoubleMap : fa(key1,key2,a,b)
       (key1 * key2 * a * b -> Monad b)
    -> b
    -> Map (key1, Map (key2, a))
    -> Monad b

  def foldDoubleMap f ob omap = 
      foldMap
        (fn (key1,map,b)->
           foldMap
             (fn (key2,a,b) -> f (key1,key2,a,b))
             b map) ob omap
}
