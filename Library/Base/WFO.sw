WFO qualifying spec
  import Empty				% Avoid importing base spec
  import List

  op  wfo: [a] (a * a -> Boolean) -> Boolean

  def wfo pred =
    fa(p) (ex(y) p y) => (ex(y) (p y && (fa(x) p x => ~(pred(x, y)))))


  op projection1 : [a, b] (a * a -> Boolean) -> ((a * b) * (a * b) ->     Boolean)

  axiom first_projection_def is
    fa(ua,va,ub,vb,p)
        p(ua,va)
     => projection1(p)((ua,ub),(va,vb))

  axiom first_projection_preserves_well_foundedness is
    fa(p) wfo(p) => wfo(projection1(p))

  op is_tail : [a]  {l : List a | ~(null l)} *  List a -> Boolean

  axiom is_tail_def is
   fa(y,l1,l2)
       l2 = cons(y,l1)
    => is_tail(l1,l2)

  axiom is_tail_well_founded is
   wfo is_tail


endspec
