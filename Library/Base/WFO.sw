WFO qualifying spec
  import Empty				% Avoid importing base spec

  op  wfo: [a] (a * a -> Boolean) -> Boolean

  def wfo pred =
    fa(p) (ex(y) p y) => (ex(y) (p y && (fa(x) p x => ~(pred(x, y)))))

endspec
