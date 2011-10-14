spec {
  import Double

  type Delta a = a * a
  type Proc (args,rtn,store) = (args * rtn * Delta store) -> Bool
}
