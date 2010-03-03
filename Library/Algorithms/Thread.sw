Thread qualifying
spec
  type Thread a

  op [a] makeThread(f: () -> a): Thread a
 
  op [a] joinThread(t: Thread a): a

  op [a] terminateThread(t: Thread a): ()

  type Mutex

  op makeMutex(nm: String): Mutex

  op getMutex(mx: Mutex): ()
  op releaseMutex(mx: Mutex): ()

  op haveMutex?(mx: Mutex): Bool

  op [a] withMutex(mx: Mutex) (body: a): a

  %% Higher-level Utilities

  op [a,b] mapT (f: a -> b) (l: List a) : List b =
    let threads = List.map (fn x -> makeThread(fn () -> f x)) l in
    List.map joinThread threads    

endspec
