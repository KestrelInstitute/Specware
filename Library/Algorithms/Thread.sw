(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Thread qualifying
spec
  import /Library/Legacy/Utilities/System
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
  op [a,b] mapT (f: a -> b) (l: List a) : List b
(* Can't define in Specware because fn () -> .. actually generates a lambds with one arg
    let threads = List.map (fn x -> makeThread(fn () -> f x)) l in
    List.map joinThread threads    
*)

endspec
