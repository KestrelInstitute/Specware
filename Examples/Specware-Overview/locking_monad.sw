(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


spec
  import /Library/Structures/Data/Monad
  import /Library/DataStructures/Sets

  % the type of locks
  type Lock

  % the order in which locks must be acquired; reflexivity allows
  % re-entrant locks
  op lockBefore : Lock * Lock -> Bool
  % axiom lockBefore_irreflexivity is fa (l) ~(lockBefore(l,l))
  axiom lockBefore_reflexivity is fa (l) lockBefore(l,l)
  axiom lockBefore_antisymmetry is fa (l1,l2) lockBefore(l1,l2) && (lockBefore(l2,l1)) => l1=l2
  axiom lockBefore_transitivity is
    fa (l1,l2,l3) lockBefore(l1,l2) && lockBefore(l2,l3) => lockBefore(l1,l3)

  % the type of shared variables guarded by locks
  type Shared a

  % returns the lock for a shared variable
  op lockForVar : [a] Shared a -> Lock

  % specification of the locks acquired at some point during a
  % computation
  op [a] locksAcquired : Monad a -> Set Lock

  % states that it is ok to call a function while holding a lock for a
  % shared variable: s's lock must be before all vars locked by f
  op [a,b,c] holdingLockOk? (s : Shared c) (f : a -> Monad b) : Bool =
    fa (x:a,l':Lock) l' in? (locksAcquired (f x)) => lockBefore(lockForVar s,l')

  % perform an atomic update on a shared variable, passing the current
  % value to f and getting the new value, along with an auxiliary
  % return value, back from f; note that f cannot lock s again, so
  % that we don't get deadlock
  op [a,b] atomic_update (s : Shared a) (f : a -> Monad (a * b) | holdingLockOk? s f) : Monad b

  % perform an atomic read: just acts as the identity on a variable
  op [a,b] atomic_read (s : Shared a) (f : a -> Monad b | holdingLockOk? s f) : Monad b =
    atomic_update s (fn x -> monadBind (f x, fn y -> return (x, y)))

  axiom locksAcquired_return is [a,b]
    fa (x:a) locksAcquired (return x) = empty_set
  axiom locksAcquired_bind is [a,b,c]
    fa (m:Monad a, f:a->Monad b, l)
      (l in? locksAcquired (monadBind (m, f))) =>
        (l in? locksAcquired m) || (ex (x:a) l in? (locksAcquired (f x)))
  axiom locksAcquired_atomic is [a,b]
    fa (s,f,l)
      l in? (locksAcquired (atomic_update s f : Monad b)) =>
        l = lockForVar s || (ex (x:a) l in? (locksAcquired (f x)))
end-spec
