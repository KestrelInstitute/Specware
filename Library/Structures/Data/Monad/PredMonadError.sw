(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This file defines predicate monads for reasoning about monadic computations
that can potentially raise errors, i.e., monads that satisfy the MonadError
spec.  To reason about these computations, we add error-related combinators to
MPred, to recognize uses of error-related combinators in Monad. Thus,
technically, MPred is an error monad as well. *)

PredMonad qualifying spec
  import PredMonad
  import MonadError

  (* Predicates for recognizing computations that raise and catch errors *)
  op [a] raiseErr (err: Err) : MPred a
  op [a] catchErrs : MPred a * (Err -> MPred a) -> MPred a

  (* Error monad laws for MPred *)
  axiom raise_bind is [a,b]
    fa (err,f:a -> MPred b) monadBind (raiseErr err, f) = raiseErr err
  axiom catch_return is [a]
    fa (x:a,f) catchErrs (return x, f) = return x
  axiom raise_catch is [a]
    fa (err,f:Err -> MPred a) catchErrs (raiseErr err, f) = f err

  (* Relationship between Monad and MPred error combinators *)
  axiom satisfies_raiseErr is [a]
    fa (m:Monad a,err) m |= raiseErr err <=> m = raiseErr err
  axiom satisfies_catchErrs is [a]
    fa (m:Monad a,P,Q)
      (ex (m',f) m' |= P && (fa (err) f err |= Q err)) =>
      m |= catchErrs (P,Q) <=>
      (ex (m',f) m' |= P && (fa (err) f err |= Q err) && m = catchErrs (m',f))

end-spec
