%%
%% The spec for monads with error-reporting
%%

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
