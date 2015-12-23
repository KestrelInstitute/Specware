(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* This spec is copied from Specware4/Library/Unvetted. It is copied, as
opposed to just referenced, for stability: specs under Unvetted may change at
any time (see README under that directory). Eventually, when this spec becomes
part of the standard library (i.e. it is moved from Unvetted to some other
directory), this copy can be replaced by a reference to the (stable) library
spec. *)



(*
2005:11:04
DC

This is a polymorphic spec for a state plus exception monad. It is inspired by
looking at specs ExceptionMonads and StateMonads.

Ideally, it should be composed of the exception monad and state monad, but to do
this requires spec parameters which we can achieve with morphisms, but that is
too cumbersome at this point.

2005:11:14
AC
- Renamed spec from StateAndExceptionMonad to StateAndExceptionMonads for
consistency with specs StateMonads and ExceptionMonads.
- Switched order of type Result and type Monad to maintain ordered references.
- Removed comment "% unit operator" from declaration of op throw.

*)


SStateExceptionMonad qualifying spec
  import /Library/Legacy/Deprecated

  type Result (exc, a) =
    | RETURN a
    | THROW  exc

  type Monad (state, exc, a) = state -> Result (exc, a) * state

  op return : [state, exc, a] a -> Monad(state,exc,a)  % unit operator
  def return x = fn state -> (RETURN x, state)

  op throw : [state,exc,a] exc -> Monad(state,exc,a)
  def throw x = fn state -> (THROW x, state)

  op monadBind : [state,exc,a,b]  % bind operator
    Monad(state,exc,a) * (a -> Monad(state,exc,b)) ->
    Monad(state,exc,b)
  def monadBind (first,next) =
    fn state ->
      case first state of
	| (THROW  e, newState) -> (THROW e, newState)
	| (RETURN x, newState) -> next x newState

  op monadSeq : [state,exc,a,b]  % specialized bind operator
     Monad(state,exc,a) * Monad(state,exc,b) -> Monad(state,exc,b)
  def monadSeq (m1,m2) = monadBind (m1, (fn _ -> m2))

  % apply monadic computation f to sequence s from left to right, returning
  % resulting sequence if no exceptions, otherwise stop at first exception:

  op mapSeq : [state,exc,a,b] (a -> Monad(state,exc,b)) -> List a ->
                              Monad (state,exc, List b)
  def mapSeq f s =
    if null s then return nil
    else {x <- f (hd s);
          r <- mapSeq f (tl s);
          return (cons(x, r))}

  op mapSeqPartial : [state,exc,a,b] (a -> Monad(state,exc,Option b)) -> List a ->
                              Monad (state,exc, List b)
  def mapSeqPartial f s =
    if null s then return nil
    else {x <- f (hd s);
          r <- mapSeqPartial f (tl s);
	  case x of
	    | Some x -> return (cons(x, r))
	    | None -> return r}

  % apply sequence of monadic computations ff to equally long sequence s
  % from left to right, returning resulting sequence if no exceptions,
  % otherwise stop at first exception:

  op mapSeqSeq : [state,exc,a,b]
     {(ff,s) : List (a -> Monad(state,exc,b)) * List a | ff equiLong s} ->
     Monad (state,exc, List b)
  def mapSeqSeq (ff,s) =
    if empty? s then return empty
    else {x <- (head ff) (head s);
          r <- mapSeqSeq (tail ff, tail s);
         return (x |> r)}

endspec
