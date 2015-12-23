(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
2005:03:17
LM
A simple error monad, if a string is good enough for the error message
Ops zip & unzip and conversions fallibleToOption and optionToFallible
thrown in as extras

*)

Fallible qualifying spec

  % A slight generalization of Option, in which the failed case carries
  % a string that can be used for conveying an error message

  import translate translate /Library/Unvetted/Monad by {
      Monad._   +-> _,
      Kleisli._ +-> KleisliFallible._}
    by {Monad +-> Fallible}

  type Fallible a =
     | OK a
     | KO String

% op  monadBind : [a,b] Fallible a * (a -> Fallible b) -> Fallible b
  def monadBind(x?, f) =
    case x? of
       | OK x -> f x
       | KO e -> KO e

% op  return : [a] a -> Fallible a
  def return = OK

  op  unzip : [a, b] Fallible(a * b) -> Fallible a * Fallible b
  def unzip = fn
    | OK (x, y) -> (OK x, OK y)
    | KO e      -> (KO e, KO e)

  % zip o unzip = id, but in general unzip(zip xy) ~= xy

  op  zip : [a, b] Fallible a * Fallible b -> Fallible(a * b)
  def zip(x?, y?) =
    case x? of
       | OK x -> (case y? of
                     | OK y -> OK (x, y)
                     | KO e -> KO e)
       | KO e -> KO e

  op  fallibleToOption : [a] Fallible a -> Option a
  def fallibleToOption x? =
    case x? of
       | OK x -> Some x
       | KO _ -> None

  op  optionToFallible : [a] Option a -> Fallible a
  def optionToFallible x? =
    case x? of
       | Some x -> OK x
       | None   -> KO ""

endspec
