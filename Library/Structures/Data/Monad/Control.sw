(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Monad qualifying spec
  import /Library/Structures/Data/Monad

  op If : fa(a) Monad Bool -> Monad a -> Monad a -> Monad a
  def If Test Then Else = {
      b <- Test;
      if b then
        Then
      else
        Else
    }

  op When : Monad Bool -> Monad () -> Monad ()
  def When Test Then = If Test Then (return ())

  op While : Monad Bool -> Monad () -> Monad ()
  def While Test Body =  When Test {Body; While Test Body}

  op Not : Monad Bool -> Monad Bool
  def Not stmt = {
      res <- stmt;
      return (~res)
    }

  op And infixl 15 : Monad Bool * Monad Bool -> Monad Bool
  def And (x,y) = {
    xval <- x;
    if xval then
      y
    else
      return false
  }

  op Or infixl 14 : Monad Bool * Monad Bool -> Monad Bool
  def Or (x,y) = {
    xval <- x;
    if xval then
      return true
    else
      y
  }
endspec
