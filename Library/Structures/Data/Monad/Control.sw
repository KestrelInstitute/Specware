Monad qualifying spec
  import /Library/Structures/Data/Monad

  op If : fa(a) Monad Boolean -> Monad a -> Monad a -> Monad a
  def If Test Then Else = {
      b <- Test;
      if b then
        Then
      else
        Else
    }

  op When : Monad Boolean -> Monad () -> Monad ()
  def When Test Then = If Test Then (return ())

  op While : Monad Boolean -> Monad () -> Monad ()
  def While Test Body =  When Test {Body; While Test Body}

  op Not : Monad Boolean -> Monad Boolean
  def Not stmt = {
      res <- stmt;
      return (~res)
    }

  op And infixl 15 : Monad Boolean * Monad Boolean -> Monad Boolean
  def And (x,y) = {
    xval <- x;
    if xval then
      y
    else
      return false
  }

  op Or infixl 14 : Monad Boolean * Monad Boolean -> Monad Boolean
  def Or (x,y) = {
    xval <- x;
    if xval then
      return true
    else
      y
  }
endspec
