(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

IO qualifying spec
  import translate (translate Exception by  {Monad.Monad +-> IO.IO})
           by {Monad._ +-> IO._}
  import /Library/Legacy/Utilities/System

  type IO.Exception = String

  type Result a =
    | Ok a
    | Exception Exception

  type IO.IO a = () -> Result a * ()

  def IO.monadBind (f,g) =
    fn () -> (case (f ()) of
      | (Ok y, newState) -> (g y newState)
      | (Exception except, newState) -> (Exception except, newState))

  def IO.return x = fn state -> (Ok x, state)

  op print : String -> IO ()
  def print str = fn state -> (Ok (toScreen str), state)

  op writeLine : String -> IO ()
  def writeLine str = fn state -> (Ok (writeLine str), state)

  op error : [a] String -> IO a
  def error str = fn () -> (Exception str, ())

  def IO.raise str = fn () -> (Exception str, ())

  op run : [a] IO a -> a
  def run f =
    case f () of
      | (Ok x, _) -> x
      | (Exception exception, _) ->
         fail ("run: uncaught exception:\n  " ^ exception)

  def IO.catch f handler =
    fn () ->
      (case f () of
        | (Ok x, newState) -> (Ok x, newState)
        | (Exception except, newState) -> handler except newState)


  op when : Bool -> IO () -> IO ()
  def when p command = if p then command else return ()

  op unless : Bool -> IO () -> IO ()
  def unless p command = if ~p then command else return ()

  op mapM : [a,b] (a -> IO b) -> (List a) -> IO (List b)
  def mapM f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- mapM f xs;
            return (Cons (xNew,xsNew))
          }

  op foldM : [a,b] (a -> b -> IO a) -> a -> List b -> IO a
  def foldM f a l =
    case l of
      | [] -> return a
      | x::xs -> {
            y <- f a x;
            foldM f y xs
          }

#translate Haskell -morphism Monad
  type IO.IO -> IO
  IO.monadBind -> >>=
  IO.return -> return
  IO.catch -> catch
  IO.raise -> raise
  IO.print -> putStr
  IO.writeLine -> putStrLn
  IO.error -> fail
  IO.when -> when
  IO.unless -> unless
  IO.mapM -> mapM
  IO.foldM -> foldM
#end

endspec
