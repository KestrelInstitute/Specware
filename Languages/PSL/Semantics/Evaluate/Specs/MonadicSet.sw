spec
  import /Library/Structures/Data/Sets/Monomorphic/AsLists  % premature refinement
  import translate (Monad qualifying /Library/Structures/Data/Monad/Iterate) by {
    Monad.Enumerable +-> Set,
    Monad.TakeResult +-> TakeResult,
    Monad.takeOne +-> takeOne,
    Monad.fold +-> foldMonad
  }
endspec
