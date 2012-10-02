let Monad = /Library/Structures/Data/Monad/Fold in
spec
  import translate (translate Monad
    by {Collection +-> Set, Monad.Monad +-> SpecCalc.Env})
    by {Monad._ +-> SpecCalc._}
  import ../Sets/AsListsEq
endspec
