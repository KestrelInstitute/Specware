spec
  import ../ClaimSets

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Claim.Claim})
    by {Elem._ +-> Claim._, MonadFold._ +-> ClaimSetEnv._, _ +-> ClaimSet._}

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Claim.Ref})
    by {Elem._ +-> ClaimRef._, MonadFold._ +-> ClaimRefEnv._, _ +-> ClaimRefSet._}
endspec

