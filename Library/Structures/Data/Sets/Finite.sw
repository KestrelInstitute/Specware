spec
  import ../Sets
  import translate ../Finite by {
    Finite.Collection +-> Set,
    Finite.pp +-> pp,
    Finite.fold +-> fold
  }
endspec
