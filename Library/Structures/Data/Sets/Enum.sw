spec
  import ../Sets
  import translate ../Enum by {
    Enum.Collection +-> Set,
    Enum.TakeResult +-> TakeResult,
    Enum.takeOne +-> takeOne
  }
endspec
