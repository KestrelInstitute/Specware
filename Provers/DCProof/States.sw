(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  import ExtProofsAPI

  type Tree a
  op empty: [a] Tree a

  op addSubTreeo: Tree * 

  type Context
  type Goal
  
  type State
  op context: State -> Context
  op tree: State -> Tree(Goal)  

  op initialState: State
  axiom initialStateTree is tree(initialState) = empty


endspec
