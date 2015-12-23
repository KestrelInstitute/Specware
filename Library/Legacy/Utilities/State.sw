(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* State Primitives *)

(* This should be used sparingly! *)

State qualifying spec 
 type Ref T = | Ref T

 op [T] mkRef: T -> Ref T

 op := infixl 4 : [T] Ref T * T -> ()
 op ! : [T] Ref T -> T

 % def := (cell,value) = ()
 % def !(x) = case x of ref(y) => y end 
endspec
