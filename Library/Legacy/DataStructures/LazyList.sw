(* Lazy Lists 

We use the Lazy list abstraction to organize a branching search.
*)

LazyList qualifying
spec

 type LazyList a = | Nil | Cons a * (() -> LazyList a)

 op toList        : [a]   LazyList a -> List a
 op fromList      : [a]   List a -> LazyList a
 op unit          : [a]   a -> LazyList a
 op >>= infixl 25 : [a,b] LazyList a * (a -> LazyList b) -> LazyList b
 op @@  infixl 25 : [a]   LazyList a * (() -> LazyList a) -> LazyList a
 op mapFlat       : [a,b] (a -> LazyList b) -> List a -> LazyList b
 op mapEach       : [a,b] (List a * a * List a -> LazyList b) -> List a -> LazyList b
 op map           : [a,b] (a -> b) -> LazyList a -> LazyList b
 op emptyList     : [a]   LazyList a
 op find          : [a] (a -> Boolean) -> LazyList a -> Option a
 op app	          : [a]   (a -> ()) -> LazyList a -> ()

 def emptyList = Nil

 def fromList = 
       fn [] -> Nil
        | hd::tl -> Cons(hd,fn () -> fromList tl)

 def toList = 
     fn Nil -> []
      | Cons(hd,tl) -> List.cons(hd,toList(tl()))

 def unit a = Cons(a,fn () -> Nil)

 def >>= = 
       (fn (Nil,_) ->  Nil
         | (Cons(a,la),f) -> (f a @@ (fn () -> la() >>= f)))

 def @@ = 
       fn (Nil,f) -> f()
        | (Cons(a,la),f) -> Cons(a,fn() -> la() @@ f)

 def mapFlat f = 
       fn [] -> Nil
        | l::ls -> (f l @@ (fn () -> mapFlat f ls))

 def map f = fn Nil -> Nil 
              | Cons(a,la) -> Cons(f a,fn () -> map f (la ())) 
   
 def mapEach f ls = 
     let
	def loop(ls,first) = 
            case ls
              of [] -> emptyList
	       | x::rest -> 
		 (f(first,x,rest)) @@
		 (fn () -> loop(rest,first ++ [x]))
     in
         loop(ls,[])

 def find p l =
   case l of
     | Nil -> None
     | Cons(a,_) | p a -> Some a
     | Cons(_,f) -> find p (f())

 def app f = fn Nil -> () | Cons(a,la) -> (f a; app f (la ()))

endspec

