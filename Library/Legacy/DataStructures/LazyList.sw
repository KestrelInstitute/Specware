\section{Lazy Lists}

We use the Lazy list abstraction to organize a branching search.

\begin{spec}
LazyList qualifying
spec

 sort LazyList a = | Nil | Cons a * (() -> LazyList a)

 op toList        : fa(a)   LazyList a -> List a
 op fromList      : fa(a)   List a -> LazyList a
 op unit          : fa(a)   a -> LazyList a
 op >>= infixl 25 : fa(a,b) LazyList a * (a -> LazyList b) -> LazyList b
 op @@  infixl 25 : fa(a)   LazyList a * (() -> LazyList a) -> LazyList a
 op mapFlat       : fa(a,b) (a -> LazyList b) -> List a -> LazyList b
 op mapEach       : fa(a,b) (List a * a * List a -> LazyList b) -> List a -> LazyList b
 op map           : fa(a,b) (a -> b) -> LazyList a -> LazyList b
 op emptyList     : fa(a)   LazyList a
 op app	          : fa(a)   (a -> ()) -> LazyList a -> ()

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

 def app f = fn Nil -> () | Cons(a,la) -> (f a; app f (la ()))

endspec
\end{spec}
