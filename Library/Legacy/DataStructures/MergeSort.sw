\section{MergeSort} 

List sorting routines using a smooth applicative merge sort
Taken from the SML/NJ distribution, which again is
taken from, ML for the Working Programmer, LCPaulson. pg 99-100, which again is.
taken from ...

\begin{spec} 
MergeSort qualifying spec {
  import /Library/Base

  op sortGT     : fa(a) (a * a -> Boolean) -> List a -> List a
  op uniqueSort : fa(a) (a * a -> Comparison) -> List a -> List a
  op sorted     : fa(a) (a * a -> Boolean) -> List a -> Boolean

  def sortGT cmpGT ls =
    case ls of
      | [] -> []
      | [_] -> ls
      | _ ->  
         let def merge (xs,ys) = 
           case (xs,ys) of
             | ([],ys) -> ys
             | (xs,[]) -> xs
             | (x::xs,y::ys) ->
                if cmpGT(x,y) then
                  Cons (y, merge (Cons(x,xs),ys))
                else
                  Cons(x, merge (xs,Cons(y,ys))) in
         let def mergepairs(ls,k) = 
           case ls of
             | [l] -> ls
             | l1::l2::ls ->
                if k rem 2 = 1 then
                  Cons (l1, Cons (l2,ls))
                else
                  mergepairs (Cons (merge (l1,l2),ls), k div 2)
             | _ -> System.fail "Impossible: mergepairs" in
         let def nextrun(run,xs) =
           case xs of
             | [] -> (List.rev run,[])
             | x::xs ->
                 if cmpGT(x, hd run) then
                   nextrun (Cons (x,run),xs)
                 else
                   (rev run,Cons (x,xs)) in
         let def samsorting (xs,ls,k) = 
           case xs of
             | [] -> List.hd (mergepairs (ls,0))
             | x::xs -> 
                let (run,tail) = nextrun ([x],xs) in 
                samsorting (tail, mergepairs (Cons (run,ls),k + 1), k + 1)
         in 
           (case ls of
             | [] -> []
             | _ -> samsorting (ls, [], 0))
         
  def uniqueSort cmpfn ls = 
    let def merge(xs,ys) = 
      case (xs,ys) of
        | ([],ys) -> ys
        | (xs,[]) -> xs
        | (x::xs,y::ys) ->
            (case cmpfn (x,y) of
              | Greater -> Cons(y,merge(Cons(x,xs),ys))
              | Equal   -> merge(Cons(x,xs),ys)
              | _       -> Cons(x,merge(xs,Cons(y,ys)))) in
    let def mergepairs(ls,k) = 
      case ls of
        | [l] -> ls
        | l1::l2::ls ->
            if k rem 2 = 1 then 
              Cons(l1,Cons(l2,ls))
            else
              mergepairs(Cons(merge(l1,l2),ls), k div 2)
        | _ -> System.fail "Impossible: mergepairs" in
    let def nextrun(run,xs) =
      case xs of
        | [] -> (List.rev run,[])
        | x::xs -> 
            (case cmpfn(x, hd run) of
              | Greater -> nextrun(Cons(x,run),xs)
              | Equal   -> nextrun(run,xs)
              | _       -> (rev run,Cons(x,xs))) in
    let def samsorting(xs,ls,k) = 
      case xs of
        | [] -> List.hd(mergepairs(ls,0))
        | x::xs -> 
            let (run,tail) = nextrun([x],xs) in 
            samsorting(tail, mergepairs(Cons(run,ls),k + 1), k + 1)
    in 
      case ls of
        | [] -> []
        | _ -> samsorting(ls, [], 0)
         
  def sorted cmpGT xs = 
    case xs of
      | (x::(rest as (y::_))) -> ~(cmpGT (x,y)) & (sorted cmpGT rest)
      | _ -> true
}
\end{spec} 
