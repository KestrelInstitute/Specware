% Why is this called ListPair?

ListPair qualifying spec {
  import /Library/Base

  op zip    : fa (a,b) List a *  List b -> List (a * b)
  op unzip  : fa (a,b) List (a * b) -> List a *  List b
  op map    : fa (a,b,c) (a * b -> c) -> List a * List b -> List c
  op all    : fa (a,b) (a * b -> Boolean) -> List a * List b -> Boolean
  op exists : fa (a,b) (a * b -> Boolean) -> List a * List b -> Boolean
  op foldr  : fa (a,b,c) (a * b * c -> c) -> c -> List a * List b -> c 
  op foldl  : fa (a,b,c) (a * b * c -> c) -> c -> List a * List b -> c 
  op app    : fa (a,b) (a * b -> ()) -> List a * List b -> ()

  def zip (l,r) = 
    case (l,r) of
      | (a::l,b::r) -> Cons((a,b),zip(l,r))
      | _ -> []
      
  def unzip l =
    let def unzipLoop (l,a,b) = 
      case l of
        | [] -> (List.rev a, List.rev b)
        | (x,y)::l -> unzipLoop (l,Cons(x,a),Cons(y,b))
    in
      unzipLoop(l,[],[])

  def map f (l,r) = 
    case (l,r) of
      | (x::l,y::r) -> Cons(f(x,y),map f (l,r))
      | _ -> []

  def all p (l,r) = 
    case (l,r) of
      | (x::l,y::r) -> p (x,y) & all p (l,r)
      | _ -> true

  def exists p (l,r) = 
    case (l,r) of
      | (x::l,y::r) -> p (x,y) or exists p (l,r)
      | _ -> false
      
  def foldr f u (l,r) = 
    case (l,r) of
      | (x::l,y::r) -> f (x,y,foldr f u (l,r))
      | _ -> u

  def foldl f u (l,r) = 
    case (l,r) of
      | (x::l,y::r) -> foldl f (f (x,y,u)) (l,r)
      | _ -> u

  def app f (l,r) = 
    case (l,r) of
      | (l1::l2,r1::r2) -> (f (l1,r1); app f (l2,r2))
      | _ -> ()
}
