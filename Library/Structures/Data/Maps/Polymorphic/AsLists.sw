\section{Naive Polymorphic Maps as Lists}

This is a hopelessly naive implementation of Maps as association Lists.
The eval is embarassing.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig
  import ../Polymorphic

  sort Map (key,a) = List (key * a)

  % op emptyMap : fa(key,a) Map (key,a)
  def emptyMap = Nil

  % The following function will disappear when the library is restructured
  % with separate directories for total and partial maps.

  % op evalPartial : fa(key,a) Map(key,a) -> key -> Option a
  def evalPartial map x = 
    case map of
        [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             evalPartial tl x

  % op eval : fa(key,a) Map(key,a) -> key -> a
  def eval map x = 
    case map of
        [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if x = y then
             val
           else
             eval tl x

  % op update : fa (key,a) Map (key,a) -> key -> a -> Map (key,a)
  def update map x y =
    case map of
        [] -> [(x,y)]
      | (u,v)::tl ->
          if (x = u) then
            Cons ((x,y),tl)
          else
            Cons ((u,v), update tl x y)

  % op remove : fa (a,key) Map (key,a) -> key -> Map (key,a)
  def remove map x =
    case map of
        [] -> []
      | (u,v)::y ->
           if u = x then
             y
           else
             Cons((u,v),remove y x)

\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  % op image : fa (key,a) Map (key,a) -> Set a

  % op imageToList : fa(key,a) Map (key,a) -> List a
  % def imageToList map =
  %  foldMap (fn values -> fn _ -> fn value -> Cons (value, values))
  %          []
  %          map      

  % op mapToList : fa(key,a) Map (key,a) -> List (key * a)
  def mapToList l = l

  % op domain : fa(key,a) Map (key,a) -> Set key
  % op domainToList : fa(key,a) Map (key,a) -> List key

  % op inDomain? : fa(key,a) Map (key,a) -> key -> Boolean
  % def inDomain? map key =
  %   case map of
  %       [] -> false
  %     | (x,y)::tl -> (x = key) or (inDomain? tl key)

  % op numItems : fa(a,key) Map (key,a) -> Nat
  % op mapi : fa(key,a,b) (key -> a -> b) -> Map (key,a) -> Map (key,b)
\end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  % op mapMap : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
  def mapMap f map =
    case map of
      | [] -> []
      | (x,y)::tl -> Cons ((x,f y), (mapMap f tl))

  % op foldMap : fa(Dom,Cod,a) (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  def foldMap f z map =
    case map of
      | [] -> z
      | (x,y)::tl -> foldMap f (f z x y) tl


  % op foldriDouble : fa(key1,key2,a,b) (key1 -> key2 -> a -> b -> b)
  %      -> b -> Map (key1, Map (key2, a)) -> b

  % TODO: make compose partial?
  % op compose : fa(dom,med,rng) Map (dom,med) -> Map (med,rng) -> Map (dom,rng)
  def compose m1 m2 = 
    foldMap (fn new_map -> fn dom -> fn med -> 
	     let cod = eval m2 med in % evalPartial ??
	     update new_map dom cod)
            emptyMap
            m1

  % op unionWith : fa(key,a) (a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op unionWithi : fa(key,a) (key -> a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op intersectWith : fa(key,a) (a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map(key,a)
  % op intersectWithi : fa(key,a) (key -> a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op filter  : fa(key,a) (a -> Boolean) -> Map (key,a) -> Map (key,a)	  
  % op filteri : fa(key,a) (key -> a -> Boolean) -> Map (key,a) -> Map (key,a)

  % op mapPartial : fa(key,a,b) (a -> Option b) -> Map (key,a) -> Map (key,b)
  def mapPartial f m = 
    let
      def g m key item = 
        case f item of
          | None -> m
          | (Some revised_item) -> update m key revised_item
    in
      foldMap g emptyMap m

  % op compare : fa(a,key) (a * a -> Comparison)
  %      -> Map (key,a) -> Map (key,a) -> Comparison
  % op fromSet : fa (a,b) Set (a * b) -> Map (a, b)
  % op fromList : fa (a,b) List (a * b) -> Map (a, b)
  % op subset? : fa (a,b) Map (a,b) -> Map (a,b) -> Boolean
  % op all : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
  % op exists : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
}
\end{spec}
