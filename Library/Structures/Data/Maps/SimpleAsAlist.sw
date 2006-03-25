\section{Simple Polymorphic Maps as Lists}

\begin{spec}
Map qualifying
spec
  import Simple

  sort Map (key,a) = List (key * a)

  % op emptyMap : fa(key,a) Map (key,a)
  def emptyMap = Nil

  % The following function will disappear when the library is restructured
  % with separate directories for total and partial maps.

  % op evalPartial : fa(key,a) Map(key,a) -> key -> Option a
  def apply (map, x) = 
    case map of
        [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             apply (tl, x)

  % op eval : fa(key,a) Map(key,a) -> key -> a
  def eval (map, x) = 
    case map of
        [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if x = y then
             val
           else
             eval (tl, x)

  % op update : fa (key,a) Map (key,a) -> key -> a -> Map (key,a)
  def update (map, x, y) =
    let def memb(key,m) =
          case m of
	    [] -> []
	   | (y,val)::tl -> 
	      if x = y then m 
	       else memb(key,tl) 
    in
    case memb(x,map) of
      | [] -> cons((x,y),map)
      | l ->
        let def addBeforeTail(m,l,newpr) =
	      if m = l then cons(newpr,tl l)
		else
		  case m of
		    | [] -> [newpr]		% Can't happen
		    | p::r -> cons(p,addBeforeTail(r,l,newpr))
	in addBeforeTail(map,l,(x,y))
% Adds at end which is not generally desirable as it means copying whole map if not already there
%    case map of
%        [] -> [(x,y)]
%      | (u,v)::tl ->
%          if (x = u) then
%            Cons ((x,y),tl)
%          else
%            Cons ((u,v), update tl x y)


  % op remove : fa (a,key) Map (key,a) -> key -> Map (key,a)
  def remove (map, x) =
    case map of
        [] -> []
      | (u,v)::y ->
           if u = x then
             y
           else
             Cons((u,v),remove (y, x))

\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  % op imageToList : fa(key,a) Map (key,a) -> List a
  def imageToList map =
    foldi (fn (_, value, values) -> Cons (value, values))
      [] map      

  % op mapToList : fa(key,a) Map (key,a) -> List (key * a)
  def mapToList l = l

  % op domainToList : fa(key,a) Map (key,a) -> List key
  def domainToList map = 
    foldi (fn (value, _, values) -> Cons (value, values))
      [] map      

  % op inDomain? : fa(key,a) Map (key,a) -> key -> Boolean
  def inDomain? (map, key) =
    case map of
        [] -> false
      | (x,y)::tl -> (x = key) or (inDomain? (tl, key))

  % op numItems : fa(a,key) Map (key,a) -> Nat
  def numItems = length

  % op map : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
  def map f m =
    case m of
        [] -> []
      | (x,y)::tl -> Cons ((x,f y), (map f tl))

  % op mapi : fa(key,a,b) (key * a -> b) -> Map (key,a) -> Map (key,b)
  def mapi f m =
    case m of
        [] -> []
      | (x,y)::tl -> Cons ((x,f(x,y)), (mapi f tl))

  % op app : fa(key,a,b) (a -> ()) -> Map (key,a) -> ()
  def app f map =
    case map of
        [] -> ()
      | (x,y)::tl -> let _ = f y in app f tl

  % op appi : fa(key,a,b) (key * a -> ()) -> Map (key,a) -> ()
  def appi f map =
    case map of
        [] -> ()
      | (x,y)::tl -> let _ = f(x,y) in appi f tl

  def foldi f z map =
    case map of
        [] -> z
      | (x,y)::tl -> foldi f (f (x,y,z)) tl

  def mapPartial f m = 
    let
      def g (key,item,m) = 
        case f item of
          | None -> m
          | (Some new_item) -> update (m, key, new_item)
    in
      foldi g emptyMap m

  def mapiPartial f m = 
    let
      def g (key,item,m) = 
        case f (key,item) of
          | None -> m
          | (Some new_item) -> update (m, key, new_item)
    in
      foldi g emptyMap m

  % op fromList : fa (a,b) List (a * b) -> Map (a, b)
  % op subset? : fa (a,b) Map (a,b) -> Map (a,b) -> Boolean
  % op all : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
  % op exists : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
endspec
\end{spec}
