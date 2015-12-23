(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% Simple Polymorphic Maps as Association Lists (Alists).
%TODO Do simple maps have the property that two maps are equal if they agree on every key?
%TODO Do the Alists have that property?  What about the order of entries in the alist?

MapList =
MapL qualifying
spec
  type Map (key,a) = List (key * a)
endspec

SimpleAsAlist =
MapL qualifying
spec
  import Simple[morphism Simple#Map -> MapList {}] %TODO This anonymous morphism might give problems.  Separate it out?
  %TODO Is this the same as just importing Simple#Map and then defining the type Map?

  import /Library/Legacy/Utilities/System  %allows the call to 'fail' below... TODO get rid of that and this import?

  % Here we give definitions to the ops declared in Simple.sw:

  % op emptyMap : [key,a] Map (key,a)
  def [key,a] emptyMap : Map (key,a) = Nil

  % The following function will disappear when the library is restructured
  % with separate directories for total and partial maps.

  % op evalPartial : [key,a] Map(key,a) -> key -> Option a
  def apply (map, x) = 
    case map of
        [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             apply (tl, x)

  % op eval : [key,a] Map(key,a) -> key -> a
  def eval (map, x) = 
    case map of
        [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if x = y then
             val
           else
             eval (tl, x)

  % op update : [key,a] Map (key,a) -> key -> a -> Map (key,a)
  def [key,a] update (map: Map(key,a), x: key, y: a): Map(key,a) =
    let def memb(key,m) =
          case m of
	    [] -> []
	   | (y,val)::tl -> 
	      if x = y then m 
	       else memb(key,tl) 
    in
    case memb(x,map) of
      | [] -> Cons((x,y),map)
      | l ->
        let def addBeforeTail(m,l,newpr) =
	      if m = l then Cons(newpr,tail l)
		else
		  case m of
		    | [] -> [newpr]		% Can't happen
		    | p::r -> Cons(p,addBeforeTail(r,l,newpr))
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

(*
The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.
*)
  % op imageToList : [key,a] Map (key,a) -> List a
  def imageToList map =
    foldi (fn (_, value, values) -> Cons (value, values))
      [] map      

  % op mapToList : [key,a] Map (key,a) -> List (key * a)
  def mapToList l = l

  % op domainToList : [key,a] Map (key,a) -> List key
  def domainToList map = 
    foldi (fn (value, _, values) -> Cons (value, values))
      [] map      

  % op inDomain? : [key,a] Map (key,a) -> key -> Bool
  def inDomain? (map, key) =
    case map of
        [] -> false
      | (x,y)::tl -> (x = key) || (inDomain? (tl, key))

  % op numItems : fa(a,key) Map (key,a) -> Nat
  def numItems = length

  % op map : [key,a,b] (a -> b) -> Map (key,a) -> Map (key,b)
  def map f m =
    case m of
        [] -> []
      | (x,y)::tl -> Cons ((x,f y), (map f tl))

  % op mapi : [key,a,b] (key * a -> b) -> Map (key,a) -> Map (key,b)
  def mapi f m =
    case m of
        [] -> []
      | (x,y)::tl -> Cons ((x,f(x,y)), (mapi f tl))

  % op app : [key,a,b] (a -> ()) -> Map (key,a) -> ()
  def app f map =
    case map of
        [] -> ()
      | (x,y)::tl -> let _ = f y in app f tl

  % op appi : [key,a,b] (key * a -> ()) -> Map (key,a) -> ()
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

endspec

M = morphism Simple -> SimpleAsAlist {}
