\section{Naive Polymorphic Maps as Lists}

This is a hopelessly naive implementation of Maps as association Lists.
The eval is embarassing.

Note that the value of this file is a function rather than a spec.
The function takes a string and returns a spec. The string is used
to suffix the names of the sorts and operators. 

See the comment for monomorphic sets.

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
\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  % op image : fa (key,a) Map (key,a) -> Set a
  % op imageToList : fa(key,a) Map (key,a) -> List a
\end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  % op mapMap : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
  def mapMap f map =
    case map of
        [] -> []
      | (x,y)::tl -> Cons ((x,f y), (mapMap f tl))

  % op foldMap : fa(Dom,Cod,a) (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  def foldMap f z map =
    case map of
        [] -> z
      | (x,y)::tl -> foldMap f (f z x y) tl

  % op inDomain? : fa(key,a) Map (key,a) -> key -> Boolean
  def inDomain? map key =
    case map of
        [] -> false
      | (x,y)::tl -> (x = key) or (inDomain? tl key)

  % op mapToList : fa(key,a) Map (key,a) -> List (key * a)
  def mapToList l = l

  % op remove : fa (a,key) Map (key,a) -> key -> Map (key,a)
  def remove map x =
    case map of
        [] -> []
      | (u,v)::y ->
           if u = x then
             y
           else
             Cons((u,v),remove y x)

  % op mapPartial : fa(key,a,b) (a -> Option b) -> Map (key,a) -> Map (key,b)
  def mapPartial f m = 
    let
      def g m key item = 
        case f item of
          | None -> m
          | (Some item_) -> update m key item_
    in
      foldMap g emptyMap m

}
\end{spec}
