An internal category of finite polymorphic sets.

\begin{spec}
let Cats = Initial in
let Elements = Finite qualifying /Library/Structures/Data/Sets/Polymorphic in
let Maps = Poly qualifying /Library/Structures/Data/Maps/Polymorphic in
spec
  import Cats
  import Maps
  import Elements

  sort Morphism a = {
    dom : Finite.Set a,
    cod : Finite.Set a,
    map : Poly.Map (a,a)
  }

  sort SetCat a = Cat (Finite.Set a, Morphism a)

  op setCat : fa (a) (a -> Pretty) -> Cat (Finite.Set a, Morphism a)
  def setCat ppElem = {
    ident = fn obj -> {dom = obj, cod = obj, map =
       fold_fin (fn map -> fn x -> Poly.update map x x) Poly.empty obj},
    dom = fn {dom = d, cod = _, map = _} -> d,
    cod = fn {dom = _, cod = c, map = _} -> c,
%     composable? =
%        fn {dom = _, cod = cod, map = _} ->
%          fn {dom = dom, cod = _, map = _} ->
%            (dom = cod),
    compose =
       fn {dom = d1, cod = c1, map = m1} ->
         fn {dom = d2, cod = c2, map = m2} ->
           {dom = d1, cod = c2, map = Poly.compose m1 m2},
    ppObj = ppSet_fin ppElem,
    ppArr = fn {dom = _, cod = _, map = map} -> Poly.ppMap ppElem ppElem map
  }
end
\end{spec}
    
looks like we need a sort for concrete category where we can enumerate
over the objects and arrows:

Presumably these are not all the arrows but the generators.
We want these as the domain of a functor.
But in the case of diagrams, the codomain will not have an enumerable set
of objects

\begin{verbatim}
sort Object a = Set a

sort Cat a {
  objects : Set a,
  arrows : Set (Morphism a),
  ident : Set a -> Morphism a,
  domain : Morphism a -> Set a,
  codomain : Morphism a -> Set a,
  compose : Morphism a -> Morphism a -> Set a
}
\end{verbatim}

So the lesson is that no matter how hard you try, if you want to
construct a diagram then the domain will have to be enumerable. However,
it is unlikely that the target category will be enumerable. Consider
for example, when the target is the category of specifications.
The problem is that having graphs alone as shapes is not going to be
enough. Down the road we are going to want sketches and whatnot. Perhaps
even topological spaces.

So should the domain of a diagram be a category? Should a diagram be
a functor where the domain and codomains are categories. Are there
structures suitable for both enumerable and non-enumerable categories?
