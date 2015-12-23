(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Finite Maps}

We include a copy of finite collections. This is the collection (set)
of key/value pairs that correspond to the graph of the map. This way we
get the operators to iterate over the map and to pretty print it.

\begin{spec}
let
  KeyValue =
   translate (translate ../Collections/Finite
     by {Collection +-> Map, Elem._ +-> KeyValue._})
     by {KeyValue.Elem +-> KeyValue}
in spec
  import KeyValue
  import ../Maps

  type KeyValue = Dom * Cod

  op map : Map -> (Cod -> Cod) -> Map
  def map m f = fold (fn (m,(k,v)) -> update (m, k, f v), empty, m)

  def KeyValue.pp (dom,cod) =
    ppConcat [
        pp dom,
        pp " +-> ",
        pp cod
      ]

  def pp map =
    let def ppContents map =
      case takeOne map of
        | None -> ppNil
        | One (keyValue,rest) ->
           (case takeOne rest of
             | None -> pp keyValue
             | One (_,_) ->
                 ppGroup (ppConcat [
                   pp keyValue,
                   pp ",",
                   ppBreak,
                   ppContents rest
                 ]))
     in
       ppConcat [pp "{", ppContents map, pp "}"]
endspec
\end{spec}

Why is \Op{map} here?

Also \Op{pp} should be defined in terms of \Op{fold}. The op \Op{takeOne} is mathematically
reasonable but difficult to implement without an ordering on the elements.

So we would want to fold the following over map

fn (rest,keyValue) ->
  if rest = ppNil then
    pp keyValue
  else
    ppConcat (ppConcat [
      pp keyValue,
      pp ",",
      ppBreak,
      rest
    ])

but this doesn't satisfy the foldable condition. Same problem if we wanted a list from
a map.
