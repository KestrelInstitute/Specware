\section{Finite Maps}

We include a copy of finite collections. This is the collection (set)
of key/value pairs that correspond to the graph of the map. This way we
get the operators to iterate over the map and to pretty print it.

\begin{spec}
let
  KeyValue =
   translate
     (translate ../Collections/Finite by {Collection +-> Map, Elem._ +-> KeyValue._})
   by {KeyValue.Elem +-> KeyValue}
in spec
  import KeyValue
  import ../Maps
  sort KeyValue = Dom * Cod

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
                   pp rest
                 ]))
     in
       ppConcat [pp "{", ppContents map, pp "}"]
endspec
\end{spec}
