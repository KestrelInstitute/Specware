\section{Simple Polymorphic Maps as Lists}

\begin{spec}
spec
  import /Library/Structures/Data/Maps/Finite

  sort Map = List (Dom * Cod)

  op Dom.eq? : Dom * Dom -> Boolean

  def empty = Nil

  def evalPartial (map, x) = 
    case map of
      | [] -> None
      | (y,val)::tl -> 
           if Dom.eq? (x,y) then
             (Some val)
           else
             evalPartial (tl, x)

  def eval (map, x) = 
    case map of
      | [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if Dom.eq? (x,y) then
             val
           else
             eval (tl, x)

  def update (map, x, y) =
    let
      def member? (key,m) =
        case m of
          | [] -> []
          | (y,val)::tl -> 
              if Dom.eq? (x,y) then
                m 
              else
                member? (key,tl) 
    in
      case member? (x,map) of
        | [] -> cons ((x,y),map)
        | l ->
           let
             def addBeforeTail (m,newPair) =
               if m = l then
                 cons (newPair,tl l)
               else
                 case m of
                   | [] -> [newPair]                % Can't happen
                   | p::r -> cons (p,addBeforeTail (r,newPair))
           in
             addBeforeTail (map,(x,y))

  def takeOne map =
    case map of
      | [] -> None
      | (x,y)::rest -> One ((x,y),rest)

  def fold = foldl

  (*
   * These can migrate to the more abstract specification.
   *)
  def foldl (f,unit,map) =
    case takeOne map of
      | None -> unit
      | One (p,rest) -> foldl (f, f (unit,p), rest)

  def foldr (f,unit,map) =
    case takeOne map of
      | None -> unit
      | One (p,rest) -> f (foldr (f,unit,rest), p)
endspec
\end{spec}
