\section{Simple Polymorphic Maps as Lists}

\begin{spec}
Map qualifying spec
  sort Map (key,a) = List (key * a)

  op empty : fa(key,a) Map (key,a)
  def empty = Nil

  op evalPartial : fa(key,a) Map (key,a) * key -> Option a
  def evalPartial (map, x) = 
    case map of
      | [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             evalPartial (tl, x)

  op eval : fa(key,a) Map (key,a) * key -> a
  def eval (map, x) = 
    case map of
      | [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if x = y then
             val
           else
             eval (tl, x)

  op update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  def update (map, x, y) =
    let
      def member? (key,m) =
        case m of
          | [] -> []
          | (y,val)::tl -> 
              if x = y then
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
endspec
\end{spec}
