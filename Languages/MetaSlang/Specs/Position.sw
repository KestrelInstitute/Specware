(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Position qualifying spec 

 % first char is at line 1, column 0, byte 0

 type Filename = String
 type LineColumn     = (Nat * Nat)          
 type LineColumnByte = (Nat * Nat * Nat)   

 type Position     = | Internal String % msg explains context for term
                     | String   String   * LineColumnByte * LineColumnByte 
                     | File     Filename * LineColumnByte * LineColumnByte 


 op startLineColumnByte : LineColumnByte
 op endLineColumnByte   : String -> LineColumnByte

 def startLineColumnByte       : LineColumnByte = (1,0,0)
 def endLineColumnByte  string : LineColumnByte =
  let last = (length string) - 1 in 
  %% TODO: fold over string looking for newlines
  (1, last, last)

 def internalPosition : Position = Internal "built-in"
 def noPos            : Position = Internal "no position"

 op begLineNum(pos: Position): Nat =
   % 0 means there is no info
   case pos of
     | File (_, (left, _, _), _) -> left
     | String (_, (left, _, _), _) -> left
     | _ -> 0

 % ------------------------------------------------------------------------

 op print : Position -> String
 def print position =
  case position of
    | Internal msg -> msg
    | String (string, left, right) ->
       let printPos = fn (line,column,byte) -> (Nat.show line)^"."^(Nat.show column) in
       printPos left ^ "-" ^ printPos right ^ " in " ^ string
    | File (filename, left, right) ->
       let printPos = fn (line,column,byte) -> (show line)^"."^(show column) in
       printPos left ^ "-" ^ printPos right

% temporary hack .. some places need the filename and some places don't
% this one includes the filename.
 op printAll : Position -> String
 def printAll position =
  case position of
    | Internal msg -> msg
    | String (string, left, right) ->
       let printPos = fn (line,column,byte) -> (show line)^"."^(show column) in
       printPos left ^ "-" ^ printPos right ^ " in [" ^ string ^ "]"
    | File (filename, left, right) ->
       let printPos = fn (line,column,byte) -> (show line)^"."^(show column) in
       (*"in " ^*) filename ^ "\n" ^  printPos left ^ "-" ^ printPos right 

 op  printIfExternal : Position -> String
 def printIfExternal position =
  case position of
    | Internal msg -> ""
    | _ -> printAll position

 op positionSource(pos: Position): String =
   case pos of
    | Internal msg -> msg
    | String (string, _, _) -> string
    | File (filename, _, _) -> filename

 op endPosition(pos: Position): Position =
   case pos of
    | Internal msg -> pos
    | String (string, _, (l, c, b)) ->
      let after_end = (l, c+1, b+1) in
      String (string, after_end, after_end)
    | File (filename, _, (l, c, b)) ->
      let after_end = (l, c+1, b+1) in
      File (filename, after_end, after_end)
      

 % ------------------------------------------------------------------------

 def chooseNonZeroPos (p1: Position, p2: Position) : Position =
   case (p1, p2) of
    | (File _,    _       ) -> p1
    | (_,         File _  ) -> p2
    | (String _,  _       ) -> p1
    | (_,         String _) -> p2
    | _ -> p1

 % ------------------------------------------------------------------------

 op compare : Position * Position -> Comparison
 def compare (p1, p2) =
  %% This seems way too complicated...
  let def compareLineColumnByte ((_, _, b1), (_, _, b2)) =
       if b1 < b2 then Less      
       else if b1 > b2 then Greater
       else Equal
  in
  case p1 of
    | Internal msg_1 ->
      (case p2 of
        | Internal msg_2 -> String.compare (msg_1, msg_2)
        | String   _     -> Less
        | File     _     -> Less
	)
    | String (string_1, left_1, right_1) ->
      (case p2 of
        | Internal _ -> Greater
        | String (string_2, left_2, right_2) -> 
          (case String.compare (string_1, string_2) of
            | Equal -> (case compareLineColumnByte (left_1, left_2) of
                         | Equal -> compareLineColumnByte (right_1, right_2)
			 | c     -> c)
            | c     -> c)
        | File     _ -> Less
	)
    | File (file_1, left_1, right_1) ->
      (case p2 of
        | Internal _ -> Greater
        | String   _ -> Greater
        | File (file_2, left_2, right_2) ->
          (case String.compare (file_1, file_2) of
            | Equal -> (case compareLineColumnByte (left_1, left_2) of
                         | Equal -> compareLineColumnByte (right_1, right_2)
			 | c     -> c)
            | c     -> c)
	)
end-spec
