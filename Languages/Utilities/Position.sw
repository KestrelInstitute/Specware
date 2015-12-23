(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Notes qualifying spec
{

 % first char is at line 1, column 0, byte 0

 type Filename       = String
 type LineColumn     = (Nat * Nat)          
 type LineColumnByte = (Nat * Nat * Nat)   

 type Position = | Internal String         % string explains context for term
                 | String   String   * LineColumnByte * LineColumnByte 
                 | File     Filename * LineColumnByte * LineColumnByte 

 op startLineColumnByte : LineColumnByte = 
  (1,0,0)

 op endLineColumnByte   (str : String) : LineColumnByte =
  %% TODO: fold over string looking for newlines
  let last = (length str) - 1 in 
  (1, last, last)

 op internalPosition : Position = Internal "built-in"
 op noPos            : Position = Internal "no position"

 % ------------------------------------------------------------------------

 op printLCB (lcb as (line, column, byte) : LineColumnByte) : String =
   (show line) ^ "." ^ (show column) 

 op print (pos : Position) : String =
  case pos of
    | Internal msg                     -> msg
    | String   (string,   left, right) -> printLCB left ^ "-" ^ printLCB right ^ " in " ^ string
    | File     (filename, left, right) -> printLCB left ^ "-" ^ printLCB right

 % temporary hack .. some places need the filename and some places don't
 % this one includes the filename.
 op printAll (pos: Position) : String =
  case pos of
    | Internal msg                     -> msg
    | String   (string,   left, right) ->                    printLCB left ^ "-" ^ printLCB right ^ " in [" ^ string ^ "]"
    | File     (filename, left, right) -> filename ^ "\n" ^  printLCB left ^ "-" ^ printLCB right 

 op printIfExternal (position : Position) : String =
  case position of
    | Internal msg -> ""
    | _ -> printAll position

 op positionSource (pos: Position) : String =
   case pos of
    | Internal msg              -> msg
    | String   (string,   _, _) -> string
    | File     (filename, _, _) -> filename

 % ------------------------------------------------------------------------

 op chooseNonZeroPos (p1: Position, p2: Position) : Position =
   case (p1, p2) of
    | (File _,    _       ) -> p1
    | (_,         File _  ) -> p2
    | (String _,  _       ) -> p1
    | (_,         String _) -> p2
    | _ -> p1

 % ------------------------------------------------------------------------

 op compare (p1 : Position, p2 : Position) : Comparison = 
  %% This seems way too complicated...
  let 
    def compare_lcbs ((_, _, b1), (_, _, b2)) =
      if b1 < b2 then 
        Less      
      else if b1 > b2 then 
        Greater
      else 
        Equal
  in
  case p1 of

    | Internal msg_1 ->
      (case p2 of
         | Internal msg_2 -> String.compare (msg_1, msg_2)
         | String   _     -> Less
         | File     _     -> Less)

    | String (string_1, left_1, right_1) ->
      (case p2 of
         | Internal _ -> Greater
         | String (string_2, left_2, right_2) -> 
           (case String.compare (string_1, string_2) of
              | Equal -> (case compare_lcbs (left_1, left_2) of
                            | Equal -> compare_lcbs (right_1, right_2)
                            | comp -> comp)
              | comp -> comp)
         | File     _ -> Less)

    | File (file_1, left_1, right_1) ->
      (case p2 of
         | Internal _ -> Greater
         | String   _ -> Greater
         | File (file_2, left_2, right_2) ->
           (case String.compare (file_1, file_2) of
              | Equal -> (case compare_lcbs (left_1, left_2) of
                            | Equal -> compare_lcbs (right_1, right_2)
                            | comp -> comp)
              | comp -> comp))
}
