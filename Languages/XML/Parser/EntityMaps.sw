(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying
spec

 import ../XML_Sig

 %% Simple-minded alist -- could get fancier if speed is any kind of problem

 type GE_Map = List (Name * Content)
 type PE_Map = List (Name * UChars)

 def GE.empty_map : GE_Map = []
 def PE.empty_map : PE_Map = []

 op GE.update : GE_Map * Name * Content -> GE_Map
 op PE.update : PE_Map * Name * UChars  -> PE_Map

 def GE.update (map, name, content) =
   %% prior values take precedence
   case eval (map, name) of
     | Some _ -> map
     | None   -> (name, content) :: map

 def PE.update (map, name, uchars) =
   %% prior values take precedence
   case eval (map, name) of
     | Some _ -> map
     | None   -> (name, uchars) :: map

 op GE.eval : GE_Map * Name -> Option Content
 op PE.eval : PE_Map * Name -> Option UChars

 def GE.eval (map, name) =
   case map of
     | (key, value) :: tail ->
       if key = name then
	 Some value
       else
	 GE.eval (tail, name)
     | [] -> None

 def PE.eval (map, name) =
   case map of
     | (key, value) :: tail ->
       if key = name then
	 Some value
       else
	 PE.eval (tail, name)
     | [] -> None

endspec