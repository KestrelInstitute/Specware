(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Notes qualifying spec 
{
 import Position
 import Pedigree

 type Note  = | Position Position
              | Pedigree Pedigree
              | Comment  String
                 
 type Notes = List Note 

 type Annotated a = {body : a, notes : Notes}

 op [a] bare (x : a) : Annotated a = {body = x, notes = []}

 %% other names considered for 'bare': 
 %% plain, bald, unadorned, unnoted, simple, internal, anon, anonymous
 %% vanilla, unclad, just, clean, clear, raw, neat, trim, mere
}
