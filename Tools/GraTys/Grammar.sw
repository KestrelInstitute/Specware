(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
   import Structs

   type Notion = String
   type Tsymbol = String
   
   type Grammar = Map (Notion, Seq Alternative)

   type Alternative = Seq Element

   type Element =
     | Notion Notion
     | Tsymbol Tsymbol
     | Option Notion
     | Seq Notion
     | ProperSeq Notion

endspec
