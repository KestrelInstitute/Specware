(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* This file contains some candidate extensions of the Specware library. *)

spec

import /Library/General/OptionExt
import /Library/General/Map
import /Library/General/EndoRelation

theorem optionEqSome is [a]
  fa (x:Option a, y:a)
    x = Some y <=> x ~= None && y = unwrap x

endspec
