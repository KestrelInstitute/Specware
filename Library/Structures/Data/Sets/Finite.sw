(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  import translate ../Collections/Finite by {Collection +-> Set}
  import ../Sets

  def pp set =
    let def ppContents set =
      case takeOne set of
        | None -> ppNil
        | One (value,rest) ->
           (case takeOne rest of
             | None -> pp value
             | One (_,_) ->
                 ppGroup (ppConcat [
                   pp value,
                   pp ",",
                   ppBreak,
                   ppContents rest
                 ]))
     in
       ppConcat [pp "{", ppContents set, pp "}"]
 
endspec
