(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CountTermTypes qualifying spec

import /Languages/MetaSlang/Specs/Environment

type Tally = {name           : String,
              n_apply        : Nat,
              n_applyn       : Nat,
              n_record       : Nat,
              n_bind         : Nat,
              n_the          : Nat,
              n_let          : Nat,
              n_letrec       : Nat,
              n_var          : Nat,
              n_fun          : Nat,
              n_lambda       : Nat,
              n_ifthenelse   : Nat,
              n_seq          : Nat,
              n_typedterm    : Nat,
              n_transform    : Nat,
              n_pi           : Nat,
              n_and          : Nat,
              n_any          : Nat,
              n_mystery      : Nat}

op zero_tally : Tally = 
 {name           = "zero_tally",
  n_apply        = 0,
  n_applyn       = 0,
  n_record       = 0,
  n_bind         = 0,
  n_the          = 0,
  n_let          = 0,
  n_letrec       = 0,
  n_var          = 0,
  n_fun          = 0,
  n_lambda       = 0,
  n_ifthenelse   = 0,
  n_seq          = 0,
  n_typedterm    = 0,
  n_transform    = 0,
  n_pi           = 0,
  n_and          = 0,
  n_any          = 0,
  n_mystery      = 0}

op newTally (name : String) : Tally = 
 zero_tally << {name = name}

op priorTally : Ref Tally = Ref zero_tally

op printTallyDiffs (t1 : Tally, t2 : Tally) : () =
 let _ = writeLine "=================================" in
 let _ = writeLine "Differences in term distributions" in
 let _ = writeLine ("  " ^ t2.name ^ " => " ^ t1.name) in 

 %% -------------------- common ------------------
 let _    = writeLine "" in

 let diff = t1.n_lambda       - t2.n_lambda       in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Lambda\t\t " ^ show diff) 
 in
 let diff = t1.n_apply        - t2.n_apply        in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Apply\t\t " ^ show diff) 
 in
 let diff = t1.n_fun          - t2.n_fun          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Fun\t\t " ^ show diff) 
 in
 let diff = t1.n_var          - t2.n_var          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Var\t\t " ^ show diff) 
 in

 let diff = t1.n_record       - t2.n_record       in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Record\t\t " ^ show diff) 
 in
 let diff = t1.n_let          - t2.n_let          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Let\t\t " ^ show diff) 
 in
 let diff = t1.n_letrec       - t2.n_letrec       in
 let _    = if diff = 0 then
              ()
            else
              writeLine("LetRec\t\t " ^ show diff) 
 in
 let diff = t1.n_ifthenelse   - t2.n_ifthenelse   in
 let _    = if diff = 0 then
              ()
            else
              writeLine("IfThenElse\t " ^ show diff) 
 in
 let diff = t1.n_typedterm    - t2.n_typedterm    in
 let _    = if diff = 0 then
              ()
            else
              writeLine("TypedTerm\t " ^ show diff) 
 in
 %% -------------------- rare --------------------
 let _    = writeLine "" in

 let diff = t1.n_seq          - t2.n_seq          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Seq\t\t " ^ show diff) 
 in
 let diff = t1.n_bind         - t2.n_bind         in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Bind \t\t " ^ show diff) 
 in
 let diff = t1.n_the          - t2.n_the          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("The\t\t " ^ show diff) 
 in
 let diff = t1.n_transform    - t2.n_transform    in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Transform\t " ^ show diff) 
 in
 %% -------------------- none? --------------------
 let _    = writeLine "" in

 let diff = t1.n_and          - t2.n_and          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("And\t\t " ^ show diff) 
 in
 let diff = t1.n_pi           - t2.n_pi           in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Pi   \t\t " ^ show diff) 
 in
 let diff = t1.n_any          - t2.n_any          in
 let _    = if diff = 0 then
              ()
            else
              writeLine("Any\t\t " ^ show diff) 
 in
 let diff = t1.n_applyn       - t2.n_applyn       in
 let _    = if diff = 0 then
              ()
            else
              writeLine("ApplyN\t\t " ^ show diff) 
 in
 let diff = t1.n_mystery      - t2.n_mystery      in
 let _    = if diff = 0 then
              ()
            else
              writeLine("<mystery>\t\t " ^ show diff) 
 in
 ()

              
op printTally (tally : Tally) : () =
 let _ = printTallyDiffs (tally, !priorTally) in
 let _ = writeLine "=================================" in
 %% -------------------- common ------------------
 let _    = writeLine "" in

 let _ = writeLine ("# Lambda     = " ^ show tally.n_lambda     ) in
 let _ = writeLine ("# Apply      = " ^ show tally.n_apply      ) in
 let _ = writeLine ("# Fun        = " ^ show tally.n_fun        ) in
 let _ = writeLine ("# Var        = " ^ show tally.n_var        ) in

 let _ = writeLine ("# Record     = " ^ show tally.n_record     ) in
 let _ = writeLine ("# Let        = " ^ show tally.n_let        ) in
 let _ = writeLine ("# LetRec     = " ^ show tally.n_letrec     ) in
 let _ = writeLine ("# Ifthenelse = " ^ show tally.n_ifthenelse ) in
 let _ = writeLine ("# Typedterm  = " ^ show tally.n_typedterm  ) in

 %% -------------------- rare --------------------
 let _    = writeLine "" in

 let _ = writeLine ("# Seq        = " ^ show tally.n_seq        ) in
 let _ = writeLine ("# Bind       = " ^ show tally.n_bind       ) in
 let _ = writeLine ("# The        = " ^ show tally.n_the        ) in
 let _ = writeLine ("# Transform  = " ^ show tally.n_transform  ) in

 %% -------------------- none? --------------------
 let _    = writeLine "" in

 let _ = writeLine ("# And        = " ^ show tally.n_and        ) in
 let _ = writeLine ("# Pi         = " ^ show tally.n_pi         ) in
 let _ = writeLine ("# Any        = " ^ show tally.n_any        ) in
 let _ = writeLine ("# ApplyN     = " ^ show tally.n_applyn     ) in
 let _ = writeLine ("# unknown    = " ^ show tally.n_mystery    ) in
 let _ = writeLine "=================================" in
 let _ = priorTally := tally in
 ()

op tally_term (tally : Tally) (term : MSTerm) : MSTerm * Tally =
 let tally =
     case term of
       | Apply      _ -> tally << {n_apply     = tally.n_apply     + 1}
       | ApplyN     _ -> tally << {n_applyn    = tally.n_applyn    + 1}
       | Record     _ -> tally << {n_record    = tally.n_record    + 1}
       | Bind       _ -> tally << {n_bind      = tally.n_bind      + 1}
       | The        _ -> tally << {n_the       = tally.n_the       + 1}
       | Let        _ -> tally << {n_let       = tally.n_let       + 1}
       | LetRec     _ -> tally << {n_letrec    = tally.n_letrec    + 1}
       | Var        _ -> tally << {n_var       = tally.n_var       + 1}
       | Fun        _ -> tally << {n_fun       = tally.n_fun       + 1}
       | Lambda     _ -> tally << {n_lambda    = tally.n_lambda    + 1}
       | IfThenElse _ -> tally << {n_ifthenelse= tally.n_ifthenelse+ 1}
       | Seq        _ -> tally << {n_seq       = tally.n_seq       + 1}
       | TypedTerm  _ -> tally << {n_typedterm = tally.n_typedterm + 1}
       | Transform  _ -> tally << {n_transform = tally.n_transform + 1}
       | Pi         _ -> tally << {n_transform = tally.n_pi        + 1}
       | Any        _ -> tally << {n_transform = tally.n_any       + 1}
       | And        _ -> tally << {n_and       = tally.n_and       + 1}
       | _            -> 
         let _ = writeLine("unknown : " ^ anyToString term) in
         tally << {n_mystery   = tally.n_mystery   + 1}
 in
 (term, tally)

op tally_type (tally : Tally) (typ : MSType) : MSType * Tally =
 (typ, tally)

op tally_pattern (tally : Tally) (pat : MSPattern) : MSPattern * Tally =
 (pat, tally)

op SpecTransform.initTermTypeCounter (spc : Spec) : () =
 let _ = priorTally := newTally "zero_tally" in
 ()

op SpecTransform.countTermTypes (spc : Spec, msg : String) : () =
 let tally = newTally msg in
 let tsp   = (tally_term, tally_type, tally_pattern) in
 let tally = foldOpInfos (fn (info, tally) ->
                            let (_, tally) = mapAccumTerm tsp tally info.dfn in
                            tally)
                         tally
                         spc.ops
 in
 let _ = printTally tally in
 ()

end-spec
