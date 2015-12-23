(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Specware qualifying spec
{
  import Make
  import /Languages/SpecCalculus/Semantics/Bootstrap % for cleanEnv

  %% toplevel cmd "genall" arrives here...
  op genAll  (pos : Position) (uid : RelativeUID) : SpecCalc.Env () =
   genMany pos uid (TRUE) (FALSE)

  op stop_after_n (n : Nat) : (PrismStatus -> Bool) =
    fn status -> status.version >= n

  op genMany (pos        : Position) 
             (uid        : RelativeUID) 
             (use?       : PrismStatus -> Bool) 
             (terminate? : PrismStatus -> Bool) 
    : SpecCalc.Env () =
    let 
      def aux first? incr_version? =
	{
         status <- nextPrismStatus incr_version?;
         if (terminate? status) then
           return ()  
         else if (~ first?) && initialStatus? status then 
           return ()
         else if use? status then
           let str = case status.choices of
                       | []   -> ""
                       | [c1] -> show c1.n
                       | c1 :: choices ->
                         foldl (fn (str, choice) -> str ^ ", " ^ show choice.n) (show c1.n) choices
           in
           {
            spec_info <- SpecCalc.evaluateUID pos uid;
            print ("\ngenAll:  version = " ^ show status.version ^ " for choices: [" ^ str ^ "]\n");
            makeLCJ spec_info uid status;
            print ("\n");
            aux false true
            }
         else
           aux false false
        }
    in
    {
     cleanEnv; 
     initPrismStatus;
     aux true true
     }

  op initialStatus? (status : PrismStatus) :  Bool =
   foldl (fn (done?, choice) ->
            if choice.n > 0 then
              false
            else
              done?)
         true 
         status.choices
    
}

