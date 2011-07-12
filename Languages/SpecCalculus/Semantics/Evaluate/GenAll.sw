Specware qualifying spec
{
  import Make
  import /Languages/SpecCalculus/Semantics/Bootstrap % for cleanEnv

  %% toplevel cmd "genall" arrives here...
  op  genAll  (pos : Position) (uid : RelativeUID) : SpecCalc.Env () =
    let 
      def aux first? =
	{
         setIncrementNextPrism true;
         choices <- getPrismChoices;
         %% Touching the prisms should ensure that every unit even indirectly referencing them is re-evaluated.
         choices <- touchPrismsAboutToChange choices;  
         writeGlobalVar ("PrismChoices", choices);
         if (~ first?) && allChoicesAreZero? choices then
           %% Since this isn't the first pass, an increment must have overflowed back to the origin.
           return ()
         else
           {
            spec_info <- SpecCalc.evaluateUID pos uid;
            version   <- prismVersion;
            print ("genAll:  version = " ^ anyToString version ^ "\n");
            makeLCJ spec_info uid version;
            print ("\n");
            aux false
            }
        }
    in
    {
     cleanEnv; 
     writeGlobalVar ("PrismChoices", []);
     writeGlobalVar ("IncrementNextPrism?", true); % is default value ever used?
     aux true
     }

  op allChoicesAreZero? (choices : PrismChoices) :  Bool =
   foldl (fn (done?, choice) ->
            if choice.n > 0 then
              false
            else
              done?)
         true 
         choices
    
  op touchPrismsAboutToChange (choices : PrismChoices) : SpecCalc.Env PrismChoices =
   case choices of
     | [] -> return []
     | choice :: choices ->
       {
        %% We always touch the first prism.
        touch choice.uid;
        let n = choice.n + 1 in
        if n < cardinality choice then
          let choice = choice << {n = n} in
          %% Don't touch subsequent prisms when they are not going to change.
          return (choice :: choices)
        else
          %% If incrementing this choice would overflow and carry over
          %% into a change to next choice, then keep touching prisms.
          let choice = choice << {n = 0} in
          {
           choices <- touchPrismsAboutToChange choices;
           return (choice :: choices)
           }
       }

  op touch (uid : UnitId) : Env () =
   let touched = futureTimeStamp in
   {
    optValue <- lookupInLocalContext (UnitId_Relative uid);
    case optValue of
      | Some v ->
        bindInLocalContext (UnitId_Relative uid) (v.1, touched, v.3)
      | None ->
        {
         optValue <- lookupInLocalContext (SpecPath_Relative uid);
         case optValue of
           | Some v ->
             bindInLocalContext (SpecPath_Relative uid) (v.1, touched, v.3)
           | None ->
             {
              optValue <- lookupInGlobalContext uid;
              case optValue of
                | Some v -> bindInGlobalContext uid (v.1, touched, v.3, v.4)
                | None -> return ()
                  }}
        }

  op prismVersion : SpecCalc.Env String =
   {
    choices <- getPrismChoices;
    return (case choices of
              | [] -> "OnlyVersion"
              | pcs ->
                foldl (fn (s, pc) -> s ^ "_" ^ (natToString pc.n))
                      "Version"
                      pcs)
    }

}

