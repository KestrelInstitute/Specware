Specware qualifying
spec
  import Make

  %% toplevel cmd "genall" arrives here...
  op  genAll  (pos : Position) (uid : RelativeUID) : SpecCalc.Env ValueInfo =
    let 
      def aux old_pcs =
	{
	 %% running cleanEnv causes uid to re-evaluate, 
	 %% rather than being fetched directly from cache...
	 myCleanEnv;  

	 spec_info <- SpecCalc.evaluateUIDX pos uid;
	 new_pcs <- getPrismChoices; % get from environment
	 version <- return (prismVersion (old_pcs, new_pcs));
	 makeLCJ  spec_info uid version;
	 print ("\n");
	 case new_pcs of
	   | [] -> return spec_info
	   | _ -> aux new_pcs
        }
    in
    aux []

  op  prismVersion : PrismChoices * PrismChoices -> String
  def prismVersion (old_pcs, new_pcs) =
    case old_pcs of
      | [] -> (case new_pcs of 
		 | [] -> "OnlyVersion"
		 | pc :: pcs -> foldl (fn (s, pc) -> s ^ "_0") "Version_0" pcs)
      | pc :: pcs ->
        foldl (fn (s, pc) -> s ^ "_" ^ (natToString pc.n))
	      ("Version_" ^ (natToString pc.n)) 
	      pcs

  %% clone of op in Specware.sw -- simpler than restructuring code
  op  myCleanEnv: SpecCalc.Env ()
  def myCleanEnv =
    {resetGlobals;
     myEnsureBase;
     cleanupGlobalContext}
     
  %% clone of op in Specware.sw -- simpler than restructuring code
  op  myEnsureBase: SpecCalc.Env ()
  def myEnsureBase =
    {(optBaseUnitId,_) <- getBase;
     (case optBaseUnitId of
	| None   -> setBaseToPath "/Library/Base"
	| Some _ -> return ())}


endspec
