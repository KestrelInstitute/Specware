spec {

  import /Languages/MetaSlang/CodeGen/Lisp/Lisp
  import /Languages/MetaSlang/Specs/StandardSpec
  
  sort SnarkSpec =
    {
     name: String,
     sortDecls: LispTerms,
     assertions: LispTerms,
     conjectures: LispTerms
    }

  op snarkSpec: Spec -> SnarkSpec

  def snarkSpec(spc) =
    {name = "Anonymous",
     sortDecls = snarkSorts(spc),
     assertions = [],
     conjectures = []
     }

  op snarkSorts: Spec -> LispTerms

  def snarkSorts(spc) =
      let declare_sort = Op "DECLARE-SORT" in
      let sorts = sortsAsList(spc) in
      map(fn (qual, id, info) ->
	     Apply (declare_sort, [Const (Symbol(qual, id))]))
         sorts


  def ppSpec (s : SnarkSpec) : Pretty =
      let sortDecls = s.sortDecls 	in
      let name = s.name 		in
%      let assertions = s.assertions in
%      let conjectures = s.conjectures in
      let ppSortTerms = map ppTerm sortDecls in
      prettysAll
     (
     (section (";;; Snark spec: " ^ name,
	       [string ("(in-package \"" ^ "SNARK" ^ "\")")]))
     ++ 
     (section (";;; Sorts",     List.map ppTerm     sortDecls))
%     List.++ [string "#||"] 
%     List.++ section (";;; Axioms",             List.map ppTerm       s.axioms)
%     List.++ [string "||#", emptyPretty ()]
    )

  op ppSpecToFile : SnarkSpec * String * Text -> ()

  def ppSpecToFile (spc, file, preamble) =
    let p = ppSpec spc in
    let t = format (80, p) in
    toFile (file, t ++ preamble)

  op ppSpecToTerminal : SnarkSpec -> ()

  def ppSpecToTerminal spc =
    let p = ppSpec spc in
    let t = format (80, p) in
    toTerminal t

  op ppSpecsToFile : List SnarkSpec * String * Text -> ()

  def ppSpecsToFile (specs, file, preamble) =
    let ps = List.map ppSpec specs in
    let p  = prettysAll ps in
    let t  = format (80, p) in
    toFile (file, t ++ preamble)

  op toSnark        : Spec -> SnarkSpec
  op toSnarkEnv     : Spec -> SnarkSpec
  op toSnarkFile    : Spec * String * Text -> ()
  op toSnarkFileEnv : Spec * String * Text -> ()

  def toSnark spc =
      toSnarkEnv(spc)

(*
  def toSnarkEnv (spc) =
      let _   = writeLine "toSnark"                             in
      let spc = System.time(translateMatch(spc))          in
      let spc = System.time(arityNormalize(spc)) in
      let spc = System.time(lisp(spc))                             in
      spc 
*)

  def toSnarkEnv (spc) =
%      let _   = writeLine ("Translating " ^ spc.name ^ " to Snark.") in
%      let spc = translateMatch(spc)          in
%      let spc = arityNormalize(spc) in
      let spc = snarkSpec(spc)                          in
%      let _ = ppSpecToTerminal spc         in
      spc 
             
  def toSnarkFile (spc, file, preamble) =  
      toSnarkFileEnv (spc, file, preamble) 

  def toSnarkFileEnv (spc, file, preamble) =
      let _ = writeLine("Writing Snark file "^file) in
      let spc = toSnarkEnv (spc) in
      ppSpecToFile (spc, file, preamble)



  }
