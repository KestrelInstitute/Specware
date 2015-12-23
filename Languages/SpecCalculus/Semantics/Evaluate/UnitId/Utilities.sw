(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
Derived from r1.5 SW4/Languages/SpecCalculus/Semantics/UnitId.sl
*)

SpecCalc qualifying spec
  import /Languages/SpecCalculus/Semantics/Environment
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
  import /Library/Unvetted/StringUtilities

 type UIDPath    = List String
 type Shadowing  = List UIDPath
 type Shadowings = List Shadowing
 type Chars      = List Char


(*
Given a string (assumed to be a filesystem path), this parses
the string and attempts to form a canonical unitId for that object.
If the string does not begin with `/', then it is assumed to be
relative to the directory in which \Specware\ was invoked. In this
case we prefix the path with the current directory to make it
absolute and canonical.

The following two functions do not handle '#' in a path. However,
in the places they are used at present, no such paths are expected.
*)

  op  pathToCanonicalUID : String -> Env UnitId
  def pathToCanonicalUID str =
    return (pathStringToCanonicalUID(str,false))

  op  topPathToCanonicalUID : String -> Env UnitId
  def topPathToCanonicalUID str =
    return (pathStringToCanonicalUID(str,true))

  op  pathStringToCanonicalUID : String * Bool -> UnitId
  def pathStringToCanonicalUID (str,global?) =
    %% Windows SWPATHs can have \'s                       
    let str :: opt_hash = splitStringAt(str,"\#") in
    let str = map (fn #\\ -> #/ | c -> c) str in
    let absoluteString =
      case (explode str) of
        | #/ :: _ -> str
        | c :: #: :: r -> (Char.show(toUpperCase c)) ^ ":" ^ (implode r)
        | _ -> (getCurrentDirectory ()) ^ "/" ^ str
    in
    let relPath = splitStringAt(absoluteString,"/") in
    let relPath = filter (fn s -> s ~= "") relPath in
    {path = if global? then addDevice? relPath else relPath,
     hashSuffix = case opt_hash of
                    | [hash_nm] -> Some hash_nm
                    | _ -> None}

(*
This is like the above except that in this case the path is relative.
That is, if it starts with `/' then it assumed relative to something
in the \verb+SWPATH+. It if doesn't start with `/', then it is assumed
relative to the UnitId making the reference.

A UnitId is a path of elements separated by '/' and possibly suffixed
with a final path element separated from the rest with '#'.
Note that not all UnitId's are parsed here. Those appearing in specs
are parsed by the usual MetaSlang parser. This is used to handle
strings typed into the lisp interface.

There are a number of well-formedness conditions. The character
'#' cannot appear in a path element. A path like with \ldots /# \ldots
is not valid. A path without an element preceeding the '#' is invalid.
*)

  op  pathToRelativeUID : String -> Env RelativeUID
  def pathToRelativeUID str =
    let charList : Chars = explode str in
    let pathElems : List Chars = splitAtChar #/ charList in
    let def validElem charList =
      when (## in? charList)
        (raise (SyntaxError "Unit identifier path element contains # symbol")) in
    {
      when (pathElems = [])
        (raise (SyntaxError "Empty unit identifier"));
      suffix <- last pathElems;
      pathPrefix <- removeLast pathElems;
      mapM validElem (pathPrefix : List Chars);
      firstSuffixChar <- first suffix;
      lastSuffixChar <- last suffix;
      when (firstSuffixChar = ##)
        (raise (SyntaxError "Misplaced #"));
      when (lastSuffixChar = ##)
        (raise (SyntaxError "Misplaced #"));
      (case (splitAtChar ## suffix) of
         | [] -> SpecCalc.error "pathToRelativeUID: Internal error"
         | [pathEnd] ->
            (case charList of
              | #/::_ -> return (SpecPath_Relative
                        {path = (map implode (pathPrefix ++ [pathEnd])),
                         hashSuffix = None})
              | _ -> return (UnitId_Relative
                        {path = (map implode (pathPrefix ++ [pathEnd])),
                         hashSuffix = None}))
         | [pathEnd,hashSuffix] ->
            (case charList of
              | #/::_ -> return (SpecPath_Relative
                         {path = (map implode (pathPrefix ++ [pathEnd])),
                          hashSuffix = Some (implode hashSuffix)})
              | _ -> return (UnitId_Relative
                         {path = (map implode (pathPrefix ++ [pathEnd])),
                          hashSuffix = Some (implode hashSuffix)}))
         | _ -> raise (SyntaxError "Unit identifier contains two or more # symbols"))
    }
(*
Normalizes a canonical unitId by removing
occurrences of ``.'' and ``..''. The function iterates until
a fixpoint is reached since there may be sequences of "..".
*)
  op  normalizeUID : UnitId -> UnitId
  def normalizeUID {path,hashSuffix} =
    let
      def onePass elems =
        case elems of
          | [] -> []
          | elem::"."::rest -> Cons (elem,rest)
          | elem::".."::rest -> rest
          | elem::rest -> Cons (elem, (onePass rest))
      def iterate current next =
        if current = next then
          current
        else
          iterate next (onePass next)
    in
      {path = addDevice?(iterate path (onePass path)), hashSuffix = hashSuffix}

  %% This would fix bug 005 but break PSL bootstrap...
  %% def normalizeUID {path,hashSuffix} =
  %%   {path       = trueFilePath (path, false), % false means absolute, true means relative 
  %%   hashSuffix = hashSuffix}

  op  addDevice?: UIDPath -> UIDPath
  def addDevice? path =
    if msWindowsSystem?
      then (if ~(path = []) && deviceString? (head path)
	     then path
	     else Cons("C:",path))  %Don't like the hard-coded C: here.
      else path
(*
This converts a canonical UnitId to a filesystem path name. It will
always be prefixed with a "/". When converting to a path, any
hash suffix is ignored.
*)
  op  uidToFullPath : UnitId -> String
  def uidToFullPath {path,hashSuffix=_} =
   let device? = deviceString? (head path) in
   let mainPath = flatten (foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             [] (if device? then tail path else path))
   in if device?
	then (head path) ^ mainPath
	else mainPath


  op  uidToPath : UnitId -> String
  def uidToPath {path,hashSuffix=_} =
    %foldr (fn (elem,path) -> "/" ^ elem ^ path) "" path
   let path = abbreviatedPath path in
   let device? = deviceString? (head path) in
   %% More efficient
   let tildaPath? = (head path = "~") in
   let mainPath = flatten (foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             [] (if tildaPath? || device? then tail path else path))
   in if tildaPath?
	then "~" ^ mainPath
	else if device?
	then (head path) ^ mainPath
	else mainPath

  op  abbreviatedPath: UIDPath -> UIDPath
  def abbreviatedPath path =
    let home = case getEnv "HOME" of
                | Some str -> splitStringAt(str,"/")
                | None ->
               case getEnv "HOMEPATH" of
                | Some str -> splitStringAt(str,"/")
                | None -> []
    in
    if home = [] then path
    else
    let def removeCommonPrefix(p,home) =
          case (p,home) of
	    | (p,[]) -> ["~"] ++ p	% Success
	    | ([],_) -> path % [] could cause errors in callers
	    | (p1::rp,h1::rh) ->
	      if p1 = h1 then removeCommonPrefix(rp,rh)
		else path		% Return top-level version
	    | _ -> path
    in
    removeCommonPrefix(path,home)

(*
This is like the above but accommodates the suffix as well.
*)
  op  uidsToString : UnitIds -> String
  def uidsToString uids =
    case uids of
      | [] -> "[]"
      | uid :: uids ->
        "[" ^ (uidToString uid) ^ (foldl (fn (s,uid) -> s ^ ", " ^ uidToString uid) "" uids) ^ "]"

 %op  SpecCalc.uidToString : UnitId -> String % already declared in /Languages/SpecCalculus/Semantics/Exception.sw
  def SpecCalc.uidToString {path,hashSuffix} =
   let path = abbreviatedPath path in
   let device? = deviceString? (head path) in
   let tildaPath? = (head path = "~") in
   let mainPath = flatten (foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             [] (if tildaPath? || device? then tail path else path))
   in
   let fileName =
     if tildaPath? then
        "~" ^ mainPath
     else if device?
     then (head path) ^ mainPath
     else mainPath
   in
   case hashSuffix of
     | None -> fileName
     | Some suffix -> 
       if fileName = "" then
	 suffix
       else
	 fileName ^"\#"^ suffix


 %op  SpecCalc.relativeUID_ToString : RelativeUID -> String % already declared in /Languages/SpecCalculus/Semantics/Exception.sw
  def SpecCalc.relativeUID_ToString rel_uid =
   case rel_uid of
     | UnitId_Relative {path, hashSuffix} -> 
       (let filename = case path of
			 | []    -> "" % ???
			 | _ -> 
	                   flatten (tail (foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                                          [] 
                                          path))
	in
        case hashSuffix of
	  | None        -> filename
	  | Some suffix -> 
	    if filename = "" then 
	      suffix
	    else 
	      filename ^"\#"^ suffix)
     | SpecPath_Relative unitId -> uidToString unitId


(*
Convert a canonical UnitId to one relatived to some base.
Used by print commands defined in /Languages/SpecCalculus/Semantics/Evaluate/Print.sw
*)

  op  relativizeUID : UnitId -> UnitId -> RelativeUID
  def relativizeUID base target =
    UnitId_Relative {path       = relativizePath base.path target.path,
                     hashSuffix = target.hashSuffix}

  op  relativizePath : UIDPath -> UIDPath -> UIDPath
  def relativizePath base target =
    let 
      def addUpLinks (base,target) =
	case base of
	  | []      -> target
	  | _::tail -> Cons("..", addUpLinks (tail, target))

      def removeCommonPrefix (base,target) =
        case (base,target) of
	  | ([],target) -> target 
	  | (base,  []) -> addUpLinks (base, [])
	  | (bx::bt, tx::tt) ->
	    if bx = tx then removeCommonPrefix(bt,tt)
	    else addUpLinks (bt, target)
    in
    removeCommonPrefix (base, target) % and add updots

(*
This takes a string that is assumed to be punctuated some number of times
(possibly none) with the specified char. This breaks the string into
segments with the given char removed. Thus \verb+splitStringAtChar #/ "a/b//c"+
yields \verb+["a", "b", "c"].

The next function will go away.
*)
(*
  op  splitStringAtChar : Char -> String -> Strings
  def splitStringAtChar char str =
    let def parseCharList chars =
      case chars of
        | [] -> []
        | fst::rest ->
           if fst = char then
             parseCharList rest
           else
             let (taken,left) = takeWhile (fn c -> ~(c = char)) chars in
             Cons ((implode taken), parseCharList left)
    in
      parseCharList (explode str)
*)

  op  splitAtChar : Char -> Chars -> List Chars
  def splitAtChar char charList =
    let def parseCharList chars =
      case chars of
        | [] -> []
        | fst::rest ->
           if fst = char then
             parseCharList rest
           else
             let (taken,left) = takeWhile (fn c -> ~(c = char)) chars in
             Cons (taken, parseCharList left)
    in
      parseCharList charList
(*
This takes a prefix from the list while the given predicate holds. It
doesn't belong here.
*)
  op  takeWhile : [a] (a -> Bool) -> List a -> (List a) * (List a)
  def takeWhile pred l =
    case l of
      | [] -> ([],[])
      | x::xs ->
          if (pred x) then
            let (take,rest) = takeWhile pred xs in
              (Cons (x,take), rest)
          else
            ([], l)
(*
The next two functions will disappear.
  op  removeLastElem : Strings -> Env Strings
  def removeLastElem elems =
    case elems of
      | [] -> SpecCalc.error "removeLastElem: encountered empty string list"
      | x::[] -> return []
      | x::rest -> {
          suffix <- removeLastElem rest;
          return (Cons (x,suffix))
        }

  op  lastElem : Strings -> Env String
  def lastElem elems =
    case elems of
      | [] -> SpecCalc.error "lastElem: encountered empty string list"
      | x::[] -> return x
      | _::rest -> lastElem rest

*)

  op  removeLast: [a] List a -> Env (List a)
  def removeLast elems =
    case elems of
      | [] -> SpecCalc.error "removeLast: encountered empty list"
      | x::[] -> return []
      | x::rest -> {
          suffix <- removeLast rest;
          return (Cons (x,suffix))
        }

  op  first : [a] List a -> Env a
  def first elems =
    case elems of
      | [] -> SpecCalc.error "first: encountered empty list"
      | x::_ -> return x

  op  last : [a] List a -> Env a
  def last elems =
    case elems of
      | [] -> SpecCalc.error "last: encountered empty list"
      | x::[] -> return x
      | _::rest -> last rest
(*
Functions for finding definitions in specs in the environment. Used by
emacs interface functions.
*)
  %% Top-level functions
  op  findDefiningUID : QualifiedId * String * (Option GlobalContext) -> List (String * String)
  def findDefiningUID(qId,uidStr,optGlobalContext) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
          let unitId = pathStringToCanonicalUID(uidStr,false) in
            case (findDefiningUIDforOpInContext(qId,unitId,globalContext,[],false)).1
               ++ (findDefiningUIDforTypeInContext(qId,unitId,globalContext,[],false)).1
               ++ findTheoremLocations(qId,uidStr,optGlobalContext) of
              | []     -> removeDuplicates((searchForDefiningUID(qId,optGlobalContext)))
              | result -> removeDuplicates result

  op  searchForDefiningUID : QualifiedId * (Option GlobalContext) -> List (String * String)
  def searchForDefiningUID(qId,optGlobalContext) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
        removeDuplicates
          ((searchForDefiningUIDforOp(qId,globalContext,[],false))
           ++ (searchForDefiningUIDforType(qId,globalContext,[],false)))

  op  findDefiningUIDforOp
       : QualifiedId * Spec * UnitId * UnitIds * GlobalContext * UnitIds * Bool
           -> List (String * String) * UnitIds
  def findDefiningUIDforOp(opId,spc,unitId,depUIDs,globalContext,seenUIDs,rec?) =
    let def findLocalUID (opId,seenUIDs) =
          if localOp?(opId,spc)
	    then ([("Op", uidToFullPath unitId)],seenUIDs)
	  else
	    foldr (fn (unitId,(result,seenUIDs)) ->
		   let (new,seenUIDs) = findDefiningUIDforOpInContext(opId,unitId,globalContext,seenUIDs,true) in
		   (new ++ result, seenUIDs))
	          ([],seenUIDs) 
		  depUIDs
    in   
    %% If being called recursively, we have already identified a particlar op in its spec and
    %% we are trying to find it local spec in imports so use findTheOp instead of findAllOps
    if rec? then
      case findTheOp(spc,opId) of
	| Some _ -> findLocalUID (opId,seenUIDs)
	| None   ->
          case opId of
	    | Qualified (q, id) ->
	      (if q = UnQualified then
		 ([],seenUIDs)
		 %% If the spec was imported using "qualifiying" then the original def may be unqualified
	       else 
		 findDefiningUIDforOp (Qualified (UnQualified, id),
				       spc,
				       unitId,
				       depUIDs,
				       globalContext,
				       seenUIDs,
				       true))
	    | _ -> ([],seenUIDs) 
    else 
      case findAllOps (spc, opId) of
	| [] -> ([],seenUIDs)
	| infos ->
	  %% This is the top-level version so seenUIDs should be [] and returned seenUIDs will be ignored
	  %% seenUIDs for one op shouldn't affect seenUIDs for another
          foldr (fn (info,(val,_)) ->
		 let (nval,seenUIDs) = 
                     case filePositionOfTerm info.dfn of
                       | Some(File (file_name, (left, _, _), _)) -> ([(show left, file_name)], seenUIDs)
                       | _ -> findLocalUID (primaryOpName info,seenUIDs) in
		 (nval ++ val,seenUIDs))
	        ([],seenUIDs)
		infos

  op  findDefiningUIDforOpInContext: QualifiedId * UnitId * GlobalContext * UnitIds * Bool
                                     -> List (String * String) * UnitIds
  def findDefiningUIDforOpInContext (opId, unitId, globalContext, seenUIDs, rec?) =
    case evalPartial globalContext unitId of
      | Some(Spec spc,_,depUIDs,_) ->
        findDefiningUIDforOp (opId, spc, unitId,
			      filter (fn uid -> uid nin? seenUIDs) depUIDs,
			      globalContext, Cons(unitId,seenUIDs), rec?)
      | _ -> ([],seenUIDs)

  op  getTermForUnitId: UnitId * GlobalContext -> Option SCTerm
  def getTermForUnitId (unitId,globalContext) =
    case evalPartial globalContext unitId of
      | Some(_,_,_,term) -> Some term
      | _ -> None

  op findUnitIdForUnit (val : Value, globalContext : GlobalContext) : Option UnitId =
    foldMap (fn result -> fn unitId -> fn (vali,_,_,_) ->
	     case result of
	       | Some _ -> result
	       | None -> if val = vali then Some unitId else None)
      None globalContext

  op setCurrentUIDforSpec(spc: Spec): Env () =
    % let _ = writeLine("setCurrentUIDforSpec:\n"^printSpec spc) in
    {globalContext <- getGlobalContext;
     case findUnitIdForUnit(Spec spc, globalContext) of
       | None -> return ()
       | Some uid ->
         setCurrentUID uid}

  op UIDfromPosition(pos: Position): Option UnitId =
    case pos of
      | File(filnm, _, _) ->
        let end_uid = length filnm - 3 in
        let filnm = if testSubseqEqual?(filnm, ".sw",  end_uid, 0)
                      then subFromTo(filnm, 0, end_uid) else filnm
        in
        let uid = pathStringToCanonicalUID(filnm, false) in
        Some (uid << {hashSuffix = Some ""}
              )
       | _ -> None

  op setCurrentUIDfromPos(pos: Position): Env (UnitId) =
    % let _ = writeLine("setCurrentUIDfromPos:\n"^anyToString pos) in
    {saveUID <- getCurrentUID;
     (case pos of
      | File(filnm, _, _) ->
        let end_uid = length filnm - 3 in
        let filnm = if testSubseqEqual?(filnm, ".sw",  end_uid, 0)
                      then subFromTo(filnm, 0, end_uid) else filnm
        in
        {uid <- pathToCanonicalUID filnm;
         %% Putting hashSuffix enables sub units to be found
         when (saveUID.path ~= uid.path)
           (setCurrentUID (uid << {hashSuffix = Some "dummy"}))}
       | _ -> return ());
     return saveUID}


  op  findUnitIdTermForUnit: Value * GlobalContext -> Option (UnitId * SCTerm)
  def findUnitIdTermForUnit (val, globalContext) =
    foldMap (fn result -> fn unitId -> fn (vali,_,_,term) ->
	     case result of
	       | Some _ -> result
	       | None -> if val = vali then Some (unitId,term) else None)
      None globalContext

  op getSpecPath0(): UnitIds

  op relativePath(ref_path: UIDPath, path: UIDPath): UIDPath =
    let ref_len = length ref_path in
    if ref_len <= length path
        && ref_path = subFromTo(path, 0, ref_len)
      then subFromTo(path, ref_len, length path)
      else path

  op relativeToSpecPath({path, hashSuffix}: UnitId): UnitId =
    let swpaths = getSpecPath0() in
    let rel_paths0 :: rel_paths = map (fn path_uid -> relativePath(path_uid.path, path)) swpaths in
    let min_path = foldl (fn (min_path, l) -> if length l < length min_path then l else min_path) rel_paths0 rel_paths in
    {path = min_path, hashSuffix = hashSuffix}

  op findRelativeUIDforValue(val: Value): Option RelativeUID =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
    case findUnitIdTermForUnit(val, global_context) of
      | None -> None
      | Some (uid, _) -> Some(SpecPath_Relative(relativeToSpecPath uid))

  op  findDefiningTermForUnit: Value * GlobalContext -> Option SCTerm
  def findDefiningTermForUnit (val, globalContext) =
    foldMap (fn result -> fn unitId -> fn (vali,_,_,term) ->
	     case result of
	       | Some _ -> result
	       | None -> if val = vali then Some (term) else None)
      None globalContext

  op  searchForDefiningUIDforOp: QualifiedId * GlobalContext * UnitIds * Bool
                                -> List (String * String)
  def searchForDefiningUIDforOp (opId, globalContext, seenUIDs, rec?) =
    %% Currently rec? is always false
    foldMap (fn result -> fn unitId -> fn (val,_,depUIDs,_) ->
	     case result of
	       | _::_ -> result		% After finding any stop looking
	       | []   ->
	     case val of
	       | Spec spc ->
	         (findDefiningUIDforOp (opId,
					spc,
					unitId,
					depUIDs,
					globalContext,
					seenUIDs,
					rec?)).1
	       | _ -> [])
      []
      globalContext

  op  findDefiningUIDforType : QualifiedId * Spec * UnitId * UnitIds * GlobalContext * UnitIds * Bool
                               -> List (String * String) * UnitIds
  def findDefiningUIDforType (typeId, spc, unitId, depUIDs, globalContext, seenUIDs, rec?) =
    let def findLocalUID (typeId,seenUIDs) =
          if localType? (typeId, spc) then
	    ([("Type", uidToFullPath unitId)],seenUIDs)
	  else
	    foldr (fn (unitId,(result,seenUIDs)) ->
		   let (new,seenUIDs)
		      = findDefiningUIDforTypeInContext (typeId,
							 unitId,
							 globalContext,
							 seenUIDs,
							 true)
		   in
		   (new ++ result,seenUIDs))
	          ([],seenUIDs) 
		  depUIDs
    in   
    %% If being called recursively, we have already identified a particlar type in its spec and
    %% we are trying to find it local spec in imports so use findTheType instead of findAllTypes
    if rec? then
      case findTheType (spc, typeId) of
	| Some _ -> findLocalUID (typeId,seenUIDs)
	| None   ->
          case typeId of
	    | Qualified (q, id) ->
	      (if q = UnQualified then
		 ([],seenUIDs)
		 %% If the spec was imported using "qualifiying" then the original def may be unqualified
	       else 
		 findDefiningUIDforType (Qualified (UnQualified, id),
					 spc,
					 unitId,
					 depUIDs,
					 globalContext,
					 seenUIDs,
					 true))
	    | _ -> ([],seenUIDs) 
    else 
      case findAllTypes(spc,typeId) of
	| [] -> ([],seenUIDs)
	| infos ->
	  %% This is the top-level version so seenUIDs should be [] and returned seenUIDs will be ignored
	  %% seenUIDs for one op shouldn't affect seenUIDs for another
          foldr (fn (info, (val,_)) ->
		 let (nval,seenUIDs) =
                     case filePositionOfType info.dfn of
                       | Some(File (file_name, (left, _, _), _)) -> ([(show left, file_name)], seenUIDs)
                       | _ -> findLocalUID (primaryTypeName info, seenUIDs)
                 in
		 (nval ++ val,seenUIDs))
	        ([],seenUIDs)
		infos

  op  findDefiningUIDforTypeInContext : QualifiedId * UnitId * GlobalContext * UnitIds * Bool
                                       -> List (String * String) * UnitIds
  def findDefiningUIDforTypeInContext (typeId, unitId, globalContext, seenUIDs, rec?) =
    case evalPartial globalContext unitId of
      | Some (Spec spc, _, depUIDs,_) ->
        findDefiningUIDforType (typeId, spc, unitId,
				filter (fn uid -> uid nin? seenUIDs) depUIDs,
				globalContext, Cons(unitId, seenUIDs), rec?)
      | _ -> ([],seenUIDs)

  op  searchForDefiningUIDforType : QualifiedId * GlobalContext * UnitIds * Bool -> List (String * String)
  def searchForDefiningUIDforType (typeId, globalContext, seenUIDs, rec?) =
    foldMap (fn result -> fn unitId -> fn (val, _, depUIDs, _) ->
	     case result of
	       | _::_ -> result		% After finding any stop looking
	       | []   ->
	     case val of
	       | Spec spc ->
	         (findDefiningUIDforType (typeId, spc, unitId, depUIDs, globalContext, seenUIDs, rec?)).1
	       | _ -> [])
      []
      globalContext

  %% TODO: This seems correct only for Windows.
  op absolutePath? (path : UIDPath) : Bool =
    case path of
      | [] -> false
      | s :: _ -> deviceString? s

%%% Find theorems in Spec
op findTheoremLocationsInSpec(Qualified(qual,id): QualifiedId, spc: Spec): List(String * String) =
  let results = foldlSpecElements
                  (fn (result, el) ->
                     case el of
                       | Property(_, Qualified(p_qual,p_id), _, _, File(filnm, (line, col, byte), _))
                       | p_id = id && (p_qual = qual || qual = UnQualified) ->
                         (show line, filnm) :: result
                       | _ -> result)
                  [] spc.elements
  in
  removeDuplicates results

op findTheoremLocations(qid: QualifiedId, uidStr: String, optGlobalContext: Option GlobalContext): List(String * String) =
  case optGlobalContext of
    | None -> []
    | Some globalContext ->
  let unitId = pathStringToCanonicalUID(uidStr,false) in
  case evalPartial globalContext unitId of
    | Some(Spec spc,_,_,_) -> findTheoremLocationsInSpec(qid, spc)
    | _ -> findTheoremLocationsInEnv(qid, optGlobalContext)

op findTheoremLocationsInEnv(qid: QualifiedId, optGlobalContext: Option GlobalContext): List(String * String) =
  case optGlobalContext of
    | None -> []
    | Some globalContext ->
  foldMap (fn result -> fn unitId -> fn (val,_,_,_) ->
	     case result of
	       | _::_ -> result		% After finding any stop looking
	       | []   ->
	     case val of
	       | Spec spc ->
                 findTheoremLocationsInSpec(qid, spc)
	       | _ -> [])
      []
      globalContext



 %%% Find relationship between Specs
 op  importPathsBetween: Spec * Spec -> List (List SCTermBody)
 def importPathsBetween(spc1,spc2) =
   let def findPaths(sp,path) =
         if sp = spc2
	   then [path]
	   else foldl (fn (result,el) ->
		       case el of
			 | Import(i_stm,i_spc,_,_) ->
			   findPaths(i_spc,Cons(i_stm.1,path)) ++ result
			 | _ -> result)
	          [] sp.elements
   in
     findPaths(spc1,[])

 op SpecTermToSpecName: SCTerm -> (Option String)
 def SpecTermToSpecName (scterm as (term,_)) =
   case term of
     | UnitId rUID -> Some (showRelativeUID(rUID))
     | Spec _ -> None
     | _ -> None


endspec
