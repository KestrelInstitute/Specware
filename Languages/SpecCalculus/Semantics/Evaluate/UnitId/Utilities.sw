(*
Derived from r1.5 SW4/Languages/SpecCalculus/Semantics/UnitId.sl
*)

SpecCalc qualifying spec
  import ../../Environment
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

  op  pathStringToCanonicalUID : String * Boolean -> UnitId
  def pathStringToCanonicalUID (str,global?) =
    %% Windows SWPATHs can have \'s                       
    let str = map (fn #\\ -> #/ | c -> c) str in
    let absoluteString =
      case (explode str) of
        | #/ :: _ -> str
        | c :: #: :: r -> (Char.toString(toUpperCase c)) ^ ":" ^ (implode r)
        | _ -> (getCurrentDirectory ()) ++ "/" ++ str
    in
    let relPath = splitStringAtChar #/ absoluteString in
    {path = if global? then addDevice? relPath else relPath,
     hashSuffix = None}

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
    let charList : List Char = explode str in
    let pathElems : List (List Char) = splitAtChar #/ charList in
    let def validElem charList =
      when (member (##,charList))
        (raise (SyntaxError "Unit identifier path element contains # symbol")) in
    {
      when (pathElems = [])
        (raise (SyntaxError "Empty unit identifier"));
      suffix <- last pathElems;
      pathPrefix <- removeLast pathElems;
      mapM validElem (pathPrefix : List (List Char));
      firstSuffixChar <- first suffix;
      lastSuffixChar <- last suffix;
      when (firstSuffixChar = ##)
        (raise (SyntaxError "Misplaced #"));
      when (lastSuffixChar = ##)
        (raise (SyntaxError "Misplaced #"));
      (case (splitAtChar ## suffix) of
         | [] -> error "pathToRelativeUID: Internal error"
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
The following is used to normalize a canonical unitId by removing
occurrences of ``.'' and ``..''. The function needs to be iterated until
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

  op  addDevice?: List String -> List String
  def addDevice? path =
    if msWindowsSystem?
      then (if ~(path = []) && deviceString? (hd path)
	     then path
	     else Cons("C:",path))
      else path
(*
This converts a canonical UnitId to a filesystem path name. It will
always be prefixed with a "/". When converting to a path, any
hash suffix is ignored.
*)
  op  uidToFullPath : UnitId -> String
  def uidToFullPath {path,hashSuffix=_} =
   let device? = deviceString? (hd path) in
   let mainPath = concatList (foldr (fn (elem,result) -> cons("/",cons(elem,result)))
			        [] (if device? then tl path else path))
   in if device?
	then (hd path) ^ mainPath
	else mainPath


  op  uidToPath : UnitId -> String
  def uidToPath {path,hashSuffix=_} =
    %foldr (fn (elem,path) -> "/" ^ elem ^ path) "" path
   let path = abbreviatedPath path in
   let device? = deviceString? (hd path) in
   %% More efficient
   let tildaPath? = (hd path = "~") in
   let mainPath = concatList (foldr (fn (elem,result) -> cons("/",cons(elem,result)))
			        [] (if tildaPath? or device? then tl path else path))
   in if tildaPath?
	then "~" ^ mainPath
	else if device?
	then (hd path) ^ mainPath
	else mainPath

  op  abbreviatedPath: List String -> List String
  def abbreviatedPath path =
    let home = case getEnv "HOME" of
                | Some str -> splitStringAtChar #/ str
                | None ->
               case getEnv "HOMEPATH" of
                | Some str -> splitStringAtChar #/ str
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
  op  uidsToString : List UnitId -> String
  def uidsToString uids =
    case uids of
      | [] -> "[]"
      | uid :: uids ->
        "[" ^ (uidToString uid) ^ (foldl (fn (uid, s) -> s ^ ", " ^ uidToString uid) "" uids) ^ "]"

  op  uidToString : UnitId -> String
  def uidToString {path,hashSuffix} =
   let path = abbreviatedPath path in
   let device? = deviceString? (hd path) in
   let tildaPath? = (hd path = "~") in
   let mainPath = concatList (foldr (fn (elem,result) -> cons("/",cons(elem,result)))
                                [] (if tildaPath? or device? then tl path else path))
   in
   let fileName =
     if tildaPath? then
        "~" ^ mainPath
     else if device?
     then (hd path) ^ mainPath
     else mainPath
   in
   case hashSuffix of
     | None -> fileName
     | Some suffix -> 
       if fileName = "" then
	 suffix
       else
	 fileName ^"#"^ suffix


  op  relativeUID_ToString : RelativeUID -> String
  def relativeUID_ToString rel_uid =
   case rel_uid of
     | UnitId_Relative {path, hashSuffix} -> 
       (let filename = case path of
			 | []    -> "" % ???
			 | _ -> 
	                   concatList (tl (foldr (fn (elem,result) -> cons("/",cons(elem,result)))
					         [] 
						 path))
	in
        case hashSuffix of
	  | None        -> filename
	  | Some suffix -> 
	    if filename = "" then 
	      suffix
	    else 
	      filename ^"#"^ suffix)
     | SpecPath_Relative unitId -> uidToString unitId


(*
Convert a canonical UnitId to one relatived to some base.
Used by print commands defined in /Languages/SpecCalculus/Semantics/Evaluate/Print.sw
*)

  op  relativizeUID : UnitId -> UnitId -> RelativeUID
  def relativizeUID base target =
    UnitId_Relative {path       = relativizePath base.path target.path,
		  hashSuffix = target.hashSuffix}

  op  relativizePath : List String -> List String -> List String 
  def relativizePath base target =
    let 
      def addUpLinks (base,target) =
	case base of
	  | []      -> target
	  | _::tail -> cons("..", addUpLinks (tail, target))

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
  op  splitStringAtChar : Char -> String -> List String
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

  op  splitAtChar : Char -> List Char -> List (List Char)
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
  op  takeWhile : fa (a) (a -> Boolean) -> List a -> (List a) * (List a)
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
*)
  op  removeLastElem : (List String) -> Env (List String)
  def removeLastElem elems =
    case elems of
      | [] -> error "removeLastElem: encountered empty string list"
      | x::[] -> return []
      | x::rest -> {
          suffix <- removeLastElem rest;
          return (Cons (x,suffix))
        }

  op  lastElem : (List String) -> Env String
  def lastElem elems =
    case elems of
      | [] -> error "lastElem: encountered empty string list"
      | x::[] -> return x
      | _::rest -> lastElem rest

  op  removeLast: fa (a) List a -> Env (List a)
  def removeLast elems =
    case elems of
      | [] -> error "removeLast: encountered empty list"
      | x::[] -> return []
      | x::rest -> {
          suffix <- removeLast rest;
          return (Cons (x,suffix))
        }

  op  first : fa (a) List a -> Env a
  def first elems =
    case elems of
      | [] -> error "first: encountered empty list"
      | x::_ -> return x

  op  last : fa (a) List a -> Env a
  def last elems =
    case elems of
      | [] -> error "last: encountered empty list"
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
               ++ (findDefiningUIDforSortInContext(qId,unitId,globalContext,[],false)).1 of
              | []     -> removeDuplicates((searchForDefiningUID(qId,optGlobalContext)))
              | result -> removeDuplicates result

  op  searchForDefiningUID : QualifiedId * (Option GlobalContext) -> List (String * String)
  def searchForDefiningUID(qId,optGlobalContext) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
        removeDuplicates
          ((searchForDefiningUIDforOp(qId,globalContext,[],false))
           ++ (searchForDefiningUIDforSort(qId,globalContext,[],false)))

  op  findDefiningUIDforOp
       : QualifiedId * Spec * UnitId * List UnitId * GlobalContext * List UnitId * Boolean
           -> List (String * String) * List UnitId
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
		 let (nval,seenUIDs) = findLocalUID (primaryOpName info,seenUIDs) in
		 (nval ++ val,seenUIDs))
	        ([],seenUIDs)
		infos

  op  findDefiningUIDforOpInContext: QualifiedId * UnitId * GlobalContext * List UnitId * Boolean
                                     -> List (String * String) * List UnitId
  def findDefiningUIDforOpInContext (opId, unitId, globalContext, seenUIDs, rec?) =
    case evalPartial globalContext unitId of
      | None -> ([],seenUIDs)
      | Some(Spec spc,_,depUIDs) ->
        findDefiningUIDforOp (opId, spc, unitId,
			      filter (fn uid -> ~(member(uid,seenUIDs))) depUIDs,
			      globalContext, Cons(unitId,seenUIDs), rec?)

  op  findUnitIdforUnit: Value * GlobalContext -> Option UnitId
  def findUnitIdforUnit (val, globalContext) =
    foldMap (fn result -> fn unitId -> fn (vali,_,_) ->
	     case result of
	       | Some _ -> result
	       | None -> if val = vali then Some unitId else None)
      None globalContext

  op  searchForDefiningUIDforOp: QualifiedId * GlobalContext * List UnitId * Boolean
                                -> List (String * String)
  def searchForDefiningUIDforOp (opId, globalContext, seenUIDs, rec?) =
    %% Currently rec? is always false
    foldMap (fn result -> fn unitId -> fn (val,_,depUIDs) ->
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

  op  findDefiningUIDforSort : QualifiedId * Spec * UnitId * List UnitId * GlobalContext * List UnitId * Boolean
                               -> List (String * String) * List UnitId
  def findDefiningUIDforSort (sortId, spc, unitId, depUIDs, globalContext, seenUIDs, rec?) =
    let def findLocalUID (sortId,seenUIDs) =
          if localSort? (sortId, spc) then
	    ([("Sort", uidToFullPath unitId)],seenUIDs)
	  else
	    foldr (fn (unitId,(result,seenUIDs)) ->
		   let (new,seenUIDs)
		      = findDefiningUIDforSortInContext (sortId,
							 unitId,
							 globalContext,
							 seenUIDs,
							 true)
		   in
		   (new ++ result,seenUIDs))
	          ([],seenUIDs) 
		  depUIDs
    in   
    %% If being called recursively, we have already identified a particlar sort in its spec and
    %% we are trying to find it local spec in imports so use findTheSort instead of findAllSorts
    if rec? then
      case findTheSort (spc, sortId) of
	| Some _ -> findLocalUID (sortId,seenUIDs)
	| None   ->
          case sortId of
	    | Qualified (q, id) ->
	      (if q = UnQualified then
		 ([],seenUIDs)
		 %% If the spec was imported using "qualifiying" then the original def may be unqualified
	       else 
		 findDefiningUIDforSort (Qualified (UnQualified, id),
					 spc,
					 unitId,
					 depUIDs,
					 globalContext,
					 seenUIDs,
					 true))
	    | _ -> ([],seenUIDs) 
    else 
      case findAllSorts(spc,sortId) of
	| [] -> ([],seenUIDs)
	| infos ->
	  %% This is the top-level version so seenUIDs should be [] and returned seenUIDs will be ignored
	  %% seenUIDs for one op shouldn't affect seenUIDs for another
          foldr (fn (info, (val,_)) ->
		 let (nval,seenUIDs) = findLocalUID (primarySortName info,seenUIDs) in
		 (nval ++ val,seenUIDs))
	        ([],seenUIDs)
		infos

  op  findDefiningUIDforSortInContext : QualifiedId * UnitId * GlobalContext * List UnitId * Boolean
                                       -> List (String * String) * List UnitId
  def findDefiningUIDforSortInContext (sortId, unitId, globalContext, seenUIDs, rec?) =
    case evalPartial globalContext unitId of
      | None -> ([],seenUIDs)
      | Some (Spec spc, _, depUIDs) ->
        findDefiningUIDforSort (sortId, spc, unitId,
				filter (fn uid -> ~(member(uid,seenUIDs))) depUIDs,
				globalContext, Cons(unitId, seenUIDs), rec?)

  op  searchForDefiningUIDforSort : QualifiedId * GlobalContext * List UnitId * Boolean -> List (String * String)
  def searchForDefiningUIDforSort (sortId, globalContext, seenUIDs, rec?) =
    foldMap (fn result -> fn unitId -> fn (val, _, depUIDs) ->
	     case result of
	       | _::_ -> result		% After finding any stop looking
	       | []   ->
	     case val of
	       | Spec spc ->
	         (findDefiningUIDforSort (sortId, spc, unitId, depUIDs, globalContext, seenUIDs, rec?)).1
	       | _ -> [])
      []
      globalContext

  op  absolutePath?: List String -> Boolean
  def absolutePath? path =
    case path of
      | [] -> false
      | s :: _ -> deviceString? s

 %%% Find relationship between Specs
 op  importPathsBetween: Spec * Spec -> List (List (Term_ Position))
 def importPathsBetween(spc1,spc2) =
   let def findPaths(sp,path) =
         if sp = spc2
	   then [path]
	   else foldl (fn (el,result) ->
		       case el of
			 | Import(i_stm,i_spc,_) ->
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
