(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% This file contains a utility to generate a graph of the
%% (transitive) imports of a Spec.  The output goes to a file in the
%% deps/ subdirectory of the directory that contains the spec as a graphviz 'dot' file.

%% This file might be similar to some of the operations done by Languages/MetaSlang/Transformations/SliceSpec.sw

%% The top level function to call is showImportsForSpec.  Example call (from the Specware shell):
%%   showimports /usr/home/kestrel/ewsmith/Dropbox/vTPM/vTPM/Examples/Arrays_1#Imp

ShowImports qualifying spec 

import Types
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Monad
import /Languages/MetaSlang/Specs/Printer
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import ShowUtils

% prints <unqualified> if no qualifier
op printQualifiedIdFull (Qualified (q, id) : QualifiedId) : String =
  q ^ "." ^ id

  
%% --------------------------------------------------------------------------------
%% Give the signature of utilities so we don't have to import them

type GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a

%op  Specware.evaluateUnitId: String -> Option Value
% op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId

  %op  SpecCalc.uidToFullPath: UnitId -> String
op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo

% op uidToDepsName ({path,hashSuffix=_}: UnitId) : String =
%   let device? = deviceString? (head path) in
%   let main_name = last path in
%   let path_dir = butLast path in 
%   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
%                             ["/deps/",main_name]
%                             (if device? then tail path_dir else path_dir))
%   in if device?
%        then (head path) ^ mainPath
%      else mainPath

  %% Used because the use of "#" causes problems with syntax coloring.
op numberSignString : String = implode [##]

% op uidStringPairForValue (val: Value) : Option (UnitId * String * String) =
%   case MonadicStateInternal.readGlobalVar "GlobalContext" of
%   | None -> None
%   | Some global_context ->
%     case findUnitIdForUnit(val,global_context) of
%     | None -> None
%     | Some uid ->
%       Some (uid,
%             fileNameInSubDir(uid, "deps"),
%             case uid.hashSuffix of
%             | Some loc_nm -> numberSignString ^ loc_nm
%             | _ -> "")

% op uidStringForValue (val:Value) : Option String =
%   case uidStringPairForValue val of
%   | None -> None
%   | Some(_,filnm,hash) -> Some(filnm ^ hash)

op showUID(uid : UnitId): String =
   uidToFullPath(uid)


% A Graph is a mapping from source nodes to destination nodes (expressed as terms). 
type Graph = STHMap.Map (UnitId,List SCTerm)

% Generate the graphviz dot output for a single spec as a node.
op showNode(fro:UnitId)(tos:List SCTerm):String =
    foldr (fn (to,xs) -> "\"" ^ (showUnitId fro) ^ "\" -> \""  ^ showUnitId (mkAbsolute fro to) ^ "\"\n" ^ xs ) "" tos

% Generate the graphviz dot output for a graph.
op showGraph (gr:Graph):String =
  "digraph imports {\n" ^
  "node [shape=box weight=bold fontsize=18 color=black fontcolor=black]" ^
  foldMap (fn accum -> fn key -> fn  v -> accum ^ "\n" ^ showNode key v ) "" gr ^
  "\n}"


% The import state has a worklist of (spec terms/specs) yet to
% process, along with an import graph. The worklist may include specs
% that have already been processed, but the work function, found
% below, will skip those elements.
type State = (List (UnitId * Spec) * Graph)

% Main import algorithm. Iteratively get the imports for a spec from
% the worklist, merge in the associated graph, add the new imports to
% the worklist, repeat.
op work(st:State):Graph = 
  let gr = project 2 st in
  case project 1 st of
    | [] -> project 2 st
    | (nm,spc)::rest -> 
         if inDomain?(gr,nm)
           then work (rest,gr)
         else let (next,gr') = genSpec (project 2 st) nm spc in
              work (rest ++ next, gr')

% For a specific spec, generate the list of imports and a graph with
% the spec as a node, and edges to the imported specs.
op genSpec (gr:Graph) (nm:UnitId)  (spc : Spec) : (List (UnitId * Spec) * Graph) =
   let next = procImport nm spc.elements in
   let next_nodes = map (project 2) next in
   let next_work = map (fn p -> (project 1 p, project 3 p)) next in
   (next_work, update(gr,nm,next_nodes))

op mkAbsolute(base:UnitId)(relTerm:SCTerm):UnitId =
    case baseTerm relTerm of
     | (UnitId (UnitId_Relative id), pos) -> 
       let _ = writeLine ("Resolving UID Relative " ^ showUnitId id ^ " from " ^ showUnitId base) in
       let relPath = id.path in
       let bPath = reverse base.path in
       let newPath =  (comb (tail bPath) relPath) in
       let newId = id << { path = newPath } in
       let _ = writeLine (showUnitId newId) in
       newId

     | (UnitId (SpecPath_Relative id), pos) -> 
       let _ = writeLine ("Resolving SpecPath Relative " ^ showUnitId id ^ " from " ^ showUnitId base) in
       id



op isOk(relTerm:SCTerm): Bool =
    case baseTerm relTerm of
     | (UnitId (UnitId_Relative id), pos) -> true
     | (UnitId (SpecPath_Relative id), pos) -> true
     | _ -> false

% Combine paths represented as lists in reverse order (that is, from
% leaf to the root of the filesystem). Assumes that the first
% (filename) element of baseRev has already been dropped.

% The baseRev parameter represents a base directory. It should be in
% revere order (from leaf to root) and the trailing filename should be
% dropped. The relRev parameter represents the relative path. This
% function handles leading '..' paths, but won't work correctly with
% paths like 'A/../B', although it's unlikely anyone would ever write such a thing.
op comb(baseRev:List String)(relRev:List String):List String =
   case (baseRev,relRev) of
     | (_::bRest, ".."::rRest) -> comb bRest rRest
     | (_,_) -> reverse baseRev ++ relRev


% Given a list of elements -- some which may be imports, generate an alist of 
% import term and imported spec.
op procImport (nm:UnitId) (elems : List SpecElement) : List (UnitId * SCTerm * Spec)  =
  case elems of
  | [] -> []
  | (Import (scterm, spc, specelems, _))::rest -> 
    if isOk scterm
     then (mkAbsolute nm scterm, scterm, spc)::(procImport nm rest)
     else (procImport nm rest)
  | (_::rest)  -> procImport nm rest

% Take a SCTerm and turn it into a canonical name. This strips off all
% all of the 'qualify', 'translate', and 'subst' expressions, so that
% the graph doesn't end up with a ton of nodes for each of
% these. Rather, there will be a single node for the spec that is
% being tranlated/qualified/substituted. 

op baseTerm(tm:SCTerm):SCTerm =
  case tm of
    | (UnitId id, pos) -> tm
    | (Qualify (tm',nm), pos) -> baseTerm tm'
    | (Translate (tm', renm), pos) -> baseTerm tm'
    | (SpecMorph (tm',_ , _ , _),pos) -> baseTerm tm'
    | (Subst (tm', morph, pragmas), pos) -> baseTerm tm'
    | _ -> tm
      % Yeah, there's probably a better way to raise an error so that
      % we can inspect the raw data structure
    % | _ -> let _ = writeLine ("Non-uid" ^ showSCTerm tm) 
    %        in show (1/0) % showSCTerm tm                         

op resolveRelative(base:UnitId, rel:RelativeUID):UnitId 



%% Evaluate the given unit and print its deps.
%% Returns a flag indicating whether the operation succeeded (failure may happen if the spec fails to be processed).
op showImportsForSpec (uid_str : String) : Bool =
  let _ = writeLine ("Printing imports for unit: "^uid_str) in
    %% Evaluate the unit (if necessary):
    case evaluateUnitId uid_str of
    | None -> let _ = writeLine ("ERROR: Could not evaluate UID: " ^ uid_str) in false
    | Some val ->
      (case val of
       | Spec spc ->
         (case (uidForValue val) of
          | None -> let _ = writeLine "ERROR: Can't get UID string from value" in false
          | Some uid ->
            let uidstr = fileNameInSubDir(uid, "deps") in
            let file_name = uidstr ^ ".dot" in
            let _ = ensureDirectoriesExist file_name in
            % Create a relative ID for the unit?
            let uid = pathStringToCanonicalUID (uid_str, true) in
            let start_list = [(uid, spc)] in
            let gr = work (start_list, emptyMap) in
	    % let _ = writeLine("Writing deps to: "^file_name^"\n") in
            let _ = writeStringToFile(showGraph gr,file_name) in
              true)
       | _ -> let _ = writeLine "ERROR: The unit evaluated to something other than a spec." in false)



%% This is the top level Metaslang function for the 'showimports' command.  It
%% is called by the hand-written Lisp function showdeps in toplevel.lisp.
%% The optional_argstring is the entire argument string passed to showimports, or None.
%% FIXME add more processing of the argument string:
%%   strip leading spaces
%%   handle Windows path names (driver letter plus colon, backslashes instead of slashes).
%% Then get rid of the awkward call to uidStringForValue?
%% The return value is an optional string to make the new value of *last-unit-Id-_loaded*.
%% FIXME can the previous unit loaded be something unexpected, like a spec transform term?
op evaluateShowImports (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String =  
 let _ = writeLine "Calling evaluateShowImports." in
  let _ = writeLine ("The user's home directory: "^homedir) in
  let _ = writeLine ("arg string: "^(case optional_argstring of Some str -> ("\""^str^"\"") | None -> "No arg string supplied.")) in
  %FIXME handle the case when this is a qid?
  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  %% Get the unit ID to process:
  let opt_uid_str =
    (case optional_argstring of
       %% No arguments given at all, so use the last unit loaded, if there is one.
     | None -> (case lastUnitIdLoaded of
                | None -> let _ = writeLine("ERROR: No unit given and no previous unit loaded.") in None
                | Some uid_str -> lastUnitIdLoaded)
       %% Otherwise, the argument string is the unit ID to process:
     | Some argstring -> optional_argstring) in
    (case opt_uid_str of
     | None -> None %% fail and don't change *last-unit-Id-_loaded*
     | Some uid_str -> 
       let uid_str = substHomeDir(uid_str, homedir) in
       %% Print the import graph to the file and return a new value for *last-unit-Id-_loaded* if the operation succeeded.
       let success? = showImportsForSpec uid_str in
       if success? then Some uid_str else None)



% Take a spec unitid and turn in into a worklist item, for use with work.
op workListItem (uid_str : String) : Option (UnitId * Spec) =
  let _ = writeLine ("Printing imports for unit: "^uid_str) in
    %% Evaluate the unit (if necessary):
    case evaluateUnitId uid_str of
    | None -> let _ = writeLine ("ERROR: Could not evaluate UID: " ^ uid_str) in None
    | Some val ->
      (case val of
       | Spec spc ->
         (case (uidForValue val) of
          | None -> let _ = writeLine "ERROR: Can't get UID string from value" in None
          | Some uidstr ->
            % Create a relative ID for the unit?
            let uid = pathStringToCanonicalUID (uid_str, true) in
            Some (uid,spc))
       | _ -> let _ = writeLine "ERROR: The unit evaluated to something other than a spec." in None)


op [a] fromSome (x:Option a ):a =
  case x of
    | Some y -> y

% Generate the imports graph for a collection of specs
op combineImports (files:List String):Graph = 
  let worklist = map workListItem files in
  let valid = map fromSome (filter some? worklist) in
  let gr = work (valid, emptyMap) in
  let _ = writeStringToFile(showGraph gr,"/tmp/allimports.dot") in
  gr



end-spec

% To process a whole directory, do something like this from the emacs specware shell:
% (ShowImports::combineImports (mapcar 'namestring (directory "/Users/garrinkimmell/Kestrel/specware/Library/**/*.sw")))

