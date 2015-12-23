(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


%% Beginning to factor MetaSlang bootstrap engine out from general Specware product
%% Specware   = Bootstrap + OtherStuff
%% Bootstrap  = basic MetaSlang and SpecCalculus, plus Lisp code generation
%% OtherStuff = Prover, Java code generation, C code generation, Interpreter, XML, etc.

%% Bootstap and non-bootstrap things are still rather intertwined
%% in the source tree, but this is a start towards clarification.

Specware qualifying spec
  import Bootstrap
  import /Languages/MetaSlang/Transformations/Interpreter    % for MSInterpreter.eval
 %import /Languages/SpecCalculus/AbstractSyntax/Printer      % for showUI
 %import /Languages/XML/XML                                  % for XML I/O
  import /Languages/MetaSlang/Transformations/EditFunctions  % Functions called from XEmacs
  import /Languages/SpecCalculus/AbstractSyntax/CheckSpec
  import /Languages/SpecCalculus/AbstractSyntax/ShowData
  import /Languages/ACL2/SpecToACL2
  import /Languages/SpecCalculus/AbstractSyntax/ShowDeps
  import /Languages/SpecCalculus/AbstractSyntax/ShowImports
  import /Languages/MetaSlang/CodeGen/C/PrintSpecAsC
  import /Languages/MetaSlang/Transformations/ReorderArgs    % Transform of args

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Java
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op evaluateJavaGen_fromLisp : String * Option String -> Bool
  def evaluateJavaGen_fromLisp (path,optopath) = 
    %let optspec = getOptSpec optopath in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID position unitId;
      evaluateJavaGen (spcInfo, (UnitId unitId, position), optopath);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 

  op evaluateUID_fromJava : String -> Bool
  def evaluateUID_fromJava path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        evaluateUID position unitId;
        return ()
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandlerForJava)


  op toplevelHandlerForJava: Exception -> SpecCalc.Env Bool
  def toplevelHandlerForJava except =
    {cleanupGlobalContext;		% Remove InProcess entries
     % saveSpecwareState;			% So work done before error is not lost
     return (reportExceptionToJava except);
     return false}

  op reportExceptionToJava: Exception -> ()
  def reportExceptionToJava except =
    case except of
      | Unsupported  (position,msg) -> 
        reportErrorAtPosToJava(position,"Unsupported operation: " ^ msg)
      | UIDNotFound  (position,unitId) ->
        reportErrorAtPosToJava(position,"Unknown unit " ^ (showRelativeUID unitId))
      | FileNotFound (position,unitId) ->
        reportErrorAtPosToJava(position,"Unknown unit " ^ (showRelativeUID unitId))
      | SpecError    (position,msg) ->
        reportErrorAtPosToJava(position,"Error in specification: " ^ msg)
      | MorphError   (position,msg) ->
        reportErrorAtPosToJava(position,"Error in morphism: " ^ msg)
      | DiagError    (position,msg) ->
        reportErrorAtPosToJava(position,"Diagram error: " ^ msg)
      | TypeCheck    (position,msg) ->
        reportErrorAtPosToJava(position,"Type error: " ^ msg)
      | Proof        (position,msg) ->
        reportErrorAtPosToJava(position,"Proof error: " ^ msg)
      | TransformError(position,msg) ->
        reportErrorAtPosToJava(position,"Transformation error: " ^ msg)
      | TypeCheckErrors (errs, err_spc) -> reportTypeErrorsToJava errs
      | _ -> reportErrorToJava("",0,0,printException except)

  op reportTypeErrorsToJava : List(String * Position) -> ()
  def reportTypeErrorsToJava errs =
    app (fn (msg,pos) -> reportErrorAtPosToJava(pos,msg)) errs

  op reportErrorAtPosToJava: Position * String -> ()
  def reportErrorAtPosToJava(pos,msg) =
    case pos of
      | File (file, (left_line, left_column, left_byte), right) ->
        reportErrorToJava(file,left_line,left_column,msg)
      | _ -> reportErrorToJava("",0,0,msg)

  op reportErrorToJava: String * Nat * Nat * String -> ()
  %% redefined in /Gui/src/Lisp/init-java-connection.lisp
  def reportErrorToJava (file, line, col, msg) =
    let _ = toScreen ("call to reportErrorToJava, but java connection not initialized: ") in
    let _ = toScreen (" File:   " ^ file)              in
    let _ = toScreen (" Line:   " ^ Nat.show line) in  
    let _ = toScreen (" Column: " ^ Nat.show col)  in
    let _ = toScreen (" Msg:    " ^ msg)               in
    ()

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% C 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op evaluateCGen_fromLisp : String * Option String -> Bool
  def evaluateCGen_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".c") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      evaluateGenerate ("c", (UnitId unitId, position), target) position;
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% C ("thin" version)
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% TODO Something like this must already exist somewhere.
  op splitStringAtChar (string : String, char : Char) : List String =
  let chars = explode string in
  let charlists = (splitAtChar char chars) in
  let strings = map implode charlists in
  strings

  %% This is the top level Metaslang function for the "thin" C generator.  It
  %% is called by the hand-written Lisp function gen-c-thin in toplevel.lisp.
  %% argstring is the (optional) entire argument string passed to gen-c-thin (or None)
  %% FIXME add more parsing of the arguments:
  %% handle .. (seems to work)? handle ~ for home directory (or not?)?
  %% example call: gen-c-thin ../Examples/FactorialChoppedAuto#FacChopFinal facchop
  %% FIXME If the given spec imports other specs, should all the code go into one .c file?
  %%   probably the structure of the C code files should mirror the structure of the units...
  %% The return value is an optional string to make the new value of *last-unit-Id-_loaded*.
  %% FIXME can the previous unit loaded be something unexpected, like a spec transform term?
  op evaluateGenCThin (argstring : Option String, lastUnitIdLoaded : Option String) : Option String = 
  let _ = writeLine "Calling evaluateGenCThin." in
  let _ = writeLine ("arg string: "^(case argstring of Some str -> ("\""^str^"\"") | None -> "No arg string supplied.")) in
  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  %% Determine the unit and the opname to process:
  let (opt_uid_str, opt_opname_str) =
  (case argstring of
     %% No arguments given at all, so use the last unit loaded, if there is one.
     | None -> (case lastUnitIdLoaded of
                  | None -> let _ = writeLine("ERROR: No unit given and no previous unit loaded.") in (None, None)
                  | Some uid_str -> (lastUnitIdLoaded, None)) %% TODO should we also store the last opname given to gen-c-thin?
     | Some argstring ->
       %% Parse and process the arguments:
       let args = splitStringAtChar(argstring, #\s) in % split into substrings separated by spaces
       if (length args = 0) then
         let _ = writeLine("ERROR: No unit given and no previous unit loaded (argument is all spaces).") in (None, None)
       else if (length args = 1) then
         %% If a single arg is given it must be a unit ID:
         (Some (head args), None)
       else if (length args = 2) then
         %% If two args are given, they must be a unit ID and an opname:
         %TODO handle the case when this is a qid?
         (Some (head args), Some (head (tail args)))
       else
         let _ = writeLine("ERROR: More than two args given to gen-c-thin.") in (None, None)
       ) in
  (case opt_uid_str of
     | None -> None %% fail and don't change *last-unit-Id-_loaded*
     | Some uid_str ->
       %% Attempt to evaluate the spec:
       let spc = evaluateUnitId uid_str in
       case spc of
         | None -> let _ = writeLine "ERROR: Processing the unit failed to return anything." in None
         | Some (Spec spc) ->
           (case opt_opname_str of
              %% no opname given, so process all ops in the spec
              | None -> let resultokay? = PrintAsC.evaluateGenCThinHelper(All, uid_str, spc) in
                (if resultokay? then
                   Some uid_str % set *last-unit-Id-_loaded*
                 else
                   None)
              | Some opname_str -> %FIXME pull out this parsing of a possible qid
                (let strings = splitStringAtChar(opname_str, #.) in
                 if ((length strings) > 2) || ((length strings) < 1) then
                   let _ = writeLine "ERROR: Invalid opname." in None
                 else
                   let opqid = (case strings of 
                                  | [string] -> (mkUnQualifiedId (head strings))
                                  | [string1, string2] -> mkQualifiedId(string1, string2)) in
                   let resultokay? = PrintAsC.evaluateGenCThinHelper(QID opqid, uid_str, spc) in
                   (if resultokay? then
                      Some uid_str % set *last-unit-Id-_loaded*
                    else
                      None)))
         | _ -> let _ = writeLine "ERROR: Processing the unit returned something other than a spec." in None)
  
  
       
  
                  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Interpreter
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  evalDefInSpec: String * QualifiedId -> Option MSIValue
  def evalDefInSpec(path,qid) =
    let prg = {
	       cleanEnv;
	       currentUID <- pathToCanonicalUID ".";
	       setCurrentUID currentUID;
	       path_body <- return (removeSWsuffix path);
	       unitId <- pathToRelativeUID path_body;
	       position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
	       spcInfo:ValueInfo <- evaluateUID position unitId;
	       return (let (value,_,_) = spcInfo in
		       case coerceToSpec value of
			 | Spec spc ->
			   (case AnnSpec.findTheOp (spc, qid) of
			      | Some info -> 
			        (if definedOpInfo? info then
				   let tm = firstOpDefInnerTerm info in
				   Some (MSInterpreter.eval (tm, spc))
				 else
				   None)
			      | _ -> None) % Dummy
			 | _ -> None)
	      }
      in
      runSpecCommand (catch prg toplevelHandlerOption)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Prover
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
(*
  op evaluateProofCheck_fromLisp : String * Option String -> Bool
  def evaluateProofCheck_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (name^".sw") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      %% spcInfo <- evaluateUID position unitId;
      catch {
        (val,_,_) <- evaluateUID position unitId;
        case val of
          | Spec spc -> {
              ctxt <- specToContext spc;
              SpecCalc.print (SpecCalc.printContext ctxt);
	      ctxtProof <- return (contextProof ctxt);
	      %_ <- fail "foo";
	      %SpecCalc.print (printProof ctxtProof);
	      checkedProof <- return (runCheck ctxtProof);
	      case checkedProof of
		% Actually ckeck that the judgement is well formed context of ctxt.
		| RETURN j -> SpecCalc.print (SpecCalc.printJudgement(j))
		| THROW exc -> SpecCalc.print (SpecCalc.printFailure(exc));
              return ()
            }
          | _ -> {
              print "Unit is not a spec";
              return ()
            }
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
*)
  op evaluateProofGen_fromLisp : String * Option String * Bool -> Bool
  def evaluateProofGen_fromLisp (path,targetFile, fromObligations?) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (name^".sw") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID position unitId;
      evaluateProofGen (spcInfo, (UnitId unitId, position), target, fromObligations?);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 


  %% Second argument is interpreted as spec containing options for the code generation.

  op evaluateProofGenLocal_fromLisp : String * Option String * Bool -> Bool
  def evaluateProofGenLocal_fromLisp (path,targetFile, fromObligations?) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (name ^ ".sw") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      pos <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID pos unitId;
      evaluateProofGenLocal (spcInfo, (UnitId unitId, pos), target, fromObligations?);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)

end-spec

