
%% Beginning to factor MetaSlang bootstrap engine out from general Specware product
%% Specware   = Bootstrap + OtherStuff
%% Bootstrap  = basic MetaSlang and SpecCalculus, plus Lisp code generation
%% OtherStuff = Prover, Java code generation, C code generation, Interpreter, XML, etc.

%% Bootstap and non-bootstrap things are still rather intertwined
%% in the source tree, but this is a start towards clarification.

Specware qualifying spec
  import Bootstrap
  import ../../MetaSlang/Transformations/Interpreter % for MSInterpreter.eval
  import ../AbstractSyntax/Printer % for showUI
  import /Languages/XML/XML        % for XML I/O

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Java
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op evaluateJavaGen_fromLisp : String * Option String -> Boolean
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

  op evaluateUID_fromJava : String -> Boolean
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


  op toplevelHandlerForJava: Exception -> SpecCalc.Env Boolean
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
      | TypeCheckErrors errs      -> reportTypeErrorsToJava errs
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
    let _ = toScreen (" Line:   " ^ Nat.toString line) in  
    let _ = toScreen (" Column: " ^ Nat.toString col)  in
    let _ = toScreen (" Msg:    " ^ msg)               in
    ()

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% C 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op evaluateCGen_fromLisp : String * Option String -> Boolean
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
  %%% Interpreter
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  evalDefInSpec: String * QualifiedId -> Option MSInterpreter.Value
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
  op evaluateProofCheck_fromLisp : String * Option String -> Boolean
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
  op evaluateProofGen_fromLisp : String * Option String * Boolean -> Boolean
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

  op evaluateProofGenLocal_fromLisp : String * Option String * Boolean -> Boolean
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

