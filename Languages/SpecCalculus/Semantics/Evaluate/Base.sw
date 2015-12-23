(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec
  import UnitId
  import UnitId/Utilities
  import /Languages/SpecCalculus/Semantics/Value
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm, sameSCTerm?

  def SpecCalc.sameSCTerm? (x, y) =
    case (x.1, y.1) of
      | (Quote x, Quote y) -> x.1 = y.1
      | (Other _, _) -> otherSameSCTerm? (x, y)
      | (_, Other _) -> otherSameSCTerm? (x, y)
      | _ -> 
	case (x.1, y.1) of
	  | (Qualify (x, q1), Qualify (y, q2)) -> q1 = q2 && sameSCTerm? (x, y)
	  %% TODO: "=" is a very crude test, so there are other cases to worry about 
	  | _ -> x.1 = y.1

  %op SpecCalc.setBaseToPath : String -> Env ()
  def SpecCalc.setBaseToPath path = {
      relative_uid <- pathToRelativeUID path;
      setBaseToRelativeUID relative_uid
    }

  op setBaseToRelativeUID : RelativeUID -> Env ()
  def setBaseToRelativeUID relative_uid = {
      oldBase <- getBase;
      let
        def handler exception = {
            print ((printException exception) ^ "\n");
            print "Evalution of new base spec failed. Previous base spec restored";
            setBase oldBase
          }
        def prog () = {
            setBase (None,initialSpecInCat); % ?? emptySpec ??
	    clearBaseNames;
            val <- evaluateReturnUID internalPosition relative_uid false;
            case val of
                | ((Spec spc,_,_),unitId) -> {
                     print ("\nSetting base to " ^ (uidToString unitId) ^ "\n\n");
                     setBase (Some relative_uid, spc)
                   }
                | (_,unitId) ->
                   raise (TypeCheck (internalPosition, (showRelativeUID relative_uid) ^ " is not a spec"))
           }
      in
        catch (prog ()) handler
    }

   %op SpecCalc.reloadBase : Env ()
   def SpecCalc.reloadBase = {
      (optUnitId,spc) <- getBase;
      case optUnitId of
        | None -> return ()
        | Some relative_uid -> setBaseToRelativeUID relative_uid
    }
endspec
