SpecCalc qualifying spec
  import UnitId
  import UnitId/Utilities
  import ../Value

  op setBaseToPath : String -> Env ()
  def setBaseToPath path = {
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
            val <- evaluateReturnUID internalPosition relative_uid;
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

   op reloadBase : Env ()
   def reloadBase = {
      (optUnitId,spc) <- getBase;
      case optUnitId of
        | None -> return ()
        | Some relative_uid -> setBaseToRelativeUID relative_uid
    }
endspec
