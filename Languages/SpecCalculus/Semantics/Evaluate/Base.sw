spec
  import UnitId
  import UnitId/Utilities
  import ../Value

  op setBaseToPath : String -> Env ()
  def setBaseToPath path = {
      relativeUnitId <- pathToRelativeUID path;
      setBaseToRelativeUnitId relativeUnitId
    }

  op setBaseToRelativeUnitId : RelativeUnitId -> Env ()
  def setBaseToRelativeUnitId relativeUnitId = {
      oldBase <- getBase;
      let
        def handler exception = {
            print ((printException exception) ^ "\n");
            print "Evalution of new base spec failed. Previous base spec restored";
            setBase oldBase
          }
        def prog () = {
            setBase (None,emptySpec);
            val <- evaluateReturnUID internalPosition relativeUnitId;
            case val of
                | ((Spec spc,_,_),unitId) -> {
                   print ("Setting base to " ^ (uidToString unitId));
                   setBase (Some relativeUnitId, spc)
                 }
               | (_,unitId) ->
                   raise (TypeCheck (internalPosition, (showRelativeUID relativeUnitId) ^ " is not a spec"))
           } in
        catch (prog ()) handler
    }

   op reloadBase : Env ()
   def reloadBase = {
      (optUnitId,spc) <- getBase;
      case optUnitId of
        | None -> return ()
        | Some relativeUnitId -> setBaseToRelativeUnitId relativeUnitId
    }
endspec
