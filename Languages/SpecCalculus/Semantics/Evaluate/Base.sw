spec
  import Signature
  import URI/Utilities
  import ../Value

  op setBaseToPath : String -> Env ()
  def setBaseToPath path = {
      relativeUnitId <- pathToRelativeURI path;
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
            val <- evaluateReturnURI internalPosition relativeUnitId;
            case val of
                | ((Spec spc,_,_),unitId) -> {
                   print ("Setting base to " ^ (uriToString unitId));
                   setBase (Some relativeUnitId, spc)
                 }
               | (_,unitId) ->
                   raise (TypeCheck (internalPosition, (showRelativeURI relativeUnitId) ^ " is not a spec"))
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
