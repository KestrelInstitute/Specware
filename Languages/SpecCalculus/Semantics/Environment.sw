\section{The Specware Environment}

The environment is the monadic context for the spec calculus interpreter. 
The monad handles, state, (very primitive) IO, and exceptions. In principle,
the datatype should be defined compositionally but this isn't supported as
yet. In the meantime, the monad and the operations for dealing with it
are described monolithically ... everything appears below. Ugh!

\begin{spec}
SpecCalc qualifying spec {
  import ../AbstractSyntax/Types   
  import ../AbstractSyntax/Printer
  import /Library/IO/Primitive/IO
  import translate (translate /Library/Structures/Data/Monad/Base
    by {Monad +-> Env})
    by {Monad._ +-> Env._}
  import Exception
  import Value
\end{spec}

The Monad/Base spec supplies declarations of
ths sort Monad and the operators monadSeq, monadBind and return. 

All terms in the calculus have a value.  A value is a specification, a
diagram, morphism etc.  We combine them with a coproduct.

\begin{spec}
  sort Info
\end{spec}

The interpreter maintains state.  The state of the interpreter includes
two maps assigning a value to a URI. We call these \emph{name contexts}
(but some thought should go into the nomenclature for contexts,
environments, state \emph{etc}). One context is a global context. This
are names of URIs that resolve to objects in the file system. The other
is a local context. These are names bound by \verb+let+ expressions. The
scope of such names is limited.

A name is a URI, a let bound name or a name bound by one amongst a list
of definitions in a file. The latter two are cast into URIs.

By recording the binding of a name to a value in an environment, we seek
to avoid re-elaborating spec terms.

The state also includes the URI for the object currently being evaluated.
This is needed to resolve relative URIs found within the object. A
\emph{relative} URI is resolved relative to the \emph{canonical} URI for
the object containing the reference. A canonical path is always relative
to the root of the filesystem. A URI in the environment should always be
a canonical path.  See \url{Languages/SpecCalculus/AbstractSyntax/Types}.

TimeStamps are the universal time values as returned by the lisp
function file-write-date. URI_Dependency are the URIs that a value
depends on. ValueInfo is a value plus its URI_Dependency and a
TimeStamp that is latest of the TimeStamps of the files of its
URI_Dependency.

\begin{spec}
  sort TimeStamp = Time          % Not a fixnum
  op futureTimeStamp: TimeStamp		% > than any TimeStamp in foreseeable future
  def futureTimeStamp = 9999999999
  sort URI_Dependency = List URI
  sort ValidatedURIs = List URI
  sort ValueInfo = Value * TimeStamp * URI_Dependency
  sort GlobalContext = PolyMap.Map (URI, ValueInfo)
  sort LocalContext  = PolyMap.Map (RelativeURI, ValueInfo)
  sort State = GlobalContext * LocalContext * Option URI * ValidatedURIs

  op ppValueInfo : ValueInfo -> Doc
  def ppValueInfo (value,timeStamp,depURIs) =
    ppConcat([ppValue value,
              ppString (Nat.toString timeStamp)]
             ++ map ppURI depURIs)
\end{spec}

The first in this product is the global name context. The second is the
local name context. As the state is extended it will be better to make
the above a named record and it will become more very useful to have a
syntax for updating selected fields in a record.

The result of a statement is \verb+Ok+ or an exception.

\begin{spec}
  sort Result a =
    | Ok a
    | Exception Exception
\end{spec}

Now we define the type for an IO / exception monad.

\begin{spec}
  sort Env a = State -> (Result a) * State
\end{spec}

Abstract operations for getting and setting something in the name context.
The lookup functions return optional values. It might be better if they
raised exceptions. Or perhaps we need both forms. Wait and see how they
are used.

\begin{spec}
  op bindInGlobalContext : URI -> ValueInfo -> Env ()
  def bindInGlobalContext uri value =
    fn (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (), (update globalContext uri value, localContext,currentURI,validatedURIs))

  op removeFromGlobalContext : URI -> Env ()
  def removeFromGlobalContext uri =
    fn (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (), (remove globalContext uri, localContext,currentURI,validatedURIs))

  op lookupInGlobalContext : URI -> Env (Option ValueInfo)
  def lookupInGlobalContext uri =
    fn state as (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (evalPartial globalContext uri), state)

  op getGlobalContext : Env GlobalContext
  def getGlobalContext = fn (globalContext,localContext,uri,validatedURIs) ->
    (Ok globalContext, (globalContext,localContext,uri,validatedURIs))

  op setGlobalContext : GlobalContext -> Env ()
  def setGlobalContext newGlobalContext =
    fn (globalContext,localContext,uri,validatedURIs) ->
    (Ok (), (newGlobalContext,localContext,uri,validatedURIs))

  op bindInLocalContext : RelativeURI -> ValueInfo -> Env ()
  def bindInLocalContext uri value =
    fn (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (), (globalContext, update localContext uri value,currentURI,validatedURIs))

  op lookupInLocalContext : RelativeURI -> Env (Option ValueInfo)
  def lookupInLocalContext uri =
    fn state as (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (evalPartial localContext uri), state)

  op showLocalContext : Env String
  def showLocalContext = fn state as (globalContext,localContext,uri,validatedURIs) ->
    (Ok (ppFormat (ppMap ppRelativeURI ppValueInfo localContext)), state)

  op printLocalContext : Env ()
  def printLocalContext = {
      str <- showLocalContext;
      print ("local context: " ^ str ^ "\n")
    }

  op showGlobalContext : Env String
  def showGlobalContext = fn state as (globalContext,localContext,uri,validatedURIs) ->
    (Ok (ppFormat (ppMap (fn uri -> ppString (showURI uri))
              ppValueInfo globalContext)), state)

  op printGlobalContext : Env ()
  def printGlobalContext = {
      str <- showGlobalContext;
      print ("global context: " ^ str ^ "\n")
    }

  op cleanupGlobalContext : Env ()
  def cleanupGlobalContext =
    { gCtxt <- getGlobalContext;
      setGlobalContext (mapPartial (fn x as (val,_,_) ->
				     case val of
				      | InProcess -> None
				      | _ -> Some x)
		          gCtxt)
     }
\end{spec}

When evaluating new locally scoped bindings, we need to be able to
retrieve the local context and restore it later. Also, we we evaluate
a new URI, we must abandon the local context in the URI.

\begin{spec}
  op getLocalContext : Env LocalContext
  def getLocalContext = fn (globalContext,localContext,uri,validatedURIs) ->
    (Ok localContext, (globalContext,localContext,uri,validatedURIs))

  op setLocalContext : LocalContext -> Env ()
  def setLocalContext newLocalContext =
    fn (globalContext,localContext,uri,validatedURIs) ->
    (Ok (), (globalContext,newLocalContext,uri,validatedURIs))

  op clearLocalContext : Env ()
  def clearLocalContext = setLocalContext emptyMap
\end{spec}

The corresponding operations for retrieving and setting the current URI.

\begin{spec}
  op getCurrentURI : Env URI
  def getCurrentURI = fn state as (globalContext,localContext,optURI,validatedURIs) ->
    (case optURI of
      | None -> (Exception (Fail "No current URI"), state)
      | Some uri -> (Ok uri, state))

  op setCurrentURI : URI -> Env ()
  def setCurrentURI newURI =
    fn (globalContext,localContext,oldURI,validatedURIs) ->
    (Ok (), (globalContext,localContext, Some newURI,validatedURIs))
\end{spec}

\begin{spec}
  op  validatedURI?: URI -> Env Boolean
  def validatedURI? uri =
    fn state as (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (member(uri,validatedURIs)), state)

  op  setValidatedURI: URI -> Env ()
  def setValidatedURI uri =
    fn (globalContext,localContext,currentURI,validatedURIs) ->
      (Ok (), (globalContext,localContext,currentURI,cons(uri,validatedURIs)))
\end{spec}

The initial state within Specware has no URI's evaluated and a current
URI that corresponds to "/". The latter needs thought.

\begin{spec}
  op initialSpecwareState : State
  def initialSpecwareState = (emptyMap, emptyMap, Some {path=["/"], hashSuffix=None},[])
\end{spec}

Next we define the monad sequencing operators.  The names of the operators
are fixed. The names are generated by the MetaSlang parser.  The first
operator binds the output of the first operation.

\begin{spec}
  % sort Monad a = Env a
  % op monadBind : fa (a,b) (Env a) * (a -> Env b) -> Env b
  def monadBind (f,g) =
    fn state -> (case (f state) of
      | (Ok y, newState) -> (g y newState)
      | (Exception except, newState) -> (Exception except, newState))
\end{spec}

The second simply sequences two operations without any extra binding.

\begin{spec}
  % op monadSeq : fa (a,b) (Env a) * (Env b) -> Env b
  def monadSeq (f,g) = monadBind (f, (fn _ -> g))
\end{spec}

The unit of the monad.

\begin{spec}
  % op return : fa (a) a -> Env a
  def return x = fn state -> (Ok x, state)
\end{spec}

Raise an exception. Should this be called throw?

\begin{spec}
  op specwareWizard? : Boolean

  op raise : fa (a) Exception -> Env a
  def raise except = fn state -> 
    let _ =
      if specwareWizard? then
        fail (System.toString except)
      else
        ()
    in
      (Exception except, state)
\end{spec}

This is meant to be for unrecoverable errors. Perhaps it should just call
\verb+fail+. Heaven help someone trying to debug monadic code within
the lisp debugger.

\begin{spec}
  op error : fa (a) String -> Env a
  def error str = raise (Fail str)
\end{spec}

This is for going into the Lisp Debugger when called during nomal madic execution.

\begin{spec}
  op mFail : fa(a) String -> Env a
  def mFail str = fn state -> let _ = (fail str) in (Exception (Fail str), state)
\end{spec}

This is used for catching an exception. We execute the first operation
If that raise an exception, then control is transferred to the second
sequence with the value of the exception passed as an argument.
Should catch save the state and restore it in the handler? No and it
probably isn't tractable anyway.

\begin{spec}
  op catch : fa (a) Env a -> (Exception -> Env a) -> Env a
  def catch f handler =
    fn state ->
      (case (f state) of
        | (Ok x, newState) -> (Ok x, newState)
        | (Exception except, newState) -> handler except newState)
\end{spec}

Some basic operations for debugging. There should be a proper IO monad.

\begin{spec}
  op trace : String -> Env ()
  % def trace str = return ()  % change to print when needed.
  def trace str = print str

  op print : String -> Env ()
  def print str =
    fn state ->
      let _ = toScreen str in
      (Ok (), state)
\end{spec}

Some hacks for twiddling memory.  hackMemory essentially calls (room nil)
in an attempt to appease Allegro CL into not causing mysterious storage 
conditions during the bootstrap. (sigh)  

\begin{spec}
  op garbageCollect : Boolean -> Env ()
  def garbageCollect full? =
    fn state ->
      let _ = System.garbageCollect full? in
      (Ok (), state)

  op hackMemory : () -> Env ()
  def hackMemory _ =
    fn state ->
      let _ = System.hackMemory() in
      (Ok (), state)
\end{spec}

The following is used when one wants to guard a command with a predicate.
The predicate is not computed in the monad.

\begin{spec}
  op when : Boolean -> Env () -> Env ()
  def when p command = if p then (fn s -> (command s)) else return ()
\end{spec}

The following is essentially a \verb+foldl+ over a list but within a
monad. We may want to change the order this function takes its arguments
and the structure of the argument (ie. curried or not) to be consistent
with other fold operations. (But they are in the order that I like :-).

This needs to go into a Monad library. The spec
Library/Structures/Data/Monad now exists but not used.

\begin{spec}
  op foldM : fa (a,b) (a -> b -> Env a) -> a -> List b -> Env a
  def foldM f a l =
    case l of
      | [] -> return a
      | x::xs -> {
            y <- f a x;
            foldM f y xs
          }
\end{spec}

Analogously, this is the monadic version of \verb+map+. Both of these
need to have better names. Can we drop the 'M' suffix and
rely on the overloading?

\begin{spec}
  op mapM : fa (a,b) (a -> Env b) -> (List a) -> Env (List b)
  def mapM f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- mapM f xs;
            return (Cons (xNew,xsNew))
          }
\end{spec}

\begin{spec}
%   op getCurrentDirectory : Env String
%   def getCurrentDirectory = return currentDirectory

  op fileExistsAndReadable? : String -> Env Boolean
  def fileExistsAndReadable? fileName = return (fileExistsAndReadable fileName)
\end{spec}

\begin{spec}
}
\end{spec}
