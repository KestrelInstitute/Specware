\section{Operations in the State Monad}

We define here a family of functions for allocating, reading and writing
global and local variables.

The first spec defines the API to a family of primitive (impure) state
operations.

As discussed below, the implementation of these operations is unsafe.
In particular, it is possible to create a local variable in one monadic
context and then access it in another.  However, provided one does not
do such things, the local operations are safe.

See below for further notes regarding the safety of these operations.

\begin{spec}
let
  MonadicStateInternal = spec
    sort VarRef a = | VarRef a

    op newGlobalVar : fa (a) String * a -> Boolean
    op readGlobalVar : fa (a) String -> Option a
    op writeGlobalVar : fa (a) String * a -> Boolean

    op newVar : fa (a) a -> VarRef a
    op writeVar : fa (a) VarRef a * a -> VarRef a
  endspec
\end{spec}

Below is the definition of the state monad. Some sorts and ops remain
abstract.  This implementation remains unsafe for both global and local
variables.

Local variables are implemented using a cons cell when the tail of the
cell is the value if the variable.  The cell itself is considered a
\Sort{VarRef}. Writing to the variable means replacing the tail.

The problem with local variables is that, even if the user is reponsible
and uses only the monadic operations to access the variable, there is
nothing to stop him or her creating a variable in one monadic context,
leaving the monadic context (and exporting the variable reference)
and then accessing the same variable in a different monadic context.

The better way to implement local state would be as follows:
\begin{itemize}
\item Factor this spec such that the implementation becomes a refinement
of an abstract spec.
\item Include in the abstract spec the function
\begin{verbatim}
    op Monad.run : fa (a) Env a -> a
\end{verbatim}
for running something inside the state monad.
\item In the refined spec, include a sort \Sort{State} and define the monad
sort to be something like \Sort{Monad a = State -> (Result a) * State}.
Here \Sort{Result a} is for accommodating exceptions.
\item Refine \Sort{State} to be (or include) a side-effecting map or array and a counter.
\item Refine \Op{newVar} to use the counter to fill in the next position
in the map with the given value and increment the counter. The old
counter value is returned \emph{plus the map} as the variable reference. Now
when one leaves the context, the map disappears.
\item Refine \Op{readVar} such that it first checks to see if the map
associated with the variable reference is the same as the map in the monadic context.
If it isn't then we must fail ungracefully as the program is not well formed.
\end{litemize}

The problem with the above approach is that once we leave a scope, the
local variable should become garbage. If the local variables perist in a
global shared map, they will never be collected.  Perhaps there should be context
counter in the global context. Each time we do a run, we increment the
counter. Each variable cell is then augmented with the counter. When we
read, we check the current global counter with that of the variable and
if they disagree then something bad has happened. So there must
be two counters. One for the next run and one identifying the context
we are in. The latter must be woven through the function calls.

There \emph{might} be a similar problem with global variables though
given that we are accessing the variable by name rather than by reference,
then as I see it, there is little difference between accessing a global
variable and creating, reading and writing a file.

There is, however, a bad problem with type safety. One can write a variable
with a value of one type and read the variable into a different type.

One way to remedy this is as follows:
\begin{itemize}
\item Define a sort \Sort{GlobalVar} to have a constructor for each global
variable: eg
\begin{verbatim}
  sort AllGlobals = | V1 (Option S1)
                    | V2 (Option S2)
                    | ...
  sort GlobalVar s = Option s -> AllGlobals
\end{verbatim}
where each \Op{V1} is a variable name.
\item Refine \Sort{State} (discussed above) to include a mutable map
where for each $i$, \Op{Vi None} maps to \Op{Vi x} where $x$ is the
value of the variable.
\item Define operators with the same name (or approx the same name)
and type as the constructors.
\begin{verbatim}
    op v1 : GlobalVar S1
    def v1 x = V1 x
\end{verbatim}
This will become unnecessary when constructors and ops become identified.
\item Refine \Op{readGlobalVar v} to be lookup \Term{(v None)} in the
mutable map.  
\item Refine \op{Monad.run} to save and restore the global
variables to the Lisp context (and perhaps even the filesystem).
\end{itemize}

\begin{spec}
in Monad qualifying spec
  import MonadicStateInternal qualifying MonadicStateInternal
  import Exception

  op redefinedGlobalVariable : String -> Exception
  op undefinedGlobalVariable : String -> Exception

  sort State  % This remains abstract.

  op renewGlobalVar : fa (a) String * a -> Monad ()
  def renewGlobalVar (name,value) =
    if MonadicStateInternal.newGlobalVar (name,value) then
      return ()
    else
      return ()

  op newGlobalVar : fa (a) String * a -> Monad ()
  def newGlobalVar (name,value) =
    if MonadicStateInternal.newGlobalVar (name,value) then
      return ()
    else
      return ()
      % raise (redefinedGlobalVariable name)
    
  op writeGlobalVar : fa (a) String * a -> Monad ()
  def writeGlobalVar (name,value) =
    if MonadicStateInternal.writeGlobalVar (name, value) then
      return ()
    else
      raise (undefinedGlobalVariable name)

  op readGlobalVar : fa (a) String -> Monad a
  def readGlobalVar name =
    case MonadicStateInternal.readGlobalVar name of
      | Some value -> return value
      | None -> raise (undefinedGlobalVariable name)

  op newVar : fa (a) a -> Monad (VarRef a)
  def newVar value = return (MonadicStateInternal.newVar value)

  op readVar : fa (a) VarRef a -> Monad a
  def readVar (VarRef value) = return value


  op writeVar : fa (a) VarRef a * a -> Monad (VarRef a)
  def writeVar (varRef,value) = return (MonadicStateInternal.writeVar (varRef,value))
endspec
\end{spec}
