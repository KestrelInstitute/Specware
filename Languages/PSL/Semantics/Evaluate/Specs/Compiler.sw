\section{Compilation of Oscar/PSL Procedures into BSpecs}

## There are name conflicts for the product accessors for Procedures, Oscar.Specs and CompCtxt

\begin{spec}
SpecCalc qualifying spec
  import /Languages/PSL/AbstractSyntax/Types
  import Oscar
  import MonadicLists
  import Context
  import MetaSlang
  import MetaSlang/Legacy
  import SortList
  import Subst
  import Claim/Legacy    % shameful

  sort TimeStamp
  sort UnitId_Dependency
\end{spec}

An Oscar spec consists of a collection of "elements" called "OscarSpec
elements".  Elements include, sorts, ops, axioms plus vars and
procedures. Objects are to come later.

A value of an Oscar spec is a mode spec and a map from procedure names
to procedure values. A mode spec is a conventional spec that holds extra
information such as which ops are vars and which are conventional ops.
The variables in the mode spec are all those variables that are in
scope in the accompanying procedures. This mode spec is sometimes called
a context.

Each procedure definition gives rise to two things in an Oscar value.
First, it appears in the procedure map. Second, it gives rise to
an op in the mode spec. This op denotes a relation that serves
to encapsulate the procedure for the benefit of callers. That is, a call
to a procedure is represented by a transition labelled with an
instance of the predicate for the procedure.

The predicate for a procedure denotes an input/output relation. The input 
are the parameters to the procedure plus the variables in scope when the
procedure is declared. The output is the return value (if there is one)
and the new values for the global variables.

For instance, suppose we have a procedure "proc exp (x : Nat, y : Nat)
: Nat" for computing exponential, and this procedure is defined in a
context with variables u:String, v :Boolean. Then in the context we
would have an op:

op exp : Proc (Nat * Nat, Nat, String * Boolean)

where

sort Proc (arg,rtn,store) = (arg * rtn * (Delta store)) -> Boolean
sort Delta x = x * x

A call of the form "z := exp (u,5)" would yield a transition
labelled with an axiom:

axiom call is exp ((u,5),z',((u,v),(u',v')))

\begin{spec}
  op evaluateOscarSpecElems  : Oscar.Spec -> List (OscarSpecElem Position) -> Env (Oscar.Spec * TimeStamp * UnitId_Dependency)
  op evaluateOscarSpecContextElems : Oscar.Spec -> List (OscarSpecElem Position) -> Env Oscar.Spec

  op sortOpInfoList : List Op.OpInfo -> List Op.OpInfo
  def sortOpInfoList infoList =
    let
      def cmpOpInfo (o1:Op.OpInfo,o2:Op.OpInfo) =
        (show (idOf o1)) leq (show (idOf o2))
    in
      sortList cmpOpInfo infoList

  op evaluateProcElemPassOne : Oscar.Spec -> OscarSpecElem Position -> Env Oscar.Spec
  def evaluateProcElemPassOne oscarSpec (elem,position) =
    case elem of
      | Proc (procName,procInfo) -> {
          (*
           * We begin by defining the operator to represent the procedure in the static context. This
           * op has Proc sort and is used to label those transitions that call the procedure.
           *)
          argProd <- mkProduct (map (fn (name,srt) -> toType srt) (formalArgs procInfo), position); 
          varOps <- return (sortOpInfoList (foldVariables
               (fn varList -> fn (varInfo:Op.OpInfo) -> cons (varInfo,varList)) [] (modeSpec oscarSpec)));
          storeProd <- mkProduct (map (fn (varInfo:Op.OpInfo) -> type varInfo) varOps, position);
          procType <- mkBase (makeId "Proc", [argProd,toType procInfo.returnSort,storeProd], position); 
          procId <- return (makeId procName);
          procOp <- makeOp (procId, procType);
          modeSpec <- addOp (modeSpec oscarSpec) procOp position;
          return (oscarSpec withModeSpec modeSpec)
        }
      | _ -> return oscarSpec
\end{spec}

We want to construct a placeholder for the procedure. This includes an
almost empty BSpec. The modes of this BSpec must be labelled. We extend
the current dynamic context with operators (variables) for the formal
parameters to the procedure. These are now variables that are in scope.

The vertices of the underlying graph are integers that cast into
MetaSlang terms. We use terms since this helps us later when we do
partial evaluation.  The initial bSpec has states 0 and 1 corresponding
to the initial and final states.

\begin{spec}
  op evaluateProcElemPassTwo : Oscar.Spec -> OscarSpecElem Position -> Env Oscar.Spec
  def evaluateProcElemPassTwo oscarSpec (elem,position) =
    case elem of
      | Proc (procName,procInfo) -> {
          procId <- return (makeId procName);
          varOps <- return (sortOpInfoList (foldVariables
               (fn varList -> fn (varInfo:Op.OpInfo) -> cons (varInfo,varList)) [] (modeSpec oscarSpec)));
          varsInScope <- return (map refOf varOps);
          argVars <-
             let def paramsToOps params =
                case params of
                  | [] -> return []
                  | (paramName,paramSort)::params -> {
                       vars <- paramsToOps params;
                       varInfo <- makeOp (makeId paramName, toType paramSort);
                       return (cons (varInfo,vars))
                    }
             in
               paramsToOps (formalArgs procInfo);
          initialSpec <-
             fold (fn spc -> fn varInfo -> {
                    spc <- addVariable spc varInfo position;
                    return spc
                }) (Oscar.modeSpec oscarSpec) argVars; 
 
          (finalSpec,returnInfo) <- 
             case procInfo.returnSort of
               | Product ([],_) -> return (initialSpec, None)
               | _ -> {
                     varInfo <- makeOp (makeId "#return#" procName, toType (returnSort procInfo));
                     spc <- addVariable initialSpec varInfo position;
                     returnRef <- refOf varInfo;
                     return (spc, Some returnRef)
                   };

          initialSpecElab <- elaborate initialSpec; 

          finalSpecElab <- elaborate finalSpec; 

          bSpec <- return (
             let (initial,final) = (mkNatVertex 0, mkNatVertex 1) in
             let bSpec = addMode (BSpec.make initial finalSpecElab) final finalSpecElab in
             bSpec withFinal (VrtxSet.singleton final));
          proc <- return (makeProcedure (map refOf argVars) varsInScope
                                 returnInfo
                                 (Oscar.modeSpec oscarSpec)
                                 bSpec);
          addProcedure oscarSpec procId proc
        }
      | _ -> return oscarSpec

  op toType : ASort Position -> Type
  % def toType srt = (tyVarsOf srt,srt)
  def toType srt = ([],srt)
\end{spec}

### In the above, the dynamic context always includes the return operator.
In fact it need only appear in the final spec and in the apex of any
transition that ends in the final spec. The point is that
the assign operation isn't quite smart enough.

In the second pass of compiling a procedure we actually compile the command
in the body of the procedure.

The procedure context also includes a new entry for the procedure we
are about to compile. This is so that the procedure can be recursive.

The initial and final states here must agree with those used above
when the initial bSpec was constructed. Perhaps they shouldn't be
hard coded.

After compiling the procedure, we replace the procedure entry in the
oscarSpec computed in the first pass in the oscarSpec with a new one containing
the full bSpec.

\begin{spec}
  op evaluateProcElemPassThree : Oscar.Spec -> OscarSpecElem Position -> Env Oscar.Spec
  def evaluateProcElemPassThree oscarSpec (elem,position) =
    case elem of
      | Proc (procName,procInfo) -> {
           procValue <- return (eval (procedures oscarSpec, (makeId procName) :Id.Id));
           (initial,final) <- return (mkNatVertex 0, mkNatVertex 1);
           newModeSpec <- union (modeSpec (bSpec procValue) initial) (modeSpec oscarSpec);
           ctxt : CompCtxt <-
                return {
                  procedures = procedures oscarSpec,
                  modeSpec = newModeSpec,
                  graphCounter = 2,  % = final + 1
                  varCounter = 0,
                  initial = initial,
                  final = final,
                  exit = final,
                  break = None,
                  continue = None,
                  bSpec = bSpec procValue,
                  returnInfo = returnInfo procValue
                };
      
           ctxt <- compileCommand ctxt procInfo.command;
           proc <- makeProcedure (parameters procValue) (varsInScope procValue)
                                         (returnInfo procValue)
                                         (modeSpec procValue)
                                         (bSpec ctxt);
           oscarSpec <- addProcedure oscarSpec (makeId procName) proc;
           return oscarSpec
         }
      | _ -> return oscarSpec
\end{spec}

The following function compiles a procedure declaration (sort
\verb+ProcInfo+, plus the name of sort \verb+Ident+) into a procedure
representation (sort \verb+Procedure+).

Some care will have to take when choosing the sorts for the vertices and
edges of the shape graph. Procedures are to be partial evaluated. The
partial evaluator generates new vertices from old by augmenting a vertex
with a model.  The types of the vertices before and after should be the
same. A reasonable choice is to instantiate the vertex and edge sorts
for the graphs to be MetaSlang terms.

To compile the procedure, we generate a \BSpec\ from the \verb+command+
field of the of the procedure declaration. The compilation of a command
takes place in a context. Before passing the context to
\verb+compileCommand+, the dynamic context is updated with variables
for the procedure's arguments, as well as an extra variable for the result.
The variable for the result cannot be named as the procedure, because
the static context already includes an operator that encapsulated the
procedure, and that operator has a different type. So, we just prepend
the name of the procedure with \verb+return\_+. The value returned by
the procedure is the value of such variable when the procedure is exited.
The partial evaluator makes use of this convention.

The code assumes that there is no hiding of variables: variables declared in
a procedure (including its arguments) must be distinct from variables
declared, say, in an enclosing procedure. However, two procedures in separate
``branches'' may indeed have common variable names, because they will be
never mixed in the specs labeling \BSpecs.

In the above, note that the procedure is already represented
in the static context by an operator. A procedure is in scope within its
own definition \emph{i.e.} procedures may be recursive.

We compile commands recursively. The compilation of a command returns
a \BSpec, and \BSpecs\ returned by sub-commands are suitably combined
into a larger \BSpec\ for the super-command. Since commands may
recursively contain declarations, which include procedures, the
compilation of a command also returns the procedures nested inside the
command.

The partial evaluator requires the nodes and edges of the generated
\BSpecs\ to be MetaSlang terms (of sort \verb+ATerm+). It does not
matter which exact terms, as long as they are terms. So, we use MetaSlang
natural number constants. Since we need to combine \BSpecs\ for
sub-commands into \BSpecs\ for super-commands, we generate
graphs with disjoint nodes and edges for the sub-commands. We achieve that
by threading a counter (\emph{i.e.} a natural number) through the
functions to compile commands. The counter is used generate unique
``names'' for nodes and edges.

\begin{spec}
  sort Systems.Elem = ATerm Position
\end{spec}

Even if bipointed \BSpecs\ have one starting node and a set of ending nodes,
compilation always produces singleton sets of ending nodes. The partial
evaluator may generate sets with more than one node, that is the
reason for having a set of ending nodes.

We compile a command with respect to a compilation context.
The context includes the identities of the vertices in the BSpec
to be connected by the command. That is, the endpoints of a command are already
part of the BSpec by the time we compile the command. 

\begin{spec}
  op compileCommand : CompCtxt -> Command Position -> Env CompCtxt
\end{spec}

\begin{spec}
  def compileCommand ctxt (cmd,position) =
    case cmd of
      | Seq cmds -> compileSeq ctxt cmds
      | If [] -> specError "compileCommand: If: empty list of alternatives" position
      | If alts -> {
          ctxt <- compileAlternatives ctxt alts;
          axm <- return (mkNot (disjList (map (fn ((guard,term),_) -> guard) alts, position), position));
          prop <- makeAxiom (makeId "guard") axm;
          apexSpec <- addInvariant (modeSpec ctxt) prop position;
          connectVertices ctxt (initial ctxt) (final ctxt) apexSpec OpRefSet.empty
        }
\end{spec}

To compile a loop, we compile the alternatives in the body in such a
way that all the branches connect the initial point in the current BSpec
with itself. We also connect the initial vertex with the final vertex
labelled with an axiom representing the negation of the disjunction
of the guards in the alternatives. This is the exit branch of the loop.

### When we create the axiom, we give it an empty list of type variables
under the assumption that they are never used. Needs thought.

\begin{spec}
      | Do [] -> fail "compileCommand: Do: empty list of alternatives"
      | Do alts -> {
          saveFinal <- return (final ctxt);
          saveBreak <- return (break ctxt);
          saveContinue <- return (continue ctxt);
          ctxt <- return (ctxt withBreak (Some (final ctxt)));
          ctxt <- return (ctxt withContinue (Some (initial ctxt)));
          ctxt <- return (ctxt withFinal (initial ctxt));
          ctxt <- compileAlternatives ctxt alts; 
          ctxt <- return (((ctxt withFinal saveFinal) withContinue saveContinue) withBreak saveBreak);
          axm <- return (mkNot (disjList (map (fn ((guard,term),_) -> guard) alts, position), position));
          prop <- makeAxiom (makeId "guard") axm;
          apexSpec <- addInvariant (modeSpec ctxt) prop position;
          connectVertices ctxt (initial ctxt) (final ctxt) apexSpec OpRefSet.empty
        }
\end{spec}

An assignment command connects the initial and final points of the
current \BSpec\ with a single transition. 

The tricky bit is to construct the spec for the assignment and the
morphism in the opspan. The point is that the variables not appearing
on the left side of the assignment do not change and the issue is how
to express this. Also we must bear in mind that the left side of the
assignment may be a functional term where, essentially, one is updating
a map.

There are a few ways to do this.  
Assume we have an assignment \verb+f x := t+ in a dynamic context
consisting of \verb+f : X -> T+,
\verb+x : X +, \verb+g : Y -> Z+, and \verb+z : Z+.

\begin{itemize}
\item In the first case, the spec at the apex of the opspan imports a
copy of the spec at the start and a copy of the spec at the end of the
transition. To avoid name clashes, all the ops from the destination are
``primed''. The opspan morphisms to the apex are the obvious imports. Then
we add the following formula at the apex:
\begin{verbatim}
  axiom f' x = t
    & x' = x
    & g' = g
    & z' = z
    & fa x' : X . x' != x => (f' x) = (f x)
\end{verbatim}

\item The second approach is like the above. In this case the signature
of the spec for the transition (at the apex) is the spec at the start
of the transiton plus primed versions of only those operators that change. In
this case only \verb+f'+ is added. The axiom at the apex deals only with
those variables that change. Thus it would contain only the first and
last conjuncts from the above.

The opspan morphisms are as follows.  The morphism from the start state
is the canonical injection (identity on names). The morphism from the
final spec to the apex is the identity everywhere except for identifiers
changed by the transition. In that case the identifier is mapped to its
primed version. For the above, this would be \verb+f+ $\mapsto$ \verb+f'+.

An alternative axiomitization of the above in the case
where one is updating a function space, would have an update function
in the global static spec
\[
\mathit{update}\ f\ x\ t =
\lambda \ y . \mathbf{if} \ x = y\ \mathbf{then}\ t\ \mathbf{else}\ (f\ x)
\]
and then label the transition with:
\begin{verbatim}
  axiom f' = update f x t
\end{verbatim}

\item The final approach would be to use either of the above
but rather than \verb+fa+, to fold a conjunction over the clause to right
of the \verb+fa+ operation over the domain of the map \verb+f+ 
\end{itemize}

We choose the second approach. The code is complicated somewhat by
the possibility that the right hand side may be an expression (without
side-effects) of a procedure call. The latter appears as an application
where the function symbol is the name of a previously declared procedure.
It is further complicated by the possibility that the procedure name
may appear qualified or unqualified.

\begin{spec}
      | Assign (trm1,trm2) ->
          (case trm2 of
            | ApplyN ([Fun(OneName(id,fixity),srt,position),argTerm],_) ->
                if ~((evalPartial (procedures ctxt, (makeId id):Id.Id)) = None) then
                  compileProcCall ctxt (Some trm1) (makeId id) argTerm position
                else
                  compileAssign ctxt trm1 trm2 position
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,position),argTerm],_) ->
                if ~((evalPartial (procedures ctxt, (makeId id1 id2):Id.Id)) = None) then
                  compileProcCall ctxt (Some trm1) (makeId id1 id2) argTerm position
                else
                  compileAssign ctxt trm1 trm2 position
            | _ ->
                compileAssign ctxt trm1 trm2 position)
\end{spec}

To handle a Return command, we must first check that function returns
something when it has been declared to do so, and doesn't return anything
if it has been given a return sort of \verb|()|.

If it returns nothing, then we connect the current start vertex with
the exit vertex with a transition that is taken unconditionally and has
no effect. Right now we include a transition with a single \verb|true|
axiom but we might be better off without an axiom at all.

\begin{spec}
      | Return optTerm ->
          (case (optTerm,returnInfo ctxt) of
            | (None,None) -> {
                  prop <- makeAxiom (makeId "assign") (mkTrue position);
                  apexSpec <- addInvariant (modeSpec ctxt) prop position;
                  connectVertices ctxt (initial ctxt) (exit ctxt) apexSpec OpRefSet.empty
                }
            | (None,Some returnRef) -> {
                  returnVar <- deref (specOf (modeSpec (bSpec ctxt) (exit ctxt)), returnRef);
                  specError ("Procedure has return sort " ^ (show (type returnVar)) ^ " but no return value") position
                }
            | (Some term, None) ->
                specError "Procedure with unit sort returns a value" position
            | (Some term, Some returnRef) -> {
                  returnVar <- deref (specOf (modeSpec (bSpec ctxt) (exit ctxt)), returnRef);
                  lhs <- mkFun (idToNameRef (idOf returnVar), type returnVar, position);
                  saveLast <- return (final ctxt);
                  ctxt <- return (ctxt withFinal (exit ctxt));
                  ctxt <-
                    case term of
                      | ApplyN ([Fun(OneName(id,fixity),srt,position),argTerm],_) ->
                          if ~((evalPartial (procedures ctxt, (makeId id):Id.Id)) = None) then
                            compileProcCall ctxt (Some lhs) (makeId id) argTerm position
                          else
                            compileAssign ctxt lhs term position
                      | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,position),argTerm],_) ->
                          if ~((evalPartial (procedures ctxt, (makeId id1 id2):Id.Id)) = None) then
                            compileProcCall ctxt (Some lhs) (makeId id1 id2) argTerm position
                          else
                            compileAssign ctxt lhs term position
                      | _ -> compileAssign ctxt lhs term position;
                  return (ctxt withFinal saveLast)
                })
\end{spec}

\begin{spec}
      | Continue -> 
          (case (continue ctxt) of
             | Some continueVertex ->
                 connectVertices ctxt (initial ctxt) continueVertex (modeSpec ctxt) OpRefSet.empty
             | None ->
                 specError "continue appears outside of a loop" position) 

      | Break ->
          (case (break ctxt) of
             | Some breakVertex ->
                 connectVertices ctxt (initial ctxt) breakVertex (modeSpec ctxt) OpRefSet.empty
             | None ->
                 specError "break appears outside of a loop" position)
\end{spec}

\begin{spec}
	  | Exec trm ->
          (case trm of
            | ApplyN ([Fun(OneName(id,fixity),srt,position),argTerm],_) ->
                if ~((evalPartial (procedures ctxt, (makeId id):Id.Id)) = None) then
                  compileProcCall ctxt None (makeId id) argTerm position
                else
                  specError ("call to undefined procedure: " ^ id) position
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,position),argTerm],_) ->
                if ~((evalPartial (procedures ctxt, (makeId id1 id2):Id.Id)) = None) then
                  compileProcCall ctxt None (makeId id1 id2) argTerm position
                else
                  specError ("call to undefined procedure: " ^ id1 ^ "." ^ id2) position
            | _ ->
               specError "invalid procedure call or relation statement" position)
\end{spec}


begin{spec}
      | Relation trm -> compileAxiomStmt ctxt trm position
end{spec}

To compile a \verb+let+, we first compile its declarations, thus enlarging
the context. Then, we compile the command in the enlarged context.
We add a transition into and a transition out of the \BSpec\ produced
by compiling the command. The spec labeling the starting and ending vertices
of the \BSpec\ for the \verb+let+ are determined by the smaller (i.e., not
enlarged) context.

This will actually evaluate nested imports which is all wrong.

The following is wrong as the variables should come in and then out of scope.

\begin{spec}
      | Let (decls,cmd) -> {
            oscarSpec <- return (Oscar.make (modeSpec ctxt) (procedures ctxt));
            newOscarSpec <- evaluateOscarSpecContextElems oscarSpec decls;
            saveModeSpec <- return (modeSpec ctxt);
            ctxt <- return (ctxt withModeSpec (modeSpec newOscarSpec));
            ctxt <- compileCommand ctxt cmd;
            return (ctxt withModeSpec saveModeSpec)
          }
\end{spec}

Compiling a skip is a transition where the maps are identities and
the axiom is just true.

Should really check that the specs at the start and end are the same.
This should be an invariant. Must check.

\begin{spec}
      | Skip -> {
          axm <- makeAxiom (makeId "skip") (mkTrue position);
          apexSpec <- addInvariant (modeSpec ctxt) axm position;  % why bother?
          connectVertices ctxt (initial ctxt) (final ctxt) apexSpec OpRefSet.empty
        }
\end{spec}

\begin{spec}
  op compileAssign : CompCtxt -> MSlang.Term -> MSlang.Term -> Position -> Env CompCtxt
  def compileAssign ctxt lhs rhs position = {
    (leftId, leftPrimedTerm) <- processLHS lhs position; 
    varInfo <- catch
     (findTheVariable (modeSpec ctxt) leftId)
     (fn except ->
        case except of
          | SpecError (pos,str) -> specError ("Variable '" ^ (show leftId) ^ "' is undefined") position
          | _ -> raise except);
    apexSpec <- addVariable (modeSpec ctxt) (varInfo withId (makePrimedId leftId)) position; 
    axm <- mkEquality (leftPrimedTerm,rhs,position);
\end{spec}

Here we add the axioms encoding the assignment to the apex spec. Right
now the axiom has no type varibles in the sort scheme. There might
be scope for more polymorphism if we use the \verb+tyVarsOf+ function
that Alessandro wrote below rather than use, as below, an empty list of
type variables.

\begin{spec}
    trm <- makeAxiom (makeId "assign") axm; 
    apexSpec <- addInvariant apexSpec trm position;
    connectVertices ctxt (initial ctxt) (final ctxt) apexSpec
                                  (OpRefSet.singleton (refOf varInfo))
  }
\end{spec}

The left-hand-side of an assignment can be an operator or an application.
Later we will enforce more restrictions on the left with respect to
the nature of the applications.  The following function returns a
``primed'' version of the principal operator. Hence, in \verb+x :=
g(x,y)+, the \verb+x+ becomes \verb+x'+ and in \verb+f(x,y) := g(x,y)+,
then \verb+f(x,y)+ becomes \verb+f'(x,y)+.  It also returns the name
of the principal identifier. The identifier is assumed to be local
to the current spec and unqualified.  The ``priming'' is obtaining by
suffixing the variable's name by "'".  Note, however, that apostrophe is
not allowed in MetaSlang identifiers.  This implies that if one cannot
write the specs out and read them in again, but at least ensures there
is no clash with user-introduced variables.

Don't even think about using infix operators on the left of the
assignment.  As things are now, we are processing left-side applications
\emph{before} infixes are resolved.  That is, we assume that the left-most
in the application operator is the operator being applied to the remaining
elements in the list.

normalization of application

eval x 3 and
whenever we see apply [

  op normalizeTerm : Spec.Spec -> ATerm Position -> Env (ATerm Position)
  def normalizeTerm spc term =
    def fixTerm spc term =
      case term of
        | ApplyN ([x,y],pos) ->
            
A :> B :> C
a b c => ((a b) c)
but the problem is that this doesn't handle the infix operators. hence is needs to happen
after infix operators have been resolved. perhaps the answer is that when someone declares
f : Map A B
they get a map and the also get an overloaded function that is
Over.f a = eval f a
and then we go through and replace every instance of op Over.f with eval f

this doesn't work in the following case:

var z : A => B => C -> A => (B => C) -> z : X
sort X = Map_A_Y
sort Y = Map_B_C
op Y.eval : Map_B_C -> B -> C
op X.eval : Map_A_Y -> A -> Y

z a b -> ((z a) b) -> (Y.eval (X.eval z a) b)
 
\begin{spec}
  op processLHS : ATerm Position -> Position -> Env (Id.Id * (ATerm Position))
  def processLHS term position =
    let
      def firstPass trm l pos =
        case l of
          | [] -> trm
          | x::l -> firstPass (ApplyN ([trm,x],pos)) l pos
      def secondPass trm =
        case trm of
          | ApplyN ([x,y],pos) ->
              let srt = freshMetaTyVar pos in
              ApplyN ([ApplyN ([Fun (OneName ("eval",Nonfix),srt,pos), secondPass x],pos),y],pos)
              % ApplyN ([ApplyN (Fun (OneName ("eval",Nonfix),srt,pos) (secondPass x) pos),y],pos)
          | _ -> trm
    in
      case term of
        | Fun (OneName(id,fixity),srt,pos) ->
            return (makeId id, Fun(OneName(id ^ "'",fixity),srt,pos))
        | ApplyN ((Fun (OneName(id,fixity),srt,pos))::args,pos) ->
            % let newTerm = secondPass (firstPass (Fun (OneName(id ^ "'",fixity),srt,pos)) args pos) in
            let newArgs = cons (Fun (OneName(id ^ "'",fixity),srt,pos),args) in
            return (makeId id, ApplyN (newArgs,pos))
        | ApplyN ((Fun (TwoNames(id1,id2,fixity),srt,pos))::args,pos) ->
            let newArgs = cons (Fun (TwoNames(id1,id2 ^ "'",fixity),srt,pos),args) in
            return (makeId id1 id2, ApplyN (newArgs,pos))
        | Fun (TwoNames(id1,id2,fixity),srt,pos) ->
            let newTerm = Fun (TwoNames(id1,id2 ^ "'",fixity),srt,pos) in
            return (makeId id1 id2, newTerm)
        % | ApplyN ((Fun (Op(id,fixity),srt,pos))::args,pos) ->
        %    (id, ApplyN (Cons (Fun(Op(makePrimedId id,fixity),srt,pos),args),pos))
        % | Fun (Op(id,fixity),srt,pos) -> (id, Fun(Op(makePrimedId id,fixity),srt,pos))
        | _ -> specError "Left side of assignment is neither a variable nor an assignment" position
\end{spec}

This is a function introduced for DTR but supporting a feature that
is meant to be in PSL (questions of concrete syntax remain). This
is used when a boolean valued term is used as a program statement.
The term denotes a relation between the new and old values of the
variables in scope. The new names for the new values are ``primed''.
This constructs a spec where the apex spec has as its axiom the
given term.  The operators in the dynamic context include both
the variables in context and primed versions of the variables. A better
scheme would be to introduced primed copies of the variables 
only for those that change value
there needs t be a better way of computing the free variables .. and
striclty speaking, we can't do it until after typechecking since
if a var appears on its own we don't know until after typechecking whether
it is a constuctor.
So the following doesn't handle the situation where the name are captured by lambda's.

\begin{spec}
  op isPrimedName? : QualifiedId -> Boolean
  def isPrimedName? (qualId as (Qualified (qual,id))) = hd (rev (explode id)) = #'
\end{spec}

  op freeNames : fa (a) ATerm a -> List QualifiedId
  def freeNames term =
    let
      def foldP names pattern = names
      def foldS names srt = names
      def foldT names term = 
        case term of
          | Fun (OneName(id,fxty),srt,_) -> ListUtilities.insert (unQualified id,names)
          | Fun (TwoNames(id1,id2,fxty),srt,_) -> ListUtilities.insert (Qualified (id1,id2),names)
          | _ -> names
    in
      foldTerm (foldT,foldS,foldP) [] term

  op compileAxiomStmt : CompCtxt -> ATerm Position -> Position -> Env CompCtxt

  def compileAxiomStmt ctxt trm position = {
    primedNames <- return (filter isPrimedName? (freeNames trm));
    apexSpec <- foldM (fn spc -> fn qualId ->
      (case findTheOp (dynamic ctxt,removePrime qualId) of
         | None ->
             raise (SpecError (position, "compileAxiomStmt: unprimed id '"
                          ^ (printQualifiedId (removePrime qualId)) ^ "' is undefined"))
         | Some (names,fixity,sortScheme,optTerm) -> {
                  print ("compileAxiomStmt: " ^ (printQualifiedId qualId) ^ "\n");
                  addOp [qualId] fixity sortScheme optTerm spc position}
       )) (dynamic ctxt) primedNames; 
     apexSpec <- return (addInvariant (("axiom stmt",[],trm),apexSpec));
     connectVertices ctxt (initial ctxt) (final ctxt) apexSpec
  }
end{spec}

The following function is used to compile a procedure call, whose result
is either assigned or discarded.  The arguments to this function are
a procedure (name), a term representing the argument (or arguments)
to the procedure and an optional term. If present, the term represents
the left hand side of the assignment where the procedure is called.
If absent, then there is no return value.

The sort of this function is a nightmare.

For the time being, we will assume that the names of the arguments
differ from anything in the dynamic context. This bad.

What follows is has become a bit of a dog's breakfast. The complication
comes from handling both the case where the function we're compiling
returns something and the case where it doesn't. There should be better
way to factor this.

It might be better to define two different Proc sorts .. one for functions
that return something and one for functions that don't .. and then handle
the two cases separately throughout the code.

It might simplify code generation as well.

Should we allow the case (as in C) where one calls a function which
returns something but where we choose to ignore what we get back?

Alessndro accommodated this in an earlier version of the compiler but
it complicated things for the partial evaluator so it was removed. It
should probably be reintroduced. Basically, if the procedure returns
something but it is not used, we create a meta-slang variable and use
it in the return location. Then, we add an existential quantifier in
front of the axiom term.

To compile a procedure call whose result gets assigned to a variable,
we use the operator that encapsulates the procedure. We have to create,
in the apex spec, primed versions of all the variables. Then, we have
to create two records one with the non-primed variables, and one with the
primed ones. The two records form the third argument to the operator
for the procedure in the axiom.

We assume that the left hand side term of the assignment is a variable.
Its primed version becomes the second argument to the operator for the
procedure in the axiom. The first argument is the tuple of terms given
as arguments to the procedure, and they are all non-primed.

To compile a procedure call with no return value, we create a
one-transition \BSpec\ similar to the one above. The difference is that
the second argument to the operator representing the return value of
the procedure is the unit \verb+()+.

\begin{spec}
  op compileProcCall :
       CompCtxt
    -> Option MSlang.Term
    -> Id.Id
    -> MSlang.Term
    -> Position
    -> Env CompCtxt

  def compileProcCall ctxt trm? procId argTerm position = {
      procOpInfo <- catch
        (findTheOp (modeSpec ctxt) procId) 
        (fn except ->
           case except of
             | SpecError (pos,str) ->
                 specError ("Call to undefined procedure: " ^ (show procId)) position
             | _ -> raise except);

      (*
       * If the procedure we are calling returns something, then we need to add a primed
       * version of the receiving variable to the mode spec. If it doesn't return something
       * then we assume the return value is ().
       *)
      (apexSpec,leftPrimedTerm,changedVars) <-
        case trm? of
          | None -> return (modeSpec ctxt, mkRecord ([],position), OpRefSet.empty)
          | Some trm -> {
               (leftId, leftPrimedTerm) <- processLHS trm position;
               varInfo <-
                 catch 
                   (findTheVariable (modeSpec ctxt) leftId)
                   (fn except ->
                      case except of
                        | SpecError _ -> specError ("Variable '" ^ (show leftId) ^ "' is undefined") position
                        | _ -> raise except);
               apexSpec <- addVariable (modeSpec ctxt) (varInfo withId (makePrimedId leftId)) position; 
               return (apexSpec,leftPrimedTerm, singleton (refOf varInfo))
            };
\end{spec}

So a procedure can write to anything in scope when it was declared.
What about local variables that are introduced after the procedure is declared
but before the procedure is called. They must be renamed when they are introduced.
If a variable name appears here and in the dynamic context of the procedure,
then they are the same variable. Moreover we can be certain that the new primed
version of the variable doesn't exist.

So what is the rule for names. When we call the procedure, we need to
pass the entire state that is in scope when the procedure is declared.
This is all the local names in the procInfo.dynamicSpec.

# The order in which the list if changed ops is obtained is significant. It
must agree with the definition of the Proc op for this procedure.

\begin{spec}
      procInfo <- return (eval (procedures ctxt, procId)); 
      apexSpec <- foldVariables (fn modeSpec -> fn varInfo ->
        addVariable modeSpec (varInfo withId (makePrimedId (idOf varInfo))) position) apexSpec (modeSpec procInfo);
      varOps <- return (map (fn varRef -> deref (specOf (modeSpec procInfo),varRef)) (varsInScope procInfo));
      varList <- return (map (fn (varInfo:Op.OpInfo) -> mkFun (idToNameRef (idOf varInfo), type varInfo, position)) varOps);
      oldStore <- mkTuple (varList, position);
      varList <- return (map (fn (varInfo:Op.OpInfo) -> mkFun (idToNameRef (makePrimedId (idOf varInfo)), type varInfo, position)) varOps);
      newStore <- mkTuple (varList, position);
      storePair <- mkTuple ([oldStore,newStore], position); 
      totalTuple <- mkTuple ([argTerm,leftPrimedTerm,storePair], position); 
      procOp <- mkFun (idToNameRef procId, type procOpInfo, position);
      axm <- mkApplyN (procOp, totalTuple, position);
      trm <- makeAxiom (makeId "call") axm; 
      apexSpec <- addInvariant apexSpec trm position;
      connectVertices ctxt (initial ctxt) (final ctxt) apexSpec (union (changedVars, variables (modeSpec procInfo)))
   }
\end{spec}

The following compiles a sequence of commands. For each command
we introduce a new vertex ``between'' the current initial and final
vertices, compile the first command between the initial and new vertices
and compile the rest between the new and final vertex.

\begin{spec}
  op compileSeq : CompCtxt -> List (Command Position) -> Env CompCtxt

  def compileSeq ctxt cmds =
    case cmds of
      | [] -> return ctxt
      | [cmd] -> compileCommand ctxt cmd
      | cmd::rest -> {
            (newVertex,ctxt) <- newVertex ctxt; 
            ctxt <- ctxt withBSpec (addMode (bSpec ctxt) newVertex (modeSpec ctxt));
            saveLast <- return (final ctxt);
            ctxt <- compileCommand (ctxt withFinal newVertex) cmd;
            compileSeq ((ctxt withFinal saveLast) withInitial newVertex) rest
          }
\end{spec}

To compile a collection of alternatives, we compile each alternative
separately but in such a way that they all connect the same
initial and final states. 

To compile an individual alternative, we create a new transition for
the guard (from the initial vertex to a new vertex) and the compile the
command in the alternative (between the new and final vertices).

Perhaps addMode and friends shoul act on and return a context rather than a bSpec.

\begin{spec}
  op compileAlternative : CompCtxt -> Alternative Position -> Env CompCtxt
  def compileAlternative ctxt ((trm,cmd),pos) = {
      (newVertex,ctxt) <- newVertex ctxt; 
      bSpec <- return (addMode (bSpec ctxt) newVertex (modeSpec ctxt)); 
      ctxt <- ctxt withBSpec bSpec;
      prop <- makeAxiom ((makeId "guard"):Id.Id) trm;
      apexSpec <- addInvariant (modeSpec ctxt) prop pos; 
      saveFirst <- return (initial ctxt);
      ctxt <- connectVertices ctxt (initial ctxt) newVertex apexSpec OpRefSet.empty;
      ctxt <- compileCommand (ctxt withInitial newVertex) cmd;
      return (ctxt withInitial saveFirst)
    }
 
  op compileAlternatives : CompCtxt -> List (Alternative Position) -> Env CompCtxt
  def compileAlternatives ctxt alts =
    case alts of
      | [alt] -> compileAlternative ctxt alt
      | firstAlt::restAlts -> {
            ctxt <- compileAlternative ctxt firstAlt;
            compileAlternatives ctxt restAlts
          }
\end{spec}

The following function creates a vertex/edge (of sort \verb+Vrtx.Vertex+
from a natural number. 

\begin{spec}
  sort Vrtx.Vertex =
    | Nat Nat
    | Pair (Vrtx.Vertex * Subst)

  op Vrtx.eq? : Vrtx.Vertex * Vrtx.Vertex -> Boolean 
  def Vrtx.eq? = Vrtx.equalVertex?

  op Vrtx.equalVertex? : Vrtx.Vertex * Vrtx.Vertex -> Boolean 
  def Vrtx.equalVertex? (v1,v2) =
    case (v1,v2) of
      | (Nat n1, Nat n2) -> n1 = n2
      | (Pair (v1,s1), Pair (v2,s2)) -> equalVertex? (v1,v2) & equalSubst? (s1,s2)

  def Vrtx.pp vertex =
    case vertex of
      | Nat n -> String.pp (Nat.toString n)
      | Pair (vertex,subst) ->
         ppConcat [
           String.pp "(",
           pp vertex,
           String.pp ",",
           pp subst,
           String.pp ")"
         ]
  def Vrtx.show vertex = ppFormat (pp vertex)

  op mkNatVertex : Nat -> Vrtx.Vertex
  def mkNatVertex n = Nat n

  op newVertex : CompCtxt -> Env (Vrtx.Vertex * CompCtxt)
  def newVertex ctxt =
    return (mkNatVertex (graphCounter ctxt),
     ctxt withGraphCounter ((graphCounter ctxt) + 1))
\end{spec}

\begin{spec}
  sort Edg.Edge =
    | Nat Nat
    | Triple (Edg.Edge * Subst * Subst)

  def Edg.pp edge = 
    case edge of
      | Nat n -> String.pp (Nat.toString n)
      | Triple (edge,pre,post) ->
          ppConcat [
            String.pp "(",
            pp edge,
            String.pp ",",
            pp pre,
            String.pp ",",
            pp post,
            String.pp ")"
          ]

  op Edg.eq? : Edg.Edge * Edg.Edge -> Boolean 
  def Edg.eq? = Edg.equalEdge?

  op Edg.equalEdge? : Edg.Edge * Edg.Edge -> Boolean 
  def Edg.equalEdge? (e1,e2) =
    case (e1,e2) of
      | (Nat n1, Nat n2) -> n1 = n2
      | (Triple (e1,s1,t1), Triple (e2,s2,t2)) -> equalEdge? (e1,e2) & equalSubst? (s1,s2) & equalSubst? (t1,t2)

  def Edg.show edge = ppFormat (pp edge)

  op mkNatEdge : Nat -> Edg.Edge
  def mkNatEdge n = Nat n

  op newEdge : CompCtxt -> Env (Edg.Edge * CompCtxt)
  def newEdge ctxt =
    return (mkNatEdge (graphCounter ctxt),
      ctxt withGraphCounter ((graphCounter ctxt) + 1))
\end{spec}

\begin{spec}
  op connectVertices : CompCtxt -> Vrtx.Vertex -> Vrtx.Vertex -> ModeSpec -> OpRefSet.Set -> Env CompCtxt
  def connectVertices ctxt first last spc changedVars = {
    (newEdge,ctxt) <- newEdge ctxt; 
    transSpec <- return (TransSpec.make spc changedVars);
    elabTransSpec <- elaborate transSpec;
    bSpec <- return (addTrans (bSpec ctxt) first last newEdge
       (modeSpec elabTransSpec)
       (forwMorph elabTransSpec)
       (backMorph elabTransSpec));
    return (ctxt withBSpec bSpec)
  }
\end{spec}

do we rename before or after type checking. before .. otherwise it simply
won't type check

we carry a set of op names that are currently in scope.
we look at a procedure. if the argument matches something in scope,
we create a new name from the old name and
apply the substitution to the name and all free occurrences of it.
add the (now corrected parameters to the set of names in scope and
the recursively visit the inner scopes.

All of this crap is because we do a naive compilation into a diagram
Better to get there by PE .. compiler should name things apart.
Or should happen at runtime as in a compiler.

This nonsense will mean that if we declare the same variable at the same
level, it will be renamed the second time.

# we don't check for clashes between procedure names, vars etc.

\begin{spec}
   sort NamePair = String * String
 
   sort XSubst = List (NamePair * NamePair)
   op XSubst.pp : XSubst -> Doc
   def XSubst.pp subst =
     ppConcat [
       ppString "[",
       ppSep (ppString ",") (map (fn ((d1,d2),(c1,c2)) -> 
            ppString (d1 ^ "." ^ d2 ^ "+->" ^ c1 ^ "." ^ c2)) subst),
       ppString "]"
     ]

   op XSubst.show : XSubst -> String
   def XSubst.show subst = ppFormat (pp subst)

   op qidToNamePair : QualifiedId -> NamePair
   def qidToNamePair (Qualified qid) = qid

   op stringToNamePair : String -> NamePair
   def stringToNamePair str = ("<unqualified>",str)  % hack

   op lookup : fa(a,b) List (a * b) -> a -> Option b 
   def lookup subst key =
     case subst of
       | [] -> None
       | (x,y) :: rest -> 
           if key = x then
             Some y
           else
             lookup rest key

   op applySubstToQid : XSubst -> QualifiedId -> QualifiedId
   def applySubstToQid subst (qualId as (Qualified qid)) =
     case lookup subst qid of
       | None -> qualId
       | Some newQid -> Qualified newQid

   op applySubstToString : XSubst -> String -> String
   def applySubstToString subst str = 
     case lookup subst (UnQualified,str) of
       | None -> str
       | Some (_,newStr) -> newStr

   op applySubstToVar : XSubst -> ATerm Position -> ATerm Position
   def applySubstToVar subst (var as (Var ((name,srt),pos))) = 
     case lookup subst (UnQualified,name) of
       | None -> var
       | Some (_,newStr) -> (Var ((newStr,srt),pos))

   op applySubstToPair : XSubst -> NamePair -> NamePair
   def applySubstToPair subst pair = 
     case lookup subst pair of
       | None -> pair
       | Some newPair -> newPair

   import PS qualifying /Library/Structures/Data/Sets/Finite/Polymorphic/AsLists

   sort NameSet = PS.Set NamePair

   op NameSet.pp : NameSet -> Doc
   def NameSet.pp nameSet =
      ppConcat [
        ppString "{",
        ppSep (ppString ",") (map (fn (n1,n2) -> ppString (n1 ^ "." ^ n2)) nameSet),
        ppString "}"
      ]

   op NameSet.show : NameSet -> String
   def NameSet.show nameSet = ppFormat (pp nameSet)
   
   op renameElems :  List (OscarSpecElem Position) -> List (OscarSpecElem Position)
   def renameElems elems =
     let (newElems,usedNames,subst) = renameSpecElems elems PS.empty [] in
     newElems

   op renameSpecElems : List (OscarSpecElem Position) -> NameSet -> XSubst -> (List (OscarSpecElem Position)) * NameSet * XSubst
   def renameSpecElems specElems usedNames subst =
     let 
       def takeName ((decl,x),usedNames) =
         case decl of
           | Import spcTerm -> usedNames
           | Sort ([qid],_) -> usedNames
           | Op ([qid],_) -> PS.insert (usedNames, qidToNamePair qid)
           | Var ([qid],_) -> PS.insert (usedNames, qidToNamePair qid)
           | Def ([qid],_) -> PS.insert (usedNames, qidToNamePair qid)
           | Claim claim -> usedNames
           | Proc (name,{formalArgs,returnSort,command}) -> PS.insert (usedNames, stringToNamePair name)
           | _ -> usedNames
       def renameDecl usedNames subst (decl,x) =
         let newDecl = case decl of
           | Sort ([qid],_) -> decl
           | Op ([qid],(fxty,schemes,[])) ->
                let newQid = applySubstToQid subst qid in
                  Op ([newQid],(fxty,schemes,[]))
           | Op ([qid],(fxty,schemes,[(tyVars,term)])) ->
                let newQid = applySubstToQid subst qid in
                let newTerm = renameTerm usedNames subst term in
                  Op ([newQid],(fxty,schemes,[(tyVars,newTerm)]))
           | Var ([qid],(fxty,schemes,[])) ->
                let newQid = applySubstToQid subst qid in
                  Var ([newQid],(fxty,schemes,[]))
           | Var ([qid],(fxty,schemes,[(tyVars,term)])) ->
                let newQid = applySubstToQid subst qid in
                let newTerm = renameTerm usedNames subst term in
                  Var ([newQid],(fxty,schemes,[(tyVars,newTerm)]))
           | Def ([qid],(fxty,schemes,[(tyVars,term)])) ->
                let newQid = applySubstToQid subst qid in
                let newTerm = renameTerm usedNames subst term in
                  Def ([newQid],(fxty,schemes,[(tyVars,newTerm)]))
           | Claim (type,name,tyVars,term) ->
                let newTerm = renameTerm usedNames subst term in
                  Claim (type,name,tyVars,newTerm)
           | Proc (name,procInfo) -> 
               let newName = applySubstToString subst name in
               let newProcInfo = renameProcInfo usedNames subst procInfo in
                 Proc (newName,newProcInfo)
           | Import _ -> decl
         in
           (newDecl,x)
     in
       let boundNames = List.foldl takeName PS.empty specElems in
       %  let _ = toScreen ("renameSpecElem: boundNames = " ^ (show boundNames) ^ "\n") in
       %  let _ = toScreen ("renameSpecElem: usedNames = " ^ (show usedNames) ^ "\n") in
       let conflicts = PS.intersect (boundNames,usedNames) in
       %  let _ = toScreen ("renameSpecElem: conflicts = " ^ (show conflicts) ^ "\n") in
       let (newUsedNames,newSubst) = List.foldl newProgVar (usedNames,subst) conflicts in
       let newBoundNames = map (applySubstToPair newSubst) boundNames in
       let newUsedNames = PS.union (usedNames,newBoundNames) in
       %  let _ = toScreen ("renameSpecElem: newSubst (after) = " ^ (show newSubst) ^ "\n") in
       %  let _ = toScreen ("renameSpecElem: newUsedNames (after) = " ^ (show newUsedNames) ^ "\n") in
       let newDecls = map (renameDecl newUsedNames newSubst) specElems in
         (newDecls,newUsedNames,newSubst)

  op renameProcInfo : NameSet -> XSubst -> ProcInfo Position -> ProcInfo Position
  def renameProcInfo usedNames subst {formalArgs,returnSort,command} =
    let boundNames = List.foldl (fn ((x,_),s) -> PS.insert (s, stringToNamePair x)) PS.empty formalArgs in
    let conflicts = PS.intersect (boundNames,usedNames) in
    %   let _ = toScreen ("renameProcInfo: conflicts = " ^ (show conflicts) ^ "\n") in
    let (newUsedNames,newSubst) = List.foldl newProgVar (usedNames,subst) conflicts in
    %   let _ = toScreen ("renameProcInfo: newSubst (after) = " ^ (show newSubst) ^ "\n") in
    %   let _ = toScreen ("renameProcInfo: newUsedNames (after) = " ^ (show newUsedNames) ^ "\n") in
    let newBoundNames = map (applySubstToPair newSubst) boundNames in
    let newUsedNames = PS.union (usedNames,newBoundNames) in
    let newFormalArgs = map (fn (id,srt) -> (applySubstToString newSubst id,srt)) formalArgs in
    let newCommand = renameCommand newUsedNames newSubst command in
      {formalArgs=newFormalArgs,returnSort=returnSort,command=newCommand}

  op renameAlt : NameSet -> XSubst -> Alternative Position -> Alternative Position
  def renameAlt usedNames subst ((term,command),position) =
    ((renameTerm usedNames subst term, renameCommand usedNames subst command), position)

  op renameCommand : NameSet -> XSubst -> Command Position -> Command Position
  def renameCommand usedNames subst (command,x) =
    case command of
      | If alts -> (If (map (renameAlt usedNames subst) alts),x)
      | Do alts -> (Do (map (renameAlt usedNames subst) alts),x)
      | Assign (lhs,rhs) -> (Assign (renameTerm usedNames subst lhs, renameTerm usedNames subst rhs),x)
      | Let (decls,body) ->
         let (newDecls,newUsedNames,newSubst) = renameSpecElems decls usedNames subst in
         let newBody = renameCommand newUsedNames newSubst body in
           (Let (newDecls,newBody),x)
      | Seq commands -> (Seq (map (renameCommand usedNames subst) commands),x)
      | Relation term -> (Relation (renameTerm usedNames subst term),x)
      | Exec term -> (Exec (renameTerm usedNames subst term),x)
      | Return (Some term) -> (Return (Some (renameTerm usedNames subst term)),x)
      | Return None -> (Return None,x)
      | Continue -> (Continue,x)
      | Break -> (Break,x)
      | Skip -> (Skip,x)
      | Case t -> (Case t,x)

  op newProgVar : NamePair * (NameSet * XSubst) -> (NameSet * XSubst)
  def newProgVar (name0 as (qual,id),(usedNames,subst)) = 
     let
        def loop (counter, name) = 
            if PS.member? (usedNames, name)
                then loop(counter + 1, (qual, id ^ (Nat.toString counter)))
            else name
        in
     let newName = loop(0,name0) in
       (PS.insert (usedNames, newName), cons ((name0,newName),subst))

 op renameTerm : NameSet -> XSubst -> ATerm Position -> ATerm Position
 def renameTerm usedNames subst term =
   let
     def sub (M:MS.Term):MS.Term = 
       case M of
         | Var ((id,srt),a) ->
             if PS.member? (usedNames, stringToNamePair id) then
               Var ((applySubstToString subst id,srt),a)
             else
               term
         | ApplyN (terms,a) -> ApplyN (map sub terms, a) 
         | Apply (M1,M2,a) -> Apply (sub M1,sub M2, a) 
         | Record (fields,a) -> Record (map (fn(f,M)-> (f,sub M)) fields, a)
         | Fun (OneName (id,fixity),srt,pos) -> Fun (OneName (applySubstToString subst id,fixity),srt,pos)
         | Fun (TwoNames (id1,id2,fixity),srt,pos) ->
             let (newId1,newId2) = applySubstToPair subst (id1,id2) in
               Fun (TwoNames (newId1,newId2,fixity),srt,pos)
         | Fun _ -> M 
         | Lambda (rules,a) -> Lambda (map (renameRule usedNames) rules, a)
         | Let (decls,M,a) -> 
             let newDecls = map (fn (pat,M) -> (pat,sub M)) decls in
             let newUsedNames = List.foldl (fn ((pat,m),usedNames) -> removePatternVars pat usedNames) usedNames decls in
               Let (newDecls, renameTerm newUsedNames subst M,a)
         | LetRec (decls,M,a) -> 
             let newUsedNames = List.foldl (fn (((name,srt),term),usedNames) -> PS.delete (usedNames,(UnQualified,name))) usedNames decls in
             let newDecls = map (fn (name,term) -> (name,renameTerm newUsedNames subst term)) decls in
               LetRec (newDecls, renameTerm newUsedNames subst M, a)
         | Bind (b,vars,M,a) -> Bind (b, vars, sub M, a)
         | IfThenElse (t1,t2,t3,a) -> IfThenElse (sub t1, sub t2, sub t3, a)
         | Seq (terms,a) -> Seq (map sub terms, a)
         | SortedTerm (term,srt,a) -> SortedTerm (sub term, srt, a)

     def renameRule usedNames (pat,cond,term) = 
          let newUsedNames = removePatternVars pat usedNames in
          let newCond = renameTerm newUsedNames subst cond in
          let newTerm = renameTerm newUsedNames subst term in
          (pat,newCond,newTerm)
   in
     sub term

 op removePatternVars : APattern Position -> NameSet -> NameSet
 def removePatternVars pat usedNames = 
   case pat of
     | VarPat ((v,srt),a) -> PS.delete (usedNames, (UnQualified,v))
     | RecordPat (fields,a) -> 
        foldl (fn ((name,pat),usedNames) -> removePatternVars pat usedNames) usedNames fields
     | EmbedPat(oper,Some pat,srt,a) -> removePatternVars pat usedNames
     | EmbedPat(oper,None,srt,_) -> usedNames
     | AliasPat(p1,p2,a) ->
        let newUsedNames = removePatternVars p1 usedNames in
          removePatternVars p2 newUsedNames
     | QuotientPat(pat,trm,a) -> removePatternVars pat usedNames
     | RelaxPat(pat,trm,a) -> removePatternVars pat usedNames
     | _ -> usedNames
endspec
\end{spec}
