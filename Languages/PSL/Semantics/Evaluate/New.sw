\section{Compilation of Oscar/PSL Procedures into BSpecs}

## There are name conflicts for the product accessors for Procedures, PSpecs and ProcContext
## There are name conflicts for BSpecs and ProcContexts

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../PSpec
  import /Languages/SpecCalculus/Semantics/Evaluate/Signature 
  import /Languages/MetaSlang/Specs/Elaborate/Utilities
  import /Languages/MetaSlang/AbstractSyntax/Fold
  import /Library/Legacy/DataStructures/ListPair
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/Utilities
  import ../Utilities
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec
  import SpecCalc qualifying /Languages/BSpecs/Predicative/Multipointed
  import Utils
\end{spec}

An Oscar spec consists of a collection of "elements". Until object support
is added, these are called "PSpec elements" where the P refers to "procedure".

A procedure definition gives rise to two additions to the context.
The code for the procedure generates a Procedure object that holds,
amongst other things,

The type of a procedure 
from the type of its arguments to its result type. The real type should
be as a predicate relating the input (the values of the arguments and
the value of the variables in scope) and the output (the return value
and the new values of global variables).

As it stands, there is a dynamic spec as part of the pSpec and a dynamic
spec as part of each procedure. Both give the names in scope inside
the procedure.

a PSpecContextElem refers to anything in an Oscar specification that is
not a procedure. This includes vars and ops.

\begin{spec}
  op evaluatePSpecElems  : PSpec -> List (PSpecElem Position) -> SpecCalc.Env (PSpec * TimeStamp * URI_Dependency)
  op evaluatePSpecContextElems : PSpec -> List (PSpecElem Position) -> SpecCalc.Env PSpec

  op evaluatePSpecProcElemPassOne : PSpec -> PSpecElem Position -> SpecCalc.Env PSpec
  def evaluatePSpecProcElemPassOne pSpec (elem,position) =
    case elem of
      | Proc (procName,procInfo) -> {

% We begin by defining the operator to represent the procedure in the static context. This
% op has Proc sort and is used to label those transitions that call the procedure.

          argProd <- return (mkProductAt (map (fn (name,srt) -> srt) procInfo.args) position); 
          tmpSpec <- return (subtractSpec pSpec.dynamicSpec pSpec.staticSpec);
          storeProd <- return (mkProductAt
            (foldriAQualifierMap
               (fn (qual,id,opInfo,recSorts) -> Cons (sortOf (sortScheme opInfo),recSorts)) [] tmpSpec.ops) position);
          procSort <- return (mkBaseAt (unQualified "Proc") [argProd,procInfo.returnSort,storeProd] position); 
          qualProcId as Qualified (procQual,procName) <- return (unQualified procName);
          static <- staticSpec pSpec;
          static <- addOp [qualProcId] Nonfix (tyVarsOf procSort,procSort) [] static position;
          pSpec <- setStaticSpec pSpec static;
          pSpec <-
            case findAQualifierMap (static.ops, procQual, procName) of
              | None -> return pSpec
              | Some info -> {
                    dynamic <- dynamicSpec pSpec;
                    dynamic <- addNonLocalOpInfo dynamic procQual procName info;
                    setDynamicSpec pSpec dynamic
                 };
\end{spec}

We want to construct a placeholder for the procedure. This includes an
almost empty BSpec. The modes of this BSpec must be labelled. We extend
the current dynamic context with operators (variables) for the formal
parameters to the procedure. These are now variables that are in scope.

The vertices of the underlying graph are integers that cast into
MetaSlang terms. We use terms since this helps us later when we do
partial evaluation.  The initial bSpec has states 0 and 1 corresponding
to the initial and final states.

Might be better to make the bSpec an Option and just omit it in the first
pass.

### There may be a problem that the names are added unqualified.

The next two are relevant if we label each transition with
both the static and dynamic specs and we record the deltas
in the construction of both.

## Do we need to carry the static spec around if it can
always be recovered from the dynamic spec? Intuitively
we are carrying around the slice.

          dyCtxt <- return (setLocalOps (pSpec.dynamic, []));
          dyCtxt <- return (setImportedSpec (dyCtxt,pSpec.dynamic));

\begin{spec}
          initialDyCtxt <-
             foldM (fn dCtxt -> fn (argName,argSort) ->
                       addOp [unQualified argName]
                             Nonfix
                             (tyVarsOf argSort,argSort)
                             []
                             dCtxt position)
                         pSpec.dynamicSpec procInfo.args;

 
          (finalDyCtxt,returnInfo : ReturnInfo) <- 
             case procInfo.returnSort of
               | Product ([],_) -> return (initialDyCtxt, None)
               | _ -> {
                     dyCtxt <- addOp [unQualified ("return#" ^ procName)]
                                     Nonfix
                                     (tyVarsOf procInfo.returnSort,procInfo.returnSort)
                                     [] initialDyCtxt position;
                     return (dyCtxt, Some {returnSort=procInfo.returnSort,returnName= ("return#" ^ procName)})
                   };

          initialDyCtxtElab <- elaborateSpec initialDyCtxt; 
          finalDyCtxtElab <- elaborateSpec finalDyCtxt; 

          bSpec <- return (
             let (initialV,finalV) = (mkNatVertexEdge 0, mkNatVertexEdge 1) in
             % let bSpec = addMode (newSystem initialV initialDyCtxtElab) finalV finalDyCtxtElab in
             let bSpec = addMode (newSystem initialV finalDyCtxtElab) finalV finalDyCtxtElab in
             setFinalModes bSpec (V.singleton finalV));
          proc <- return (makeProcedure (map (fn (x,y) -> x) procInfo.args)
                                 returnInfo
                                 pSpec.staticSpec  
                                 pSpec.dynamicSpec
                                 bSpec);
          setProcedures pSpec (PolyMap.update pSpec.procedures (unQualified procName) proc)
        }
      | _ -> return pSpec
\end{spec}

### In the above, the dynamic context always includes the return operator.
In fact it need only appear in the final spec and in the apex of any
transition that ends in the final spec. The point is that
the assign operation isn't quite smart enough.

In the second pass of compiling a procedure we actually compile the command
in the body of the procedure.

We construct an initial ProcContext object against which we will compile
the command defining the procedure.

The procedure context also includes a new entry for the procedure we
are about to compile. This is so that the procedure can be recursive.

### why is the returnInfo in two places .. the ProcContext and the Procedure

The initial and final states here must agree with those used above
when the initial bSpec was constructed. Perhaps they shouldn't be
hard coded.

### A problem here is that the dynamic field in ctxt gets an elaborated
### spec when initialized? This means it will be elaborated again as we
### compile the command for the procedure and assemble the bSpec.

### Procedure (procValue) object has type ReturnInfo but really all
### one needs to keep is the return name.

After compiling the procedure, we replace the procedure entry in the
pSpec computed in the first pass in the pSpec with a new one containing
the full bSpec.

\begin{spec}
  op evaluatePSpecProcElemPassTwo : PSpec -> PSpecElem Position -> SpecCalc.Env PSpec
  def evaluatePSpecProcElemPassTwo pSpec (elem,position) =
    case elem of
      | Proc (procName,procInfo) -> {
           procValue <- return (PolyMap.eval pSpec.procedures (unQualified procName));
           (initialV,finalV) <- return (mkNatVertexEdge 0, mkNatVertexEdge 1);
           ctxt : ProcContext <-
                return {
                  procedures = pSpec.procedures,
                  dynamic = modeSpec procValue.bSpec initialV,
                  static = procValue.staticSpec, % ## This is wrong .. should be from the start state as well
                  graphCounter = 2,  % = finalV + 1
                  varCounter = 0,
                  initialV = initialV,
                  finalV = finalV,
                  exit = finalV,
                  break = None,
                  continue = None,
                  bSpec = procValue.bSpec,
                  returnInfo = procValue.returnInfo
                };
      
           ctxt <- compileCommand ctxt procInfo.command;
           proc <- return (makeProcedure procValue.parameters
                                         procValue.returnInfo
                                         procValue.staticSpec
                                         procValue.dynamicSpec
                                         ctxt.bSpec);
           pSpec <- addProcedure pSpec (unQualified procName) proc;
           return pSpec
         }
      | _ -> return pSpec
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

The argument context is used to generate the specs labeling nodes and
edges. Both the static and the dynamic context should be included. However,
for efficiency reasons, and since there is no integrity checking, we
just use the dynamic context.

Even if bipointed \BSpecs\ have one starting node and a set of ending nodes,
compilation always produces singleton sets of ending nodes. The partial
evaluator may generate sets with more than one node, though: that is the
reason for having a set of ending nodes.

The current version includes in the morphism, only those
things where the map differs from the canonical injection.

The next function should be defined inside the scope of the second
however, Specware does not have let-polymorphism.

This constructs a new Map to be used n a spec morphism. It does so by
converting an association list (which is easy to give as an argument)
into a map (which is also implemented as an association list (duh!)). The
indirection is silly at this point but may help us later when the maps
are not implemented by association lists.

Note that the generated map gives only where the morphism differ from
the identity.  However it checks that everything in the domain is mapped
to something that exists in the codomain, or if it is not mapped, then
the name in the domain appears unchanged in the codomain.

Would prefer if we had a syntax for map comprehensions. It would
make much of the following unnecessary.

\begin{spec}
  op makeMap :
    fa (a) AQualifierMap a
        -> AQualifierMap a
        -> List (QualifiedId * QualifiedId)
        -> SpecCalc.Env (PolyMap.Map (QualifiedId,QualifiedId))
    
  def makeMap domMap codMap modifiers =
    foldOverQualifierMap (fn (domQual,domId,info,newMap) -> 
       case lookup modifiers (Qualified (domQual,domId)) of
         | None ->
             (case findAQualifierMap (codMap,domQual,domId) of
                | None -> raise (SpecError (internalPosition,
                            "no target for " 
                          ^ (printQualifiedId (Qualified (domQual,domId)))))
                | Some _ -> return newMap)
         | Some (codQualId as (Qualified (codQual,codId))) ->
             (case findAQualifierMap (codMap,codQual,codId) of
                | None -> raise (SpecError (internalPosition,
                            "specified target qualified id does not exit: " 
                          ^ (printQualifiedId (Qualified (codQual,codId)))))
                | Some _ -> return (PolyMap.update newMap (Qualified (domQual,domId)) codQualId)))
           emptyMap domMap

  op mkMorph :
       Spec
    -> Spec
    -> List (QualifiedId * QualifiedId)
    -> List (QualifiedId * QualifiedId)
    -> SpecCalc.Env Morphism
  def mkMorph dom cod sortModifiers opModifiers = {
     sortMap <- makeMap dom.sorts cod.sorts sortModifiers;
     opMap <- makeMap dom.ops cod.ops opModifiers;
     return {
        dom = dom,
        cod = cod,
        opMap = opMap,
        sortMap = sortMap
     }
   }
\end{spec}

We compile a command with respect to a procedure context. The context records, amongst
other things, the current static and dynamic specs. These give, respectively, the
constants and variables currently in scope. Also in the context is a so-called BSpec.
This is the flow-graph currently being constructed.

The context also includes the identities of the vertices in the BSpec
to be connected by the command. That is, the endpoints of a command are already
part of the BSpec by the time we compile the command. 

\begin{spec}
  op compileCommand : ProcContext -> Command Position -> SpecCalc.Env ProcContext
  def compileCommand ctxt (cmd,position) =
    case cmd of
\end{spec}

\begin{spec}
      | Seq cmds -> compileSeq ctxt cmds
      | If [] -> raise (SpecError (position, "compileCommand: If: empty list of alternatives"))
      | If alts -> compileAlternatives ctxt alts
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
          saveFinal <- return (finalV ctxt);
          saveBreak <- return (break ctxt);
          saveContinue <- return (continue ctxt);
          ctxt <- return (setBreak ctxt (Some (finalV ctxt)));
          ctxt <- return (setContinue ctxt (Some (initialV ctxt)));
          ctxt <- return (setFinal ctxt (initialV ctxt));
          ctxt <- compileAlternatives ctxt alts; 
          ctxt <- return (setFinal ctxt saveFinal);
          ctxt <- return (setContinue ctxt saveContinue);
          ctxt <- return (setBreak ctxt saveBreak);
          axm <- return (mkNotAt (disjList (map (fn ((guard,term),_) -> guard) alts) position) position);
          apexSpec <- return (addAxiom (("guard", [], axm), dynamic ctxt));
          apexElab <- elaborateSpec apexSpec;
          connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab []
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
                if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                  compileProcCall ctxt (Some trm1) (unQualified id) argTerm position
                else
                  compileAssign ctxt trm1 trm2 position
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,position),argTerm],_) ->
                if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                  compileProcCall ctxt (Some trm1) (Qualified (id1,id2)) argTerm position
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
                  apexSpec <- return (addAxiom (("assign", [], mkTrueAt position),dynamic ctxt)); 
                  apexElab <- elaborateSpec apexSpec; 
                  connectVertices ctxt (initialV ctxt) (exit ctxt) apexElab []
                }
            | (None,Some {returnSort,returnName}) ->
                raise (SpecError (position, "Procedure has return sort " ^ (printSort returnSort) ^ " but no return value"))
            | (Some term, None) ->
                raise (SpecError (position, "Procedure with unit sort returns a value"))
            | (Some term, Some {returnSort,returnName}) -> {
                  lhs <- return (mkFunAt (OneName (returnName,Nonfix)) returnSort position);
                  saveLast <- return (finalV ctxt);
                  ctxt <- return (setFinal ctxt (exit ctxt));
                  ctxt <-
                    case term of
                      | ApplyN ([Fun(OneName(id,fixity),srt,position),argTerm],_) ->
                          if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                            compileProcCall ctxt (Some lhs) (unQualified id) argTerm position
                          else
                            compileAssign ctxt lhs term position
                      | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,position),argTerm],_) ->
                          if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                            compileProcCall ctxt (Some lhs) (Qualified (id1,id2)) argTerm position
                          else
                              compileAssign ctxt lhs term position
                      | _ -> compileAssign ctxt lhs term position;
                  return (setFinal ctxt saveLast)
                })
\end{spec}

\begin{spec}
      | Continue -> 
          (case (continue ctxt) of
             | Some continueVertex -> {
                   apexElab <- elaborateSpec (dynamic ctxt); 
                   connectVertices ctxt (initialV ctxt) continueVertex apexElab []
                 }
             | None ->
                 raise (SpecError (position, "continue appears outside of a loop")))

      | Break ->
          (case (break ctxt) of
             | Some breakVertex -> {
                   apexElab <- elaborateSpec (dynamic ctxt); 
                   connectVertices ctxt (initialV ctxt) breakVertex apexElab []
                 }
             | None ->
                 raise (SpecError (position, "break appears outside of a loop")))
\end{spec}

	  | Exec trm -> compileAxiomStmt pSpec initialV finalV exit bSpec cnt trm
      | Relation trm -> compileAxiomStmt ctxt trm

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
            pSpec <- return {staticSpec = static ctxt, dynamicSpec = dynamic ctxt, procedures = procedures ctxt};
            newPSpec <- evaluatePSpecContextElems pSpec decls;
            saveStatic <- return (static ctxt);
            saveDynamic <- return (dynamic ctxt);
            ctxt <- return (setStatic (setDynamic ctxt newPSpec.dynamicSpec) newPSpec.staticSpec);
            ctxt <- compileCommand ctxt cmd;
            return (setStatic (setDynamic ctxt saveDynamic) saveStatic)
          }
\end{spec}

Compiling a skip is a transition where the maps are identities and
the axiom is just true.

Should really check that the specs at the start and end are the same.
This should be an invariant. Must check.

\begin{spec}
      | Skip -> {
          apexSpec <- return (addAxiom (("assign", [], mkTrueAt position),dynamic ctxt));  % why bother?
          apexElab <- elaborateSpec apexSpec; 
          connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab []
        }
\end{spec}

\begin{spec}
  op compileAssign : ProcContext -> ATerm Position -> ATerm Position -> Position -> SpecCalc.Env ProcContext
  def compileAssign ctxt trm1 trm2 position = {
    (leftId, leftPrimedTerm) <- return (processLHS trm1); 
    apexSpec <- 
       (case findTheOp (dynamic ctxt, leftId) of
          | None ->
             raise (SpecError (position, "compileCommand: Assign: id '"
                          ^ (printQualifiedId leftId) ^ "' is undefined"))
          | Some (names,fixity,sortScheme,optTerm) ->
             addOp [makePrimedId leftId] fixity sortScheme optTerm (dynamic ctxt) position); 
\end{spec}
 
The next clause may seem puzzling. The point is that, from the time
the spec is assigned to the first state until we handle the subsequent
assignment, a new variable may have been created. Introducing the variable
(via a \verb+let+) does not give require a transition.  So by the time
we get here, the dynamic context may have grown beyond what appears
at the initial state. If the operator is absent from the start state,
then it cannot appear on the right side and hence should be discarded
from the spec at the apex. While it may make some sense semantically,
it may lead to a misleading error message at elaboration time. If the
variable just declared appears on the right, then using the code below
gives rise to an error where the operator is undeclared. In fact, the
user has simply used an unitialized variable.  Nevertheless, for the
time being, I've chosen to remove it.

                 let spc = ctxt.dynamic in
                 let mSpec = modeSpec_ms bspec initial in
                 (case StringMap_find (mSpec.ops,leftId) of
                     None -> {name = spc.name,
                              sorts = spc.sorts,
                              ops = StringMap_remove (spc.ops,leftId),
                              properties = spc.properties,
                              imports = spc.imports}
                   | Some _ -> ctxt.dynamic) in
\begin{spec}
          % let apexSpec =
              % addOp_ast((primedId,fixity,(tyVarsOf srt,srt),None),apexSpec) in
    axm <- return (mkEqualityAt leftPrimedTerm trm2 position);
\end{spec}

Here we add the axioms encoding the assignment to the apex spec. Right
now the axiom has no type varibles in the sort scheme. There might
be scope for more polymorphism if we use the \verb+tyVarsOf+ function
that Alessandro wrote below rather than use, as below, an empty list of
type variables.

\begin{spec}
    apexSpec <- return (addAxiom (("assign",[],axm),apexSpec)); 
    apexElab <- elaborateSpec apexSpec; 
    connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab [leftId]
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

### A possible bug here is that the names we return are qualified rather
than OneName TwoNames ... this means that the typechecker will ignore them

\begin{spec}
  op processLHS : ATerm Position -> QualifiedId * (ATerm Position)
  def processLHS term =
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
          | _ -> trm
    in
      case term of
        | Fun (OneName(id,fixity),srt,pos) ->
           (unQualified id, Fun(OneName(id ^ "'",fixity),srt,pos))
        | ApplyN ((Fun (OneName(id,fixity),srt,pos))::args,pos) ->
            let newTerm = secondPass (firstPass (Fun (OneName(id ^ "'",fixity),srt,pos)) args pos) in
            (unQualified id, newTerm)
        % | ApplyN ((Fun (TwoNames(id1,id2,fixity),srt,pos))::args,pos) ->
        %    (Qualified (id1,id2), ApplyN (Cons (Fun(TwoNames(id1,id2 ^ "'",fixity),srt,pos),args),pos))
        % | Fun (TwoNames(id1,id2,fixity),srt,pos) ->
        %    (Qualified(id1,id2), Fun(TwoNames(id1,id2 ^ "'",fixity),srt,pos))
        % | ApplyN ((Fun (Op(id,fixity),srt,pos))::args,pos) ->
        %    (id, ApplyN (Cons (Fun(Op(makePrimedId id,fixity),srt,pos),args),pos))
        % | Fun (Op(id,fixity),srt,pos) -> (id, Fun(Op(makePrimedId id,fixity),srt,pos))
        | _ -> fail "bad lhs"

  op makePrimedId : QualifiedId -> QualifiedId
  def makePrimedId (Qualified (qual,id)) = Qualified (qual,id ^ "'")
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

  op removePrime : QualifiedId -> QualifiedId
  def removePrime (qualId as (Qualified (qual,id))) =
    let chars = rev (explode id) in
    case chars of
      | #'::rest -> Qualified (qual, implode (rev rest))
      | _ -> qualId

        % | Fun (TwoNames(id1,id2,fxty),srt,_) -> hd (rev (explode id2)) = #'
        % | _ -> false

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

  op compileAxiomStmt : ProcContext -> ATerm Position -> Position -> SpecCalc.Env ProcContext

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
     apexSpec <- return (addAxiom (("axiom stmt",[],trm),apexSpec));
     apexElab <- elaborateSpec apexSpec; 
     connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab (map (fn name -> removePrime name) primedNames)
  }
\end{spec}

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
       ProcContext
    -> Option (ATerm Position)
    -> QualifiedId
    -> ATerm Position
    -> Position
    -> SpecCalc.Env ProcContext
\end{spec}

\begin{spec}
  def compileProcCall ctxt trm? procId argTerm position = {
      procOpInfo <-
        (case findTheOp (static ctxt, procId) of
          | None ->
             raise (SpecError (position, "compileProcCall: call to undefined procedure: " ^ (printQualifiedId procId)))
          | Some info -> return info);

      (leftQualId as Qualified(leftQual,leftId), leftPrimedTerm) <-
         return (case trm? of
           | Some trm -> processLHS trm
           % | None -> ("dummy", mkRecord []);
%                  (case procOpInfo of
%                      (_,(_,(Base(_,srts),_)),_) -> 
%                          (mkVar_ast("x___x",hd(tl srts)),hd(tl srts))
%                    | _ -> fail
%                        ("compileProcCall: bad procedure opInfo: " ^ pr))
           | _ -> fail "compileProcCall: result term not a variable"); 
\end{spec}

So a procedure can write to anything in scope when it was declared.
What about local variables that are introduced after the procedure is declared
but before the procedure is called. They must be renamed when they are introduced.
If a variable name appears here and in the dynamic context of the procedure,
then they are the same variable. Moreover we can be certain that the new primed
version of the variable doesn't exist.

#### The bug here is that we want the dynamic spec that does not contain
### the arguments

So what is the rule for names. When we call the procedure, we need to
pass the entire state that is in scope when the procedure is declared.
This is all the local names in the procInfo.dynamicSpec.

# Something funny about the way we retieve the local ops and local op info.

\begin{spec}
      procInfo <- return (eval (procedures ctxt) procId); 
      localDynamicOps <- return (getLocalOps procInfo.dynamicSpec);
      print ("localDynamicOps = " ^ (show " " (map printQualifiedId localDynamicOps)) ^ "\n");
      changedOps <-
        foldOverQualifierMap
           (fn (qual,id,opInfo,opList) ->
               return (if (member (mkQualifiedId (qual,id), localDynamicOps)) then
                         Cons ((qual,id,opInfo),opList)
                       else
                         opList))
           []
           procInfo.dynamicSpec.ops;
      apexSpec <- foldM (fn spc -> fn (qual,id,opInfo) -> addLocalOpInfo spc qual (id ^ "'") opInfo)
                             ctxt.dynamic
                             changedOps;
      oldRec <- return (mkTupleAt 
           (map (fn (qual,id,opInfo) -> mkOp (mkQualifiedId (qual,id), sortOf (sortScheme opInfo))) changedOps) position);
      newRec <- return (mkTupleAt
           (map (fn (qual,id,opInfo) -> mkOp (mkQualifiedId (qual,id ^ "'"), sortOf (sortScheme opInfo))) changedOps) position);
      changedNames <- return (map (fn (qual,id,opInfo) -> mkQualifiedId (qual,id)) changedOps);
      changedNames <-
        return (case trm? of
                  | None -> changedNames
                  | Some _ -> Cons (leftQualId,changedNames));
      print ("changedNames = " ^ (show " " (map printQualifiedId changedNames)) ^ "\n");

      recPair <- return (mkTupleAt [oldRec,newRec] position); 
      totalTuple <- return (mkTupleAt [argTerm,leftPrimedTerm,recPair] position); 
      % procOp <- return (mkOpAt procId sortOf (sortScheme procOpInfo) position);
      procOp <- let procName =
        case procId of
          | Qualified (qual,id) ->
             if qual = UnQualified then
               OneName (id,Nonfix)
             else
               TwoNames (qual,id,Nonfix) in
             return (mkFunAt procName (sortOf (sortScheme procOpInfo)) position);
      axm <- return (mkApplyNAt procOp totalTuple position);
      apexSpec <-
        case trm? of
          | Some trm -> 
              (case findTheOp (dynamic ctxt, leftQualId) of
                 | None ->
                     raise (SpecError (position,
                                      "compileProcCall: id '" ^ (printQualifiedId leftQualId) ^ "' is undefined"))
                 | Some (names,fixity,sortScheme,optTerm) ->
\end{spec}

The point here is that, if the variable was defined in an scope outside
the procedure, then, thanks to the addOp above, it will already exist
in the apexSpec. Hence, before adding we must make sure its not already
there.

\begin{spec}

                       (case findTheOp (apexSpec, makePrimedId leftQualId) of
                          | None -> addLocalOpInfo apexSpec leftQual (leftId ^ "'") (map makePrimedId names,fixity,sortScheme,optTerm)
                          | Some _ -> return apexSpec))
          | None -> return apexSpec; 
      apexSpec <- return (addAxiom (("call", [], axm), apexSpec));
      apexElab <- elaborateSpec apexSpec;
      connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab changedNames
   }
\end{spec}

The following compiles a sequence of commands. For each command
we introduce a new vertex ``between'' the current initial and final
vertices, compile the first command between the initial and new vertices
and compile the rest between the new and final vertex.

\begin{spec}
  op compileSeq : ProcContext -> List (Command Position) -> SpecCalc.Env ProcContext

  def compileSeq ctxt cmds =
    case cmds of
      | [] -> return ctxt
      | [cmd] -> compileCommand ctxt cmd
      | cmd::rest -> {
            (newVertex,ctxt) <- return (newGraphElement ctxt); 
            ctxt <- return (setBSpec ctxt (addMode (bSpec ctxt) newVertex (dynamic ctxt)));
            saveLast <- return (finalV ctxt);
            ctxt <- compileCommand (setFinal ctxt newVertex) cmd;
            compileSeq (setInitial (setFinal ctxt saveLast) newVertex) rest
          }
\end{spec}

sort ReturnInfo = Option {returnName : String, returnSort : PSort}

During compilation we carry around some contex information. This requires some
more thought as not all the compilation functions need all the information.
Perhaps this should be added to the local monadic state. Perhaps the operations
should be monadic.

Some of the state is changed and must be restored as one enters and leaves a context.
The rest changes monotonically.  Perhaps the product should be partitioned
to reflect this and thereby simplify the task of restoring the context.

\begin{spec}

sort ProcContext = {
    procedures : PolyMap.Map (QualifiedId,Procedure),
    dynamic : Spec,
    static : Spec,
    graphCounter : Nat,
    varCounter : Nat,
    initialV : V.Elem,
    finalV : V.Elem,
    exit : V.Elem,
    break : Option V.Elem,
    continue : Option V.Elem,
    bSpec : BSpec,
    returnInfo : ReturnInfo
  }

op procedures : ProcContext -> PolyMap.Map (QualifiedId, Procedure)
def procedures ctxt = ctxt.procedures

op dynamic : ProcContext -> Spec
def dynamic procContext = procContext.dynamic

op static : ProcContext -> Spec
def static procContext = procContext.static

op graphCounter : ProcContext -> Nat
def graphCounter procContext = procContext.graphCounter

% Should really identify V.Elem with E.Elem since in the
% twist they have the same.
% The implementation of this function is naive in the sense that
% it creates and destroys things on the heap more than it should.
op newGraphElement : ProcContext -> (V.Elem * ProcContext)
def newGraphElement procContext =
  (mkNatVertexEdge (graphCounter procContext),
   setGraphCounter procContext ((graphCounter procContext) + 1))

% perhaps we should have just new var and new graph element functions?
op varCounter : ProcContext -> Nat
def varCounter procContext = procContext.varCounter

op initialV : ProcContext -> V.Elem
def initialV procContext = procContext.initialV

op setInitial : ProcContext -> V.Elem -> ProcContext 
op setGraphCounter : ProcContext -> Nat -> ProcContext 
op setFinal : ProcContext -> V.Elem -> ProcContext 
op setExit : ProcContext -> V.Elem -> ProcContext 
op setBreak : ProcContext -> Option V.Elem -> ProcContext 
op setContinue : ProcContext -> Option V.Elem -> ProcContext 
op setBSpec : ProcContext -> BSpec -> ProcContext 
op setReturnInfo : ProcContext -> ReturnInfo -> ProcContext 

op finalV : ProcContext -> V.Elem
def finalV procContext = procContext.finalV

op exit : ProcContext -> V.Elem
def exit procContext = procContext.exit

op break : ProcContext -> Option V.Elem
def break procContext = procContext.break

op continue : ProcContext -> Option V.Elem
def continue procContext = procContext.continue

op bSpec : ProcContext -> BSpec
def bSpec procContext = procContext.bSpec

op returnInfo : ProcContext -> ReturnInfo
def returnInfo procContext = procContext.returnInfo

op setStatic : ProcContext -> Spec -> ProcContext 
op setDynamic : ProcContext -> Spec -> ProcContext 

% op setProcedures : ProcContext -> PolyMap.Map (QualifiedId,Procedure) -> ProcContext 
% def setProcedures procContext procs = {
%     procedures = procs,
%     dynamic = procContext.dynamic,
%     static = procContext.static,
%     graphCounter = procContext.graphCounter,
%     varCounter = procContext.varCounter,
%     initialV = procContext.initialV,
%     finalV = procContext.finalV,
%     exit = procContext.exit,
%     break = procContext.break,
%     continue = procContext.continue,
%     bSpec = procContext.bSpec,
%     returnInfo = procContext.returnInfo
%   }

def setDynamic procContext spc = {
    procedures = procContext.procedures,
    dynamic = spc,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setStatic procContext spc = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = spc,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setFinal procContext vertex = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = vertex,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setBreak procContext optVertex = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = optVertex,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setContinue procContext optVertex = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = optVertex,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setInitial procContext vertex = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = vertex,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
  }

def setBSpec procContext bSpec = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = procContext.graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = bSpec,
    returnInfo = procContext.returnInfo
  }

def setGraphCounter procContext graphCounter = {
    procedures = procContext.procedures,
    dynamic = procContext.dynamic,
    static = procContext.static,
    graphCounter = graphCounter,
    varCounter = procContext.varCounter,
    initialV = procContext.initialV,
    finalV = procContext.finalV,
    exit = procContext.exit,
    break = procContext.break,
    continue = procContext.continue,
    bSpec = procContext.bSpec,
    returnInfo = procContext.returnInfo
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
  op compileAlternatives : ProcContext -> List (Alternative Position) -> SpecCalc.Env ProcContext

  def compileAlternative ctxt ((trm,cmd),pos) = {
      (newVertex,ctxt) <- return (newGraphElement ctxt); 
      bSpec <- return (addMode (bSpec ctxt) newVertex (dynamic ctxt)); 
      ctxt <- return (setBSpec ctxt bSpec);
      apexSpec <- return (addAxiom (("guard",[],trm), dynamic ctxt)); 
      apexElab <- elaborateSpec apexSpec;
      saveFirst <- return (initialV ctxt);
      ctxt <- connectVertices ctxt (initialV ctxt) newVertex apexElab [];
      ctxt <- compileCommand (setInitial ctxt newVertex) cmd;
      return (setInitial ctxt saveFirst)
    }
 
  def compileAlternatives ctxt alts =
    case alts of
      | [alt] -> compileAlternative ctxt alt
      | firstAlt::restAlts -> {
            ctxt <- compileAlternative ctxt firstAlt;
            compileAlternatives ctxt restAlts
          }
\end{spec}

The following function creates a vertex/edge (of sort \verb+Vertex.Elem+
from a natural number. More precisely, it creates a vertex/edge consisting
of the MetaSlang term for that natural number.

\begin{spec}
  op mkNatVertexEdge : Nat -> V.Elem
  def mkNatVertexEdge n = Just (mkNat n)
\end{spec}

Elaborating a spec means, amongst other things, typechecking, resolving
infix operators, detecting constructor in patterns, resolving 
unqualified operators appearing in terms, and other things.

\begin{spec}
  op unQualified : String -> QualifiedId
  def unQualified name = Qualified (UnQualified,name)

  op elaborateSpec : Spec -> SpecCalc.Env Spec
  def elaborateSpec spc =
    case elaboratePosSpec (spc, "internal") of
      | Spec elabSpc -> return (convertPosSpecToSpec elabSpc)
      | Errors errors -> raise (TypeCheckErrors errors)

  op addNonLocalSortInfo : Spec -> Qualifier -> Id -> SortInfo -> SpecCalc.Env Spec
  def addNonLocalSortInfo spc qual id newInfo = {
      mergedInfo <- mergeSortInfo newInfo (findAQualifierMap (spc.sorts,qual,id)) internalPosition;
      return (setSorts (spc, insertAQualifierMap (spc.sorts,qual,id,mergedInfo)))
    }

  op addNonLocalOpInfo : Spec -> Qualifier -> Id -> OpInfo -> SpecCalc.Env Spec
  def addNonLocalOpInfo spc qual id newInfo = {
      mergedInfo <- mergeOpInfo newInfo (findAQualifierMap (spc.ops,qual,id)) internalPosition;
      return (setOps (spc, insertAQualifierMap (spc.ops,qual,id,mergedInfo)))
    }

  op addLocalOpInfo : Spec -> Qualifier -> Id -> OpInfo -> SpecCalc.Env Spec
  def addLocalOpInfo spc qual id newInfo = {
      mergedInfo <- mergeOpInfo newInfo (findAQualifierMap (spc.ops,qual,id)) internalPosition;
      return (addLocalOpName (setOps (spc, insertAQualifierMap (spc.ops,qual,id,mergedInfo)),Qualified (qual,id)))
    }

  op connectVertices : ProcContext -> V.Elem -> V.Elem -> Spec -> List QualifiedId -> SpecCalc.Env ProcContext
  def connectVertices ctxt first last spc changedNames = {
    (newEdge,ctxt) <- return (newGraphElement ctxt); 
    morph1 <- mkMorph (modeSpec (bSpec ctxt) first) spc [] [];
    morph2 <- mkMorph (modeSpec (bSpec ctxt) last) spc [] (map (fn x -> (x, makePrimedId x)) changedNames);
    bSpec <- return (addTrans (bSpec ctxt) first last newEdge spc morph1 morph2);
    return (setBSpec ctxt bSpec)
  }

  op getLocalOps : fa (a) ASpec a -> OpNames
  def getLocalOps {importInfo,sorts,ops,properties} =
    let {imports,importedSpec,localOps,localSorts} = importInfo in localOps

  op getLocalSorts : fa (a) ASpec a -> SortNames
  def getLocalSorts {importInfo,sorts,ops,properties} =
    let {imports,importedSpec,localOps,localSorts} = importInfo in localSorts

  op sortScheme : fa (a) AOpInfo a -> ASortScheme a
  def sortScheme (names,fxty,sortScheme,optTerm) = sortScheme

  op sortOf : fa (a) ASortScheme a -> ASort a
  def sortOf (tyVars,srt) = srt
\end{spec}

The following function is used to extract a list of type variables from
a sort. The list is free of repetitions, \emph{i.e.} all its elements are
distinct. This function does not belong here: it should be part of the
spec for the MetaSlang abstract syntax, but it is ok for now.

\begin{spec}
  op tyVarsOf : PSort -> List TyVar
  def tyVarsOf srt =
    let def tyVarsOfAux (srt:PSort, tvs:TyVars) : TyVars =
      case srt of
        | Arrow (srt1,srt2,_) -> tyVarsOfAux (srt1, tyVarsOfAux (srt2,tvs))
        | Product (idSrts,_) -> foldl tyVarsOfAux tvs (map (fn (x,y) -> y) idSrts)
        | CoProduct (idSrts,_)
                 -> foldl (fn ((id,srt),tvs1) ->
                              case srt of
                                | Some srt -> tyVarsOfAux (srt,tvs1)
                                | None -> tvs1)
                          tvs
                          idSrts
        | Quotient (srt1,_,_) -> tyVarsOfAux (srt1,tvs)
        | Subsort (srt1,_,_) -> tyVarsOfAux (srt1,tvs)
        | Base (_,srts,_) -> foldl tyVarsOfAux tvs srts
%        | PBase (_,srts,_) -> foldl tyVarsOfAux tvs srts
        | TyVar (tv,_) -> if member (tv,tvs) then tvs else List.insert (tv,tvs)
        | MetaTyVar _ -> tvs
    in
      tyVarsOfAux (srt,[])
\end{spec}

The next is a local hack. The point is that the user wants a convenient
way to have an association list without defining all the maps and whatnot.

Perhaps we should have a simple spec for association lists.

\begin{spec}
  op lookup : List (QualifiedId * QualifiedId) -> QualifiedId -> Option QualifiedId
  def lookup l id =
    case l of
      | [] -> None
      | (key,val)::rest ->
          if key = id then
            Some val
          else
            lookup rest id
}
\end{spec}
