\section{Compilation of PSL Procedures into BSpecs}

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

  op sortScheme : fa (a) AOpInfo a -> ASortScheme a
  def sortScheme (names,fxty,sortScheme,optTerm) = sortScheme

  op sortOf : fa (a) ASortScheme a -> ASort a
  def sortOf (tyVars,srt) = srt
\end{spec}

It is called to process the "procedure elements" found in an
Oscar specification. It compiles the procedure defined in the element.

Note that it incorrectly gives the type of a procedure as a function
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

          argProd <- return (mkProduct (map (fn (name,srt) -> srt) procInfo.args)); 
          tmpSpec <- return (subtractSpec pSpec.dynamicSpec pSpec.staticSpec);
          storeRec <- return (mkProduct_local
            (foldriAQualifierMap
               (fn (qual,id,opInfo,recSorts) ->
                   if qual = UnQualified then
                     Cons ((id,sortOf (sortScheme opInfo)),recSorts)
                   else
                     Cons ((qual ^ "_" ^ id,sortOf (sortScheme opInfo)),recSorts))
                        [] tmpSpec.ops));
          % let procSort = mkBase(unQualified "Proc",[argProd,procInfo.returnSort,storeRec]) in 
          procSort <- return (mkArrow (argProd,procInfo.returnSort));
          % static <- staticSpec pSpec;
          % static <- addOp [unQualified procName] Nonfix (tyVarsOf procSort,procSort) None static (Internal "evaluatePSpecProcElem");
          % pSpec <- setStaticSpec pSpec static;
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
          dyCtxt <-
             foldM (fn dCtxt -> fn (argName,argSort) ->
                       addOp [unQualified argName]
                             Nonfix
                             (tyVarsOf argSort,argSort)
                             []
                             dCtxt (Internal "evaluatePSpecProcElem"))
                         pSpec.dynamicSpec procInfo.args;

 
          (dyCtxt,returnInfo : ReturnInfo) <- 
             case procInfo.returnSort of
               | Product ([],_) -> return (dyCtxt, None)
               | _ -> {
                     dyCtxt <- addOp [unQualified ("return_" ^ procName)]
                                     Nonfix
                                     (tyVarsOf procInfo.returnSort,procInfo.returnSort)
                                     [] dyCtxt internalPosition;
                     return (dyCtxt, Some {returnSort=procInfo.returnSort,returnName= ("return_" ^ procName)})
                   };

          dyCtxtElab <- elaborateSpec dyCtxt; 

          bSpec <- return (
             let (initialV,finalV) = (mkNatVertexEdge 0, mkNatVertexEdge 1) in
             let bSpec = addMode (newSystem initialV dyCtxtElab) finalV dyCtxtElab in
             setFinalModes bSpec (V.singleton finalV));
          proc <- return (makeProcedure (map (fn (x,y) -> x) procInfo.args)
                                 returnInfo
                                 pSpec.staticSpec
                                 dyCtxtElab
                                 bSpec);
          setProcedures pSpec (PolyMap.update pSpec.procedures (unQualified procName) proc)
        }
      | _ -> return pSpec
\end{spec}

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
            ctxt : ProcContext <-
                return {
                  procedures = pSpec.procedures,
                  dynamic = procValue.dynamicSpec,
                  static = procValue.staticSpec,
                  graphCounter = 2,  % = finalV + 1
                  varCounter = 0,
                  initialV = mkNatVertexEdge 0,
                  finalV = mkNatVertexEdge 1,
                  exit = mkNatVertexEdge 1,
                  break = None,
                  continue = None,
                  bSpec = procValue.code,
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
\end{spec}

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

  % sort BSpecs.Morphism = SpecCat.Morphism  %% Why do we need this?

  op compileCommand : 
        ProcContext
     -> Command Position
     -> SpecCalc.Env ProcContext

  def compileCommand ctxt (cmd,pos) =
    case cmd of
\end{spec}

Compiling a sequence of commands means compiling the individual commands
and gluing the end of one onto the start of next. We assume that the list of
commands is not empty.

problem here... how does the static context get updated with the new
procedures? And how do we accumulate the procedures? Probably ok ..
the other procedures are not in scope?

\begin{spec}
      | Seq cmds -> compileSeq ctxt cmds
\end{spec}

The compilation of an \verb+if+ consist of first compiling the
list of alternatives, then adding identity transitions out of the end of
each alternative into a common (new) vertex. Note that the compilation of
the list of alternatives results in the compilation of the commands for all
the alternatives, with transitions out of a common starting node into each
alternative: these transitions are labeled by the respective guards.

\begin{spec}
      | If [] -> raise (SpecError (pos, "compileCommand: If: empty list of alternatives"))
      | If alts -> compileAlternatives ctxt alts
\end{spec}

To compile a loop, we first compile the alternatives. Then we add identity
transitions from the ending vertices of the \BSpecs\ for the alternatives
to the starting node of the returned system (from which there are
transitions to all the commands of the alternatives, guarded by the guards
of the alternatives). In addition, we create a transition from the starting
vertex out to a newly created vertex, which becomes the ending vertex of
the \BSpec\ for the \verb+if+ command. This transition is the exit
transition for the loop, so it is labeled by the conjunction of the
negations of all the guards of the alternatives.

When we create the axiom, we give it an empty list of type variables
under the assumption that they are never used. Needs thought.

\begin{spec}
      | Do [] -> fail "compileCommand: Do: empty list of alternatives"
      | Do alts -> {
          saveLast <- return (finalV ctxt);
          ctxt <- compileAlternatives (setFinal ctxt (initialV ctxt)) alts; 
          ctxt <- return (setFinal ctxt saveLast);
          axm <- return (mkNot (disjList (map (fn ((guard,term),_) -> guard) alts)));
          apexSpec <- return (addAxiom (("guard", [], axm), dynamic ctxt));
          apexElab <- elaborateSpec apexSpec;
          connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab []
        }
\end{spec}

An assignment command maps to a \BSpec\ with a single transition. The
start and end states of the transition are labeled with a copy of the
dynamic context; as mentioned above, each should import a copy of the
static context.

The tricky bit is to construct the spec for the assignment and the
morphism in the opspan. The point is that the variables not appearing
on the left side of the assignment do not change and the issue is how
to express this. Also we must bear in mind that the left side of the
assignment may be a functional term where, essentially, one is updating
a map.

There are a few ways to do this.  
Assume we have an assignment \verb+f(x) := t+ in a dynamic context
consisting of \verb+f : X -> T +,
\verb+x : X +, \verb+g : Y -> Z+, and \verb+z : Z+.

\begin{itemize}
\item In the first case, the spec at the apex of the opspan imports a
copy of the spec at the start and a copy of the spec at the end of the
transition. To avoid name clashes, all the ops from the destination are
``primed''. The opspan morphisms to the apex are the obvious imports. Then
we add the following formula at the apex:
\begin{verbatim}
  axiom f'(x) = t
    & x' = x
    & g' = g
    & z' = z
    & fa x' : X . x' != x => (f' x) = (f x)
\end{verbatim}

\item The second approach is like the above. In this case the signature
of the spec for the transition (at the apex) is the spec at the start
of the transiton plus primed versions of those operators that change. In
this case only \verb+f'+ is added. The axiom at the apex deals only with
those variables that change. Thus it would contain only the first and
last conjuncts from the above. 

\item The final approach would be to use either of the above
but rather than \verb+fa+, to fold a conjunction over the clause to right
of the \verb+fa+ operation over the domain of the map \verb+f+ 
\end{itemize}

We choose the second approach.

\begin{spec}
      | Assign (trm1,trm2) ->
          (case trm2 of
            | ApplyN ([Fun(OneName(id,fixity),srt,_),Record (args,_)],_) ->
                % print "Assign: OneName found (with record args)";
                if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                  compileProcCall ctxt (Some trm1) (unQualified id) (map (fn (x,y) -> y) args)
                else
                  compileAssign ctxt trm1 trm2
            | ApplyN ([Fun(OneName(id,fixity),srt,pos),arg],_) ->
                % print "Assign: OneName found (unary arg)";
                if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                  compileProcCall ctxt (Some trm1) (unQualified id) [arg]
                else
                  compileAssign ctxt trm1 trm2
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,_),Record (args,_)],_) ->
                % print "Assign: TwoNames found (with record args)";
                if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                  compileProcCall ctxt (Some trm1) (Qualified (id1,id2)) (map (fn (x,y) -> y) args)
                else
                  compileAssign ctxt trm1 trm2
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,pos),arg],_) ->
                % print "Assign: TwoNames found (unary arg)";
                if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                  compileProcCall ctxt (Some trm1) (Qualified (id1,id2)) [arg]
                else
                  compileAssign ctxt trm1 trm2
            | _ ->
                compileAssign ctxt trm1 trm2)
\end{spec}

What would be an abstract operation for constructing a transition
should hide the creation of the edge and labelling of the edge
connect ctxt start end formula frame

or maybe a collection of functions

one for guards
one for assignments

\begin{spec}
      | Return optTerm ->
          (case (optTerm,returnInfo ctxt) of
            | (None,None) -> {
                  apexSpec <- return (addAxiom (("assign", [], mkTrue ()),dynamic ctxt));  % why bother?
                  apexElab <- elaborateSpec apexSpec; 
                  connectVertices ctxt (initialV ctxt) (exit ctxt) apexElab []
                }
            | (None,Some {returnSort,returnName}) ->
                raise (SpecError (pos, "Procedure has return sort " ^ (printSort returnSort) ^ " but no return value"))
            | (Some term, None) ->
                raise (SpecError (pos, "Procedure with unit sort returns a value"))
            | (Some term, Some {returnSort,returnName}) -> {
                  lhs <- return (Fun (OneName(returnName,Nonfix),returnSort,internalPosition));
                  saveLast <- return (finalV ctxt);
                  ctxt <- return (setFinal ctxt (exit ctxt));
                  ctxt <-
                    case term of
                      | ApplyN ([Fun(OneName(id,fixity),srt,_),Record (args,_)],_) ->
                          % print "Assign: OneName found (with record args)";
                          if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                            compileProcCall ctxt (Some lhs) (unQualified id) (map (fn (x,y) -> y) args)
                          else
                            compileAssign ctxt lhs term
                      | ApplyN ([Fun(OneName(id,fixity),srt,pos),arg],_) ->
                          % print "Assign: OneName found (unary arg)";
                          if ~((PolyMap.evalPartial (procedures ctxt) (unQualified id)) = None) then
                            compileProcCall ctxt (Some lhs) (unQualified id) [arg]
                          else
                            compileAssign ctxt lhs term
                      | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,_),Record (args,_)],_) ->
                          % print "Assign: TwoNames found (with record args)";
                          if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                            compileProcCall ctxt (Some lhs) (Qualified (id1,id2)) (map (fn (x,y) -> y) args)
                          else
                            compileAssign ctxt lhs term
                      | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,pos),arg],_) ->
                          % print "Assign: TwoNames found (unary arg)";
                          if ~((PolyMap.evalPartial (procedures ctxt) (Qualified (id1,id2))) = None) then
                            compileProcCall ctxt (Some lhs) (Qualified (id1,id2)) [arg]
                          else
                              compileAssign ctxt lhs term
                      | _ -> compileAssign ctxt lhs term;
                  return (setFinal ctxt saveLast)
                })
\end{spec}

      | Relation trm -> compileAxiomStmt ctxt trm
\begin{spec}
      | Continue -> return ctxt 
      | Break -> return ctxt
\end{spec}

Temporary while we do not need procedure calls.

	  | Exec trm -> compileAxiomStmt pSpec initialV finalV exit bSpec cnt trm

      | Exec trm ->
           (case trm of
             | Apply ((Fun(Op(id::[],fixity),srt),pos)::(Record args,_)::[]) ->
                 if ~((evalPartial_p procs id) = None) then
                   compileProcCall ctxt initialV finalV bspec cnt procs None id
                     (map (fn (x,y) -> y) args)
                 else
                   fail ("compileCommand: procedure "
                       ^ id
                       ^ " has not been declared at position "
                       ^ (printPosition_ast pos))
             | Apply ((Fun(Op(id::[],fixity),srt),pos)::arg::[]) ->
                 if ~((evalPartial_p procs id) = None) then
                   compileProcCall ctxt initialV finalV bspec cnt procs None id [arg]
                 else
                   fail ("compileCommand: procedure "
                       ^ id
                       ^ " has not been declared at position "
                       ^ (printPosition_ast pos))
             | _ ->
                fail ("compileCommand: invalid procedure call at position "
                      ^ (printPosition_ast pos)))
end{spec}

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

begin{spec}
      | AssignCall (trm,pr,args) ->
          compileProcCall ctxt initialV finalV bspec cnt procs (Some trm) pr args
end{spec}

To compile a procedure call whose result is discarded, we create a
one-transition \BSpec\ similar to the one above. The difference is that the
second argument to the operator representing the procedure is an
existentially quantified variable. So, the ``effect'' of the axiom is
simply to relate the new state's variables' values to their old values and
to the arguments passed to the procedure. The name of the existentially
quantified variable is \verb+x+ followed by three underscores followed by
\verb+x+; so, we (reasonably) assume that no other variable has that name.

begin{spec}
      | Call (pr,args) ->
          compileProcCall ctxt initialV finalV bspec cnt procs None pr args
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
          apexSpec <- return (addAxiom (("assign", [], mkTrue ()),dynamic ctxt));  % why bother?
          apexElab <- elaborateSpec apexSpec; 
          connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab []
        }
\end{spec}

\begin{spec}
  op compileAssign : ProcContext -> ATerm Position -> ATerm Position -> SpecCalc.Env ProcContext
  def compileAssign ctxt trm1 trm2 = {
    (leftId, leftPrimedTerm) <- return (processLHS trm1); 
    apexSpec <- 
       (case findTheOp (dynamic ctxt, leftId) of
          | None ->
             raise (SpecError (internalPosition, "compileCommand: Assign: id '"
                          ^ (printQualifiedId leftId) ^ "' is undefined"))
          | Some (names,fixity,sortScheme,optTerm) ->
             addOp [makePrimedId leftId] fixity sortScheme optTerm (dynamic ctxt) (Internal "compileAssign")); 
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
    axm <- return (mkEquality leftPrimedTerm trm2);
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

  op compileAxiomStmt : ProcContext -> ATerm Position -> SpecCalc.Env ProcContext

  def compileAxiomStmt ctxt trm = {
    primedNames <- return (filter isPrimedName? (freeNames trm));
    apexSpec <- foldM (fn spc -> fn qualId ->
      (case findTheOp (dynamic ctxt,removePrime qualId) of
         | None ->
             raise (SpecError (internalPosition, "compileAxiomStmt: unprimed id '"
                          ^ (printQualifiedId (removePrime qualId)) ^ "' is undefined"))
         | Some (names,fixity,sortScheme,optTerm) -> {
                  print ("compileAxiomStmt: " ^ (printQualifiedId qualId) ^ "\n");
                  addOp [qualId] fixity sortScheme optTerm spc (Internal "compileAxiomStmt")})) (dynamic ctxt) primedNames; 
     apexSpec <- return (addAxiom (("axiom stmt",[],trm),apexSpec));
     apexElab <- elaborateSpec apexSpec; 
     connectVertices ctxt (initialV ctxt) (finalV ctxt) apexElab (map (fn name -> removePrime name) primedNames)
  }
\end{spec}

The following function is used to compile a procedure call, whose result
is either assigned or discarded. This function is called by the code of
the two procedure call cases of \verb+compileCommand+. The arguments to
this function are a procedure (name), a list of arguments (which are terms),
and an optional term. If present, the term indicates that the result of the
procedure call must be assigned (to the term itself, which we assume to be
a variable); if not present, that indicates that the returned value is
discarded.

The sort of this function is a nightmare.

The code isn't quite right. It passes a store formed from the names
in the current dynamic context. But it should be the dynamic context
from where the procedure was declared. Some care must be taken
if local variables have shadowed the names when the procedure was
declared. The scheme for handling the store needs thought!

So for the time being, we will assume that the names of the arguments
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

\begin{spec}
  op compileProcCall :
       ProcContext
    -> Option (ATerm Position)
    -> QualifiedId
    -> List (ATerm Position)
    -> SpecCalc.Env ProcContext
\end{spec}

\begin{spec}
  def compileProcCall ctxt trm? procId args = {
      procOpInfo <-
        (case findTheOp (static ctxt, procId) of
          | None ->
             raise (SpecError (internalPosition, "compileProcCall: call to undefined procedure: " ^ (printQualifiedId procId)))
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
      argTuple <- return (mkTuple args); 
      oldRec <- return (mkTuple 
           (map (fn (qual,id,opInfo) -> mkOp (mkQualifiedId (qual,id), sortOf (sortScheme opInfo))) changedOps));
      newRec <- return (mkTuple 
           (map (fn (qual,id,opInfo) -> mkOp (mkQualifiedId (qual,id ^ "'"), sortOf (sortScheme opInfo))) changedOps));
      changedNames <- return (map (fn (qual,id,opInfo) -> mkQualifiedId (qual,id)) changedOps);
      changedNames <-
        return (case trm? of
                  | None -> changedNames
                  | Some _ -> Cons (leftQualId,changedNames));
      print ("changedNames = " ^ (show " " (map printQualifiedId changedNames)) ^ "\n");

      recPair <- return (mkTuple [oldRec,newRec]); 
      totalTuple <- return (mkTuple [argTuple,leftPrimedTerm,recPair]); 
      procOp <- return (mkOp (procId, sortOf (sortScheme procOpInfo)));
      axm <- return (mkApply (procOp,totalTuple));
      apexSpec <-
        case trm? of
          | Some trm -> 
              (case findTheOp (dynamic ctxt, leftQualId) of
                 | None ->
                     raise (SpecError (internalPosition,
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
op setBreak : ProcContext -> V.Elem -> ProcContext 
op setContinue : ProcContext -> V.Elem -> ProcContext 
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
separately. Each has a start state and an end state. We construct a the
system for the collection of alternatives by combining all the separate
alternatives into a single diagram and transitions to the starting nodes
of the alternatives out of a newly introduced starting node. This new starting
node is returned by \verb+compileAlternatives+ (together with the other
results), and it is used by \verb+compileCommand+ (which calls
\verb+compileAlternatives+).

There is something funny about having to save the first point. Perhaps this is the
reponsibility of the caller .. and maybe this argues for separate contexts; one scoped and one monotonic

perhaps addMode and friends shoul act on and return a context rather than a bSpec.

### bSpec badly overloaded here.

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

The following function compiles a list of commands, returning the list of
the corresponding \BSpecs, along with a system consisting of all the
\Bspecs's systems merged together. This function is used to compile all
compound commands: every compound command contains, directly or indirectly,
a list of sub-commands. The \BSpec\ for the super-command is obtained from
the ones for the sub-commands, suitably connected together (differently
for each kind of compound command). Note that the counter for unique node
and edge names is threaded through the following function, and that the
function also returns the procedures declared within the compiled commands.

The following function creates a vertex/edge (of sort \verb+Vertex.Elem+, which
is the same as \verb+Elem_e+) from
a natural number. More precisely, it creates a vertex/edge consisting of
the MetaSlang term for that natural number.

\begin{spec}
  op mkNatVertexEdge : Nat -> V.Elem
  def mkNatVertexEdge n = Just (mkNat n)
\end{spec}

As mentioned before, the partial evaluator may create \BSpecs\ with
multiple final nodes. This is why the \verb+final+ component of a
\BSpec\ is a set of nodes. However, during compilation only \BSpecs\ with
singleton sets of final nodes are generated and manipulated. So, it is
useful to have a function to retrieve the (unique) final nodes of a
\BSpec\ during compilation. Strictly speaking, the function is not
well-defined: its type should be restricted by subsorting. In addition,
the \verb+find+ operation on sets is itself problematic: while it is
well-defined, it is hard to refine it correctly. In any case,
the final code will do the right thing, so for now it is ok.

  op finalVertex : BSpec -> Vertex.Elem
  def finalVertex bspec =
      let Some v = find_p (fn x -> true) bspec.final2 in v

From the point of view of the caller, a procedure is a predicate. 
The predicate symbol is created when the procedure is declared. This
predicate must have a sort and this sort is an instance of the 
\verb+Proc+ sort defined in the base context. Given a collection
of sorts for the arguments, the return value and the store, this
constructs a sort representing an instance of the \verb+Proc+ sort.

begin{spec}
  op procSortInstance : List Sort_ast * Sort_ast * Sort_ast -> Sort_ast
  def procSortInstance (args,rtn,store) =
    mkBase_ast (["Proc"],[mkProduct_ast args,rtn,store])
end{spec}

The next is the companion to the above. This adds an operator
representing a procedure to a given spec. It might be better if the
above function was folded into this one.

begin{spec}
  op addProcOpDecl :
        String            % the name of the procedure
      * PSort        % the type of the proc (from procSortInstance)
      * Spec        % the spec to update
     -> SpecCalc.Env Spec
  def addProcOpDecl (name,srt,spc) =
      addOp (([unQualified name], Nonfix, (tyVarsOf srt, srt), None),spc)
end{spec}

The next function is used by the caller to construct a term
representing a procedure call. We are given a collection of terms
and return a term.

begin{spec}
  op mkProcCallTerm : String % procedure name
        * List Term_ast      % terms representing arguments
        * Term_ast           % identifier to receive return value
        * Term_ast           % old store   - must be a record
        * Term_ast           % indentifiers to receive new store
        -> Term_ast
  def mkProcCallTerm (name,args,rtn,oldStore,newStore) =
    let srt = procSortInstance
      ((map termSort_ast args), termSort_ast rtn, termSort_ast oldStore) in
    mkApply_ast (mkOp_ast ([name],srt),
       mkTuple_ast [mkTuple_ast args, rtn, mkTuple_ast [oldStore,newStore]])
end{spec}

Some convenience functions are omitted from the \verb+ast+ and
\verb+ast_util+ specs which exist in \verb+meta_slang+. The first
defined below has a suffix \verb+local+ to avoid a name clash with
\verb+mkEmbed0+ defined in \verb+ast_types+. Name spaces are a problem
requiring a rethink of the current practice.

\begin{spec}
  % op mkEmbed0_local : Id_ast * Sort_ast -> Term_ast
  % def mkEmbed0_local (id,srt) = (Fun (Embed(id,false),srt), pos0_ast)

  op mkNot : PTerm -> PTerm
  def mkNot trm = mkApplyN (notOp, trm)

  op mkAnd : PTerm * PTerm -> PTerm
  def mkAnd (t1,t2) = mkApplyN (andOp, mkTuple ([t1,t2]))

  op mkOr : PTerm * PTerm -> PTerm
  def mkOr (t1,t2) = mkApplyN (orOp, mkTuple ([t1,t2]))
  
  op disjList : List PTerm -> PTerm
  def disjList l =
    case l of
      | []     -> mkTrue ()
      | [x]    -> x
      | x::rest -> mkOr (x, disjList rest)

  op mkFun : PFun * PSort -> PTerm
  def mkFun (constant, srt) = Fun (constant, srt, internalPosition) 

  op mkInfixOp : QualifiedId * Fixity * PSort -> PTerm
  def mkInfixOp (qid, fixity, srt) = mkFun (Op (qid, fixity), srt)

  op binaryBoolSort : PSort
  def binaryBoolSort = mkArrow (mkProduct([boolPSort, boolPSort]), boolPSort)

  op unaryBoolSort : PSort
  def unaryBoolSort  = mkArrow (boolPSort, boolPSort)

  op notOp : PTerm 
  def notOp = mkOp (Qualified("Boolean", "~" ), unaryBoolSort)

  op andOp : PTerm 
  def andOp = mkInfixOp (Qualified("Boolean", "&" ), Infix(Right,15), binaryBoolSort)

  op orOp : PTerm 
  def orOp = mkInfixOp (Qualified("Boolean", "or"), Infix(Right,14), binaryBoolSort)

  op impliesOp : PTerm 
  def impliesOp = mkInfixOp (Qualified("Boolean", "=>"), Infix(Right,13), binaryBoolSort)

  op iffOp : PTerm 
  def iffOp = mkInfixOp (Qualified("Boolean","<=>"), Infix(Right,12), binaryBoolSort)
\end{spec}

Local functions for constucting product types a record terms. All products
have named fields. These are integers in the case of tuples. MetaSlang
assumes that all the fields are sorted in alphabetical order. A sorting
function follows.

\begin{spec}
  op mkProduct_local : List (String * PSort) -> PSort
  def mkProduct_local l =
   Product (sortList (fn ((x,_),(y,_)) -> x leq y) l, internalPosition)

  op mkRecord_local : List (String * PTerm) -> PTerm
  def mkRecord_local l =
   Record (sortList (fn ((x,_),(y,_)) -> x leq y) l, internalPosition)
\end{spec}

Quicksort a list .. for records .. this is overkill as there are only going
to be a few fields in a record.

\begin{spec}
  op sortList : fa (a) (a * a -> Boolean) -> List a -> List a
  def sortList cmp l =
    let def partitionList x l =
      case l of
         Nil -> (Nil,Nil)
       | hd::tl ->
           let (l1,l2) = partitionList x tl in
            if (cmp (hd,x)) then
              (Cons(hd,l1),l2)
            else
              (l1,Cons(hd,l2)) in
    case l of
        Nil -> Nil
      | hd::tl ->
          let (l1,l2) = partitionList hd tl in
             (sortList cmp l1) ++ [hd] ++ (sortList cmp l2)
\end{spec}

The version of \verb+mkEquals+ in \verb{ast-util} creates an operator from
the string ``='' but this is wrong since the parser converts the symbol
into the constuctor \verb+Equals+ and the typechecker doesn't know about
``=''. I have no idea why it is necessary to have a special constructor
for what is really an infix operator.  When we know the following is
right, it should replace \verb+mkEquals+ in \verb+ast-util+.

\begin{spec}
  op mkEquality : ATerm Position -> ATerm Position -> ATerm Position
  def mkEquality t1 t2 = 
    let srt = freshMetaTyVar internalPosition in
    mkApplyN (Fun(Equals,srt,internalPosition), mkTuple [t1,t2])
\end{spec}

Elaborating a spec means, amongst other things, typechecking, resolving
infix operators, detecting constructor in patterns, resolving 
unqualified operators appearing in terms, and other things.

Elaboration is performed relative to an environment. An environment is a
mapping from spec names to specs.  Unfortunately there are two varieties
of specs arising from two different abstract syntax trees: \verb+ast+
\emp{vs} \verb+meta-slang+. Hence, there are two types of environment. The
top level function, elaborateSpec, takes a \verb+meta-slang+ environment
and an \verb+ast+ spec and yields an \verb+ast+ spec. One then converts
the \verb+ast+ spec into a \verb+meta-slang+ spec and adds it to the
environment. If this sounds slightly odd, it gets worse. The first thing
\verb+elaborateSpec+ does with the \verb+meta-slang+ environment is to
convert it to a list and then into an \verb+ast+ environment.

The following is specific to our purposes. In the compiler we maintain
static and dynamic contexts. These are carried around in the compiler
as \verb+ast+ specs. The rewrite engine operates on \verb+meta-slang+
specs so we must label the bspecs with the same and hence we must elaborate
and convert the \verb+ast+ spec into \verb+meta-slang+ spec. 
The system is labelled only with the dynamic spec but the latter must
be elaborated in a context including the static spec.

The call to \verb+emptyEnv_ms+ retrieves a base environment consisting
of the specs for \verb+Nat+, \verb+Integer+, \emph{etc}.

Second argument is context .. another spec.

\begin{spec}
  op elaborateInContext : Spec -> Spec -> SpecCalc.Env Spec
  def elaborateInContext spc static = {
      staticElab <- elaborateSpec static;
      uri <- pathToRelativeURI "Static";
      spc <- mergeImport (URI uri,internalPosition) staticElab spc internalPosition;
      spcElab <- elaborateSpec spc;
      return spcElab
    }

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
}
\end{spec}
