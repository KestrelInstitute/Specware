\section{Hopelessly Naive Compilation of PSL Procedures into BSpecs}

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

  op evaluatePSpecElems  : PSpec -> List (PSpecElem Position) -> SpecCalc.Env (PSpec * TimeStamp * URI_Dependency)

  op evaluatePSpecProcElem :
           PSpec
        -> PSpecElem Position
        -> SpecCalc.Env PSpec
  def evaluatePSpecProcElem pSpec (elem,position) =
    case elem of
      | Proc (name,procInfo) ->
          let argSorts = map (fn (name,srt) -> srt) procInfo.args in
          let argProd = mkProduct argSorts in
          let resSort = procInfo.returnSort in
          let tmpSpec = subtractSpec pSpec.dynamicSpec pSpec.staticSpec in
          let storeRec = mkProduct_local
            (foldriAQualifierMap
               (fn (qual,id,opInfo,recSorts) ->
                   if qual = UnQualified then
                     Cons ((id,sortOf (sortScheme opInfo)),recSorts)
                   else
                     Cons ((qual ^ "_" ^ id,sortOf (sortScheme opInfo)),recSorts))
                        [] tmpSpec.ops) in
          % let procSort = mkBase(unQualified "Proc",[argProd,resSort,storeRec]) in {
          let procSort = mkArrow (argProd,resSort) in {
             static <- staticSpec pSpec;
             % static <- addOp [unQualified name] Nonfix (tyVarsOf procSort,procSort) None static (Internal "evaluatePSpecProcElem");
             pSpec <- setStaticSpec pSpec static;
             compileProcedure pSpec 0 name procInfo
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

We are likely to need an extra argument for generating unique vertex
and edge identifiers. There may be a win in doing this with a monad.
However, at present, there is no syntactic support for monads.

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

So, we must assume that no other operator starts with \verb+return\_+
(obviously, other procedure's return variables may start with such a
suffix, but the rest of the string will make the strings different, since
by assumptions all procedures have different names). In addition, note that
the code assumes that there is no hiding of variables: variables declared in
a procedure (including its arguments) must be distinct from variables
declared, say, in an enclosing procedure. However, two procedures in separate
``branches'' may indeed have common variable names, because they will be
never mixed in the specs labeling \BSpecs.

\begin{spec}
  op compileProcedure :
       PSpec
    -> Nat
    -> String
    -> ProcInfo Position
    -> SpecCalc.Env PSpec

  def compileProcedure pSpec cnt name {args,returnSort,command} = {
   saveDyCtxt <- dynamicSpec pSpec;
   statCtxt <- staticSpec pSpec;
   dyCtxt <-
      foldM (fn dCtxt -> fn (argName,argSort) ->
          addOp [unQualified argName]
                Nonfix
                (tyVarsOf argSort,argSort)
                []
                dCtxt (Internal "compileProcedure"))
                  saveDyCtxt args;
   dyCtxt <- 
      case returnSort of
        | Product ([],_) -> return dyCtxt 
        | _ -> addOp [unQualified ("return_" ^ name)]
                     Nonfix
                     (tyVarsOf returnSort,returnSort)
                     [] dyCtxt internalPosition;
   pSpec <- setDynamicSpec pSpec dyCtxt;
   dyCtxtElab <- elaborateInContext dyCtxt statCtxt; 
   statCtxtElab <- elaborateSpec statCtxt; 
   first <- return (mkNatVertexEdge cnt); 
   last <- return (mkNatVertexEdge (cnt+1)); 
   bSpec <- return (newSystem first dyCtxtElab);
   bSpec <- return (addMode bSpec last dyCtxtElab);
   bSpec <- return (setFinalModes bSpec (V.singleton last));
   ret : (Option String) <- return (
        case returnSort of
          | Product ([],pos) -> None
          | _ -> Some ("return_" ^ name));
   proc <- return (makeProcedure (map (fn (x,y) -> x) args)
                                 ret
                                 statCtxtElab
                                 dyCtxtElab
                                 bSpec);
   pSpec <- addProcedure pSpec (unQualified name) proc;

% again this is a little ugly .. we want to put the procedure into
% the environment in case the procedure is recursive

   (bSpec,cnt,pSpec) <- compileCommand pSpec first last last bSpec (cnt + 2) command;
   dyCtxt <- dynamicSpec pSpec;
   statCtxt <- staticSpec pSpec;
   dyCtxtElab <- elaborateInContext dyCtxt statCtxt; 
   statCtxtElab <- elaborateSpec statCtxt; 
   proc <- return (makeProcedure (map (fn (x,y) -> x) args)
                                 ret
                                 statCtxtElab
                                 dyCtxtElab
                                 bSpec);
   pSpec <- addProcedure pSpec (unQualified name) proc;
   pSpec <- setDynamicSpec pSpec saveDyCtxt;
   pSpec <- setStaticSpec pSpec statCtxt;
   return pSpec
  }
\end{spec}

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
        PSpec
     -> V.Elem
     -> V.Elem
     -> V.Elem
     -> BSpec
     -> Nat
     -> Command Position
     -> SpecCalc.Env (BSpec * Nat * PSpec)

  def compileCommand pSpec first last retn bSpec cnt (cmd,_) =
    case cmd of
\end{spec}

Compiling a sequence of commands means compiling the individual commands
and gluing the end of one onto the start of next. We assume that the list of
commands is not empty.

problem here... how does the static context get updated with the new
procedures? And how do we accumulate the procedures? Probably ok ..
the other procedures are not in scope?

\begin{spec}
      | Seq cmds -> compileSeq pSpec first last retn bSpec cnt cmds
\end{spec}

The compilation of an \verb+if+ consist of first compiling the
list of alternatives, then adding identity transitions out of the end of
each alternative into a common (new) vertex. Note that the compilation of
the list of alternatives results in the compilation of the commands for all
the alternatives, with transitions out of a common starting node into each
alternative: these transitions are labeled by the respective guards.

\begin{spec}
      | If [] -> fail "compileCommand: If: empty list of alternatives"
      | If alts -> compileAlternatives pSpec first last retn bSpec cnt alts
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
          (bSpec,cnt,pSpec) <- compileAlternatives pSpec first first retn bSpec cnt alts; 
          axm <- return (mkNot (disjList (map (fn ((guard,term),_) -> guard) alts)));
          dyCtxt <- dynamicSpec pSpec;
          staticCtxt <- staticSpec pSpec;
          apexSpec <- return (addAxiom (("guard", [], axm), dyCtxt));
          apexElab <- elaborateInContext apexSpec staticCtxt;
          morph1 <- mkMorph (modeSpec bSpec first) apexElab [] [];
          morph2 <- mkMorph (modeSpec bSpec last) apexElab [] [];
          newEdge <- return (mkNatVertexEdge cnt);
          bSpec <- return (addTrans bSpec first last newEdge apexElab morph1 morph2);
          return (bSpec, cnt+1, pSpec)
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
            | ApplyN ([Fun(OneName(id,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Assign: OneName found (with record args)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (unQualified id)) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (unQualified id) (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(OneName(id,fixity),srt,pos),arg],_) -> {
                  % print "Assign: OneName found (unary arg)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (unQualified id)) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (unQualified id) [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Assign: TwoNames found (with record args)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (Qualified (id1,id2))) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (Qualified (id1,id2)) (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,pos),arg],_) -> {
                  % print "Assign: TwoNames found (unary arg)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (Qualified (id1,id2))) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (Qualified (id1,id2)) [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Assign: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,pos),arg],_) -> {
                  % print "Assign: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,pos),arg],_) -> {
                  % print "Assign: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | _ ->
                compileAssign pSpec first last retn bSpec cnt trm1 trm2)
\end{spec}

\begin{spec}
      | Return trm2 ->
          let trm1 =
          (case trm2 of
            | ApplyN ([Fun(OneName(id,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Return: OneName found (with record args)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (unQualified id)) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (unQualified id) (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(OneName(id,fixity),srt,pos),arg],_) -> {
                  % print "Return: OneName found (unary arg)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (unQualified id)) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (unQualified id) [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Return: TwoNames found (with record args)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (Qualified (id1,id2))) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (Qualified (id1,id2)) (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(TwoNames(id1,id2,fixity),srt,pos),arg],_) -> {
                  % print "Return: TwoNames found (unary arg)";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs (Qualified (id1,id2))) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) (Qualified (id1,id2)) [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,_),Record (args,_)],_) -> {
                  % print "Return: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id (map (fn (x,y) -> y) args)
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,pos),arg],_) -> {
                  % print "Return: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | ApplyN ([Fun(Op(id,fixity),srt,pos),arg],_) -> {
                  % print "Return: op found";
                  procs <- procedures pSpec;
                  if ~((PolyMap.evalPartial procs id) = None) then
                    compileProcCall pSpec first last retn bSpec cnt (Some trm1) id [arg]
                  else
                    compileAssign pSpec first last retn bSpec cnt trm1 trm2
                }
            | _ ->
                compileAssign pSpec first last retn bSpec cnt trm1 trm2)
\end{spec}

\begin{spec}
      | Relation trm -> compileAxiomStmt pSpec first last retn bSpec cnt trm
\end{spec}

Temporary while we do not need procedure calls.

\begin{spec}
	  | Exec trm -> compileAxiomStmt pSpec first last retn bSpec cnt trm
\end{spec}

      | Exec trm ->
           (case trm of
             | Apply ((Fun(Op(id::[],fixity),srt),pos)::(Record args,_)::[]) ->
                 if ~((evalPartial_p procs id) = None) then
                   compileProcCall ctxt first last bspec cnt procs None id
                     (map (fn (x,y) -> y) args)
                 else
                   fail ("compileCommand: procedure "
                       ^ id
                       ^ " has not been declared at position "
                       ^ (printPosition_ast pos))
             | Apply ((Fun(Op(id::[],fixity),srt),pos)::arg::[]) ->
                 if ~((evalPartial_p procs id) = None) then
                   compileProcCall ctxt first last bspec cnt procs None id [arg]
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
          compileProcCall ctxt first last bspec cnt procs (Some trm) pr args
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
          compileProcCall ctxt first last bspec cnt procs None pr args
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
            (pSpec,_,_) <- evaluatePSpecElems pSpec decls;
            (bSpec,cnt,procs2) <- compileCommand pSpec first last retn bSpec cnt cmd;
            return (bSpec,cnt,pSpec)
          }
\end{spec}

begin{spec}
      | Case (trm,cases) -> fail "compileCommand: Case: not supported"
end{spec}

Compiling a skip is a transition where the maps are identities and
the axiom is just true.

Should really check that the specs at the start and end are the same.
This should be an invariant. Must check.

\begin{spec}
      | Skip -> {
          dyCtxt <- dynamicSpec pSpec;
          staticCtxt <- staticSpec pSpec;
          apexSpec <- return (addAxiom (("assign", [], mkTrue ()),dyCtxt));  % why bother?
          apexElab <- elaborateInContext apexSpec staticCtxt; 
          morph1 <- mkMorph (modeSpec bSpec first) apexElab [] [];
          morph2 <- mkMorph (modeSpec bSpec last) apexElab [] [];
          newEdge <- return (mkNatVertexEdge cnt); 
          bSpec <- return (addTrans bSpec first last newEdge apexElab morph1 morph2);
          return (bSpec,cnt+1,pSpec)
        }
\end{spec}

\begin{spec}
  op compileAssign :
       PSpec
    -> V.Elem
    -> V.Elem
    -> V.Elem
    -> BSpec
    -> Nat
    -> ATerm Position
    -> ATerm Position
    -> SpecCalc.Env (BSpec * Nat * PSpec)
  def compileAssign pSpec first last retn bSpec cnt trm1 trm2 = {
    (leftId, leftPrimedTerm) <- return (processLHS trm1); 
    dyCtxt <- dynamicSpec pSpec;
    staticCtxt <- staticSpec pSpec;
    apexSpec <- 
       (case findTheOp (dyCtxt,leftId) of
          | None ->
             raise (SpecError (internalPosition, "compileCommand: Assign: id '"
                          ^ (printQualifiedId leftId) ^ "' is undefined"))
          | Some (names,fixity,sortScheme,optTerm) ->
             addOp [makePrimedId leftId] fixity sortScheme optTerm dyCtxt (Internal "compileAssign")); 
\end{spec}
 
The next clause may seem puzzling. The point is that, from the time
the spec is assigned to the first state until we handle the subsequent
assignment, a new variable may have been created. Introducing the variable
(via a \verb+let+) does not give require a transition.  So by the time
we get here, the dynamic context may have grown beyond what appears
at the first state. If the operator is absent from the start state,
then it cannot appear on the right side and hence should be discarded
from the spec at the apex. While it may make some sense semantically,
it may lead to a misleading error message at elaboration time. If the
variable just declared appears on the right, then using the code below
gives rise to an error where the operator is undeclared. In fact, the
user has simply used an unitialized variable.  Nevertheless, for the
time being, I've chosen to remove it.

                 let spc = ctxt.dynamic in
                 let mSpec = modeSpec_ms bspec first in
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
    apexElab <- elaborateInContext apexSpec staticCtxt; 
\end{spec}

The remainder of this case, creates and labels the opspan for the transition.

\begin{spec}
    morph1 <- mkMorph (modeSpec bSpec first) apexElab [] [];
    morph2 <- mkMorph (modeSpec bSpec last) apexElab [] [(leftId,makePrimedId leftId)];
    newEdge <- return (mkNatVertexEdge cnt);
    bSpec <- return (addTrans bSpec first last newEdge apexElab morph1 morph2);
    return (bSpec,cnt+1,pSpec)
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

  op compileAxiomStmt :
       PSpec
    -> V.Elem
    -> V.Elem
    -> V.Elem
    -> BSpec
    -> Nat
    -> ATerm Position
    -> SpecCalc.Env (BSpec * Nat * PSpec)

  def compileAxiomStmt pSpec first last retn bSpec cnt trm = {
    dyCtxt <- dynamicSpec pSpec;
    staticCtxt <- staticSpec pSpec;
    names <- return (freeNames trm);
    primedNames <- return (filter isPrimedName? names);
    apexSpec <- foldM (fn spc -> fn qualId ->
      (case findTheOp (dyCtxt,removePrime qualId) of
         | None ->
             raise (SpecError (internalPosition, "compileAxiomStmt: unprimed id '"
                          ^ (printQualifiedId (removePrime qualId)) ^ "' is undefined"))
         | Some (names,fixity,sortScheme,optTerm) -> {
                  print ("compileAxiomStmt: " ^ (printQualifiedId qualId) ^ "\n");
                  addOp [qualId] fixity sortScheme optTerm spc (Internal "compileAxiomStmt")})) dyCtxt primedNames; 
      apexSpec <- return (addAxiom (("axiom stmt",[],trm),apexSpec));
      apexElab <- elaborateInContext apexSpec staticCtxt; 
      morph1 <- mkMorph (modeSpec bSpec first) apexElab [] [];
      morph2 <- mkMorph (modeSpec bSpec last) apexElab [] (map (fn name -> (removePrime name, name)) primedNames);
      newEdge <- return (mkNatVertexEdge cnt);
      bSpec <- return (addTrans bSpec first last newEdge apexElab morph1 morph2);
      return (bSpec,cnt+1,pSpec)
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
       PSpec
    -> V.Elem
    -> V.Elem
    -> V.Elem
    -> BSpec
    -> Nat
    -> Option (ATerm Position)
    -> QualifiedId
    -> List (ATerm Position)
    -> SpecCalc.Env (BSpec * Nat * PSpec)
\end{spec}

\begin{spec}
  def compileProcCall pSpec first last retn bSpec cnt trm? procId args = {
      statCtxt <- staticSpec pSpec;
      procOpInfo <-
        (case findTheOp (statCtxt,procId) of
          | None ->
             raise (SpecError (internalPosition, "compileProcCall: call to undefined procedure: " ^ (printQualifiedId procId)))
          | Some info -> return info);

      (leftId, leftPrimedTerm) <-
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

\begin{spec}
      procInfo <- return (eval pSpec.procedures procId); 
      declDynCtxt <- return procInfo.dynamicSpec;
      newOps <- foldOverQualifierMap (fn (qual,id,opInfo,map) ->
                  return (insertAQualifierMap (map, qual, id ^ "'", opInfo)))
                             pSpec.dynamicSpec.ops
                             procInfo.dynamicSpec.ops;
      apexSpec <- return (setOps (pSpec.dynamicSpec, newOps));
      argTuple <- return (mkTuple args); 
      oldRec <- return (mkTuple (foldriAQualifierMap (fn (qual,id,opInfo,terms) ->
                             Cons (mkOp (mkQualifiedId (qual,id), sortOf (sortScheme opInfo)),terms))
                             []
                             declDynCtxt.ops));
      newRec <- return (mkTuple (foldriAQualifierMap (fn (qual,id,opInfo,terms) ->
                             Cons (mkOp (mkQualifiedId (qual,id ^ "'"), sortOf (sortScheme opInfo)),terms))
                             []
                             declDynCtxt.ops));
      nameMap <- return (foldriAQualifierMap (fn (qual,id,opInfo,nameMap) ->
                             Cons ((mkQualifiedId (qual,id), mkQualifiedId (qual,id ^ "'")), nameMap))
                             []
                             declDynCtxt.ops);
      nameMap <-
        return (case trm? of
                  | None -> nameMap
                  | Some _ -> Cons ((leftId, makePrimedId leftId), nameMap));

      recPair <- return (mkTuple [oldRec,newRec]); 
      totalTuple <- return (mkTuple [argTuple,leftPrimedTerm,recPair]); 
      procOp <- return (mkOp (procId, sortOf (sortScheme procOpInfo)));
      axm <- return (mkApply (procOp,totalTuple));
      apexSpec <-
        case trm? of
          | Some trm -> 
              (case findTheOp (pSpec.dynamicSpec,leftId) of
                 | None ->
                     raise (SpecError (internalPosition,
                                      "compileProcCall: id '" ^ (printQualifiedId leftId) ^ "' is undefined"))
                 | Some (names,fixity,sortScheme,optTerm) ->
\end{spec}

The point here is that, if the variable was defined in an scope outside
the procedure, then, thanks to the addOp above, it will already exist
in the apexSpec. Hence, before adding we must make sure its not already
there.

\begin{spec}

                       (case findTheOp (apexSpec, makePrimedId leftId) of
                          | None -> addOp [makePrimedId leftId] fixity sortScheme optTerm apexSpec (Internal "compileProcCall")
                          | Some _ -> return apexSpec))
          | None -> return apexSpec; 
      apexSpec <- return (addAxiom (("call", [], axm), apexSpec));
      apexElab <- elaborateInContext apexSpec statCtxt;
      morph1 <- mkMorph (modeSpec bSpec first) apexElab [] [];
      morph2 <- mkMorph (modeSpec bSpec last) apexElab [] nameMap;
      newEdge <- return (mkNatVertexEdge cnt);
      bSpec <- return (addTrans bSpec first last newEdge apexElab morph1 morph2);
      return (bSpec,cnt+1,pSpec)
   }
\end{spec}

\begin{spec}
  op compileSeq :
        PSpec
     -> V.Elem
     -> V.Elem
     -> V.Elem
     -> BSpec
     -> Nat
     -> List (Command Position)
     -> SpecCalc.Env (BSpec * Nat * PSpec)

  def compileSeq pSpec first last retn bSpec cnt cmds =
    case cmds of
      | [] -> return (bSpec,cnt,pSpec)
      | [cmd] -> compileCommand pSpec first last retn bSpec cnt cmd   
      | cmd::rest -> {
            dyCtxt <- dynamicSpec pSpec;
            staticCtxt <- staticSpec pSpec;
            dyElab <- elaborateInContext dyCtxt staticCtxt; 
            newVertex <- return (mkNatVertexEdge cnt); 
            bSpec <- return (addMode bSpec newVertex dyElab);
            (bSpec,cnt,pSpec) <-
              compileCommand pSpec first newVertex retn bSpec (cnt+1) cmd; 
            compileSeq pSpec newVertex last retn bSpec cnt rest
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

\begin{spec}
  op compileAlternatives :
       PSpec
    -> V.Elem
    -> V.Elem
    -> V.Elem
    -> BSpec
    -> Nat
    -> List (Alternative Position)
    -> SpecCalc.Env (BSpec * Nat * PSpec)

  def compileAlternative pSpec first last retn bSpec cnt ((trm,cmd),pos) = {
      dyCtxt <- dynamicSpec pSpec;
      staticCtxt <- staticSpec pSpec;
      dyElab <- elaborateInContext dyCtxt staticCtxt;
      newVertex <- return (mkNatVertexEdge cnt); 
      bSpec <- return (addMode bSpec newVertex dyElab); 
      newEdge <- return (mkNatVertexEdge (cnt + 1)); 
      apexSpec <- return (addAxiom (("guard",[],trm),dyCtxt)); 
      apexElab <- elaborateInContext apexSpec staticCtxt;
      morph1 <- mkMorph (modeSpec bSpec first) apexElab [] []; 
      morph2 <- mkMorph dyElab apexElab [] []; 
      bSpec <- return (addTrans bSpec first newVertex newEdge apexElab morph1 morph2);
      compileCommand pSpec newVertex last retn bSpec (cnt+2) cmd
    }
 
  def compileAlternatives pSpec first last retn bSpec cnt alts =
    case alts of
      | [alt] -> compileAlternative pSpec first last retn bSpec cnt alt
      | firstAlt::restAlts -> {
            (bSpec,cnt,pSpec) <- compileAlternative pSpec first last retn bSpec cnt firstAlt;
            compileAlternatives pSpec first last retn bSpec cnt restAlts
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

The following function creates an identity spec morphism. It certainly
does not belong here, but it is ok for now.

begin{spec}
  op identityMorphism : Spec_ms -> Morphism_ms
  def identityMorphism spc = {
    dom = spc,
    cod = spc,
    sortMap = emptyMap_p,
    opMap = StringMap_foldri
      (fn (opname,opinfo,map) -> update_p map opname opname) emptyMap_p spc.ops
  }
end{spec}

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

The following two functions serve to merge two systems into one. They assume
that the two systems have disjoint shapes and common labeling categories, so
that merging boils down to simple union of vertices, edges, source and target
maps, as well as labeling maps. Obviously, these two functions do not belong
here, but it is ok for now.

begin{spec}
  op mergeSystems : fa(O,A) System(O,A) -> System(O,A) -> System(O,A)
  def mergeSystems sys1 sys2 =
      {shape = mergeSketches sys1.shape sys2.shape,
       functor = {dom = mergeSketches sys1.functor.dom sys2.functor.dom,
                  cod = sys1.functor.cod, % = sys2.functor.cod
                  vertexMap = unionWith_p (fn x -> fn y -> x) % dummy function
                                          sys1.functor.vertexMap
                                          sys2.functor.vertexMap,
                  edgeMap = unionWith_p (fn x -> fn y -> x) % dummy function
                                        sys1.functor.edgeMap
                                        sys2.functor.edgeMap}}

  op mergeSketches : Sketch -> Sketch -> Sketch
  def mergeSketches skt1 skt2 =
      {vertices = union_v skt1.vertices skt2.vertices,
       edges = union_e skt1.edges skt2.edges,
       src = unionWith (fn x -> fn y -> x) % dummy function
                       skt1.src skt2.src,
       target = unionWith (fn x -> fn y -> x) % dummy function
                          skt1.target skt2.target}
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
      | Ok elabSpc -> return (convertPosSpecToSpec elabSpc)
      | Error msg   -> raise  (OldTypeCheck msg)
\end{spec}

    let specs = StringMap_listItems (emptyEnv_ms ()) in
    let static_elab = elaborateSpec_ast (specs,static) in
    let static_ms = toMetaSlang_ast static_elab in
    let dynamic_elab = elaborateSpec_ast (specs @ [static_ms],dynamic) in
     toMetaSlang_ast dynamic_elab

  op elaborateStaticSpec : Spec_ast -> Spec_ms
  def elaborateStaticSpec static =
    let specs = StringMap_listItems (emptyEnv_ms ()) in
    let static_elab = elaborateSpec_ast (specs,static) in
      toMetaSlang_ast static_elab 
\end{spec}


-----

The remainder of the file contains code for handling cases which was
removed and will need to be reintroduced later.

It is convenient to write out a "spec" (as a file) containin everything
that we have accumulated this far before returning the spec constructed
above.

op compileCase : fa(a) Context
     -> Vertex.Elem
     -> Vertex.Elem
     -> BSpec
     -> Nat
     -> PolyMap.Map (String, Procedure)
     -> Case a
     -> BSpec * Nat * PolyMap.Map (String, Procedure)

Compiling a case may be subtle ... may need to elaborate the term
first to see if there are variables that become constructors.

op compileCase 
def compileCase
        let dyCtxt_ms = elaborateInContext ctxt.static ctxt.dynamic in
        let new = mkNatVertexEdge cnt in
        let system = addVertex bspec.system new in
        let system = labelVertex system new dyCtxt_ms in
        let new = mkNatVertexEdge cnt in
    newVert

To compile a \verb+case+, we compile its commands, obtaining the
corresponding \BSpecs. The tricky part is that each command must be compiled
in a slightly different context: precisely, the starting context extended
with the pattern variables of the case. After compiling these commands in
these enlarged contexts, we add an initial node and a final node to the overall
system. There are transitions out of the initial node to the beginning of
each case; these transitions are guarded by the guards of the corresponding
cases. Each of them also includes an axiom equating the term of the
\verb+case+ to the corresponding pattern (which determines the values of the
pattern variables at the end of the transition). There are also transitions
out of the end of each case to the final node of the overall system. We assume
that the pattern variables are distinct from any other variable in the
context. We also assume that there no wilcard variables in patterns.

          let (bspecs,axms,cnt2,procs) =
              foldr (fn (((pat,cond,cmd),_),(bspecs1,axms1,cnt1,procs1)) ->
                        let patvars = patternVariables pat in
                        let newctxt =
                            foldl (fn (pvar,ctxt1) ->
                                      {static = ctxt1.static,
                                       dynamic =
                                       addOp_ast((pvar.1,
                                              Nonfix,
                                               (tyVarsOf pvar.2,pvar.2),
                                               None),
                                             ctxt1.dynamic)})
                                  ctxt
                                  patvars in
                        let (bspec,newcnt,procs) =
                            compileCommand newctxt cnt1 cmd in
                        let axm = patternAxiom trm pat cond in
                        (cons(bspec,bspecs1),
                         cons(axm,axms1),
                         newcnt,
                         unionWith_p (fn x -> fn y -> x) procs1 procs))
                    (nil,nil,cnt,procs)
                    cases in
          let initVertex = mkNatVertexEdge cnt2 in
          let finVertex = mkNatVertexEdge (cnt2 + 1) in
          let spc = ctxt.dynamic in
          let sys = 
              foldr (fn (bspec,sys1) -> mergeSystems sys1 bspec.system)
                    {shape = emptySketch,
                     functor = {dom = emptySketch,
                                cod = specCat_ms,
                                vertexMap = emptyMap_p,
                                edgeMap = emptyMap_p}}
                    bspecs in
          let (finalSystem,cnt3,_) =
              foldl (fn (bspec,(sys1,cnt1,axms1)) ->
                        let edge1 = mkNatVertexEdge cnt1 in
                        let edge2 = mkNatVertexEdge (cnt1 + 1) in
                        let spcApex2 = modeSpec_ms bspec bspec.initial2 in
                        let spcApex1 =
                            addAxiom_ast(("",[],hd axms1),spcApex2) in
                        let m1 = (identityMorphism spc) in
                        let m2 = (identityMorphism spcApex2) in
                        let m11 = {dom = m1.dom,
                                   cod = spcApex1,
                                   sortMap = m1.sortMap,
                                   opMap = m1.opMap} in
                        let m12 = {dom = m2.dom,
                                   cod = spcApex1,
                                   sortMap = m2.sortMap,
                                   opMap = m2.opMap} in
                        let m21 = m2 in
                        let m22 = {dom = m1.dom,
                                   cod = spcApex2,
                                   sortMap = m1.sortMap,
                                   opMap = m1.opMap} in
                        let sys2 = addEdge
                                    (addEdge
                                      sys
                                      edge1
                                      initVertex
                                      bspec.initial2)
                                    edge2
                                    finVertex
                                    (finalVertex bspec) in
                        (labelEdge
                          (labelEdge sys2
                                     edge1
                                     spcApex1
                                     m11
                                     m12)
                          edge2
                          spcApex2
                          m21
                          m22,
                         cnt1 + 2,
                         tl axms1))
                    (sys, cnt2 + 2, axms)
                    bspecs in
          ({initial2 = initVertex,
            final2 = singleton_p finVertex,
            system = finalSystem},
           cnt3,
           procs)

The following function generates an appropriate axiom from a term and a
pattern, as well as a condition. The axiom equates the term to the term
obtained by converting the pattern to a term, where the pattern variables
are converted to operators. Aliasing patterns (\verb+as+) generate multiple
equations.

So, we proceed as follows. First, we extract from a pattern a list of
aliasing-free patterns, by recursively exploring the pattern and separating
the aliases. Next, we convert each obtained pattern to a single term,
and each of these terms is equated with the term given as argument.
These equations are all conjoined together and with the condition
given as argument.

  op patternAxiom : Term_ast -> Pattern_ast -> Term_ast -> Term_ast
  def patternAxiom trm pat cond =
%       let pats = removeAliases pat in
%       let trms = map patternToTerm pats in
%       let eqs = map (fn t -> mkEquals_local(trm,t)) trms in
%       foldl mkAnd_ast cond eqs
      mkEquals_local (trm, patternToTerm pat)

%%%  op removeAliases : Pattern_ast -> List Pattern_ast
%%%  def removeAliases (pat,pos) =
%%%      case pat
%%%        of AliasPat(pat1,pat2) ->
%%%           let (pats1,pats2) = (removeAliases pat1,removeAliases pat2) in
%%%           concat(pats1,pats2)
%%%         | EmbedPat(id,pat?,srt) ->
%%%           (case pat? of Some patt ->
%%%                         foldr (fn (p,pats) ->
%%%                                   cons((EmbedPat(id,Some p,srt),pos),pats))
%%%                               nil
%%%                               (removeAliases patt)
%%%                       | None ->
%%%                         [pat])
%%%         | RecordPat idpats ->
%%%           let idpats2 =
%%%               map (fn idpat -> (idpat.1,removeAliases idpat.2)) idpats in
%%%           let pats =
%%%               foldr (fn ((id,pats),recpats) ->
%%%                         foldr (fn (p,recpats1) ->
%%%                                   List.map (fn recpat -> cons((id,p),recpat))
%%%                                       recpats1)
%%%                               recpats
%%%                               pats)
%%%                     (cons(nil,nil))
%%%                     idpats2 in
%%%           map (fn p -> (RecordPat p,pos)) pats
%%%         | RelaxPat(patt,trm) ->
%%%           foldr (fn (p,pats) -> cons(RelaxPat(p,trm),pats))
%%%                 nil
%%%                 (removeAliases patt)
%%%         | QuotientPat(patt,trm) ->
%%%           foldr (fn (p,pats) -> cons(QuotientPat(p,trm),pats))
%%%                 nil
%%%                 (removeAliases patt)
%%%         | patt -> [patt]

  op patternToTerm : Pattern_ast -> Term_ast
  def patternToTerm (pat,pos) =
      case pat of
         | VarPat(id,srt) -> mkOp_ast([id],srt)
         | EmbedPat(id,pat?,srt) ->
           (case pat?
              of Some patt ->
                 mkApply_ast(mkEmbed1_ast(id,srt),patternToTerm patt)
               | None ->
                 mkEmbed0_ast_local(id,srt))
         | RecordPat idpats -> (Record(map (fn (id,pat) -> (id,patternToTerm pat)) idpats),pos0_ast)
         | StringPat s -> mkString_ast s
         | BoolPat b -> mkBool_ast b
         | CharPat c -> mkChar_ast c
         | IntPat i -> mkInt_ast i
         | RelaxPat(patt,trm) ->
           mkApply_ast(mkRelax_ast(patternSort_ast patt,trm),patternToTerm patt)
%%%         | QuotientPat(patt,trm) ->
%%%           mkApply_ast(mkApply_ast(Fun(Quotient,patternSort_ast patt),trm),
%%%                   patternToTerm patt) % not sure this is correct
         % we assume there is no AliasPat because they have all been
         % removed by removeAliases; we also ignore WildPat

The following function returns all the pattern variables contained in
a pattern, without repetitions. Even if this function does not belong here,
it is ok for now.

  op patternVariables : Pattern_ast -> List var_ast
  def patternVariables (pat,pos) =
      case pat
        of AliasPat(pat1,pat2) ->
           let (vars1,vars2) =
               (patternVariables pat1, patternVariables pat2) in
           foldl (fn (v,vs) -> if member(v,vs) then vs else cons(v,vs))
                 vars1
                 vars2
         | VarPat v -> [v]
         | EmbedPat(_,pat?,_) ->
           (case pat? of Some pat1 -> patternVariables pat1 | None -> nil)
         | RecordPat idpats ->
           foldl (fn (idpat,vs) ->
                     let vs1 = patternVariables idpat.2 in
                     foldl (fn (v,vs2) ->
                               if member(v,vs2) then vs2 else cons(v,vs2))
                           vs
                           vs1)
                 nil
                 idpats
         | RelaxPat(pat,_) ->
           patternVariables pat
         | QuotientPat(pat,_) ->
           patternVariables pat
         | _ ->
           nil % wrong for WildPat, but never used
\begin{spec}
}
\end{spec}
