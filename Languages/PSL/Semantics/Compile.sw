\section{Hopelessly Naive Compilation of PSL into BSpecs}

This spec defines the mapping from \PSL\ abstract syntax to \BSpecs. We
assume that the abstract syntax tree we are given is well-formed. For
example, we assume that it typechecks. Note however, that the static
analysis part doesn't exist yet. The assumption is a little irresponsible
but necessary in the short term.

This is an extremely naive encoding of \PSL\ into \BSpecs. There is a
considerable amount of redundancy and inefficiencies in the \BSpec\
representation as well as inefficiencies in the mapping algorithm.
One can easily imagine using more ad-hoc constructions to represent
the flow graphs in a program. However, using ad-hoc structures and
algorithms may well cause problems downstream when we want refinement,
parallel composition and parameterization and when confidence in
correctness is an issue.

One way to look at what follows is as an abstract specifications of
both the data structures (those representing \BSpecs\ and procedures)
and the algorithms that map procedural specifications to \BSpecs. These
might later be refined to more efficient structures and algorithms while
still preserving the desirable mathematical properties.

The code in this spec makes several assumptions, which are pointed out in
the text. Some of them could be made explicit in the code (and proved to be
maintained by the code) by suitable subsorts. Others just derive
from the knowledge of the kinds of programs that we have to deal with in
the short term (\emph{i.e.} for the demo).

\begin{spec}
spec {
  import Program
  import SpecEnv
\end{spec}

An environment is the static, dynamic and axiom specs plus the
collection of procedures seen thus far.

\begin{spec}
  sort PSL_Environment = Context * PolyMap.Map (String, Procedure)
  op emptyPSLEnvironment : PSL_Environment
  def emptyPSLEnvironment = (baseContext, emptyMap_p)
\end{spec}

The new top level function take a file and yields a new environment.
We compile a file with respect to an environment.

\begin{spec}
  op evaluatePSL : List PSL_Elem -> SpecCalc.Env Value
  def evaluatePSL pslElem =

  op compileFile : PSL_Environment -> String -> PSL_Environment
  def compileFile (ctxt,procs) fileName =
    case (parseFile fileName) of
        None -> fail ("Error while parsing " ^ fileName)
      | Some decls -> 
          let _ = writeLine ";;; Compiling to BSpecs" in
          let env = compileDecls ctxt procs decls in
          env
\end{spec}

Formerly the following was the top level function. Now it has been
replaced by something more abstract. This compiles a program declaration
(sort \verb+ProgDecl+) into a program (sort \verb+Program_ast+).

\begin{spec}
  op compileProgDecl : fa(a) ProgDecl a -> Program
\end{spec}

Procedure's contains commands, and commands may contain procedures (in
\verb+let+ declarations), recursively. Obviously, a program declaration
is a tree. Compilation must traverse that tree and collect all the
procedures declared in the tree. We assume that they all have different
names. The resulting map from names to procedures becomes the
\verb+procedures+ field of the program returned by \verb+compileProgDecl+.

We compile a procedure in a context. The context records information
about the ops, sorts, axioms, and vars in scope (visible) to the procedure
being compiled. It is not clear at this stage that the
axioms will be needed though they will be significant later when we
wish to do refinement. Procedures manifest themselves in the context as
normal ops, but without definitions; the definition is given by the
map from names to procedures. So, terms that include such ops encode
procedure calls. Of course, procedure calls are treated in a semantically
different way than regular function applications.

The static spec in the context are the sorts, ops and axioms not dealing
direclty with the machine state. This typically includes all the sorts
used by the program as these are not likely to change their interpretation
in the course of execution. It also includes any auxilliary operations
and axioms. As mentioned above, ops include procedures' names and signatures.

The dynamic spec in the context deals with all the operators declared
as variables and any axioms whose free variables include program
variables. It is not clear that there will ever be such axioms or what
they would mean if they were to exist. Local invariants are not carried.
As there are no axioms and no sorts, rather than type \verb+dynamic : Spec+,
it may suffice in the short term to list the identifiers as a string:
thus \verb+dynamic : List String+. Alternatively, rather than a list
of strings, a list of typed variables. Not clear at this stage that the
types help.

\begin{spec}
  sort Context = {
    static : Spec_ast,
    dynamic : Spec_ast,
    axmSpec : Spec_ast
  }
\end{spec}

The empty context is not exactly empty. It includes two polymorphic sort
declarations:

\begin{verbatim}
  sort Delta a = a * a
  sort Proc (args,rtn,store) = args * rtn * (Delta store) -> Boolean
\end{verbatim}

These are used to type the operators that encapsulate the effect
of procedures (see below).

\begin{spec}
  op baseContext : Context

  def baseContext =
    let deltaSort  = ("Delta", ["a"],
         Some (mkProduct_ast [mkTyVar_ast "a", mkTyVar_ast "a"])) in
    let procSort  = ("Proc", ["args","rtn","store"],
         Some
           (mkArrow_ast
              (mkProduct_ast [
                 mkTyVar_ast "args",
                 mkTyVar_ast "rtn",
                 mkBase_ast(["Delta"],[mkTyVar_ast "store"])],
               boolSort_ast))) in
    let static = emptySpec_ast "Static" in
    let static = addSort_ast(deltaSort,static) in
    let static = addSort_ast(procSort,static) in
    let dynamic = emptySpec_ast "Dynamic" in
    let dynamic = addImport_ast("Static", dynamic) in
    let axmSpec = emptySpec_ast "Axioms" in
    let axmSpec = addImport_ast("Static", axmSpec) in
    {static = static, dynamic = dynamic, axmSpec = axmSpec}
\end{spec}

To compile a program declaration, we assume that the list of declarations
(of which the program declaration consists) is non-empty, that its last
element is a procedure declaration, and that all its other elements are sort,
op, axiom, or var declarations. We use \verb+compileDecls+ (see below) to
build, starting with the empty context, a context incorporating all the
declarations of the program. Note that since the procedure declaration is
last in the list, when \verb+compileProcedure+ (see below) is called, it is
called with the right context (\emph{i.e.} the one consisting of all the
preceding sort, op, axiom, and var declarations).

\begin{spec}
  def compileProgDecl prgDecl =
    let (_,procs) = compileDecls baseContext emptyMap_p prgDecl in
    {procedures = procs,
     main =
       let last = nth (prgDecl, length prgDecl - 1) in
         case last of
             (Proc(name,_),_)  -> name
           | _ -> fail
                 "compileProgDecl: last toplevel definition is not a procedure"
    }
\end{spec}

Because we are dealing with a mutually recursive \verb+let+, compiling a
list of declarations requires two passes of the list. In the first pass,
we retrieve all the new names (ops, sorts, axioms, vars and procedures),
and extend the context with those names. The definitions within a let
(the right sides of the defs and the body of the procedures) are compiled
with respect to the extended context. This is certainly needed for
typechecking, but it is not needed for compilation. So, we just make one
pass: we iterate, first to last (\emph{i.e.} we use \verb+foldl+ and not
\verb+foldr+), through the list, compiling each declaration in turn.

\begin{spec}
  op compileDecls :
    fa(a) Context
    -> PolyMap.Map (String, Procedure)
    -> List (Decl a)
    -> Context * PolyMap.Map (String, Procedure)
  def compileDecls ctxt procs decls = foldl compileDecl (ctxt,procs) decls
\end{spec}

The following function compiles a declaration, updating the argument
context based on that declaration. The uncurried type of the function
matches the type of the function given as argument to \verb+foldl+, in
the definition of \verb+compileDecls+.

\begin{spec}
  op compileDecl :
    fa(a) Decl a
    * (Context * PolyMap.Map (String, Procedure))
    -> Context * PolyMap.Map (String, Procedure)

  def compileDecl (decl,(ctxt,procs)) =
      let (dcl,_) = decl in % remove annotation from declaration
      case dcl of
\end{spec}

For imports we just recursively compile the referenced file. At this
point there is no check for having already loaded the file. The list of
such files should be added to the context.

\begin{spec}
          Import fileName -> compileFile (ctxt,procs) fileName
\end{spec}

Declarations of sorts, ops, and axioms are added to the static context.

\begin{spec}
        | Sort (name,(tyVars,srtScheme)) -> ({
              static = addSort_ast((name,tyVars,srtScheme),ctxt.static),
              axmSpec = ctxt.axmSpec,
              dynamic = ctxt.dynamic
            }, procs)
        | Op (name,(fxty,srtScheme,optTrm)) -> ({
              static = addOp_ast((name,fxty,srtScheme,optTrm),ctxt.static),
              axmSpec = ctxt.axmSpec,
              dynamic = ctxt.dynamic
            }, procs)
        | Claim (Axiom,name,tyVars,term) -> ({
              static = ctxt.static,
              axmSpec = addAxiom_ast((name,tyVars,term),ctxt.axmSpec),
              dynamic = ctxt.dynamic
            }, procs)
        | Claim _ -> 
            let _ = writeLine "Ignoring a non-axiom claim" in
            (ctxt, procs)
\end{spec}

A variable is indistinguishable from an operator other than in the
concrete syntax it is preceeded by the keyword \verb+var+ rather than
\verb+op+. Variables are added to the current dynamic rather than
static context.

\begin{spec}
        | Var (name,(fxty,srtScheme,optTrm)) -> ({
              static = ctxt.static,
              axmSpec = ctxt.axmSpec,
              dynamic = addOp_ast((name,fxty,srtScheme,optTrm),ctxt.dynamic)
            }, procs)
\end{spec}

The last kind of declaration is a procedure. When we see a procedure,
our intention is to compile the procedure into a separate object of sort
\verb+Procedure+ (with an accompanying \BSpec) and add a corresponding
operator to the static context. From the point of view of the callers,
the operator \emph{encapsulates} the effect of the procedure.

This operator is defined as follows. As mentioned earlier, we assume the
sort definitions of \verb+Delta+ and \verb+Proc+ to always appear in the
static context. This assumption is actually enforced by the definition of
\verb+baseContext+ above.

Thus assuming the procedure has arguments \verb+u:U,v:V+, returns a
value of sort \verb+W+ and is defined in a dynamic context \verb+x:X,y:Y+,
then the operator for procedure \verb+p+ is defined as:

\begin{verbatim}
  op p : Proc ((U * V),W,{x:X, y:Y})
\end{verbatim}

A call to \verb+p+ in a transition would be indicated by the occurrence
of the operator \verb+p+ in the axiom in the spec for the transition.
For example,

\begin{verbatim}
  axiom p((s + 1, v), w, ({x = x,y = y},{x = x',y = y'})
\end{verbatim}

The intuition is as follows. The first argument (of type \verb+U * V+)
are the parameters to the procedure. The second, is the return value (or
type \verb+W+).  The last arguments refer to the new and old values of
the variables in scope when the procedure was declared.  Thus a procedure
is encapsulated by a predicate symbol which relates the arguments, the
return values and the new and old values of any variables in scope when
the procedure was declared. Later the last record should be limited to
only those variables actually referred to in the procedure.

There is a small problem here. When we examine a list of declarations,
we don't know that there are no more variable definitions that follow
it. Such variables should become part of the dynamic context for
the procedure. Thus when we see the procedure, we cannot immediately add
the operator for that procedure to the static context. We must wait
to check for further variables. But for now, we assume that procedure
declarations come last in the list: so, the context will have all the
needed variables when the procedure declaration is compiled.

The updated context is given as argument to \verb+compileProcedure+, which
compiles the procedure (and recursively all the procedures it contains),
returning the resulting map from names to procedures (including the
procedure on which \verb+compileProcedure+ is called).

There is a question of whether we should return the new or old context.
Presumably the procedure should be in scope to all those that 
follow it at the same level, and not just those defined within its scope.
But the question of scoping is not handled properly anyway.

Also, should the operator declaration be added to the static
or dynamic contexts? Right now it is the static context as it is not
part of the store.

\begin{spec}
        | Proc (name,procinfo) ->
            let argSorts = map (fn (name,srt) -> srt) procinfo.args in
            let argProd = mkProduct_ast(argSorts) in
            let resSort = procinfo.returnSort in
            let storeRec = mkProduct_local
              (StringMap_foldri
                 (fn (id,opinfo,recSorts) -> Cons((id,opinfo.2.2),recSorts))
                          [] ctxt.dynamic.ops) in
            let procSort = mkBase_ast(["Proc"],[argProd,resSort,storeRec]) in
            let newCtxt =
              (case StringMap_find(ctxt.static.ops,name) of
                  None -> {
                    static = addProcOpDecl(name,procSort,ctxt.static),
                    axmSpec = ctxt.axmSpec,
                    dynamic = ctxt.dynamic}
                | Some _ ->
                   let _ = writeLine ("redeclaring " ^ name) in
                     ctxt) in
            (newCtxt, compileProcedure newCtxt 0 procs (name,procinfo))
\end{spec}

The following function is used to extract a list of type variables from
a sort. The list is free of repetitions, \emph{i.e.} all its elements are
distinct. This function does not belong here: it should be part of the
spec for the MetaSlang abstract syntax, but it is ok for now.

\begin{spec}
  op tyVarsOf : Sort_ast -> TyVars_ast
  def tyVarsOf srt =
      let def tyVarsOfAux (srt:Sort_ast, tvs:TyVars_ast) : TyVars_ast =
              case srt.1
                of Arrow(srt1,srt2)
                   -> tyVarsOfAux(srt1,tyVarsOfAux(srt2,tvs))
                 | Product(idSrts)
                   -> foldl tyVarsOfAux tvs (map (fn x -> x.2) idSrts)
                 | CoProduct(idSrts)
                   -> foldl (fn (idSrt,tvs1) ->
                                case idSrt.2
                                  of Some srt -> tyVarsOfAux(srt,tvs1)
                                   | None -> tvs1)
                            tvs
                            idSrts
                 | Quotient(srt1,_)
                   -> tyVarsOfAux(srt1,tvs)
                 | Subsort(srt1,_)
                   -> tyVarsOfAux(srt1,tvs)
                 | Base(_,srts)
                   -> foldl tyVarsOfAux tvs srts
                 | TyVar tv
                   -> if member(tv,tvs) then tvs else insert(tv,tvs)
                 | MetaTyVar _ -> tvs in
      tyVarsOfAux(srt,[])
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
by assumptions all procedures have different names. In addition, note that
the code assumes that there is no hiding of variables: variables declared in
a procedure (including its arguments) must be distinct from variables
declared, say, in an enclosing procedure. However, two procedures in separate
``branches'' may indeed have common variable names, because they will be
never mixed in the specs labeling \BSpecs.

\begin{spec}
  op compileProcedure :
    fa(a) Context
    -> Nat
    -> PolyMap.Map (String, Procedure)
    -> Ident * ProcInfo a 
    -> PolyMap.Map (String, Procedure)

  def compileProcedure ctxt cnt procs (name,{args,returnSort,command}) =
      let dyCtxt =
        foldl (fn (arg,dCtxt) ->
          let (argname,argsort) = arg in
          addOp_ast((argname, Nonfix,(tyVarsOf argsort,argsort),None), dCtxt))
                       ctxt.dynamic args in
      let dyCtxt = 
        case returnSort of
            (Product [],pos) -> dyCtxt 
          | (_,pos) -> addOp_ast(("return_" ^ name,
                        Nonfix,(tyVarsOf returnSort,returnSort),None),
                       dyCtxt) in

      let newCtxt = {
          static = ctxt.static,
          axmSpec = ctxt.axmSpec,
          dynamic = dyCtxt
        } in
      let dyCtxt_ms = elaborateInContext ctxt.static dyCtxt in
      let first = mkNatVertexEdge cnt in
      let last = mkNatVertexEdge (cnt+1) in
      let system = {
          shape = emptySketch,
          functor = {
              dom = emptySketch,
              cod = specCat_ms,
              vertexMap = emptyMap_p,
              edgeMap = emptyMap_p
            }
        } in
      let system = addVertex system first in
      let system = addVertex system last in
      let system = labelVertex system first dyCtxt_ms in
      let system = labelVertex system last dyCtxt_ms in
      let bspec = {
          initial2 = first,
          final2 = singleton_p last,
          system = system
        } in

      let return : (Option String) =
        case returnSort of
            (Product [],pos) -> None
          | (_,pos) -> Some ("return_" ^ name) in

% again this is a little ugly .. we want to put the procedure into
% the environment in case the procedure is recursive

      let procs =
        update_p procs name {
          parameters = map (fn x -> x.1) args,
          return = return,
          static = elaborateStaticSpec ctxt.static, 
          dynamic = elaborateInContext ctxt.static ctxt.dynamic,
          axmSpec = elaborateInContext ctxt.static ctxt.axmSpec,
          code = bspec} in
      let (bspec,cnt,procs) =
        compileCommand newCtxt
                        first
                        last
                        bspec
                        (cnt + 2)
                        procs
                        command in
      let procs =
        update_p procs name {
          parameters = map (fn x -> x.1) args,
          return = return,
          static = elaborateStaticSpec ctxt.static, 
          dynamic = elaborateInContext ctxt.static ctxt.dynamic,
          axmSpec = elaborateInContext ctxt.static ctxt.axmSpec,
          code = bspec} in
      procs
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
\BSpecs\ to be MetaSlang terms (of sort \verb+Term_ast+). It does not
matter which exact terms, as long as they are terms. So, we use MetaSlang
natural number constants. Since we need to combine \BSpecs\ for
sub-commands into \BSpecs\ for super-commands, we generate
graphs with disjoint nodes and edges for the sub-commands. We achieve that
by threading a counter (\emph{i.e.} a natural number) through the
functions to compile commands. The counter is used generate unique
``names'' for nodes and edges.

\begin{spec}
sort Elem = Term_ms
\end{spec}

The argument context is used to generate the specs labeling nodes and
edges. Both the static and the dynamic context should be included. However,
for efficiency reasons, and since there is no integrity checking, we
just use the dynamic context.

Even if bipointed \BSpecs\ have one starting node and a set of ending nodes,
compilation always produces singleton sets of ending nodes. The partial
evaluator may generate sets with more than one node, though: that is the
reason for having a set of ending nodes.

\begin{spec}
  op compileCommand : fa(a) Context
     -> Vertex.Elem
     -> Vertex.Elem
     -> BSpec
     -> Nat
     -> PolyMap.Map (String, Procedure)
     -> Command a -> BSpec * Nat * PolyMap.Map (String, Procedure)

  def compileCommand ctxt first last bspec cnt procs (cmd,_) =
    case cmd of
\end{spec}

Compiling a sequence of commands means compiling the individual commands
and gluing the end of one onto the start of next. We assume that the list of
commands is not empty.

problem here... how does the static context get updated with the new
procedures? And how do we accumulate the procedures? Probably ok ..
the other procedures are not in scope?

\begin{spec}
      | Seq cmds -> compileSeq ctxt first last bspec cnt procs cmds
\end{spec}

The compilation of an \verb+if+ consist of first compiling the
list of alternatives, then adding identity transitions out of the end of
each alternative into a common (new) vertex. Note that the compilation of
the list of alternatives results in the compilation of the commands for all
the alternatives, with transitions out of a common starting node into each
alternative: these transitions are labeled by the respective guards.

\begin{spec}
      | If [] -> fail "compileCommand: If: empty list of alternatives"
      | If alts -> compileAlternatives ctxt first last bspec cnt procs alts
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
      | Do (alts as (((firstGuard,firstCommand),_)::restAlts)) ->
          let (bspec,cnt,procs) =
             compileAlternatives ctxt first first bspec cnt procs alts in
          let newEdge = mkNatVertexEdge cnt in
          let system = addEdge bspec.system newEdge first last in
          let axm = mkNot_ast
            (foldl (fn (((gard,cmd),_),trm) -> mkOr_ast(trm,gard))
                              firstGuard
                              restAlts) in
          let apexSpec = addAxiom_ast(("guard", [], axm), ctxt.dynamic) in
          let dynamic_ms = elaborateInContext ctxt.static ctxt.dynamic in
          let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
          let morph = identityMorphism dynamic_ms in
          let morph = {
              dom = morph.dom,
              cod = apexSpec_ms,
              sortMap = morph.sortMap,
              opMap = morph.opMap
            } in
          let system = labelEdge system newEdge apexSpec_ms morph morph in
          let bspec =
            {initial2=bspec.initial2, final2=bspec.final2, system=system} in
          (bspec,cnt+1,procs)
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
      | Assign ((trm1,pos1),(trm2,pos2)) ->
          (case trm2 of
            | Apply ((Fun(Op(id::[],fixity),srt),pos)::(Record args,_)::[]) ->
                if ~((evalPartial_p procs id) = None) then
                  compileProcCall ctxt first last bspec cnt procs (Some (trm1,pos1)) id
                    (map (fn (x,y) -> y) args)
                else
                  compileAssign ctxt first last bspec cnt procs (trm1,pos1) (trm2,pos2)
            | Apply ((Fun(Op(id::[],fixity),srt),pos)::arg::[]) ->
                if ~((evalPartial_p procs id) = None) then
                  compileProcCall ctxt first last bspec cnt procs (Some (trm1,pos1)) id [arg]
                else
                  compileAssign ctxt first last bspec cnt procs (trm1,pos1) (trm2,pos2)
            | _ ->
                compileAssign ctxt first last bspec cnt procs (trm1,pos1) (trm2,pos2))
\end{spec}

\begin{spec}
      | Exec trm -> % (trm,pos) ->
          compileAxiomStmt ctxt first last bspec cnt procs trm
%%%           (case trm of
%%%             | Apply ((Fun(Op(id::[],fixity),srt),pos)::(Record args,_)::[]) ->
%%%                 if ~((evalPartial_p procs id) = None) then
%%%                   compileProcCall ctxt first last bspec cnt procs None id
%%%                     (map (fn (x,y) -> y) args)
%%%                 else
%%%                   fail ("compileCommand: procedure "
%%%                       ^ id
%%%                       ^ " has not been declared at position "
%%%                       ^ (printPosition_ast pos))
%%%             | Apply ((Fun(Op(id::[],fixity),srt),pos)::arg::[]) ->
%%%                 if ~((evalPartial_p procs id) = None) then
%%%                   compileProcCall ctxt first last bspec cnt procs None id [arg]
%%%                 else
%%%                   fail ("compileCommand: procedure "
%%%                       ^ id
%%%                       ^ " has not been declared at position "
%%%                       ^ (printPosition_ast pos))
%%%             | _ ->
%%%                fail ("compileCommand: invalid procedure call at position "
%%%                      ^ (printPosition_ast pos)))
\end{spec}

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

\begin{spec}
      | AssignCall(trm,pr,args) ->
          compileProcCall ctxt first last bspec cnt procs (Some trm) pr args
\end{spec}

To compile a procedure call whose result is discarded, we create a
one-transition \BSpec\ similar to the one above. The difference is that the
second argument to the operator representing the procedure is an
existentially quantified variable. So, the ``effect'' of the axiom is
simply to relate the new state's variables' values to their old values and
to the arguments passed to the procedure. The name of the existentially
quantified variable is \verb+x+ followed by three underscores followed by
\verb+x+; so, we (reasonably) assume that no other variable has that name.

\begin{spec}
      | Call(pr,args) ->
          compileProcCall ctxt first last bspec cnt procs None pr args
\end{spec}

To compile a \verb+let+, we first compile its declarations, thus enlarging
the context. Then, we compile the command in the enlarged context.
We add a transition into and a transition out of the \BSpec\ produced
by compiling the command. The spec labeling the starting and ending vertices
of the \BSpec\ for the \verb+let+ are determined by the smaller (i.e., not
enlarged) context.

\begin{spec}
      | Let (decls,comm) ->
          let (ctxt2,procs) = compileDecls ctxt procs decls in
          let (bspec,cnt,procs2) =
            compileCommand ctxt2 first last bspec cnt procs comm in
          (bspec,cnt,procs2)
\end{spec}

\begin{spec}
      | Case (trm,cases) -> fail "compileCommand: Case: not supported"
\end{spec}

Compiling a skip is a transition where the maps are identities and
the axiom is just true.

Should really check that the specs at the start and end are the same.
This should be an invariant. Must check.

\begin{spec}
      | Skip ->
          let apexSpec = addAxiom_ast(("assign",[],mkTrue_ast ()),ctxt.dynamic) in
          let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
          let morph1 = identityMorphism (modeSpec_ms bspec first) in
          let morph2 = identityMorphism (modeSpec_ms bspec last) in
          let newEdge = mkNatVertexEdge cnt in
          let system = addEdge bspec.system newEdge first last in
          let system = labelEdge system newEdge apexSpec_ms morph1 morph2 in
          let bspec = {
              initial2 = bspec.initial2,
              final2 = bspec.final2,
              system=system
            } in
          (bspec,cnt+1,procs)
\end{spec}

\begin{spec}
  op compileAssign :
      Context 
      -> Vertex.Elem
      -> Vertex.Elem
      -> BSpec
      -> Nat
      -> PolyMap.Map (String, Procedure)
      -> Term_ast
      -> Term_ast
      -> BSpec * Nat * PolyMap.Map (String, Procedure)
  def compileAssign ctxt first last bspec cnt procs (trm1,pos1) (trm2,pos2) =
          let (leftId, leftPrimedTerm) = processLHS (trm1,pos1) in
          let primedId = leftId ^ "'" in

          let apexSpec : Spec_ast = 
            (case StringMap_find (ctxt.dynamic.ops,leftId) of
                None ->
                  fail ("compileCommand: Assign: id '"
                          ^ leftId ^ "' is undefined")
              | Some (fixity,sortScheme,optTerm) ->
                 addOp_ast((primedId,fixity,sortScheme,optTerm),ctxt.dynamic)) in
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
          let axm = mkEquals_local (leftPrimedTerm, (trm2,pos2)) in
\end{spec}

Here we add the axioms encoding the assignment to the apex spec. Right
now the axiom has no type varibles in the sort scheme. There might
be scope for more polymorphism if we use the \verb+tyVarsOf+ function
that Alessandro wrote below rather than use, as below, an empty list of
type variables.

\begin{spec}
          let apexSpec = addAxiom_ast(("assign",[],axm),apexSpec) in
          let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
\end{spec}

The remainder of this case, creates and labels the opspan for the transition.

\begin{spec}
          let morph1 = identityMorphism (modeSpec_ms bspec first) in
          let morph1 = {
              dom = morph1.dom,
              cod = apexSpec_ms,
              sortMap = morph1.sortMap,
              opMap = morph1.opMap
            } in
          let morph2 = identityMorphism (modeSpec_ms bspec last) in
          let morph2 = {
              dom = morph2.dom,
              cod = apexSpec_ms,
              sortMap = morph2.sortMap,
              opMap = update_p morph2.opMap leftId primedId
            } in
          let newEdge = mkNatVertexEdge cnt in
          let system = addEdge bspec.system newEdge first last in
          let system = labelEdge system newEdge apexSpec_ms morph1 morph2 in
          let bspec = {
              initial2 = bspec.initial2,
              final2 = bspec.final2,
              system=system
            } in
          (bspec,cnt+1,procs)
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
  op processLHS : Term_ast -> String * Term_ast
  def processLHS (trm,pos0) =
    case trm of
      Fun(Op(id::[],fixity),srt) -> (id, (Fun(Op([id ^"'"],fixity),srt),pos0))
    | Apply ((Fun(Op(id::[],fixity),srt),pos)::args) ->
         (id, (Apply (Cons ((Fun(Op([id^"'"],fixity),srt),pos),args)),pos0))
  
    | Apply ((Fun(Op(_::id::[],fixity),srt),pos)::args) ->
         fail ("compileLHS: (Apply): unexpected qualified id on lhs")
    | Fun(Op(_::id::[],fixity),srt) -> 
         fail ("compileLHS: (Op): unexpected qualified id on lhs")
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


\begin{spec}
  op compileAxiomStmt : Context
          -> Vertex.Elem
          -> Vertex.Elem
          -> BSpec
          -> Nat
          -> PolyMap.Map (String, Procedure)
          -> Term_ast
          -> BSpec * Nat * PolyMap.Map (String, Procedure)

  def compileAxiomStmt ctxt first last bspec cnt procs trm =
      let declDynCtxt = ctxt.dynamic in
      let apexSpec = ctxt.dynamic in
      let apexSpec = {
          name = apexSpec.name,
          sorts = apexSpec.sorts,
          ops = StringMap_foldri (fn (opr,opinfo,map) ->
                  StringMap_insert(map,opr ^ "'",opinfo))
                             apexSpec.ops
                             declDynCtxt.ops,
          properties = apexSpec.properties,
          imports = apexSpec.imports
        } in

      let apexSpec = addAxiom_ast(("axiom stmt",[],trm),apexSpec) in
      let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
      let morph1 = identityMorphism (modeSpec_ms bspec first) in
      let morph1 = {
          dom = morph1.dom,
          cod = apexSpec_ms,
          sortMap = morph1.sortMap,
          opMap = morph1.opMap
        } in
      let morph2 = identityMorphism (modeSpec_ms bspec last) in
      let morph2 = {
          dom = morph2.dom,
          cod = apexSpec_ms,
          sortMap = morph2.sortMap,
          opMap = StringMap_foldri
              (fn (opr,opinfo,map) -> update_p map opr (opr ^ "'")) morph2.opMap
                                        declDynCtxt.ops
        } in
      let newEdge = mkNatVertexEdge cnt in
      let system = addEdge bspec.system newEdge first last in
      let system = labelEdge system newEdge apexSpec_ms morph1 morph2 in
      let bspec = {
          initial2=bspec.initial2,
          final2=bspec.final2,
          system=system
        } in
      (bspec,cnt+1,procs)
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
  op compileProcCall : Context
          -> Vertex.Elem
          -> Vertex.Elem
          -> BSpec
          -> Nat
          -> PolyMap.Map (String, Procedure)
          -> Option Term_ast
          -> String
          -> List Term_ast
          -> BSpec * Nat * PolyMap.Map (String, Procedure)

  def compileProcCall ctxt first last bspec cnt procs trm? pr args =
      let procOpInfo =
        case StringMap_find(ctxt.static.ops,pr) of
            Some procOpInfo -> procOpInfo
          | None ->
             fail ("compileProcCall: call to undefined procedure: " ^ pr) in

      let (leftId,leftPrimedTerm) =
          case trm? of
               Some trm -> processLHS trm
             | None -> ("dummy", mkRecord_ast [])
%                  (case procOpInfo of
%                      (_,(_,(Base(_,srts),_)),_) -> 
%                          (mkVar_ast("x___x",hd(tl srts)),hd(tl srts))
%                    | _ -> fail
%                        ("compileProcCall: bad procedure opInfo: " ^ pr))
             | _ -> fail "compileProcCall: result term not a variable" in

      let primedId = leftId ^ "'" in
      let procInfo = eval_p procs pr in
      let declDynCtxt = fromMetaSlang_ast procInfo.dynamic in
      let apexSpec = ctxt.dynamic in
      let apexSpec = {
          name = apexSpec.name,
          sorts = apexSpec.sorts,
          ops = StringMap_foldri (fn (opr,opinfo,map) ->
                  StringMap_insert(map,opr ^ "'",opinfo))
                             apexSpec.ops
                             declDynCtxt.ops,
          properties = apexSpec.properties,
          imports = apexSpec.imports
        } in
      let argTuple = mkTuple_ast args in
      let oldRec =
          mkRecord_local(StringMap_foldri (fn (id,opinfo,pairs) ->
                              let trm = mkOp_ast([id],opinfo.2.2) in
                              Cons ((id,trm),pairs))
                             []
                             declDynCtxt.ops) in
      let newRec =
          mkRecord_local(StringMap_foldri (fn (id,opinfo,pairs) ->
                              let trm = mkOp_ast([id ^ "'"],opinfo.2.2) in
                              Cons ((id,trm),pairs))
                             []
                             declDynCtxt.ops) in
      let recPair = mkTuple_ast([oldRec,newRec]) in
      let totalTuple = mkTuple_ast([argTuple,leftPrimedTerm,recPair]) in
      let procOp = mkOp_ast([pr],procOpInfo.2.2) in

      let axm = mkApply_ast(procOp,totalTuple) in
      let apexSpec =
        case trm? of
            Some trm -> 
                (case StringMap_find (ctxt.dynamic.ops,leftId) of
                      None ->
                       fail ("compileProcCall: id '" ^ leftId ^ "' is undefined")
                    | Some (fixity,sortScheme,optTerm) ->

\end{spec}

The point here is that, if the variable was defined in an scope outside
the procedure, then, thanks to the addOp above, it will already exist
in the apexSpec. Hence, before adding we must make sure its not already
there.

\begin{spec}
                       (case StringMap_find(apexSpec.ops,primedId) of
                            None -> addOp_ast((primedId,
                               fixity,sortScheme,optTerm),apexSpec)
                          | Some _ -> apexSpec))
          | None -> apexSpec in

      let apexSpec = addAxiom_ast(("call",[],axm),apexSpec) in
      let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
      let morph1 = identityMorphism (modeSpec_ms bspec first) in
      let morph1 = {
          dom = morph1.dom,
          cod = apexSpec_ms,
          sortMap = morph1.sortMap,
          opMap = morph1.opMap
        } in
      let morph2 = identityMorphism (modeSpec_ms bspec last) in
      let morph2 = {
          dom = morph2.dom,
          cod = apexSpec_ms,
          sortMap = morph2.sortMap,
          opMap =
            let om = StringMap_foldri
              (fn (opr,opinfo,map) -> update_p map opr (opr ^ "'")) morph2.opMap
                                        declDynCtxt.ops in
            case trm? of
                None -> om
              | Some _ -> update_p om leftId primedId
        } in
      let newEdge = mkNatVertexEdge cnt in
      let system = addEdge bspec.system newEdge first last in
      let system = labelEdge system newEdge apexSpec_ms morph1 morph2 in
      let bspec = {
          initial2=bspec.initial2,
          final2=bspec.final2,
          system=system
        } in
      (bspec,cnt+1,procs)
\end{spec}

\begin{spec}
  op compileSeq :
    fa(a) Context
     -> Vertex.Elem
     -> Vertex.Elem
     -> BSpec
     -> Nat
     -> PolyMap.Map (String, Procedure)
     -> List (Command a) -> BSpec * Nat * PolyMap.Map (String, Procedure)

  def compileSeq ctxt first last bspec cnt procs cmds =
    case cmds of
        [] -> (bspec,cnt,procs)
      | cmd::[] -> compileCommand ctxt first last bspec cnt procs cmd   
      | cmd1::cmd2::rest ->
        let dyCtxt_ms = elaborateInContext ctxt.static ctxt.dynamic in
        let new = mkNatVertexEdge cnt in
        let system = addVertex bspec.system new in
        let system = labelVertex system new dyCtxt_ms in
        let bspec = {
             initial2 = bspec.initial2,
             final2 = bspec.final2,
             system = system
          } in
        let (bspec,cnt,procs) =
          compileCommand ctxt first new bspec (cnt+1) procs cmd1 in
        compileSeq ctxt new last bspec cnt procs (Cons(cmd2,rest))
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
    fa(a) Context
    -> Vertex.Elem
    -> Vertex.Elem
    -> BSpec
    -> Nat
    -> PolyMap.Map(String,Procedure)
    -> List (Alternative a)
    -> BSpec * Nat * PolyMap.Map(String,Procedure)

  def compileAlternative ctxt first last bspec cnt procs ((trm,cmd),pos) = 
    let dyCtxt_ms = elaborateInContext ctxt.static ctxt.dynamic in
    let newVertex = mkNatVertexEdge cnt in
    let system = addVertex bspec.system newVertex in
    let system = labelVertex system newVertex dyCtxt_ms in
    let newEdge = mkNatVertexEdge (cnt + 1) in
    let system = addEdge system newEdge first newVertex in
    let apexSpec = addAxiom_ast(("guard",[],trm),ctxt.dynamic) in
    let apexSpec_ms = elaborateInContext ctxt.static apexSpec in
    let morph1 = identityMorphism (modeSpec_ms bspec first) in
    let morph1 = {dom = morph1.dom,
                  cod = apexSpec_ms,
                  sortMap = morph1.sortMap,
                  opMap = morph1.opMap} in
    let dynamic_ms = elaborateInContext ctxt.static ctxt.dynamic in
    let morph2 = identityMorphism dynamic_ms in
    let morph2 = {dom = morph2.dom,
                  cod = apexSpec_ms,
                  sortMap = morph2.sortMap,
                  opMap = morph2.opMap} in
    let system = labelEdge system newEdge apexSpec_ms morph1 morph2 in
    let bspec = {initial2=bspec.initial2,final2=bspec.final2,system=system} in
      compileCommand ctxt newVertex last bspec (cnt+2) procs cmd
 
  def compileAlternatives ctxt first last bspec cnt procs alts =
    case alts of
        alt::[] -> compileAlternative ctxt first last bspec cnt procs alt
      | firstAlt::restAlts ->
          let (bspec,cnt,procs) =
             compileAlternative ctxt first last bspec cnt procs firstAlt in
          compileAlternatives ctxt first last bspec cnt procs restAlts
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

\begin{spec}
  op identityMorphism : Spec_ms -> Morphism_ms
  def identityMorphism spc = {
    dom = spc,
    cod = spc,
    sortMap = emptyMap_p,
    opMap = StringMap_foldri
      (fn (opname,opinfo,map) -> update_p map opname opname) emptyMap_p spc.ops
  }
\end{spec}

The following function creates a vertex/edge (of sort \verb+Vertex.Elem+, which
is the same as \verb+Elem_e+) from
a natural number. More precisely, it creates a vertex/edge consisting of
the MetaSlang term for that natural number.

\begin{spec}
  op mkNatVertexEdge : Nat -> Vertex.Elem
  def mkNatVertexEdge n = Just (mkNat_ms n)
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

\begin{spec}
  op procSortInstance : List Sort_ast * Sort_ast * Sort_ast -> Sort_ast
  def procSortInstance (args,rtn,store) =
    mkBase_ast (["Proc"],[mkProduct_ast args,rtn,store])
\end{spec}

The next is the companion to the above. This adds an operator
representing a procedure to a given spec. It might be better if the
above function was folded into this one.

\begin{spec}
  op addProcOpDecl :
      String            % the name of the procedure
      * Sort_ast        % the type of the proc (from procSortInstance)
      * Spec_ast        % the spec to update
      -> Spec_ast
  def addProcOpDecl (name,srt,spc) =
      addOp_ast((name, Nonfix, (tyVarsOf srt, srt), None),spc)
\end{spec}

The next function is used by the caller to construct a term
representing a procedure call. We are given a collection of terms
and return a term.

\begin{spec}
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
\end{spec}

The following two functions serve to merge two systems into one. They assume
that the two systems have disjoint shapes and common labeling categories, so
that merging boils down to simple union of vertices, edges, source and target
maps, as well as labeling maps. Obviously, these two functions do not belong
here, but it is ok for now.

\begin{spec}
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
\end{spec}

Some convenience functions are omitted from the \verb+ast+ and
\verb+ast_util+ specs which exist in \verb+meta_slang+. The first
defined below has a suffix \verb+local+ to avoid a name clash with
\verb+mkEmbed0+ defined in \verb+ast_types+. Name spaces are a problem
requiring a rethink of the current practice.

\begin{spec}
  op mkEmbed0_local : Id_ast * Sort_ast -> Term_ast
  def mkEmbed0_local (id,srt) = (Fun (Embed(id,false),srt), pos0_ast)

  op mkNot_ast : Term_ast -> Term_ast
  def mkNot_ast trm =
    let srt = mkArrow_ast(boolSort_ast, boolSort_ast) in
    mkApply_ast (mkOp_ast (["Boolean", "~"], srt), trm)

  op mkAnd_ast : Term_ast * Term_ast -> Term_ast
  def mkAnd_ast (t1,t2) =
    let srt =
      mkArrow_ast(mkProduct_ast([boolSort_ast, boolSort_ast]), boolSort_ast) in
    mkApply_ast (mkOp_ast (["Boolean", "&"], srt), mkTuple_ast([t1,t2]))

  op mkOr_ast : Term_ast * Term_ast -> Term_ast
  def mkOr_ast (t1,t2) =
    let srt =
      mkArrow_ast(mkProduct_ast([boolSort_ast, boolSort_ast]), boolSort_ast) in
    mkApply_ast (mkOp_ast (["Boolean", "or"], srt), mkTuple_ast([t1,t2]))
\end{spec}

Local functions for constucting product types a record terms. All products
have named fields. These are integers in the case of tuples. MetaSlang
assumes that all the fields are sorted in alphabetical order. A sorting
function follows.

\begin{spec}
  op mkProduct_local : List (String * Sort_ast) -> Sort_ast
  def mkProduct_local l =
   (Product (sortList (fn ((x,_),(y,_)) -> x leq y) l), pos0_ast)

  op mkRecord_local : List (String * Term_ast) -> Term_ast
  def mkRecord_local l =
   mkRecord_ast (sortList (fn ((x,_),(y,_)) -> x leq y) l)
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
def mkEquals_local (t1 as (_,pos),t2) = 
    let srt = freshMetaTyVar_ast pos in
    mkApply_ast((Fun(Equals,srt),pos),mkTuple_ast [t1,t2])
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

\begin{spec}
  op elaborateInContext : Spec_ast -> Spec_ast -> Spec_ms
  def elaborateInContext static dynamic =
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
      case pat
        of VarPat(id,srt) ->
           mkOp_ast([id],srt)
         | EmbedPat(id,pat?,srt) ->
           (case pat?
              of Some patt ->
                 mkApply_ast(mkEmbed1_ast(id,srt),patternToTerm patt)
               | None ->
                 mkEmbed0_ast_local(id,srt))
         | RecordPat idpats ->
           (Record(map (fn (id,pat) -> (id,patternToTerm pat)) idpats),pos0_ast)
         | StringPat s ->
           mkString_ast s
         | BoolPat b ->
           mkBool_ast b
         | CharPat c ->
           mkChar_ast c
         | IntPat i ->
           mkInt_ast i
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
}
\end{spec}
