BSpec qualifying spec

  import TransSpec
  import ModeSpec
  import Subst/AsOpInfo
  import Env

  sort CoAlg = List (Vertex * (List Transition))
  op CoAlg.empty : CoAlg
  def CoAlg.empty = []

  op Vrtx.eq? : Vertex * Vertex -> Boolean
  def Vrtx.eq? (v1,v2) =
    case (v1,v2) of
      | (Nat n1, Nat n2) -> n1 = n2
      | (Pair (v1,s1), Pair (v2,s2)) -> Vrtx.eq? (v1,v2) & Subst.eq? (s1,s2)
      | _ -> false

  op CoAlg.insert : CoAlg -> Vertex -> Transition -> CoAlg
  def CoAlg.insert coAlg vertex transition =
    let
      def findVertex coAlg accum =
        case coAlg of
          | [] -> Cons ((vertex,[transition]), accum)
          | (pair as (vrtx,transitions))::rest ->
              if eq? (vertex,vrtx) then
                (Cons ((vertex, Cons (transition,transitions)),accum)) ++ rest    % may need to insert the edge as a set
              else
                findVertex rest (Cons (pair,accum))
    in
      findVertex coAlg []

  sort BSpec = {
      modes : List Mode,
      transitions : List Transition,
      outTrans : CoAlg,
      inTrans : CoAlg,
      initial : Mode,
      final : List Mode,
      nextIdx : Nat,
      id : Id.Id
   }

  op BSpec.modes : BSpec -> List Mode
  def BSpec.modes bSpec = bSpec.modes

  op BSpec.pp : BSpec -> ModeSpec -> Env Doc
  def BSpec.pp = ppRaw

  op BSpec.ppShort : BSpec -> ModeSpec -> Env Doc
  def BSpec.ppShort bSpec modeSpec = {
    (visited,doc) <- ppFrom modeSpec bSpec (initial bSpec) [] ppNil;
    return (ppConcat [
            String.pp "{initial=",
            pp bSpec.initial.vertex,
            String.pp ", final={",
            ppSep (String.pp ",") (map (fn mode -> pp mode.vertex) bSpec.final),
            String.pp "}, diagram=",
            ppNewline,
            String.pp "  ",
            ppIndent doc
        ])
    }

  op BSpec.ppRaw : BSpec -> ModeSpec -> Env Doc
  def BSpec.ppRaw bSpec modeSpec =
    return (ppConcat [
            String.pp "{initial=",
            pp bSpec.initial.vertex,
            String.pp ", final={",
            ppSep (String.pp ",") (map (fn mode -> pp mode.vertex) bSpec.final),
            String.pp "}",
            ppNewline,
            String.pp "modes={",
            ppSep (String.pp ",") (map (fn mode -> pp mode.vertex) bSpec.modes),
            String.pp "}",
            ppNewline,
            String.pp "transitions={",
            ppSep (String.pp ",") (map (fn transition ->
                     ppConcat [Edg.pp transition.edge,
                               String.pp " : ",
                               Vrtx.pp (vertex (source transition)),
                               String.pp " -> ",
                               pp (vertex (target transition))]) bSpec.transitions),
            String.pp "}",
            ppNewline,
            String.pp "outTrans={",
            ppSep ppNewline (map (fn (vrtx,tlist) -> 
                     ppConcat [pp vrtx,
                               String.pp " -> {",
                               ppSep (String.pp ",") (map (fn trans -> pp trans.edge) tlist),
                               String.pp "}"]) bSpec.outTrans),
            String.pp "}",
            ppNewline,
            String.pp "inTrans={",
            ppSep ppNewline (map (fn (vrtx,tlist) -> 
                     ppConcat [pp vrtx,
                               String.pp " -> {",
                               ppSep (String.pp ",") (map (fn trans -> pp trans.edge) tlist),
                               String.pp "}"]) bSpec.inTrans),
            ppNewline,
            String.pp "nextIdx = ",
            Nat.pp bSpec.nextIdx,
            ppNewline,
            String.pp "qid = ",
         Id.pp bSpec.id
        ])


  sort Mode = {
      vertex : Vrtx.Vertex,
      modeSpec : ModeSpec
    }

  op Mode.vertex : Mode -> Vrtx.Vertex
  def Mode.vertex mode = mode.vertex

  op Mode.idOf : Mode -> Id.Id
  def Mode.idOf mode = 
    let
      def vertexId vrtx =
        case vrtx of
          | Nat (n,id) -> id
          | Pair (vrtx,subst) -> vertexId vrtx
    in
      vertexId mode.vertex

  op Mode.modeSpec : Mode -> ModeSpec
  def Mode.modeSpec mode = mode.modeSpec

  op Mode.eq? : Mode * Mode -> Boolean
  def Mode.eq? (m1,m2) = Vrtx.eq? (vertex m1, vertex m2)

  op Mode.substOf : Mode -> Subst
  def Mode.substOf mode =
    case (vertex mode) of
      | Nat _ -> []
      | Pair (vrtx,subst) -> subst

  sort Transition = {
      edge : Edge,
      source : Mode,
      target : Mode,
      transSpec : TransSpec
    }

  op Transition.edge : Transition -> Edge
  def Transition.edge transition = transition.edge

  op Transition.modeSpec : Transition -> ModeSpec
  def Transition.modeSpec transition = modeSpec transition.transSpec

  op Transition.source : Transition -> Mode
  def Transition.source transition = transition.source

  op Transition.target : Transition -> Mode
  def Transition.target transition = transition.target

  op Transition.transSpec : Transition -> TransSpec
  def Transition.transSpec transition = transition.transSpec

  sort TransSet

  sort Vrtx.Vertex =
    | Nat (Nat * Id.Id)
    | Pair (Vrtx.Vertex * Subst)

  sort Edg.Edge =
    | Nat (Nat * Id.Id)
    | Triple (Edg.Edge * Subst * Subst)

  op BSpec.initFromOld : BSpec -> BSpec * Mode
  def BSpec.initFromOld oldBSpec =
   let newBSpec = {
      modes = [initial oldBSpec],
      transitions = [],
      outTrans = CoAlg.empty,
      inTrans = CoAlg.empty,
      initial = initial oldBSpec,
      final = [],
      nextIdx = oldBSpec.nextIdx,
      id = oldBSpec.id
    } in
    (newBSpec,initial oldBSpec)

  op BSpec.make : Id.Id -> ModeSpec -> (BSpec * Mode)
  def BSpec.make id modeSpec =
   let initial = {
         vertex = Nat (0,id),
         modeSpec = modeSpec
     } in 
   let newBSpec = {
      modes = [initial],
      transitions = [],
      outTrans = CoAlg.empty,
      inTrans = CoAlg.empty,
      initial = initial,
      final = [],
      nextIdx = 1,
      id = id
    } in
    (newBSpec,initial)

  op BSpec.withModes infixl 17 : BSpec * List Mode -> BSpec
  def BSpec.withModes (bSpec,modes) = {
      modes = modes,
      transitions = bSpec.transitions,
      outTrans = bSpec.outTrans, 
      inTrans = bSpec.inTrans,
      initial = bSpec.initial,
      final = bSpec.final,
      nextIdx = bSpec.nextIdx,
      id = bSpec.id
    }

  (* the boolean is true if we do already have the given mode. *)
  op BSpec.deriveBSpec : BSpec -> Subst -> ModeSpec -> (BSpec * Mode)
  def BSpec.deriveBSpec bSpec subst modeSpec =
   let newMode = {
         vertex = Pair (vertex (initial bSpec), subst),
         modeSpec = modeSpec
     } in
   let newBSpec = {
      modes = [newMode],
      transitions = [],
      outTrans = CoAlg.empty,
      inTrans = CoAlg.empty,
      initial = newMode,
      final = [],
      nextIdx = 1,
      id = bSpec.id
    } in
    (newBSpec, newMode)

  op BSpec.deriveMode : BSpec -> Mode -> BSpec -> Subst -> ModeSpec -> (BSpec * Mode * Boolean)
  def BSpec.deriveMode oldBSpec mode newBSpec subst modeSpec =
      let newVertex = Pair (vertex mode, subst) in
      let
        def findVertex modes =
          case modes of
            | [] -> None
            | mode::rest ->
               if eq? (vertex mode, newVertex) then
                 Some mode
               else
                 findVertex rest
      in
        case findVertex (newBSpec.modes) of
          | Some mode -> (newBSpec, mode, false)
          | None ->
             let newMode = {
                 vertex = newVertex,
                 modeSpec = modeSpec
               } in
             let newBSpec = {
                 modes = Cons (newMode, newBSpec.modes),
                 transitions = newBSpec.transitions,
                 outTrans = newBSpec.outTrans, 
                 inTrans = newBSpec.inTrans,
                 initial = newBSpec.initial,
                 final = if Mode.member? oldBSpec.final mode then
                           Cons (newMode,newBSpec.final)
                         else
                           newBSpec.final,
                 nextIdx = newBSpec.nextIdx,
                 id = newBSpec.id
               } in
               (newBSpec,newMode,true)

  op BSpec.deriveTransition : Transition -> BSpec -> Mode -> Mode -> Subst -> Subst -> TransSpec -> (BSpec * Transition)
  def BSpec.deriveTransition transition newBSpec sourceMode targetMode precondition postcondition transSpec =
      let newTransition = {
          edge = Triple (edge transition, precondition,postcondition),
          source = sourceMode,
          target = targetMode,
          transSpec = transSpec
        } in
      let newBSpec = {
          modes = newBSpec.modes,
          transitions = Cons (newTransition, newBSpec.transitions),
          outTrans = insert newBSpec.outTrans (vertex sourceMode) newTransition,
          inTrans = insert newBSpec.inTrans (vertex targetMode) newTransition,
          initial = newBSpec.initial,
          final = newBSpec.final,
          nextIdx = newBSpec.nextIdx,
          id = newBSpec.id
        } in
      (newBSpec,newTransition)

  op BSpec.newMode : BSpec -> ModeSpec -> (BSpec * Mode)
  def BSpec.newMode bSpec modeSpec =
      let newMode = {
          vertex = Nat (bSpec.nextIdx,bSpec.id),
          modeSpec = modeSpec
        } in
      let newBSpec = {
          modes = Cons (newMode, bSpec.modes),
          transitions = bSpec.transitions,
          outTrans = bSpec.outTrans, 
          inTrans = bSpec.inTrans,
          initial = bSpec.initial,
          final = bSpec.final,
          nextIdx = bSpec.nextIdx + 1,
          id = bSpec.id
        } in
        (newBSpec,newMode)

  op BSpec.addMode : BSpec -> Mode -> BSpec
  def BSpec.addMode bSpec newMode = {
          modes = Cons (newMode, bSpec.modes),
          transitions = bSpec.transitions,
          outTrans = bSpec.outTrans, 
          inTrans = bSpec.inTrans,
          initial = bSpec.initial,
          final = bSpec.final,
          nextIdx = bSpec.nextIdx,
          id = bSpec.id
        }

  op BSpec.newFinalMode : BSpec -> ModeSpec -> (BSpec * Mode)
  def BSpec.newFinalMode bSpec modeSpec =
      let newMode = {
          vertex = Nat (bSpec.nextIdx,bSpec.id),
          modeSpec = modeSpec
        } in
      let newBSpec = {
          modes = Cons (newMode, bSpec.modes),
          transitions = bSpec.transitions,
          outTrans = bSpec.outTrans, 
          inTrans = bSpec.inTrans,
          initial = bSpec.initial,
          final = Cons (newMode, bSpec.final),
          nextIdx = bSpec.nextIdx + 1,
          id = bSpec.id
        } in
        (newBSpec,newMode)

  op BSpec.addFinalMode : BSpec -> Mode -> BSpec
  def BSpec.addFinalMode bSpec newMode = {
          modes = Cons (newMode, bSpec.modes),
          transitions = bSpec.transitions,
          outTrans = bSpec.outTrans, 
          inTrans = bSpec.inTrans,
          initial = bSpec.initial,
          final = Cons (newMode, bSpec.final),
          nextIdx = bSpec.nextIdx,
          id = bSpec.id
        }

  op BSpec.newTrans : BSpec -> Mode -> Mode -> TransSpec -> (BSpec * Transition)
  def BSpec.newTrans bSpec source target transSpec =
      let newTransition = {
          edge = Nat (bSpec.nextIdx,bSpec.id),
          source = source,
          target = target,
          transSpec = transSpec
        } in
      let newBSpec = {
          modes = bSpec.modes,
          transitions = Cons (newTransition, bSpec.transitions),
          outTrans = insert bSpec.outTrans (vertex source) newTransition,
          inTrans = insert bSpec.inTrans (vertex target) newTransition,
          initial = bSpec.initial,
          final = bSpec.final,
          nextIdx = bSpec.nextIdx + 1,
          id = bSpec.id
        } in
      (newBSpec,newTransition)

  op BSpec.addTrans : BSpec -> Transition -> BSpec
  def BSpec.addTrans bSpec transition = {
          modes = bSpec.modes,
          transitions = Cons (transition, bSpec.transitions),
          outTrans = insert bSpec.outTrans (vertex (source transition)) transition,
          inTrans = insert bSpec.inTrans (vertex (target transition)) transition,
          initial = bSpec.initial,
          final = bSpec.final,
          nextIdx = bSpec.nextIdx,
          id = bSpec.id
        }

  op BSpec.findTransList : CoAlg -> Mode -> List Transition
  def BSpec.findTransList coAlg mode =
    case coAlg of
      | [] -> []
      | (vrtx,transitions)::rest ->
          if Vrtx.eq? (vrtx, vertex mode) then
            transitions
          else
            findTransList rest mode

  op BSpec.outTrans : BSpec -> Mode -> List Transition
  def BSpec.outTrans bSpec mode = findTransList bSpec.outTrans mode

  op BSpec.inTrans : BSpec -> Mode -> List Transition
  def BSpec.inTrans bSpec mode = findTransList bSpec.inTrans mode

  op BSpec.initial : BSpec -> Mode
  def BSpec.initial bSpec = bSpec.initial

  op BSpec.final : BSpec -> List Mode
  def BSpec.final bSpec = bSpec.final

  def Vrtx.pp vertex =
    case vertex of
      | Nat (n,id) -> String.pp ("(" ^ (Nat.toString n) ^ "," ^ (Id.show id) ^ ")")
      | Pair (vertex,subst) ->
         ppConcat [
           String.pp "(",
           pp vertex,
           String.pp ",",
           pp subst,
           String.pp ")"
         ]

  op Vrtx.show : Vrtx.Vertex -> String
  def Vrtx.show vertex = ppFormat (pp vertex)

  def Edg.pp edge = 
    case edge of
      | Nat (n,id) -> String.pp ("(" ^ (Nat.toString n) ^ "," ^ (Id.show id) ^ ")")
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
  def Edg.eq? (e1,e2) =
    case (e1,e2) of
      | (Nat n1, Nat n2) -> n1 = n2
      | (Triple (e1,s1,t1), Triple (e2,s2,t2)) -> Edg.eq? (e1,e2) & Subst.eq? (s1,s2) & Subst.eq? (t1,t2)
      | _ -> false

  op Edg.show : Edg.Edge -> String
  def Edg.show edge = ppFormat (pp edge)

  op BSpec.ppEdge :
        ModeSpec
     -> BSpec
     -> (List Mode * Doc)
     -> Transition
     -> Env (List Mode * Doc)
  def BSpec.ppEdge baseModeSpec bSpec (visited,doc) transition =
    let
      def modeMember? modes mode =
        case modes of
          | [] -> false
          | elem::rest ->
              if Vrtx.eq? (vertex elem, vertex mode) then
                true
              else
                modeMember? rest mode
    in {
      newDoc <-
        return (ppConcat [
                  if doc = ppNil then ppNil else ppCons doc ppBreak, % do what ppSep does. could be cleaner
                  String.pp "(",
                  pp transition.edge,
                  String.pp " : ",
                  pp transition.source.vertex,
                  String.pp " -> ",
                  pp transition.target.vertex,
                  String.pp ") +-> ",
                  ppBreak,
                  String.pp "    ",
                  ppNest 4 (ppConcat [
                    pp (subtract (modeSpec transition.transSpec) baseModeSpec),
                    ppBreak,
                    String.pp "changed=",
                    pp (changedVars (backMorph transition.transSpec))
                  ])
               ]);
      if modeMember? visited (transition.target) then
        return (visited,newDoc)
      else
        ppFrom baseModeSpec bSpec transition.target visited newDoc
    }

  op Mode.member? : List Mode -> Mode -> Boolean
  def Mode.member? modes mode =
    case modes of
      | [] -> false
      | (x::y) -> Mode.eq? (x, mode) or Mode.member? y mode
  
  op ModeList.pp : List Mode -> Doc
  def ModeList.pp modes =
    ppConcat [
      String.pp "[",
      ppSep (String.pp "[") (map (fn mode -> Vrtx.pp (vertex mode)) modes),
      String.pp "]"
    ]

  op BSpec.ppFrom :
       ModeSpec
    -> BSpec
    -> Mode
    -> List Mode
    -> Doc
    -> Env (List Mode * Doc)
  def ppFrom baseModeSpec bSpec src visited doc = {
      visited <- return (Cons (src,visited));
      SpecCalc.foldM (ppEdge baseModeSpec bSpec) (visited,doc) (outTrans bSpec src) 
    }
endspec
