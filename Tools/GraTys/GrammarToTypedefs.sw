(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  import translate TheGrammar by {theGrammar +-> theAnnotatedGrammar}
  import Metakeys

  op  isNonced : Set Notion
  def isNonced = (posNat? o length) /\ (fn(s) -> sub(s, 0) = #-)

  op  unnonced : Notion -> Notion
  def unnonced n = if isNonced n then substring(n, 1, length n) else n

  op  theGrammar : Grammar
  def theGrammar = mapMap(unnonced, id) theAnnotatedGrammar

  op  domGrammar : Set Notion
  def domGrammar = dom theGrammar
  type GNotion = (Notion | domGrammar)

  op  notions : Seq GNotion
  def notions = keys theGrammar

  op  usedNotions : Seq GNotion
  def usedNotions =
  let aa : Seq Element = flatten(flatten(associates theGrammar)) in
  let def usedN (e : Element) =
    case e of
       | Notion n    -> [n]
       | Tsymbol t   -> []
       | Option n    -> [n]
       | Seq n       -> [n]
       | ProperSeq n -> [n]
  in
  filter domGrammar (flatten (map usedN aa))

  op  declaredNonces : Seq GNotion
  def declaredNonces =
    map unnonced (filter isNonced (keys theAnnotatedGrammar))

  op  nonces : Seq GNotion
  def nonces =
    let nu = filter((fn c -> c = 1) o nOcc usedNotions) usedNotions in
    let def simple(n:GNotion) = length(theGrammar@n) = 1 in
    filter simple (nu ++ declaredNonces)

  type G2TDState =
    {tdefs : Seq Typedef, nonces : Seq Notion,
     skipped : Seq Notion, badSkips : Seq Notion,
     flags : {inAlt : Bool, inCompound : Bool, isTypor : Bool}}

  type S a = a * G2TDState
  type Arrow(a, b) = S a -> S b

  op  rhs : Arrow(GNotion, Type)
  def rhs(n, s) =
    let aa = theGrammar@n in
    if length aa = 1
    then alt(hd aa, s)
    else alts(aa, s)

  op  alt : Arrow(Alternative, Type)
  def alt(a, s) =
    if length a = 0
    then (writeLine("empty alternative"); (Typename "???EMPTY", s))
    else case hd a of
       | Tsymbol t -> (writeLine("terminal element");
                       (Typename("???" ^ t), s))
       | _         ->
          if length a = 1
          then element(hd a, s)
          else compound(a, s)

  op  element : Arrow(Element, Type)
  def element(e, s) =
    let siT = s << {flags = s.flags << {isTypor = true}} in
    let def dnT s = s << {flags = s.flags << {isTypor = false}} in
    case e of
       | Notion n    -> notion(n, s)
       | Tsymbol t   -> (writeLine("terminal element");
                        (Typename("???" ^ t), s))
       | Option n    -> let (t, s) = notion(n, siT) in (Option t,    dnT s)
       | Seq n       -> let (t, s) = notion(n, siT) in (Seq t,       dnT s)
       | ProperSeq n -> let (t, s) = notion(n, siT) in (ProperSeq t, dnT s)

  op  typor? : Set Element
  def typor? e =
    case e of
       | Option _    -> true
       | Seq _       -> true
       | ProperSeq _ -> true
       | _           -> false

  op  complicated : S Notion -> Bool
  def complicated(n, s) =
    let aa = theGrammar@n in
    if length aa = 1
    then
      let a = hd aa in
      let isCompound = length a ~= 1 in
      (s.flags.inCompound && isCompound)
      || (s.flags.isTypor && ~ isCompound && exists typor? a)
      || (s.flags.inAlt && s.flags.isTypor && isCompound)
    else true

  op  notion : Arrow(Notion, Type)
  def notion(n, s as {tdefs, nonces, skipped, badSkips, flags}) =
    if members nonces n && ~(complicated(n, s))
    then
      alt(hd(theGrammar@n), s)
    else
      let nonces = nonces without [n] in
      let badSkips = badSkips ++ (if members skipped n then [n] else []) in
      (Typename n, s << {nonces = nonces, badSkips = badSkips})

  op  lcName : Notion -> Name
  def lcName n = if length n < 1 then n else
    toString(toLowerCase(sub(n, 0))) ^ substring(n, 1, length n)

  op  fName : Element -> Name
  def fName e =
    case e of
       | Notion n    -> lcName n
       | Tsymbol t   -> (writeLine("terminal element"); "???" ^ t)
       | Option n    -> lcName n ^ toString #?
       | Seq n       -> lcName n ^ toString #s
       | ProperSeq n -> lcName n ^ toString #s

  (* The following function is a general list utility *)
  op  nub : [a] Seq a -> Seq a
  def nub xs =
    case xs of
       | Nil         -> Nil
       | Cons(x, xs) -> Cons(x, (nub(filter(fn y -> y ~= x) xs)))
  
  op  compound : Arrow(Alternative, Type)
  def compound(a, s) =
    let fnn = map fName a in
    let fni = map (fn x -> (x, 0)) (nub fnn) in
    let def pE(e : Element,
               ((fs, fni), s) : S(Seq Field * Map(Name, Nat))) =
      let fN = fName e in
      let siC = s << {flags = s.flags << {inCompound = true}} in
      let (ti, s) = element(e, siC) in
      let i =
        if nOcc fnn fN <= 1 || ~(dom fni fN)
	then 0
	else fni@fN + 1
      in 
      let ii = if i = 0 then "" else toString i in
      let s = s << {flags = s.flags << {inCompound = false}} in
      ((fs ++ [{fname= metakey fN ++ ii, tipo = ti}], mapUpdate(fni, fN, i)), s)
    in
    let ((fs, fni), s) = foldl pE (([], fni), s) a in
    (Record fs, s)

  op  ucName : Notion -> Name
  def ucName n = if length n < 1 then n else
    toString(toUpperCase(sub(n, 0))) ^ substring(n, 1, length n)

  op  cName : Element -> Name
  def cName e =
    case e of
       | Notion n    -> ucName n
       | Tsymbol t   -> ucName t
       | Option n    -> ucName n
       | Seq n       -> ucName n
       | ProperSeq n -> ucName n

  op  cNameCumRest : Alternative -> Name * Alternative
  def cNameCumRest a =
    if posNat?(length a)
    then
      let e = hd a in
      let ar = if embed? Tsymbol e then tl a else a in
      (cName e, ar)
    else
      (writeLine("empty alternative"); ("???", []))

  op  alts : Arrow(Seq Alternative, Type)
  def alts(aa, s) =
    let def pC(a : Alternative, (ss, s) : S(Seq Summand)) =
      let (cn, ar) = cNameCumRest a in
      let siA = s << {flags = s.flags << {inAlt = true}} in
      let (tiQ, s) =
        if length ar = 0
	then (None, siA)
	else
	  let (ti, s) = alt(ar, siA) in
	  (Some ti, s)
      in
      let s = s << {flags = s.flags << {inAlt = false}} in
      (ss ++ [{cname = cn, tipo? = tiQ}], s)
    in
    let (ss, s) = foldl pC ([], s) aa in
    (Sum ss, s)

  op  procNotion : S GNotion -> G2TDState
  def procNotion (n, s as {tdefs, nonces, skipped, badSkips, flags}) =
    if members nonces n
    then s << {skipped = Cons(n, skipped)}
    else let (rhs, s) = rhs(n, s) in
         s << {tdefs = tdefs ++ [{typename = n, rhs = rhs}],
               flags = {inAlt = false, inCompound = false, isTypor = false}}

  op  gToTd : G2TDState -> G2TDState
  def gToTd s = foldl procNotion s notions

  op  theTypedefs : Seq Typedef
  def theTypedefs =
    let s0 = 
      {tdefs = [], nonces = nonces, skipped = [], badSkips = [],
       flags = {inAlt = false, inCompound = false, isTypor = false}}
    in
    let s = gToTd s0 in
    s.tdefs

  import TypedefToText

  op  writeTheTypedefs : ()
  def writeTheTypedefs =
    writeText(typedefsToText theTypedefs)
    
endspec
