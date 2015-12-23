(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
   import Fallible
   import Grammar

   (*
   op  pGacc : Grammar * Option Notion * Seq Alternative
               -> Seq String -> Fallible Grammar
   def pGacc(grammar, notion?, alts) = 
     case grtxt of
         | [] -> addRule(grammar, notion?, alts)
         | line :: rest ->
            let (grammar1, notion?1, alts1?) =
   (grammar, notion?, alts, grtxt) =
   *)

   type FGONSA =
       {g? : Fallible Grammar, n? : Option Notion, alts : Seq Alternative}

   op  inject_g? : Fallible Grammar -> FGONSA
   def inject_g? g? = {g? = g?, n? = None, alts = []}

   op  flushRule : FGONSA -> FGONSA
   def flushRule{g?, n?, alts} = inject_g? (case g? of
      | OK g -> (case n? of
            | Some n -> if dom g n
                       then KO("Notion `"++n++"' multiply defined")
                       else OK(g++[(n, alts)])
            | None -> g?)
      | KO _ -> g?)

   (* The following function is a general string utility *)
   type NonEmptyString = (String | posNat? o length)
   op  split : String -> Seq NonEmptyString
   def split =
     let def flushW (ssw as (ss: Seq NonEmptyString, w : String)) =
       if posNat?(length w) then (Cons(w, ss), "")
       else ssw
     in
     let def addChar(c : Char, ssw as (ss: Seq NonEmptyString, w : String)) =
       if c = #\s then flushW ssw else (ss, toString c ^ w)
     in
     project 1 o flushW o foldr addChar ([], "") o explode

   op  Char.<= infixl 20 : Char * Char -> Bool
   def Char.<= = (~) o embed? Greater o compare

   op  altparse : Seq NonEmptyString -> Alternative
   def altparse =
     let def addW(w : NonEmptyString, (alt : Seq Element, e : Element)) =
       case e of
          | Option _    -> (alt++[Option w],    Notion "")
          | Seq _       -> (alt++[Seq w],       Notion "")
          | ProperSeq _ -> (alt++[ProperSeq w], Notion "")
          | _           ->
                let c = sub(w, 0) in
                if #A Char.<= c && c Char.<= #Z then
                  (alt++[Notion w],  Notion "")
           else if c = #' then
                  (alt++[Tsymbol(substring(w, 1, length w))], Notion "")
           else if c = #! then
                (let t = substring(w, 1, length w) in
                      if t = "Option" then
                        (alt, Option "")
                 else if t = "Seq" then
                        (alt, Seq "")
                 else if t = "ProperSeq" then
                        (alt, ProperSeq "")
                 else (alt++[Option ("???"++w)], Notion ""))
           else (alt++[Option ("???"++w)], Notion "")
     in
     project 1 o foldl addW ([], Notion "")

   type NString = Int * String

   op  processLine : NString * FGONSA -> FGONSA
   def processLine((lino, line), fgonsa as {g?, n?, alts}) =
          if embed? KO g? then
            fgonsa
     else
          let ss = split line in
          if length ss = 0 then
            flushRule fgonsa
     else if sub(line,0) = #\s then
            case n? of
               | Some n -> fgonsa << {alts = alts++[altparse ss]}
               | None   -> fgonsa << {g? = KO("line "++(toString lino)++": Orphaned alternative")}
     else if length ss = 1 && sub(hd ss, length(hd ss)-1) = #: then
            let n = substring(hd ss, 0, length(hd ss)-1) in
              (flushRule fgonsa) << {n? = Some n}
     else inject_g?(KO("line `"++line++"' is improper"))
   
  (* The following function is a general list utility *)
  op numberFrom : [a] Int -> Seq a  -> Seq(Int * a)
  def numberFrom n x = case x of
     | Nil        -> Nil
     | Cons(a, y) -> Cons((n, a), numberFrom (n+1) y)

   op  parseGrammar : Seq String -> Fallible Grammar
   def parseGrammar =
     project g? o flushRule o
       foldl processLine (inject_g?(OK [])) o numberFrom 1 %pace EWD

endspec
