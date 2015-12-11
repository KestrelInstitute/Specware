(*
     Spec for 4-valued Propositional Logic

        Top
       /   \
    False  True
       \   /
        Bot 

where Bot has the intended meaning of an undefined or unknown value,
and Top has the intended meaning of an overdefined or inconsistent
value.  Interestingly, the Meet, Join, and Complement of this Boolean
Algebra are different from the And, Or, and Not that we define below
to serve as interpretations of Propositional Logic.

*)
Logic4 = Logic4 qualifying
spec
  type Logic4 = |Bot |False |True |Top

  def Logic4Le (p:Logic4, q:Logic4): Bool =
    case p of
      | Bot -> true
      | False -> (case q of
                    | False -> true
                    | Top   -> true
                    | _     -> false)
      | True -> (case q of
                    | True -> true
                    | Top  -> true
                    | _    -> false)
      | Top  -> (case q of
                    | Top  -> true
                    | _    -> false)

  (* The lattice operators *)

  def Complement4(p:Logic4):Logic4 = 
    case p of
      | False -> True
      | True -> False
      | Bot -> Top
      | Top -> Bot

  def Join4(p:Logic4, q:Logic4):Logic4 = 
    case p of
      | Top -> Top
      | False -> (case q of
                    | False -> False
                    | True  -> Top
                    | Bot   -> False
                    | Top   -> Top)
      | True  -> (case q of
                    | False -> Top
                    | True  -> True
                    | Bot   -> True
                    | Top   -> Top)
      | Bot   -> q

% Join4 is monotone; has Bot as unit, Top as zero,...

  def Meet4(p:Logic4, q:Logic4):Logic4 = 
    case p of
      | Bot -> Bot
      | False -> (case q of
                    | False -> False
                    | True  -> Bot
                    | Top   -> False
                    | Bot   -> Bot)
      | True  -> (case q of
                    | False -> Bot
                    | True  -> True
                    | Top   -> True
                    | Bot   -> Bot)
      | Top   -> q



  (* The following operators are interpretations of the classical
  Propositional operators.  Interestingly they are different than the
  lattice operators... *)

  def Not4(p:Logic4):Logic4 = 
    case p of
      | False -> True
      | True -> False
      | Bot -> Bot
      | Top -> Top


  def Or4(p:Logic4, q:Logic4):Logic4 = 
    if p = Top  || q = Top then Top
    else 
    if p = True || q = True then True
    else
    if p=False && q=False then False
    else Bot

  def And4(p:Logic4, q:Logic4):Logic4 = 
    if p = Top  || q = Top then Top
    else 
    if p = False || q = False then False
    else
    if p=True && q=True then True
    else Bot

  def logic4toBool(l4v: Logic4): Bool =
    case l4v of
      | True -> true
      | False -> false
      | Bot -> false  % could make this polarity-sensitive
      | Top -> false  % could make this polarity-sensitive

  def BooltoLogic4(b: Bool): Logic4 =
    case b of
      | true -> True
      | false -> False

end-spec

M = morphism Semilattice#JoinSemilattice -> Logic4
      { A +-> Logic4,
        <= +-> Logic4Le,
        join +-> Join4}

ExLat = spec
import Semilattice#JoinSemilattice
end-spec

ExLat1 = ExLat[M]
