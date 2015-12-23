(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*  
                     Polarity Algebra

  Polarities form a bounded lattice of size four.  As such it has a
  partial order, meet, join, plus univeral upper and lower bounds. It
  also has a complement operator that is slightly different than that
  needed to make the lattice a boolean algebra.

  The Polarity algebra serves as the abstraction domain for polarity
  analysis by abstract interpretation.

*)

spec

(* The polarity elements can be given the following interpretations:

    bot - unknown polarity
    pos - positive polarity, corresponding to monotonicity
    neg - negative polarity, corresponding to antimonotonicity
    top - mixed polarity, corresponding to substitutivity

 The partial order of the lattice induces the following structure:

      top (or 0 or =)
     /   \
   pos   neg
     \   /
      bot (or unknown)

*)

  type Polarity = |bot |pos |neg | top

  def polLe (p1:Polarity, p2:Polarity) : Bool =
    case p1 of
      | bot -> true
      | neg -> (case p2 of
                 | bot -> false
                 | pos -> false
                 | neg -> true
                 | top -> true)
      | pos -> (case p2 of
                 | bot -> false
                 | pos -> true
                 | neg -> false
                 | top -> true)
      | top -> if p2=top then true else false

% needed: partial order axioms
% needed: polGe

%----------------------------
% The join/lub of the lattice

  def polOr (p1:Polarity, p2:Polarity): Polarity =
    case p1 of
      | bot -> p2
      | pos -> (case p2 of
                 | bot -> pos
                 | pos -> pos
                 | neg -> top
                 | top -> top)
      | neg -> (case p2 of
                 | bot -> neg
                 | pos -> top
                 | neg -> neg
                 | top -> top)
      | top -> top

% needed: commutative monoid axioms
% needed: lub axiom 

%----------------------------
% The meet/glb of the lattice

  def polAnd (p1:Polarity, p2:Polarity): Polarity =
    case p1 of
      | bot -> bot
      | pos -> (case p2 of
                 | bot -> bot
                 | pos -> pos
                 | neg -> bot
                 | top -> pos)
      | neg -> (case p2 of
                 | bot -> bot
                 | pos -> bot
                 | neg -> neg
                 | top -> neg)
      | top -> p2

% needed: commutative monoid axioms
% needed: glb axiom 
% needed: distributive laws

%------------------------------------------------
% The complementation operator of the lattice ...

  def polNot (p:Polarity): Polarity =
    case p of
      | bot -> bot  % in a Boolean algebra, bot -> top
      | pos -> neg
      | neg -> pos
      | top -> top  % in a Boolean algebra, top -> bot

% is an involution
axiom polNot_involution is
  fa(p:Polarity) polNot(polNot(p)) = p

end-spec 
