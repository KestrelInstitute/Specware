(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  %% Note that EquivalenceClass, QuotientSet, and equiv are all 
  %% parameterized in unison on the same element type.  We currently 
  %% cannot express that polymorphically.
  %%
  %% On the other hand, no one currently checks the equiv condition, 
  %% so one might be tempted to hack a polymorphic version that's 
  %% useable but logically sloppy.

  type Element
  type EquivalenceClass  
  type QuotientSet       % not necessarily implemented as a set per se

  op equiv        : Element          * Element          -> Bool
  op class_member : Element          * EquivalenceClass -> Bool
  op qset_member  : EquivalenceClass * QuotientSet      -> Bool

  axiom connected is fa (z : EquivalenceClass)
                     fa (x : Element, y : Element)
		     class_member(x,z) && class_member(y,z) => equiv(x,y)

  axiom disjoint is fa (z : QuotientSet) 
                    fa (x : EquivalenceClass, y : EquivalenceClass)
		    fa (xx : Element, yy : Element)
		    qset_member(x,z) && qset_member(y,z) && ~(x=y) =>
		    class_member(xx,x) && class_member (yy,y) => ~(equiv(xx,yy))

endspec



