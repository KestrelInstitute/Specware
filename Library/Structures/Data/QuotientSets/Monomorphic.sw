spec
  %% Note that EquivalenceClass, QuotientSet, and equiv are all 
  %% parameterized in unison on the same element type.  We currently 
  %% cannot express that polymorphically.
  %%
  %% On the other hand, no one currently checks the equiv condition, 
  %% so one might be tempted to hack a polymorphic version that's 
  %% useable but logically sloppy.

  sort Element
  sort EquivalenceClass  
  sort QuotientSet       % not necessarily implemented as a set per se

  op equiv : Element * Element -> Boolean

  op class_member : Element * EquivalenceClass     -> Boolean
  op qset_member  : EquivalenceClass * QuotientSet -> Boolean

  axiom connected is fa (z : EquivalenceClass)
                     fa (x : Element, y : Element)
		     class_member(x,z) & class_member(y,z) => equiv(x,y)

  axiom disjoint is fa (z : QuotientSet) 
                    fa (x : EquivalenceClass, y : EquivalenceClass)
		    fa (xx : Element, yy : Element)
		    qset_member(x,z) & qset_member(y,z) & ~(x=y) =>
		    class_member(xx,x) & class_member (yy,y) => ~(equiv(xx,yy))

endspec



