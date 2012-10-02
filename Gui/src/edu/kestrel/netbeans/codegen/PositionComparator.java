/*
 * PositionComparator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import edu.kestrel.netbeans.Util;
import org.openide.text.PositionRef;
import org.openide.text.PositionBounds;

import edu.kestrel.netbeans.Util;

/**
 * Helps with sorting elements according to their positions.
 *
 */
class PositionComparator implements java.util.Comparator {
    public int compare(java.lang.Object p1, java.lang.Object p2) {
        if (p1 instanceof Integer) {
            return comparePosToBinding((Integer)p1, (ElementBinding)p2);
        } else if (p2 instanceof PositionRef) {
            return -comparePosToBinding((Integer)p2, (ElementBinding)p1);
        }
        ElementBinding b1 = (ElementBinding)p1;
        ElementBinding b2 = (ElementBinding)p2;
	//Util.log("*** PositionComparator.compare(): b1="+Util.print(b1)+", b2="+Util.print(b2));

        return b1.wholeBounds.getBegin().getOffset() -
               b2.wholeBounds.getBegin().getOffset();
    }
    
    private int comparePosToBinding(Integer iPos, ElementBinding b) {
        int off = iPos.intValue();
        PositionBounds w = b.wholeBounds;
        if (w.getBegin().getOffset() <= off &&
            w.getEnd().getOffset() > off)
            return 0;
        return off - w.getBegin().getOffset();
    }
    
    public boolean equals(java.lang.Object p1) {
        return (p1 instanceof PositionComparator);
    }
}
