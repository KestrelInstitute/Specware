/*
 * DefaultWrapper.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:16  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import edu.kestrel.netbeans.model.*;

/**
 *
 */
public class DefaultWrapper implements WrapperFactory {
    private static WrapperFactory instance;
    
    public synchronized static WrapperFactory getInstance() {
        if (instance != null)
            return instance;
        return instance = new DefaultWrapper();
    }
    
    /* ----------------- wrapper factory methods --------------------- */
    public SpecElement wrapSpec(MemberElement.Impl theImpl, Element parent) {
        return new SpecElement(theImpl, parent);
    }
    
    public SortElement wrapSort(SortElement.Impl theImpl, Element parent) {
        return new SortElement(theImpl, (SpecElement)parent);
    }
    
    public OpElement wrapOp(OpElement.Impl theImpl, Element parent) {
        return new OpElement(theImpl, (SpecElement)parent);
    }
    
    public ClaimElement wrapClaim(ClaimElement.Impl theImpl, Element parent) {
        return new ClaimElement(theImpl, (SpecElement)parent);
    }    
    
}
