/*
 * DefaultWrapper.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
    
}
