/*
 * WrapperFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

public interface WrapperFactory {
    public SpecElement    wrapSpec(MemberElement.Impl theImpl, Element parent);
    public SortElement    wrapSort(SortElement.Impl theImpl, Element parent);
    public OpElement      wrapOp(OpElement.Impl theImpl, Element parent);
}

