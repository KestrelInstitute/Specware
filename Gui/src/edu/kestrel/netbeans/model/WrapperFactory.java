/*
 * WrapperFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:05  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

public interface WrapperFactory {
    public SpecElement    wrapSpec(MemberElement.Impl theImpl, Element parent);
    public SortElement    wrapSort(SortElement.Impl theImpl, Element parent);
    public OpElement      wrapOp(OpElement.Impl theImpl, Element parent);
    public ClaimElement   wrapClaim(ClaimElement.Impl theImpl, Element parent);
}

