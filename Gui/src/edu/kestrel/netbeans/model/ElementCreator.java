/*
 * ElementCreator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:55  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

public interface ElementCreator {
    public SourceElementImpl createSource();
    public SpecElementImpl   createSpec(Element parent);
    public SortElementImpl   createSort(SpecElement parent);
    public OpElementImpl     createOp(SpecElement parent);
    public ClaimElementImpl  createClaim(SpecElement parent);
}
