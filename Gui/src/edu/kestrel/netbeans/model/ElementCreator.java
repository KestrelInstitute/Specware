/*
 * ElementCreator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.3  2003/02/16 02:14:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
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
    public DefElementImpl    createDef(SpecElement parent);
    public ClaimElementImpl  createClaim(SpecElement parent);
    public ImportElementImpl createImport(SpecElement parent);
}
