/*
 * WrapperFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/03/14 04:14:02  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:13:08  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:14:04  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:30  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:05  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

public interface WrapperFactory {
    public SpecElement          wrapSpec(MemberElement.Impl theImpl, Element parent);
    public SortElement          wrapSort(SortElement.Impl theImpl, Element parent);
    public OpElement            wrapOp(OpElement.Impl theImpl, Element parent);
    public DefElement           wrapDef(DefElement.Impl theImpl, Element parent);
    public ClaimElement         wrapClaim(ClaimElement.Impl theImpl, Element parent);
    public ImportElement        wrapImport(ImportElement.Impl theImpl, Element parent);
    public ProofElement         wrapProof(MemberElement.Impl theImpl, Element parent);
    public MorphismElement      wrapMorphism(MemberElement.Impl theImpl, Element parent);
}

