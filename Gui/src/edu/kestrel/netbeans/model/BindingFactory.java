/*
 * BindingFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/03/14 04:14:00  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:12:52  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:14:02  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:53  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 *
 */
public interface BindingFactory {
    public Binding.Source bindSource(SourceElement impl);
    public Binding.Spec bindSpec(SpecElement impl);
    public Binding.Sort bindSort(SortElement impl);
    public Binding.Op bindOp(OpElement impl);
    public Binding.Def bindDef(DefElement impl);
    public Binding.Claim bindClaim(ClaimElement impl);
    public Binding.Import bindImport(ImportElement impl);
    public Binding.Proof bindProof(ProofElement impl);
    public Binding.Morphism bindMorphism(MorphismElement impl);
}

