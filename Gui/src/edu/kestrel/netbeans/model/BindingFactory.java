/*
 * BindingFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
}

