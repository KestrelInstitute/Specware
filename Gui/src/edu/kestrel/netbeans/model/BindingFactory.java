/*
 * BindingFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
    public Binding.Claim bindClaim(ClaimElement impl);
}

