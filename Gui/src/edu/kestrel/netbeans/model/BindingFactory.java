/*
 * BindingFactory.java
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

/**
 *
 */
public interface BindingFactory {
    public Binding.Source bindSource(SourceElement impl);
    public Binding.Spec bindSpec(SpecElement impl);
    public Binding.Sort bindSort(SortElement impl);
    public Binding.Op bindOp(OpElement impl);
}

