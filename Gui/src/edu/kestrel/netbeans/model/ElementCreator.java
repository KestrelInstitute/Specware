/*
 * ElementCreator.java
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

public interface ElementCreator {
    public SourceElementImpl createSource();
    public SpecElementImpl   createSpec(Element parent);
    public SortElementImpl   createSort(SpecElement parent);
    public OpElementImpl     createOp(SpecElement parent);
}
