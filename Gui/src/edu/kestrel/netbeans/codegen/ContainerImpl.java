/*
 * ContainerImpl.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.util.Collection;

import org.openide.text.PositionBounds;
import org.openide.src.SourceException;

/**
 */
interface ContainerImpl extends TextBinding.Container {
    public ElementBinding findPrevious(ElementBinding ref);
    public ElementBinding findNext(ElementBinding ref);
    public ElementBinding findParent();
    public void updateChildren(Collection c);
    public void insertChild(ElementBinding n, ElementBinding previous, ElementBinding next) throws SourceException;
}

