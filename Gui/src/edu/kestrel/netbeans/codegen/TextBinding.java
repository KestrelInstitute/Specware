/*
 * TextBinding.java
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

import edu.kestrel.netbeans.model.*;

/**
 * Interface for binding Elements.
 *
 */
public interface TextBinding extends Binding {
    /** Bounds for the whole element.
     */
    public static final int BOUNDS_ALL = 0;
    
    /** Bounds that will contain the header of a spec, a sort, or an op,
     */
    public static final int BOUNDS_HEADER = 2;
    
    /** Bounds for body of a spec/sort/op.
     * Undefined otherwise.
     */
    public static final int BOUNDS_BODY = 3;

    public static final int BOUNDS_SOURCE = 10;
    
    /**
     * Returns the associated meta-slang Element.
     */
    public Element getElement();
    
    /**
     * Returns the range occupied by the element.
     */
    public PositionBounds   getElementRange(boolean defRange);
    
    /**
     * Returns a container of the specified type, or null if there is not any.
     */
    public Container getContainer(String containerType);
    
    /**
     * Updates the specified bounds. Exact types can have element-specific meaning.
     */
    public void updateBounds(int boundsType, PositionBounds bounds);
    
    /** Extension for container bindings.
     */
    public interface Container extends Binding.Container {
        public void updateChildren(Collection members);
        public boolean isEmpty();
    }
    
    public interface ExElement extends javax.swing.text.Element {
        public org.openide.text.PositionRef getDeclarationStart();
    }
}
