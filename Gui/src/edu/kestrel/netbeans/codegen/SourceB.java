/*
 * SourceB.java
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

import java.util.*;

import javax.swing.text.Position;
import javax.swing.text.StyledDocument;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import org.openide.src.MultiPropertyChangeEvent;

/**
 */
class SourceB extends ElementBinding implements Binding.Source, TextBinding.Container {
    /** Support for containment of specs.
     */
    ContainerSupport    container;
    
  //ContainerSupport    specContainer;
    
    public SourceB(SourceElement src, SourceText s) {
        super(src, s);
        //specContainer = new ContainerSupport(s, this);
    }

    public TextBinding.Container getContainer() {
        return this;
    }
    
    public boolean isEmpty() {
        return container == null ||  container.isEmpty();
    }
    
    public void updateChildren(Collection c) {
        if (container == null && c.isEmpty())
            return;
        initializeContainer();
        container.updateChildren(c);
    }
    

    protected Element cloneElement() {
        return null;
    }
    
//     public Binding.Container getSpecSection() {
//         return specContainer;
//     }
    
     public ElementBinding findBindingAt(int pos) {
       ElementBinding b = super.findBindingAt(pos);
       if (b == this) {
	 ElementBinding b2 = container.findBindingAt(pos);
	 if (b2 != null)
	   return b2;
       }
       return b;
     }
    
    /**
     * The operation does nothing, because the source cannot be removed ;-)
     */
    public void remove() throws SourceException {
    }
    
    public void updateBounds(int kind, PositionBounds b) {
        super.updateBounds(kind, b);
    }

    /**
     * This method should return PositionBounds of the maximum possible
     * extent for a container.
     */
    PositionBounds findContainerBounds(TextBinding.Container cont) {
	return bodyBounds;

	/*
         int begin = 0, end = -1;
        
//         if (cont == specContainer) {
//             begin = 0;
//         } else {
// 	  Util.log("SourceB container not equal to specContainer \n cont = "+cont+
// 					   "\n specCont = "+specContainer+
// 					   "\n Throwing IllegalArgumentException");	    
//             throw new IllegalArgumentException(cont.toString());
//         }
         if (end == -1) {
             StyledDocument doc = source.getEditorSupport().getDocument();
             if (doc == null)
                 end = begin;
             else
                 end = doc.getLength();
         }
        
         PositionBounds b =  new PositionBounds(source.createPos(begin, Position.Bias.Forward),
						source.createPos(end, Position.Bias.Backward));
         return b;
	*/
    }
    
    
    /* ============== CONTAINER MANAGEMENT METHODS ================= */
    
    public boolean canInsertAfter(Binding b) {
        if (container == null) {
            if (bodyBounds == null) {
                return true;
            } else {
                return source.canWriteInside(bodyBounds);
            }
        }
        return container.canInsertAfter(b);
    }
    
    /** The map contains mapping from target places to their new contents.
     */
    public void reorder(Map fromToMap) throws SourceException {
        container.reorder(fromToMap);
    }
    
    /** Replaces the slot contents with another element (different type permitted ?)
     */
    public void replace(Binding oldBinding, Binding newBinding) throws SourceException {
        container.replace(oldBinding, newBinding);
    }
    
    public void changeMembers(MultiPropertyChangeEvent evt) throws SourceException {
        if (container == null) {
            int etype = evt.getEventType();
            if (etype == evt.TYPE_ADD || etype == evt.TYPE_COMPOUND)
                initializeContainer();
            else
                return;
        }
        container.changeMembers(evt);
    }
    
    /**
     * Initializes a new binding for the element so the element is stored after the
     * `previous' binding, if that matters to the binding implementation.
     * @param toInitialize the binding that is being initialized & bound to the storage.
     * @param previous marker spot, the binding that should precede the new one.
     */
    public void insert(Binding toInitialize,Binding previous) throws SourceException {
        initializeContainer();
        container.insert(toInitialize, previous);
    }
    
    protected void initializeContainer() {
        if (container != null)
            return;
        container = new ContainerSupport(this.source, this);
    }
    
    
}
