/*
 * OpB.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:43  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.util.*;
import java.lang.reflect.Modifier;

import javax.swing.text.Position;
import javax.swing.text.StyledDocument;

import org.openide.text.CloneableEditorSupport;
import org.openide.text.PositionBounds;
import org.openide.text.PositionRef;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;

/**
 */
class OpB extends Member implements Binding.Op {
    
    
    public OpB(OpElement el, SourceText s) {
        super(el, s);
    }
    
    public void create(PositionBounds b) throws SourceException {
        super.create(b);
    }
    
    private OpElement cloneOp() {
        OpElement el = new OpElement();
        copyProperties(el);
        return el;
    }
        
    protected Element cloneElement() {
        Element orig = getElement();
        OpElement el = new OpElement();
        copyProperties(el);
        return el;
    }
    
    protected void copyProperties(OpElement target) {
        OpElement my = (OpElement)getElement();
        try {
            target.setName(my.getName());
            target.setSort(my.getSort());
        } catch (SourceException ex) {
            // should NOT happen
        }
    }
    
    
    /** Changes sort for the op.
     */
    public void changeSort(String sort) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        OpElement el = (OpElement)cloneElement();
        el.setSort(sort);
        regenerateHeader(el);
    }
    
    /**
     * Updates the storage binding object from an external SourceText.
     */
    public void updateFrom(Binding other) {
    }
    
}
