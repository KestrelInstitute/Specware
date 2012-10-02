/*
 * SortB.java
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

import java.io.*;
import javax.swing.text.*;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.model.Element;

class SortB extends Member implements Binding.Sort {
    private static final boolean DEBUG = false;
    
    public SortB(SortElement el, SourceText s) {
        super(el, s);
    }
    
    private SortElement cloneSort() {
        return (SortElement)cloneElement();
    }
    
    protected Element cloneElement() {
        SortElement el = new SortElement();
        copyProperties(el);
        return el;
    }
    
    protected void copyProperties(SortElement target) {
        SortElement my = (SortElement)getElement();
        try {
            target.setName(my.getName());
            target.setParameters(my.getParameters());
        } catch (SourceException ex) {
            // should NOT happen
        }
    }
    
    /**
     * Requests a change of member's name.
     */
    public void changeName(final String name) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        
	super.changeName(name);
    }
    
    /** Changes parameter list for the service.
     */
    public void changeParameters(String[] params) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        SortElement el = (SortElement)cloneElement();
        el.setParameters(params);
        regenerateHeader(el);
    }
    
    /**
     * Updates the storage binding object from an external SourceText.
     */
    public void updateFrom(Binding other) {
    }
    
    private SortElement getSort() {
        return (SortElement)getElement();
    }

    private void dumpSortBounds() {
        if (!DEBUG)
            return;
        System.err.println("Dumping bounds for: " + getSort() + "(" + this + ")"); // NOI18N
        System.err.println("whole = " + wholeBounds); // NOI18N
        System.err.println("------------------------------------");
    }
    
}
