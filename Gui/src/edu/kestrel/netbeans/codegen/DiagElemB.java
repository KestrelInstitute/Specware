package edu.kestrel.netbeans.codegen;

import java.io.*;
import javax.swing.text.*;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.model.Element;

/**
 *
 * @author  weilyn
 */
class DiagElemB extends Member implements Binding.DiagElem {
    private static final boolean DEBUG = false;
    
    public DiagElemB(DiagElemElement el, SourceText s) {
        super(el, s);
    }
    
    private DiagElemElement cloneDiagElem() {
        return (DiagElemElement)cloneElement();
    }
    
    protected Element cloneElement() {
        DiagElemElement el = new DiagElemElement();
        copyProperties(el);
        return el;
    }
    
    protected void copyProperties(DiagElemElement target) {
        DiagElemElement my = (DiagElemElement)getElement();
        try {
            target.setName(my.getName());
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
       
    /**
     * Updates the storage binding object from an external SourceText.
     */
    public void updateFrom(Binding other) {
    }
    
    private DiagElemElement getDiagElem() {
        return (DiagElemElement)getElement();
    }

    private void dumpDiagElemBounds() {
        if (!DEBUG)
            return;
        System.err.println("Dumping bounds for: " + getDiagElem() + "(" + this + ")"); // NOI18N
        System.err.println("whole = " + wholeBounds); // NOI18N
        System.err.println("------------------------------------");
    }
    
}
