/*
 * ImportB.java
 *
 * Created on February 17, 2003, 6:16 PM
 */

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
class ImportB extends Member implements Binding.Import {
    private static final boolean DEBUG = false;
    
    public ImportB(ImportElement el, SourceText s) {
        super(el, s);
    }
    
    private ImportElement cloneImport() {
        return (ImportElement)cloneElement();
    }
    
    protected Element cloneElement() {
        ImportElement el = new ImportElement();
        copyProperties(el);
        return el;
    }
    
    protected void copyProperties(ImportElement target) {
        ImportElement my = (ImportElement)getElement();
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
    
    private ImportElement getImport() {
        return (ImportElement)getElement();
    }

    private void dumpImportBounds() {
        if (!DEBUG)
            return;
        System.err.println("Dumping bounds for: " + getImport() + "(" + this + ")"); // NOI18N
        System.err.println("whole = " + wholeBounds); // NOI18N
        System.err.println("------------------------------------");
    }
    
}
