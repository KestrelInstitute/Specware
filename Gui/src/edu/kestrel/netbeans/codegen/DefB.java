/*
 * DefB.java
 *
 * Created on February 15, 2003, 5:00 PM
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
class DefB extends Member implements Binding.Def {
    private static final boolean DEBUG = false;
    
    public DefB(DefElement el, SourceText s) {
        super(el, s);
    }
    
    private DefElement cloneDef() {
        return (DefElement)cloneElement();
    }
    
    protected Element cloneElement() {
        DefElement el = new DefElement();
        copyProperties(el);
        return el;
    }
    
    protected void copyProperties(DefElement target) {
        DefElement my = (DefElement)getElement();
        try {
            target.setName(my.getName());
            target.setParameters(my.getParameters());
            target.setExpression(my.getExpression());
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
    
    /** Changes parameter list for the def.
     */
    public void changeParameters(String[] params) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        DefElement el = (DefElement)cloneElement();
        el.setParameters(params);
        regenerateHeader(el);
    }
    
    /** Changes expression for the def.
     */
    public void changeExpression(String expression) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        DefElement el = (DefElement)cloneElement();
        el.setExpression(expression);
        regenerateHeader(el);
    }
    
    /**
     * Updates the storage binding object from an external SourceText.
     */
    public void updateFrom(Binding other) {
    }
    
    private DefElement getDef() {
        return (DefElement)getElement();
    }

    private void dumpDefBounds() {
        if (!DEBUG)
            return;
        System.err.println("Dumping bounds for: " + getDef() + "(" + this + ")"); // NOI18N
        System.err.println("whole = " + wholeBounds); // NOI18N
        System.err.println("------------------------------------");
    }
    
}
