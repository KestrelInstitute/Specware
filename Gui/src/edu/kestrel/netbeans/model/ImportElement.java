/*
 * ImportElement.java
 *
 * Created on February 17, 2003, 5:34 PM
 */

package edu.kestrel.netbeans.model;

import java.io.*;
import java.beans.PropertyChangeEvent;

import org.openide.util.NbBundle;

import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;

/**
 *
 * @author  weilyn
 */
public final class ImportElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat IMPORT_FORMAT =
        new ElementFormat("import {n}"); // NOI18N

    /** Create a new import element represented in memory.
     */
    public ImportElement() {
        this(new Memory(), null);
    }

    /** Create a new import element.
     * @param impl the pluggable implementation
     * @param parent parent of this import, or <code>null</code>
     */
    public ImportElement(ImportElement.Impl impl, SpecElement spec) {
        super(impl, spec);
    }

    final ImportElement.Impl getImportImpl() {
        return (ImportElement.Impl) impl;
    }

    /** Clone the import element.
    * @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new ImportElement (new Memory (this), null);
    }

    /** Set the name of this member.
     * @param name the name
     * @throws SourceException if impossible
     */
    public final void setName(String name) throws SourceException {
        super.setName(name);
    }

    public synchronized MemberElement getUnitImported() {
	return getImportImpl().getUnitImported();
    }
        
    public synchronized void setUnitImported(MemberElement unit) throws SourceException {
	getImportImpl().setUnitImported(unit);
    }
    
    /* Prints the element into the element printer.
     * @param printer The element printer where to print to
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markImport(this, printer.ELEMENT_BEGIN);

        printer.markImport(this, printer.HEADER_BEGIN);
        printer.print(IMPORT_FORMAT.format(this));
        printer.markImport(this, printer.HEADER_END);

        printer.markImport(this, printer.ELEMENT_END);
    }

    /** Implementation of a import element.
     * @see ImportElement
     */
    public interface Impl extends MemberElement.Impl {
        
        public MemberElement getUnitImported();
        
        public void setUnitImported(MemberElement unit) throws SourceException;

    }

    static class Memory extends MemberElement.Memory implements Impl {
        MemberElement unitImported;

        Memory() {
        }

        /** Copy constructor.
	 * @param import the object to read values from
	 */
        Memory (ImportElement importElem) {
            super (importElem);
        }
        
        public synchronized void setName(String name) {
            this.name = name;
        }
    
        /** Get the imported unit for the import
         * @return the unit
         *
         */
        public synchronized MemberElement getUnitImported() {
            return unitImported;
        }
        
        /** Set the unit imported by the import
         * @param unit the imported unit
         * @throws SourceException if impossible
         *
         */
        public synchronized void setUnitImported(MemberElement unit) throws SourceException {
            MemberElement old = this.unitImported;
            this.unitImported = unit;
            PropertyChangeEvent event = new PropertyChangeEvent(this, ElementProperties.PROP_UNIT_IMPORTED,
								old, this.unitImported);
            firePropertyChange(event);
        }        
        
	public void copyFrom (ImportElement copyFrom) { 
	    try {
                if (copyFrom.getUnitImported() instanceof MemberElement) {
                    setUnitImported((MemberElement)copyFrom.getUnitImported()); 
                }
	    } catch (SourceException ex) {}

	}        
    }
}
