/*
 * OpElement.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:00  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.io.*;
import java.beans.PropertyChangeEvent;

import org.openide.util.NbBundle;

import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;

/** Describes a Op for a mode.
 *
 */
public final class OpElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat OP_FORMAT =
        new ElementFormat("op {n} : {s}"); // NOI18N

    /** Create a new Op element represented in memory.
     */
    public OpElement() {
        this(new Memory(), null);
	//Util.log("OpElement creating new Op"); 
    }

    /** Create a new Op element.
     * @param impl the pluggable implementation
     * @param parent parent of this Op, or <code>null</code>
     */
    public OpElement(OpElement.Impl impl, SpecElement spec) {
        super(impl, spec);
	//Util.log("OpElement creating new Op spec = "+((spec == null) ? "Null spec" : spec.getName())); 
    }

    final OpElement.Impl getOpImpl() {
        return (OpElement.Impl) impl;
    }

    /** Clone the op element.
    * @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new OpElement (new Memory (this), null);
    }

    /** Get the value sort of the Op.
     * @return the sort
     */
    public String getSort() {
        return getOpImpl().getSort();
    }

    /** Set the value sort of the Op.
     * @param sort the sort
     * @throws SourceException if impossible
     */
    public void setSort(String sort) throws SourceException {
        // sanity check:
        if (sort == null) {
	    throwSourceException(NbBundle.getMessage(OpElement.class, "ERR_NullSort"));
        }
        getOpImpl().setSort(sort);
    }

    /* Prints the element into the element printer.
     * @param printer The element printer where to print to
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markOp(this, printer.ELEMENT_BEGIN);

        printer.markOp(this, printer.HEADER_BEGIN);
        printer.print(OP_FORMAT.format(this));
        printer.markOp(this, printer.HEADER_END);

        printer.markOp(this, printer.ELEMENT_END);
    }

    /** Implementation of a Op element.
     * @see OpElement
     */
    public interface Impl extends MemberElement.Impl {
        /** Get the value sort of the Op.
         * @return the sort
         */
        public String getSort();

        /** Set the value sort of the Op.
         * @param sort the sort
         * @throws SourceException if impossible
         */
        public void setSort(String sort) throws SourceException;

    }

    static class Memory extends MemberElement.Memory implements Impl {
        private String sort;

        Memory() {
        }

        /** Copy constructor.
	 * @param Op the object to read values from
	 * @param clazz declaring class to use
	 */
        Memory (OpElement op) {
            super (op);
            sort = op.getSort();
        }

        /** Sort of the op.
	 * @return the sort
	 */
        public String getSort() {
            return sort;
        }

        /** Setter for sort of the op.
	 * @param sort the sort
	 */
        public void setSort(String sort) {
            String old = this.sort;
            this.sort = sort;
            firePropertyChange (PROP_SORT, old, sort);
        }

    }
}
