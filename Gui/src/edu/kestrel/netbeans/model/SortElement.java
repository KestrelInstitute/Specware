/*
 * SortElement.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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

/** Describes a sort in a class.
 *
 */
public final class SortElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat SORT_FORMAT =
        new ElementFormat("sort {n}{p,\"(\",\")\"}"); // NOI18N

    /** Create a new sort element represented in memory.
     */
    public SortElement() {
        this(new Memory(), null);
    }

    /** Create a new sort element.
     * @param impl the pluggable implementation
     * @param parent parent of this sort, or <code>null</code>
     */
    public SortElement(SortElement.Impl impl, SpecElement spec) {
        super(impl, spec);
    }

    final SortElement.Impl getSortImpl() {
        return (SortElement.Impl) impl;
    }

    /** Clone the sort element.
    * @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new SortElement (new Memory (this), null);
    }

    /** Set the name of this member.
     * @param name the name
     * @throws SourceException if impossible
     */
    public final void setName(String name) throws SourceException {
        super.setName(name);
    }

    /** Get the value parameters of the Sort.
     * @return the parameters
     */
    public String[] getParameters() {
        return getSortImpl().getParameters();
    }

    /** Set the value parameters of the Sort.
     * @param parameters the parameters
     * @throws SourceException if impossible
     */
    public void setParameters(String[] parameters) throws SourceException {
        getSortImpl().setParameters(parameters);
    }

    /* Prints the element into the element printer.
     * @param printer The element printer where to print to
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markSort(this, printer.ELEMENT_BEGIN);

        printer.markSort(this, printer.HEADER_BEGIN);
        printer.print(SORT_FORMAT.format(this));
        printer.markSort(this, printer.HEADER_END);

        printer.markSort(this, printer.ELEMENT_END);
    }

    /** Implementation of a sort element.
     * @see SortElement
     */
    public interface Impl extends MemberElement.Impl {
        /** Get the value parameters of the Sort.
         * @return the parameters
         */
        public String[] getParameters();

        /** Set the value parameters of the Sort.
         * @param parameters the parameters
         * @throws SourceException if impossible
         */
        public void setParameters(String[] parameters) throws SourceException;

    }

    static class Memory extends MemberElement.Memory implements Impl {
        private String[] parameters;

        Memory() {
            parameters = null;
        }

        /** Copy constructor.
	 * @param sort the object to read values from
	 */
        Memory (SortElement sort) {
            super (sort);
            parameters = sort.getParameters();
        }

        /** Parameters of the variable.
	 * @return the parameters
	 */
        public String[] getParameters() {
            return parameters;
        }

        /** Setter for parameters of the variable.
	 * @param parameters the variable parameters
	 */
        public void setParameters(String[] parameters) {
            String[] old = this.parameters;
            this.parameters = parameters;
            firePropertyChange (PROP_PARAMETERS, old, parameters);
        }

    }
}
