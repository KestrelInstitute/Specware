package edu.kestrel.netbeans.model;

import java.io.*;
import java.beans.PropertyChangeEvent;

import org.openide.util.NbBundle;

import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;

/** Describes a diagElem in a class.
 *
 */
public final class DiagElemElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat DIAG_ELEM_FORMAT =
        new ElementFormat("{n}"); // NOI18N

    /** Create a new diagElem element represented in memory.
     */
    public DiagElemElement() {
        this(new Memory(), null);
    }

    /** Create a new diagElem element.
     * @param impl the pluggable implementation
     * @param parent parent of this diagElem, or <code>null</code>
     */
    public DiagElemElement(DiagElemElement.Impl impl, DiagramElement diagram) {
        super(impl, diagram);
    }

    final DiagElemElement.Impl getDiagElemImpl() {
        return (DiagElemElement.Impl) impl;
    }

    /** Clone the diagElem element.
    * @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new DiagElemElement (new Memory (this), null);
    }

    /** Set the name of this member.
     * @param name the name
     * @throws SourceException if impossible
     */
    public final void setName(String name) throws SourceException {
        super.setName(name);
    }

    /* Prints the element into the element printer.
     * @param printer The element printer where to print to
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markDiagElem(this, printer.ELEMENT_BEGIN);

        printer.markDiagElem(this, printer.HEADER_BEGIN);
        printer.print(DIAG_ELEM_FORMAT.format(this));
        printer.markDiagElem(this, printer.HEADER_END);

        printer.markDiagElem(this, printer.ELEMENT_END);
    }

    /** Implementation of a diagElem element.
     * @see DiagElemElement
     */
    public interface Impl extends MemberElement.Impl {
    }

    static class Memory extends MemberElement.Memory implements Impl {

        Memory() {
        }

        /** Copy constructor.
	 * @param diagElem the object to read values from
	 */
        Memory (DiagElemElement diagElem) {
            super (diagElem);
        }

    }
}
