/*
 * DefaultElementPrinter.java
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

import java.io.PrintWriter;

import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.model.*;

/** A trivial implementation of <code>ElementPrinter</code>.
* It is backed by the supplied <code>PrintWriter</code>,
* and by default just prints the text as supplied to that print
* writer.
* It does nothing for any of the mark methods, and never
* throws {@link ElementPrinterInterruptException}.
* Subclasses may use this as an adapter for <code>ElementPrinter</code>,
* typically providing a nontrivial body for one of the mark methods.
*
*/
public class DefaultElementPrinter implements ElementPrinter {
    /** The underlaying writer. */
    private PrintWriter writer;

    /** Create a printer.
    * @param writer the writer to send printed text to
    */
    public DefaultElementPrinter(PrintWriter writer) {
        this.writer = writer;
    }

    /* Prints the given text.
    * @param text The text to write
    */
    public void print(String text) {
        writer.print(text);
    }

    /* Prints the line. New-line character '\n' should be added.
    * @param text The line to write
    */
    public void println(String text) {
        writer.println(text);
    }

    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markSpec(SpecElement element, int what)
	throws ElementPrinterInterruptException {
    }

    /** Mark a notable point in a sort element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markSort(SortElement element, int what)
	throws ElementPrinterInterruptException {
    }

    /** Mark a notable point in a op element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markOp(OpElement element, int what)
	throws ElementPrinterInterruptException {
    }

}
