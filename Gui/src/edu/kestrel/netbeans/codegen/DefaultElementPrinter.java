/*
 * DefaultElementPrinter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.6  2003/03/29 03:13:53  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:12:30  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 17:59:31  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:12:13  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:37:43  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:40  gilham
 * Initial version.
 *
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

    /** Mark a notable point in a def element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markDef(DefElement element, int what)
	throws ElementPrinterInterruptException {
    }

    /** Mark a notable point in a claim element.
     * @param element the element
     * @param what which point
     * @exception ElementPrinterInterruptException - see class description
     *
     */
    public void markClaim(ClaimElement element, int what) 
        throws ElementPrinterInterruptException {
    }    
    
    /** Mark a notable point in an import element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markImport(ImportElement element, int what)
	throws ElementPrinterInterruptException {
    }

    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markProof(ProofElement element, int what)
	throws ElementPrinterInterruptException {
    }
 
    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markMorphism(MorphismElement element, int what)
	throws ElementPrinterInterruptException {
    }   
    
    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markDiagram(DiagramElement element, int what)
	throws ElementPrinterInterruptException {
    }    

    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markColimit(ColimitElement element, int what)
	throws ElementPrinterInterruptException {
    }
    
}
