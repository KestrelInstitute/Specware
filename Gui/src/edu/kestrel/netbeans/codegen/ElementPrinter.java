/*
 * ElementPrinter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:42  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import org.openide.src.ElementPrinterInterruptException;

import edu.kestrel.netbeans.model.*;

/** Prints elements in a textual form.

*/
public interface ElementPrinter {
    /** Beginning of whole element. */
    public static final int ELEMENT_BEGIN = 0;
    /** End of whole element. */
    public static final int ELEMENT_END = 1;

    /** Beginning of header.
    * For methods, constructors, and classes.
    */
    public static final int HEADER_BEGIN = 4;
    /** End of header.
    * For methods, constructors, and classes.
    */
    public static final int HEADER_END = 5;

    /** Beginning of body.
    * For initializers, methods, constructors, and classes.
    */
    public static final int BODY_BEGIN = 6;

    /** End of body.
    * For initializers, methods, constructors, and classes.
    */
    public static final int BODY_END = 7;

    /** Print some text.
    * @param text the text
    * @exception ElementPrinterInterruptException - see class description
    */
    public void print(String text) throws ElementPrinterInterruptException;

    /** Print a line of text with a newline.
    * @param text the text
    * @exception ElementPrinterInterruptException - see class description
    */
    public void println(String text) throws ElementPrinterInterruptException;

    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markSpec(SpecElement element, int what)
    throws ElementPrinterInterruptException;

    /** Mark a notable point in a sort element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markSort(SortElement element, int what)
    throws ElementPrinterInterruptException;
    /** Mark a notable point in a op element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markOp(OpElement element, int what)
    throws ElementPrinterInterruptException;

    /** Mark a notable point in a claim element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markClaim(ClaimElement element, int what)
    throws ElementPrinterInterruptException;

}
