/*
 * ElementPrinter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/03/14 04:12:30  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 17:59:36  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:12:14  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:37:44  weilyn
 * Added support for claims.
 *
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
    /** Mark a notable point in a def element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markDef(DefElement element, int what)
    throws ElementPrinterInterruptException;
    /** Mark a notable point in a claim element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markClaim(ClaimElement element, int what)
    throws ElementPrinterInterruptException;
    /** Mark a notable point in an import element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markImport(ImportElement element, int what)
    throws ElementPrinterInterruptException;

    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markProof(ProofElement element, int what)
    throws ElementPrinterInterruptException;    
    
    /** Mark a notable point in a class element.
    * @param element the element
    * @param what which point
    * @exception ElementPrinterInterruptException - see class description
    */
    public void markMorphism(MorphismElement element, int what)
    throws ElementPrinterInterruptException;        
}
