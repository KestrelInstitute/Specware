/*
 * SourceCookie.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:46  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.cookies;

import java.util.NoSuchElementException;

import org.openide.nodes.Node;
import org.openide.cookies.EditorCookie;

import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.SourceElement;

/** A cookie for obtaining a source hierarchy from data objects.
*
*/
public interface SourceCookie extends Node.Cookie {

    /** Returns a source element describing the hierarchy
    * of the source.
    *
    * @return the element
    */
    public SourceElement getSource ();

    /** Extended source cookie permitting for bidirectional translation with Swing text elements.
    */
    public interface Editor extends SourceCookie, EditorCookie {
        /** Translate a source element to text.
        *
        * @param element an element from the source hierarchy
        * @return a text element
        */
        public javax.swing.text.Element sourceToText(Element element);

        /** Translate a text element to a source element, if it is possible to do so.
        *
        * @param element a text element
        * @return the element from the source hierarchy
        * @exception NoSuchElementException if the text element doesn't match
        *  any element from the source hierarchy
        */
        public Element textToSource(javax.swing.text.Element element)
        throws NoSuchElementException;

        /** Find the element at the specified offset in the document.
        * @param offset The position of the element
        * @return the element at the position.
        */
        public Element findElement(int offset);
    }
}
