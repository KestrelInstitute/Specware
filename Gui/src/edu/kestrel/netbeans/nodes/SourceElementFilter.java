/*
 * SourceElementFilter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.6  2003/07/05 07:46:39  lambert
 * *** empty log message ***
 *
 * Revision 1.5  2003/04/23 01:15:44  weilyn
 * ClaimCustomizer.java
 *
 * Revision 1.4  2003/04/01 02:29:40  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.3  2003/03/29 03:13:59  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.2  2003/03/14 04:14:22  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:12  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.PropertyChangeListener;

/** Interface for filtering and ordering the items in the visual
* presentation of a source element.
* Used to control the children of a source element node.
* <p>Note that this does <em>not</em> fire events for changes
* in its properties; it is expected that a new filter will instead
* be created and applied to the source children.
*
* @see SourceElement
* @see SourceChildren
*/
public class SourceElementFilter {

    public static final int       SPEC = 1;
    public static final int       PROOF = 2;
    public static final int       MORPHISM = 4;
    public static final int       DIAGRAM = 8;
    public static final int       COLIMIT = 16;
    //public static final int       UnitId = 32;
    public static final int       ALL = SPEC | PROOF | MORPHISM | DIAGRAM | COLIMIT;
    /** Default order of the top-level element types in the hierarchy.
    * A list, each of whose elements is a bitwise disjunction of element types.
    * By default, only classes and interfaces are listed, and these together.
    */
    public static final int[]     DEFAULT_ORDER = { SPEC | PROOF | MORPHISM | DIAGRAM | COLIMIT };

    /** stores property value */
    private int[]                 order = null;


    /** Get the current order for elements.
    * @return the current order, as a list of bitwise disjunctions among element
    * types (e.g. {@link #SPEC}). If <code>null</code>, the {@link #DEFAULT_ORDER},
    * or no particular order at all, may be used.
    */
    public int[] getOrder () {
        return order;
    }

    /** Set a new order for elements.
    * Should update the children list of the source element node.
    * @param order the new order, or <code>null</code> for the default
    * @see #getOrder
    */
    public void setOrder (int[] order) {
        this.order = order;
    }

}
