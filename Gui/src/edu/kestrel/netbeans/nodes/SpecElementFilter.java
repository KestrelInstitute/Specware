/*
 * SpecElementFilter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/02/13 19:42:09  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:14  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

/** Orders and filters members in a spec element node.
* <p>The semantics are very similar to those of <code>SourceElementFilter</code>.
*
*/
public class SpecElementFilter extends SourceElementFilter {

    /** Specifies a child representing a sort. */
    public static final int     SORT = 1;
    /** Specifies a child representing an op. */
    public static final int     OP = 2;
    /** Specifies a child representing a def . */
    public static final int     DEF = 4;
    /** Specifies a child representing a claim . */
    public static final int     CLAIM = 8;
    /** Does not specify a child type. */
    public static final int     ALL = SORT | OP | DEF | CLAIM;
                                      

    /** Default order and filtering.
    * Places all sorts, ops, defs and claims together in one block.
    */
    public static final int[]   DEFAULT_ORDER = {SORT | OP | DEF | CLAIM};

    /** stores property value */
    private boolean             sorted = true;

    /** Test whether the elements in one element type group are sorted.
    * @return <code>true</code> if groups in getOrder () parameter are sorted, <code>false</code> 
    * to default order of elements
    */
    public boolean isSorted () {
        return sorted;
    }

    /** Set whether groups of elements returned by getOrder () should be sorted.
    * @param sorted <code>true</code> if so
    */
    public void setSorted (boolean sorted) {
        this.sorted = sorted;
    }
}
