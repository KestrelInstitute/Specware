/*
 * SpecElementFilter.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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
    /** Specifies a child representing a contraint . */
    public static final int     OP = 2;
    /** Does not specify a child type. */
    public static final int     ALL = SORT | OP;
                                      

    /** Default order and filtering.
    * Places all constants, input variables, external variables, internal variables, modes, and sorts together
    * in one block.
    */
    public static final int[]   DEFAULT_ORDER = {SORT | OP};

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
