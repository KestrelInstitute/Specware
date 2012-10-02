package edu.kestrel.netbeans.nodes;

/** Orders and filters members in a colimit element node.
* <p>The semantics are very similar to those of <code>SourceElementFilter</code>.
*
*/
public class ColimitElementFilter extends SourceElementFilter {

    /** Specifies a child representing a diagram. */
    public static final int     DIAGRAM = 1;

    /** Does not specify a child type. */
    public static final int     ALL = DIAGRAM;
                                      

    /** Default order and filtering.
    * Places all diagrams together in one block.
    */
    public static final int[]   DEFAULT_ORDER = { DIAGRAM };

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
