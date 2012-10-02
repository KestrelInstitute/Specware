package edu.kestrel.netbeans.nodes;

/** Orders and filters members in a diagram element node.
* <p>The semantics are very similar to those of <code>SourceElementFilter</code>.
*
*/
public class DiagramElementFilter extends SourceElementFilter {

    /** Specifies a child representing a diagElem. */
    public static final int     DIAG_ELEM = 1;
    /** Specifies a child representing a sort. */
//    public static final int     SORT = 2;
    /** Specifies a child representing an op. */
//    public static final int     OP = 4;
    /** Specifies a child representing a def . */
//    public static final int     DEF = 8;
    /** Specifies a child representing a claim . */
//    public static final int     CLAIM = 16;
    /** Does not specify a child type. */
    public static final int     ALL = DIAG_ELEM;// | SORT | OP | DEF | CLAIM;
                                      

    /** Default order and filtering.
    * Places all imports, sorts, ops, defs and claims together in one block.
    */
    public static final int[]   DEFAULT_ORDER = { DIAG_ELEM };// | SORT | OP | DEF | CLAIM};

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
