/*
 * ElementNodeFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/02/13 19:42:09  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:07  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import org.openide.nodes.Node;

import edu.kestrel.netbeans.model.*;

/** A factory used to create
* instances of hierarchy node implementations.
* Loaders that use the element hierarchy
* should implement this factory
* so as to provide their own implementations of hierarchy element nodes.
* @see ClassChildren
* @see SourceChildren
*
*/
public interface ElementNodeFactory {

    /** Make a node representing a spec.
    * @param element the spec
    * @return a spec node instance
    */
    public Node createSpecNode (SpecElement element);

    /** Make a node representing a sort.
    * @param element the sort
    * @return a sort node instance
    */
    public Node createSortNode (SortElement element);

    /** Make a node representing a op.
    * @param element the op
    * @return a op node instance
    */
    public Node createOpNode (OpElement element);

    /** Make a node representing a def.
    * @param element the def
    * @return a def node instance
    */
    public Node createDefNode (DefElement element);

    /** Make a node representing a claim.
    * @param element the claim
    * @return a claim node instance
    */
    public Node createClaimNode (ClaimElement element);

    /** Make a node indicating that the creation of children
    * is still under way.
    * It should be used when the process is slow.
    * @return a wait node
    */
    public Node createWaitNode ();

    /** Make a node indicating that there was an error creating
    * the element children.
    * @return the error node
    */
    public Node createErrorNode ();

}
