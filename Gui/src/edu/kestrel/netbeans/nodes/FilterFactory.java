/*
 * FilterFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.6  2003/03/29 03:13:58  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:14:21  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:06:38  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:15:04  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:42:09  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:08  gilham
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
* @see SourceChildren
*
*/
public class FilterFactory implements ElementNodeFactory {

    private ElementNodeFactory delegate;


    public final void attachTo( ElementNodeFactory factory ) {
        delegate = factory;
    }

    /** Make a node representing a spec
    * @param element the spec
    * @return a spec node instance
    */
    public Node createSpecNode (SpecElement element) {
        return delegate.createSpecNode( element );
    }

    /** Make a node representing a sort
    * @param element the sort
    * @return a sort node instance
    */
    public Node createSortNode (SortElement element) {
        return delegate.createSortNode( element );
    }

    /** Make a node representing a op.
    * @param element the op
    * @return a op node instance
    */
    public Node createOpNode (OpElement element) {
        return delegate.createOpNode( element );
    }

    /** Make a node representing a def
    * @param element the def
    * @return a def node instance
    */
    public Node createDefNode (DefElement element) {
        return delegate.createDefNode( element );
    }

    /** Make a node representing a claim.
     * @param element the claim
     * @return a claim node instance
     *
     */
    public Node createClaimNode(ClaimElement element) {
        return delegate.createClaimNode( element );
    }
    
    /** Make a node representing an import
    * @param element the import
    * @return a import node instance
    */
    public Node createImportNode (ImportElement element) {
        return delegate.createImportNode( element );
    }

    /** Make a node representing a proof
    * @param element the proof
    * @return a proof node instance
    */
    public Node createProofNode (ProofElement element) {
        return delegate.createProofNode( element );
    }

    /** Make a node representing a morphism
    * @param element the morphism
    * @return a morphism node instance
    */
    public Node createMorphismNode (MorphismElement element) {
        return delegate.createMorphismNode( element );
    }
    
    /** Make a node representing a diagram
    * @param element the diagram
    * @return a diagram node instance
    */
    public Node createDiagramNode (DiagramElement element) {
        return delegate.createDiagramNode( element );
    }

    /** Make a node representing a colimit
    * @param element the colimit
    * @return a proof node instance
    */
    public Node createColimitNode (ColimitElement element) {
        return delegate.createColimitNode( element );
    }

    /** Make a node indicating that the creation of children
    * is still under way.
    * It should be used when the process is slow.
    * @return a wait node
    */
    public Node createWaitNode () {
        return delegate.createWaitNode( );
    }

    /** Make a node indicating that there was an error creating
    * the element children.
    * @return the error node
    */
    public Node createErrorNode () {
        return delegate.createErrorNode( );
    }

}
