/*
 * ElementFactory.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.10  2003/06/23 18:00:18  weilyn
 * internal release version
 *
 * Revision 1.9  2003/04/23 01:16:24  weilyn
 * DiagElemInfo.java
 *
 * Revision 1.8  2003/04/01 02:29:41  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.7  2003/03/29 03:14:00  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.6  2003/03/14 04:15:31  weilyn
 * Added support for proof terms
 *
 * Revision 1.5  2003/02/18 18:10:12  weilyn
 * Added support for imports.
 *
 * Revision 1.4  2003/02/17 04:35:23  weilyn
 * Added support for expressions.
 *
 * Revision 1.3  2003/02/16 02:16:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:45:53  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:17  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.Collection;
import org.openide.src.*;

/** Builder interface for creating parse results.
 * This inteface allows a parser engine to create some items of implementation
 * unknown to the engine. The engine is provided with opaque Item reference
 * and can communicate with the factory using those references.
 * The ElementFactory is focused on creating and connecting MetaSlang Source
 * elements and provides the only way how to access MetaSlangDataLoader's internals from
 * the parser engine.
 */
public interface ElementFactory {
    /* ======================= Item creator methods ========================== */
    
    /** Creates an element for a spec.
	@param name Name of the spec.
    */
    public Item createSpec(String name);
    
    /** Creates an element for a sort.
	@param name Name of the sort
	@param params Formal parameters of the sort
    */
    public Item createSort(String name, String[] params);
    
    /** Creates an element for an op.
	@param name Name of the op
	@param sort Sort of the op
    */
    public Item createOp(String name, String sort);
    
    /** Creates an element for a def.
	@param name Name of the def
	@param params Formal parameters of the def
    */
    public Item createDef(String name, String[] params, String expression);
    
    /** Creates an element for a claim.
	@param name Name of the claim
        @param claimKind Kind of the claim
        @param expression Expression of the claim
    */
    public Item createClaim(String name, String claimKind, String expression);    
    
    /** Creates an element for an import.
	@param name Name of the import
    */
    public Item createImport(String name, ElementFactory.Item item);
    
    /** Creates an element for a proof.
	@param name Name of the proof.
    */
    public Item createProof(String name, String proofString);
    
    /** Creates an element for a morphism.
     *	@param name Name of the morphism.
     *  @param sourceUnit source unit of the morphism.
     *  @param targetUnit target unit of the morphism.
    */
    public Item createMorphism(String name, String sourceUnit, String targetUnit);

    /** Creates an element for a diagElem.
	@param name Name of the diagElem
    */
    public Item createDiagElem(String name);
    
    /** Creates an element for a diagram.
	@param name Name of the diagram.
    */
    public Item createDiagram(String name);

    /** Creates an element for a colimit.
	@param name Name of the colimit.
    */
    public Item createColimit(String name);
    
    /** Creates an element for a unitId.
	@param name Name of the unitId
	@param path string path of the unitId
    */
    //public Item createUID(String name, String path);    

    public void setParent(Collection children, Item parent);

    /** Binds two Items together in a parent-child relationship.
	@param child Child item to be inserted into the parent
	@param parent Parent item
    */
    public void setParent(Item child, Item parent);
    
    /** Sets bounds for the whole element. Begin is offset of first character of the element,
	end is the offset of the last one.
    */
    public void setBounds(Item item, int begin, int end);

    /** Sets bounds for the whole element. 
    */
    public void setBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn);

    /** Sets bounds for the body of the element.
     */
    public void setBodyBounds(Item item, int begin, int end);

    public void setBodyBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn);

    public void setHeaderBounds(Item item, int begin, int end);

    public void setHeaderBounds(Item item, int beginLine, int beginColumn, int endLine, int endColumn);

    /** Sets a documentation for the element.
	@param begin offset of doc comment start
	@param end offset of doc comment end
	@param text documentation comment content
    */
    public void setDocumentation(Item item, int begin, int end, String text);
    
    public void setDocumentation(Item item, int beginLine, int beginColumn, int endLine, int endColumn, String text);

    public void markError(Item item);

    /** Only marker interface
     */
    public interface Item {
    }
}
