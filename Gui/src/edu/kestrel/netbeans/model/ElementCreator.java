/*
 * ElementCreator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.9  2003/07/05 07:46:37  lambert
 * *** empty log message ***
 *
 * Revision 1.8  2003/04/23 01:14:38  weilyn
 * BindingFactory.java
 *
 * Revision 1.7  2003/04/01 02:29:37  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.6  2003/03/29 03:13:56  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:14:01  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:12:57  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:14:03  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:39:29  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:01:55  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

public interface ElementCreator {
    public SourceElementImpl        createSource();
    public SpecElementImpl          createSpec(Element parent);
    public SortElementImpl          createSort(SpecElement parent);
    public OpElementImpl            createOp(SpecElement parent);
    public DefElementImpl           createDef(SpecElement parent);
    public ClaimElementImpl         createClaim(SpecElement parent);
    public ImportElementImpl        createImport(SpecElement parent);
    public ProofElementImpl         createProof(Element parent);
    public MorphismElementImpl      createMorphism(Element parent);
    public DiagramElementImpl       createDiagram(Element parent);
    public ColimitElementImpl       createColimit(Element parent);
    //public UnitIdElementImpl           createUnitId(Element parent);
    public DiagElemElementImpl      createDiagElem(DiagramElement parent);
}
