/*
 * DefaultWrapper.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.9  2003/07/05 07:46:39  lambert
 * *** empty log message ***
 *
 * Revision 1.8  2003/04/23 01:16:24  weilyn
 * DiagElemInfo.java
 *
 * Revision 1.7  2003/04/01 02:29:41  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.6  2003/03/29 03:14:00  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.5  2003/03/14 04:15:31  weilyn
 * Added support for proof terms
 *
 * Revision 1.4  2003/02/18 18:10:07  weilyn
 * Added support for imports.
 *
 * Revision 1.3  2003/02/16 02:16:02  weilyn
 * Added support for defs.
 *
 * Revision 1.2  2003/02/13 19:45:52  weilyn
 * Added support for claims.
 *
 * Revision 1.1  2003/01/30 02:02:16  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import edu.kestrel.netbeans.model.*;

/**
 *
 */
public class DefaultWrapper implements WrapperFactory {
    private static WrapperFactory instance;
    
    public synchronized static WrapperFactory getInstance() {
        if (instance != null)
            return instance;
        return instance = new DefaultWrapper();
    }
    
    /* ----------------- wrapper factory methods --------------------- */
    public SpecElement wrapSpec(SpecElement.Impl theImpl, Element parent) {
        return new SpecElement(theImpl, parent);
    }
    
    public SortElement wrapSort(SortElement.Impl theImpl, Element parent) {
        return new SortElement(theImpl, (SpecElement)parent);
    }
    
    public OpElement wrapOp(OpElement.Impl theImpl, Element parent) {
        return new OpElement(theImpl, (SpecElement)parent);
    }
    
    public DefElement wrapDef(DefElement.Impl theImpl, Element parent) {
        return new DefElement(theImpl, (SpecElement)parent);
    }
    
    public ClaimElement wrapClaim(ClaimElement.Impl theImpl, Element parent) {
        return new ClaimElement(theImpl, (SpecElement)parent);
    }    

    public ImportElement wrapImport(ImportElement.Impl theImpl, Element parent) {
        return new ImportElement(theImpl, (SpecElement)parent);
    }    
    
    public DiagElemElement wrapDiagElem(DiagElemElement.Impl theImpl, Element parent) {
        return new DiagElemElement(theImpl, (DiagramElement)parent);
    }
    
    public ProofElement wrapProof(ProofElement.Impl theImpl, Element parent) {
        return new ProofElement(theImpl, parent);
    }    
    
    public MorphismElement wrapMorphism(MorphismElement.Impl theImpl, Element parent) {
        return new MorphismElement(theImpl, parent);
    }    
    
    public DiagramElement wrapDiagram(DiagramElement.Impl theImpl, Element parent) {
        return new DiagramElement(theImpl, parent);
    }       

    public ColimitElement wrapColimit(ColimitElement.Impl theImpl, Element parent) {
        return new ColimitElement(theImpl, parent);
    }       

/*    public UnitIdElement wrapUnitId(UnitIdElement.Impl theImpl, Element parent) {
        return new UnitIdElement(theImpl, parent);
    }    */
    
}
