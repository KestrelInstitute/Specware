package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 */
class DiagElemCollection extends PartialCollection {
    static final DiagElemElement[] EMPTY = new DiagElemElement[0];
    
    public DiagElemCollection(ElementEvents events, ElementCreator creator, MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_DIAG_ELEMS);
    }

    public Class getElementImplClass() {
        return DiagElemElementImpl.class;
    }

    protected ElementImpl createElement(Element parent) {
        DiagElemElementImpl mimpl = creator.createDiagElem((DiagramElement) parent);
        return mimpl;
    }

    protected Object[] createEmpty() {
        return EMPTY;
    }

    protected Element[] createEmpty(int size) {
        return new DiagElemElement[size];
    }
    
    public DiagElemElement getDiagElem(String name) {
        DiagElemElement[] elems = (DiagElemElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            DiagElemElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }
}
