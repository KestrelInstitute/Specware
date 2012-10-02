/*
 * SortCollection.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 */
class SortCollection extends PartialCollection {
    static final SortElement[] EMPTY = new SortElement[0];
    
    public SortCollection(ElementEvents events,
			  ElementCreator creator, 
			  MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_SORTS);
    }

    public Class getElementImplClass() {
        return SortElementImpl.class;
    }

    protected ElementImpl createElement(Element parent) {
        SortElementImpl mimpl = creator.createSort((SpecElement) parent);
        return mimpl;
    }

    protected Object[] createEmpty() {
        return EMPTY;
    }

    protected Element[] createEmpty(int size) {
        return new SortElement[size];
    }
    
    public SortElement getSort(String name) {
        SortElement[] elems = (SortElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            SortElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }
}
