/*
 * DefCollection.java
 *
 * Created on February 15, 2003, 4:26 PM
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 *
 * @author  weilyn
 */
class DefCollection extends PartialCollection {
    static final DefElement[] EMPTY = new DefElement[0];
    
    public DefCollection(ElementEvents events,
                         ElementCreator creator, 
			 MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_DEFS);
    }

    public Class getElementImplClass() {
        return DefElementImpl.class;
    }

    protected ElementImpl createElement(Element parent) {
        DefElementImpl mimpl = creator.createDef((SpecElement) parent);
        return mimpl;
    }

    protected Object[] createEmpty() {
        return EMPTY;
    }

    protected Element[] createEmpty(int size) {
        return new DefElement[size];
    }
    
    public DefElement getDef(String name) {
        DefElement[] elems = (DefElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            DefElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }
}
