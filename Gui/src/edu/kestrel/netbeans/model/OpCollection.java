/*
 * OpCollection.java
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
class OpCollection extends PartialCollection {
    static final OpElement[] EMPTY = new OpElement[0];
    
    public OpCollection(ElementEvents events,
			ElementCreator creator, 
			MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_OPS);
    }

    public Class getElementImplClass() {
        return OpElementImpl.class;
    }

    protected ElementImpl createElement(Element parent) {
        OpElementImpl mimpl = creator.createOp((SpecElement)parent);
        return mimpl;
    }

    protected Object[] createEmpty() {
        return EMPTY;
    }

    protected Element[] createEmpty(int size) {
        return new OpElement[size];
    }
    
    public OpElement getOp(String name) {
        OpElement[] elems = (OpElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            OpElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }

    public OpElement getOp(String name, String sort) {
        OpElement[] elems = (OpElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            OpElement el = elems[i];
            if (name.equals(el.getName()) && sort.equals(el.getSort())) {
		return el;
	    }
        }
        return null;
    }
}
