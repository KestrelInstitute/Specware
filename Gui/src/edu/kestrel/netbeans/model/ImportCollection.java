/*
 * ImportCollection.java
 *
 * Created on February 17, 2003, 5:47 PM
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 *
 * @author  weilyn
 */
class ImportCollection extends PartialCollection {
    
    static final ImportElement[] EMPTY = new ImportElement[0];
    
    public ImportCollection(ElementEvents events,
			  ElementCreator creator, 
			  MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_IMPORTS);
    }

    public Class getElementImplClass() {
        return ImportElementImpl.class;
    }

    protected ElementImpl createElement(Element parent) {
        ImportElementImpl mimpl = creator.createImport((SpecElement) parent);
        return mimpl;
    }

    protected Object[] createEmpty() {
        return EMPTY;
    }

    protected Element[] createEmpty(int size) {
        return new ImportElement[size];
    }
    
    public ImportElement getImport(String name) {
        ImportElement[] elems = (ImportElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            ImportElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }
}
