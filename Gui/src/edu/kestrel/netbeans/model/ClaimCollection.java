/*
 * ClaimCollection.java
 *
 * Created on February 7, 2003, 5:57 PM
 */

package edu.kestrel.netbeans.model;

import org.openide.src.*;

/**
 *
 * @author  weilyn
 */
public class ClaimCollection extends PartialCollection {
    static final ClaimElement[] EMPTY = new ClaimElement[0];
    
    /** Creates a new instance of ClaimCollection */
    public ClaimCollection(ElementEvents events,
			   ElementCreator creator, 
			   MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_CLAIMS);
    }
    
    public Class getElementImplClass() {
        return ClaimElementImpl.class;
    }
        
    protected ElementImpl createElement(Element parent) {
        ClaimElementImpl mimpl = creator.createClaim((SpecElement)parent);
        return mimpl;
    }
    
    /** Creates empty array of the collection element's type for array-creation
     * operations.
     *
     */
    protected Object[] createEmpty() {
        return EMPTY;
    }
    
    protected Element[] createEmpty(int size) {
        return new ClaimElement[size];
    }
    
    public ClaimElement getClaim(String name) {
        ClaimElement[] elems = (ClaimElement[])getElements();
        for (int i = 0; i < elems.length; i++) {
            ClaimElement el = elems[i];
            if (el.getName().equals(name)) {
		return el;
	    }
        }
        return null;
    }    
}
