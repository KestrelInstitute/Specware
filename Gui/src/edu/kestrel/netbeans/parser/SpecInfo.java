/*
 * SpecInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:28  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.BitSet;
import java.util.Collection;
import java.util.LinkedList;

import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

/**
 * Holds parsed out information about a spec.
 *
 */
public class SpecInfo extends BaseElementInfo {
    public static final int SORT = 0;
    public static final int OP = 1;
    public static final int CLAIM = 2;

    Collection           allMembers;
    ChildCollection[]    memberLists;
    Element[]            allElements;
    
    static final ElementMatch.Finder[] DEFAULT_SORT_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };
    
    static final ElementMatch.Finder[] DEFAULT_OP_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };

    static final ElementMatch.Finder[] DEFAULT_CLAIM_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };

    private static final ElementMatch.Finder[][] FINDER_CLUSTERS = {
        DEFAULT_SORT_FINDERS,
        DEFAULT_OP_FINDERS,
        DEFAULT_CLAIM_FINDERS
    };
    
    private static final String[] CHILDREN_PROPERTIES = {
        ElementProperties.PROP_SORTS,
        ElementProperties.PROP_OPS,
        ElementProperties.PROP_CLAIMS
    };
    
    private static final Class[] CHILDREN_TYPES = {
	SortElement.class,
        OpElement.class,
        ClaimElement.class
    };
    
    public SpecInfo(String name) {
        super(name);
        allMembers = new LinkedList();
        memberLists = new ChildCollection[CHILDREN_PROPERTIES.length];
    }
    
    private void initializeChildren(int kind) {
        memberLists[kind] = new ChildCollection(FINDER_CLUSTERS[kind], 
						CHILDREN_TYPES[kind]);
    }
    
    private static final Element[] NO_MEMBERS = new Element[0];
    
    public void updateBinding(DocumentBinding updater, TextBinding b) {
        super.updateBinding(updater, b);
        updateChildren(updater, allMembers, (TextBinding.Container)b);
    }
    
    public void updateElement(LangModel.Updater model, Element target) throws SourceException {
        Util.log("SpecInfo.updateElement this = "+this+" target "+target);
        super.updateElement(model, target);
        super.updateBase(target);
        
        SpecElement spec = (SpecElement)target;

        //Util.log("Updating spec properties of " + name); // NOI18N
        
        Element[] whole = new Element[allMembers.size()];
        Element[] newEls;
        
        for (int kind = SORT; kind <= CLAIM; kind++) {
            Element[] curMembers;
            switch (kind) {
	    case SORT:
		curMembers = spec.getSorts();
		break;
	    case OP:
		curMembers = spec.getOps();
		break;
            case CLAIM:
                curMembers = spec.getClaims();
                break;
            default:
		throw new InternalError("Illegal member type"); // NOI18N
            }

            ChildCollection col = memberLists[kind];
            if (col == null && curMembers.length == 0)
                continue;
            
            int[] IDs, map;
            if (col == null) {
                newEls = (Element[])java.lang.reflect.Array.newInstance(this.CHILDREN_TYPES[kind], 0);
                map = IDs = null;
            } else {
                IDs = col.getIDs();
                newEls = col.updateChildren(spec, model, curMembers);
                map = col.getResultMap();
            }
            model.updateMembers(spec, CHILDREN_PROPERTIES[kind], newEls, IDs, map);
            if (col != null)
                col.mapChildren(newEls, whole);
        }
        model.updateMemberOrder(spec, ElementProperties.PROP_MEMBERS, whole);
    }
    
    public Element createModelImpl(LangModel.Updater model, Element parent) {
        ElementImpl impl;

        //Util.log("*** SpecInfo.createModelImpl: Creating a spec " + name); // NOI18N
	impl = model.createSpec(parent);
        return impl.getElement();
    }
    
    public void addMember(int kind, BaseElementInfo member) {
        //Util.log("*** SpecInfo.addMember: " + member.name); // NOI18N
        member.parent = this;
        int index = allMembers.size();
        allMembers.add(member);
        if (memberLists[kind] == null)
            initializeChildren(kind);
        memberLists[kind].addChild((BaseElementInfo)member, index);
    }

    public String toString() {
	return "spec "+name;
    }

}
