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
 * Holds parsed out information about a colimit.
 *
 */
public class ColimitInfo extends BaseElementInfo {
    public static final int DIAGRAM = 0;

    Collection           allMembers;
    ChildCollection[]    memberLists;
    Element[]            allElements;
    
    static final ElementMatch.Finder[] DEFAULT_DIAGRAM_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };
    
    private static final ElementMatch.Finder[][] FINDER_CLUSTERS = {
        DEFAULT_DIAGRAM_FINDERS,
    };
    
    private static final String[] CHILDREN_PROPERTIES = {
        ElementProperties.PROP_DIAGRAMS,
    };
    
    private static final Class[] CHILDREN_TYPES = {
	DiagramElement.class,
    };
    
    public ColimitInfo(String name) {
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
        Util.log("ColimitInfo.updateElement this = "+this+" target "+target);
        super.updateElement(model, target);
        super.updateBase(target);
        
        ColimitElement colimit = (ColimitElement)target;

        //Util.log("Updating colimit properties of " + name); // NOI18N
        
        Element[] whole = new Element[allMembers.size()];
        Element[] newEls;
        
        for (int kind = DIAGRAM; kind <= DIAGRAM; kind++) {
            Element[] curMembers;
            switch (kind) {
	    case DIAGRAM:
		curMembers = colimit.getDiagrams();
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
                newEls = col.updateChildren(colimit, model, curMembers);
                map = col.getResultMap();
            }
            model.updateMembers(colimit, CHILDREN_PROPERTIES[kind], newEls, IDs, map);
            if (col != null)
                col.mapChildren(newEls, whole);
        }
        model.updateMemberOrder(colimit, ElementProperties.PROP_MEMBERS, whole);
    }
    
    public Element createModelImpl(LangModel.Updater model, Element parent) {
        ElementImpl impl;

        //Util.log("*** ColimitInfo.createModelImpl: Creating a colimit " + name); // NOI18N
	impl = model.createColimit(parent);
        return impl.getElement();
    }
    
    public void addMember(int kind, BaseElementInfo member) {
        //Util.log("*** ColimitInfo.addMember: " + member.name); // NOI18N
        member.parent = this;
        int index = allMembers.size();
        allMembers.add(member);
        if (memberLists[kind] == null)
            initializeChildren(kind);
        memberLists[kind].addChild((BaseElementInfo)member, index);
    }

    public String toString() {
	return "colimit "+name;
    }

}
