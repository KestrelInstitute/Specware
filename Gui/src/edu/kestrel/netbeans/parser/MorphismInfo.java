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
 * Holds parsed out information about a morphism.
 *
 */
public class MorphismInfo extends BaseElementInfo {
/*    public static final int SORT = 0;
*/
    Collection           allMembers;
    ChildCollection[]    memberLists;
    Element[]            allElements;
    
    String sourceString;
    String targetString;
    
/*    static final ElementMatch.Finder[] DEFAULT_SORT_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };
    
*/
    private static final ElementMatch.Finder[][] FINDER_CLUSTERS = {
/*        DEFAULT_SORT_FINDERS,
*/
    };
    
    private static final String[] CHILDREN_PROPERTIES = {
/*        ElementProperties.PROP_SORTS,
*/
    };
    
    private static final Class[] CHILDREN_TYPES = {
/*	SortElement.class,
*/
    };
    
    public MorphismInfo(String name, String sourceString, String targetString) {
        super(name);
        this.sourceString = sourceString;
        this.targetString = targetString;
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
        super.updateElement(model, target);
        super.updateBase(target);
        
        MorphismElement morphism = (MorphismElement)target;
//        SourceElement src = morphism.findSource();
        UnitID sourceElem = UnitID.get(sourceString);
        System.out.println("MorphismInfo.updateElement has sourceElem = "+sourceElem);
        UnitID targetElem = UnitID.get(targetString);
        System.out.println("MorphismInfo.updateElement has targetElem = "+targetElem);
        morphism.setSourceUnitID(sourceElem);
        morphism.setTargetUnitID(targetElem);

        //Util.log("Updating morphism properties of " + name); // NOI18N
        
        Element[] whole = new Element[allMembers.size()];
        Element[] newEls;
        
/*        for (int kind = SORT; kind <= IMPORT; kind++) {
            Element[] curMembers;
            switch (kind) {
	    case SORT:
		curMembers = spec.getSorts();
		break;
	    case OP:
		curMembers = spec.getOps();
		break;
	    case DEF:
		curMembers = spec.getDefs();
		break;
            case CLAIM:
                curMembers = spec.getClaims();
                break;
            case IMPORT:
                curMembers = spec.getImports();
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
*/        model.updateMemberOrder(morphism, ElementProperties.PROP_MEMBERS, whole);
    }
    
    public Element createModelImpl(LangModel.Updater model, Element parent) {
        ElementImpl impl;

        //Util.log("*** MorphismInfo.createModelImpl: Creating a morphism " + name); // NOI18N
	impl = model.createMorphism(parent);
        return impl.getElement();
    }
    
    public void addMember(int kind, BaseElementInfo member) {
        //Util.log("*** MorphismInfo.addMember: " + member.name); // NOI18N
        member.parent = this;
        int index = allMembers.size();
        allMembers.add(member);
        if (memberLists[kind] == null)
            initializeChildren(kind);
        memberLists[kind].addChild((BaseElementInfo)member, index);
    }

    public String toString() {
	return "morphism " + sourceString + " -> " + targetString;
    }

}
