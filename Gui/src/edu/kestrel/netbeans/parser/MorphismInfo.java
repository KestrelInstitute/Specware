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
    public static final int OP = 1;
    public static final int DEF = 2;
    public static final int CLAIM = 3;
    public static final int IMPORT = 4;
*/
    Collection           allMembers;
    ChildCollection[]    memberLists;
    Element[]            allElements;
    
/*    static final ElementMatch.Finder[] DEFAULT_SORT_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };
    
    static final ElementMatch.Finder[] DEFAULT_OP_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };

    static final ElementMatch.Finder[] DEFAULT_DEF_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };

    static final ElementMatch.Finder[] DEFAULT_CLAIM_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };

    static final ElementMatch.Finder[] DEFAULT_IMPORT_FINDERS = {
        new TextPositionMatch(), new NameFinder()
    };
*/
    private static final ElementMatch.Finder[][] FINDER_CLUSTERS = {
/*        DEFAULT_SORT_FINDERS,
        DEFAULT_OP_FINDERS,
        DEFAULT_DEF_FINDERS,
        DEFAULT_CLAIM_FINDERS,
        DEFAULT_IMPORT_FINDERS,*/
    };
    
    private static final String[] CHILDREN_PROPERTIES = {
/*        ElementProperties.PROP_SORTS,
        ElementProperties.PROP_OPS,
        ElementProperties.PROP_DEFS,
        ElementProperties.PROP_CLAIMS,
        ElementProperties.PROP_IMPORTS,*/
    };
    
    private static final Class[] CHILDREN_TYPES = {
/*	SortElement.class,
        OpElement.class,
        DefElement.class,
        ClaimElement.class,
        ImportElement.class,*/
    };
    
    public MorphismInfo(String name) {
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
        Util.log("MorphismInfo.updateElement this = "+this+" target "+target);
        super.updateElement(model, target);
        super.updateBase(target);
        
        MorphismElement morphism = (MorphismElement)target;

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
	return "morphism "+name;
    }

}
