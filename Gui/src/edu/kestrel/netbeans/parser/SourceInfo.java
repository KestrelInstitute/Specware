/*
 * SourceInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.2  2003/03/14 04:15:33  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:28  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.*;

import org.openide.src.SourceException;
import org.openide.text.PositionBounds;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

public class SourceInfo extends BaseElementInfo implements DocumentModelUpdater {
    public static final int SPEC = 0;
    public static final int PROOF = 1;
    public static final int MORPHISM = 2;

    SourceElement.Impl  sourceImpl;
    LangModel.Updater   updater;
    
    Collection          allMembers;
    ChildCollection[]   memberLists;

    //ChildCollection     specs;
    //Element[]           newSpecs;
    //private static final SpecElement[] NO_SPECS = new SpecElement[0];
    
    private static final ElementMatch.Finder[] SPEC_FINDERS = {
        //new TextPositionMatch(),
        new SpecFinder()
    };
    
    private static final ElementMatch.Finder[] PROOF_FINDERS = {
        //new TextPositionMatch(),
        new ProofFinder()
    };

    private static final ElementMatch.Finder[] MORPHISM_FINDERS = {
        //new TextPositionMatch(),
        new MorphismFinder()
    };

    private static final ElementMatch.Finder[][] FINDER_CLUSTERS = {
        SPEC_FINDERS,
        PROOF_FINDERS,
        MORPHISM_FINDERS,
    };
    
    private static final String[] CHILDREN_PROPERTIES = {
        ElementProperties.PROP_SPECS,
        ElementProperties.PROP_PROOFS,
        ElementProperties.PROP_MORPHISMS,
    };
    
    private static final Class[] CHILDREN_TYPES = {
        SpecElement.class,
        ProofElement.class,
        MorphismElement.class,
    };
    
    SourceInfo() {
        super(null);
        allMembers = new LinkedList();
        memberLists = new ChildCollection[CHILDREN_PROPERTIES.length];
    }
    
    private void initializeChildren(int kind) {
        memberLists[kind] = new ChildCollection(FINDER_CLUSTERS[kind], 
						CHILDREN_TYPES[kind]);
    }
    
    public Element createModelImpl(LangModel.Updater model, Element parent) {
        return null;
    }

    //     public void addSpec(SpecInfo info) {
    //         if (specs == null)
    //             specs = new ChildCollection(SPEC_FINDERS, 
    // 					       edu.kestrel.netbeans.model.SpecElement.class);
    //         specs.addChild(info, -1);
    //     }
    
    public void updateBinding(DocumentBinding updater, TextBinding target) {
	super.updateBinding(updater, target);
        updateChildren(updater, allMembers, (TextBinding.Container)target);
	
        /*
	  if (specs != null) {
	  updateChildren(updater, specs.getChildren(), 
	  (TextBinding.Container)sb);
	  }
	*/
	}
    
    public void updateModel(LangModel.Updater updater,
			    SourceElement src, 
			    SourceElement.Impl impl) throws SourceException {
        updateElement(updater, src);
	/*
	  this.sourceImpl = impl;
        
	  int[] specMap = null;
	  if (specs == null)
	  newSpecs = NO_SPECS;
	  else {
	  newSpecs = (Element[])specs.updateChildren(src, updater, 
	  ((SourceElementImpl)impl).getSpecs());
	  specMap = specs.getResultMap();
	  }
	  updater.updateMembers(src, ElementProperties.PROP_SPECS, newSpecs, null,
	  specMap);
	*/
    }

    public void updateElement(LangModel.Updater model, Element target) throws SourceException {
	//Util.log("SourceInfo.updateElement model = "+model+" Target = "+target);
        super.updateElement(model, target);
        super.updateBase(target);        
        SourceElement source = (SourceElement)target;
        Element[] whole = new Element[allMembers.size()];
        Element[] newEls;
	for (int kind = SPEC; kind <= MORPHISM; kind++) {
            Element[] curMembers;
            switch (kind) {
	    case SPEC:
		curMembers = source.getSpecs();
		break;
            case PROOF:
                curMembers = source.getProofs();
                break;
            case MORPHISM:
                curMembers = source.getMorphisms();
                break;
            default:
		throw new InternalError("Illegal member type"); // NOI18N
            }
            ChildCollection col = memberLists[kind];
	    Util.log("SourceInfo.updateElement kind = "+kind+" Col = "+col+" CurrentMembers = "+Util.print(curMembers));
            if (col == null && curMembers.length == 0)
                continue;            
            int[] IDs, map;
            if (col == null) {
                newEls = (Element[])java.lang.reflect.Array.newInstance(this.CHILDREN_TYPES[kind], 0);
                map = IDs = null;
            } else {
                IDs = col.getIDs();
                newEls = col.updateChildren(source, model, curMembers);
                map = col.getResultMap();
            }
            model.updateMembers(source, CHILDREN_PROPERTIES[kind], newEls, IDs, map);
            if (col != null)
		col.mapChildren(newEls, whole);
        }
        model.updateMemberOrder(source, ElementProperties.PROP_MEMBERS, whole);
	//Util.log("SourceInfo.updateElement source specs "+Util.print(source.getSpecs()));
    }
    
    private static final class SpecFinder extends ElementMatch.AbstractFinder {
        protected boolean matches(BaseElementInfo info, Element el) {
            return info.name.equals(((MemberElement)el).getName());
        }
    }

    private static final class ProofFinder extends ElementMatch.AbstractFinder {
        protected boolean matches(BaseElementInfo info, Element el) {
            return info.name.equals(((MemberElement)el).getName());
        }
    }

    private static final class MorphismFinder extends ElementMatch.AbstractFinder {
        protected boolean matches(BaseElementInfo info, Element el) {
            return info.name.equals(((MemberElement)el).getName());
        }
    }

    public void addMember(int kind, BaseElementInfo member) {
        member.parent = this;
        int index = allMembers.size();
        allMembers.add(member);
        if (memberLists[kind] == null)
            initializeChildren(kind);
	//Util.log("SourceInfo.addMember Kind = "+kind+" Member = "+member+" all Members.size() = "+ index);
	//Util.log("SourceInfo.addMember memberList["+kind+"] = "+memberLists[kind]);
        memberLists[kind].addChild((BaseElementInfo)member, index);
	//Util.log("SourceInfo.addMember after adding child allMembers.size() = "+ allMembers.size() );
    }
}
