/*
 * SourceElementImpl.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.5  2003/04/23 01:14:39  weilyn
 * BindingFactory.java
 *
 * Revision 1.4  2003/04/01 02:29:38  weilyn
 * Added support for diagrams and colimits
 *
 * Revision 1.3  2003/03/29 03:13:57  weilyn
 * Added support for morphism nodes.
 *
 * Revision 1.2  2003/03/14 04:14:02  weilyn
 * Added support for proof terms
 *
 * Revision 1.1  2003/01/30 02:02:04  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.beans.PropertyChangeEvent;
import java.lang.ref.*;
import java.util.*;

import java.beans.PropertyChangeEvent;
import org.openide.src.SourceException;
import org.openide.util.Task;
import org.openide.src.MultiPropertyChangeEvent;
import org.netbeans.modules.java.model.IndexedPropertyBase;
import org.openide.ErrorManager;
import org.openide.util.Task;

import edu.kestrel.netbeans.Util;


/**
 * Represents a source file. This element manages zero or more spec & proof elements.
 * <B>This element has not any
 * Binding</B> since it has no (direct) properties.<P>
 * Although this implementation *does* implement entire SourceElement.Impl interface,
 * methods that have not anything to do with the model itself are <B>dummy</B> and
 * do nothing (parse, getStatus).
 */
public class SourceElementImpl extends MemberElementImpl implements SourceElement.Impl, ElementOrder {
    
    private static final boolean DEBUG = false;    
    
    /** Reference keeping a collection of ElementImpls residing here.
     */
  private SpecCollection  specs;
  private ProofCollection proofs;
  private MorphismCollection morphisms;
  private DiagramCollection diagrams;
  private ColimitCollection colimits;
//  private URICollection uris;
  private MemberCollection members;
    
    private static final long serialVersionUID = 8506642610861188475L;
    
    // Getters
    ///////////////////////////////////////////////////////////////////////////////////
    
    public SourceElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected void notifyElementCreated() {
        // do nothing -- override ElementImpl's behaviour.
    }
    
    protected void createFromModel(Element model) throws SourceException {
    }
    
    protected Binding createBinding(Element el) {
      //return null;
      return getModelImpl().getBindingFactory().bindSource((SourceElement)el);
    }
    
  public void setBinding (Binding b) { 
    super.setBinding(b); 
//     if (members != null){
//     Util.log("SourceElementImpl.setBinding members  = "+members.getElements().length); 
//     } else { 
//         Util.log("SourceElementImpl.setBinding members is null ");  
//     }
//     Util.log("SourceElementImpl.setBinding specs = "+getSpecs().length); 
    members = new MemberCollection(this, (Binding.Container)b); 
  }

    public Element[] getElements() { 
        return members.getElements();
    }
    
    public SpecElement getSpec(String id) {
        if (specs == null)
            return null;
        return specs.getSpec(id);
    }
    
    public SpecElement[] getSpecs() {
        if (specs == null)
            return SpecCollection.EMPTY;
        return (SpecElement[])specs.getElements();
    }
    
    // Setters/changers
    public void changeSpecs(SpecElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeSpec -- adding spec ");
        Object token = takeLock();
        try {
            if (specs == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeSpecs();
            }
	    //Util.log("SourceElementimpl.changeSpecs calling change members for Specs "+mms.length);
            specs.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
        //IndexedPropertyBase.Change changes = IndexedPropertyBase.computeChanges(getSpecs(), mms);
        //Util.log("SourceElementImpl.changeSpec -- Changes  "+changes);
        //MultiPropertyChangeEvent event = new MultiPropertyChangeEvent (this, ElementProperties.PROP_SPECS, getSpecs(), mms);
        //Util.log("SourceElementImpl.changeSpec -- event " + event);
        //firePropertyChangeEvent(event);
    }
    
    public ProofElement getProof(String id) {
        if (proofs == null)
            return null;
        return proofs.getProof(id);
    }
    
    public ProofElement[] getProofs() {
        if (proofs == null)
            return ProofCollection.EMPTY;
        return (ProofElement[])proofs.getElements();
    }
    
    // Setters/changers
    public void changeProofs(ProofElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeProof -- adding proof ");
        Object token = takeLock();
        try {
            if (proofs == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeProofs();
            }
	    //Util.log("SourceElementimpl.changeProofs calling change members for Proofs "+mms.length);
            proofs.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
        //IndexedPropertyBase.Change changes = IndexedPropertyBase.computeChanges(getProofs(), mms);
        //Util.log("SourceElementImpl.changeProof -- Changes  "+changes);
        //MultiPropertyChangeEvent event = new MultiPropertyChangeEvent (this, ElementProperties.PROP_PROOFS, getProofs(), mms);
        //Util.log("SourceElementImpl.changeProof -- event " + event);
        //firePropertyChangeEvent(event);
    }

    public MorphismElement getMorphism(String id) {
        if (morphisms == null)
            return null;
        return morphisms.getMorphism(id);
    }
    
    public MorphismElement[] getMorphisms() {
        if (morphisms == null)
            return MorphismCollection.EMPTY;
        return (MorphismElement[])morphisms.getElements();
    }
    
    // Setters/changers
    public void changeMorphisms(MorphismElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeMorphism -- adding morphism");
        Object token = takeLock();
        try {
            if (morphisms == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeMorphisms();
            }
	    //Util.log("SourceElementimpl.changeMorphisms calling change members for Morphisms "+mms.length);
            morphisms.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
        //IndexedPropertyBase.Change changes = IndexedPropertyBase.computeChanges(getMorphisms(), mms);
        //Util.log("SourceElementImpl.changeMorphism -- Changes  "+changes);
        //MultiPropertyChangeEvent event = new MultiPropertyChangeEvent (this, ElementProperties.PROP_MORPHISMS, getMorphisms(), mms);
        //Util.log("SourceElementImpl.changeMorphism -- event " + event);
        //firePropertyChangeEvent(event);
    }

    public DiagramElement getDiagram(String id) {
        if (diagrams == null)
            return null;
        return diagrams.getDiagram(id);
    }
    
    public DiagramElement[] getDiagrams() {
        if (diagrams == null)
            return DiagramCollection.EMPTY;
        return (DiagramElement[])diagrams.getElements();
    }
    
    // Setters/changers
    public void changeDiagrams(DiagramElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeDiagram -- adding diagram ");
        Object token = takeLock();
        try {
            if (diagrams == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeDiagrams();
            }
	    //Util.log("SourceElementimpl.changeDiagrams calling change members for Diagrams "+mms.length);
            diagrams.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
        //IndexedPropertyBase.Change changes = IndexedPropertyBase.computeChanges(getDiagrams(), mms);
        //Util.log("SourceElementImpl.changeDiagram -- Changes  "+changes);
        //MultiPropertyChangeEvent event = new MultiPropertyChangeEvent (this, ElementProperties.PROP_PROOFS, getDiagrams(), mms);
        //Util.log("SourceElementImpl.changeDiagram -- event " + event);
        //firePropertyChangeEvent(event);
    }

    public ColimitElement getColimit(String id) {
        if (colimits == null)
            return null;
        return colimits.getColimit(id);
    }
    
    public ColimitElement[] getColimits() {
        if (colimits == null)
            return ColimitCollection.EMPTY;
        return (ColimitElement[])colimits.getElements();
    }
    
    // Setters/changers
    public void changeColimits(ColimitElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeColimit -- adding colimit ");
        Object token = takeLock();
        try {
            if (colimits == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeColimits();
            }
	    //Util.log("SourceElementimpl.changeColimits calling change members for Colimits "+mms.length);
            colimits.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }

/*    public URIElement getURI(String id) {
        if (uris == null)
            return null;
        return uris.getURI(id);
    }
    
    public URIElement[] getURIs() {
        if (uris == null)
            return URICollection.EMPTY;
        return (URIElement[])uris.getElements();
    }
    
    // Setters/changers
    public void changeURIs(URIElement[] mms, int operation) throws SourceException {
        //Util.log("SourceElementImpl.changeURI -- adding uri ");
        Object token = takeLock();
        try {
            if (uris == null) {
                if (operation != Element.Impl.REMOVE && mms.length == 0)
		  return;
                initializeURIs();
            }
	    //Util.log("SourceElementimpl.changeURIs calling change members for URIs "+mms.length);
            uris.changeMembers(mms, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }*/

    private void notifyCreate(Element[] els) {
        for (int i = 0; i < els.length; i++) {
            ElementImpl impl = (ElementImpl)els[i].getCookie(ElementImpl.class);
            impl.notifyCreate();
        }
    }
    
    protected void notifyCreate() {
        Element[] els;
        if (this.specs != null) {
            notifyCreate(specs.getElements());
        }
        if (this.proofs != null) {
            notifyCreate(proofs.getElements());
        }
        if (this.morphisms != null) {
            notifyCreate(morphisms.getElements());
        }
        if (this.diagrams != null) {
            notifyCreate(diagrams.getElements());
        }
        if (this.colimits != null) {
            notifyCreate(colimits.getElements());
        }
        /*if (this.uris != null) {
            notifyCreate(uris.getElements());
        }*/
        super.notifyCreate();
    }
    
    private Binding.Source getSourceBinding() {
        return (Binding.Source)getBinding();
    }
    
    /** Dummy method to satisfy typing requirements. This method does not work with the
     * model, but rather serves as interface to the parser. The method may be implemented
     * in subspecs or delegating implementations.
     */
    public int getStatus() {
        return SourceElement.STATUS_NOT;
    }
    
    public org.openide.util.Task prepare() {
        return org.openide.util.Task.EMPTY;
    }
    
    public void runAtomic(Runnable run) {
        // no-op
    }
    
    public void runAtomicAsUser(Runnable run) throws SourceException {
        // no-op
    }
    
    public void updateMembers(String name, Element[] elements, int[] indices, int[] optMap) {
        if (name == ElementProperties.PROP_SPECS) {
            if (specs == null) {
                if (elements.length == 0)
                    return;
                initializeSpecs();
            }
	    //Util.log("SourceElementimpl.updateMembers calling specs update members indices =  "+Util.print(indices));
            specs.updateMembers(elements, indices, optMap);
	    //Util.log("SourceElementimpl.updateMembers after PartialCollection.updateMembers specs = "+Util.print(getSpecs())+
	    //			     " members =  "+members);
	} else if (name == ElementProperties.PROP_PROOFS) {
            if (proofs == null) {
                if (elements.length == 0)
                    return;
                initializeProofs();
            }
	    //Util.log("SourceElementimpl.updateMembers calling proofs update members indices =  "+Util.print(indices));
            proofs.updateMembers(elements, indices, optMap);
	    //Util.log("SourceElementimpl.updateMembers after PartialCollection.updateMembers proofs = "+Util.print(getProofs())+
	    //			     " members =  "+members);
	} else if (name == ElementProperties.PROP_MORPHISMS) {
            if (morphisms == null) {
                if (elements.length == 0)
                    return;
                initializeMorphisms();
            }
            morphisms.updateMembers(elements, indices, optMap);
	} else if (name == ElementProperties.PROP_DIAGRAMS) {
            if (diagrams == null) {
                if (elements.length == 0)
                    return;
                initializeDiagrams();
            }
            diagrams.updateMembers(elements, indices, optMap);
	} else if (name == ElementProperties.PROP_COLIMITS) {
            if (colimits == null) {
                if (elements.length == 0)
                    return;
                initializeColimits();
            }
            colimits.updateMembers(elements, indices, optMap);
	} /*else if (name == ElementProperties.PROP_URIS) {
            if (uris == null) {
                if (elements.length == 0)
                    return;
                initializeURIs();
            }
	    //Util.log("SourceElementimpl.updateMembers calling proofs update members indices =  "+Util.print(indices));
            uris.updateMembers(elements, indices, optMap);
	    //Util.log("SourceElementimpl.updateMembers after PartialCollection.updateMembers proofs = "+Util.print(getProofs())+
	    //			     " members =  "+members);
	} */else {
            throw new IllegalArgumentException("Unsupported property: " + name); // NOI18N
        }
    }
    
    public void updateMemberOrder(Element[] ordered) {
        members.updateOrder(ordered);
    }
    
    
    // Implementation details
    ///////////////////////////////////////////////////////////////////////////////////
    public void setParent(ElementImpl impl) {
        // no-op, sources cannot have parents.
    }
    
    private void initializeSpecs() {
      this.specs = new SpecCollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getSpecSection(),  getModelImpl(), this);
    }
    
    private void initializeProofs() {
      this.proofs = new ProofCollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getProofSection(),  getModelImpl(), this);
    }
    
    private void initializeMorphisms() {
      this.morphisms = new MorphismCollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getMorphismSection(),  getModelImpl(), this);
    }

    private void initializeDiagrams() {
      this.diagrams = new DiagramCollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getProofSection(),  getModelImpl(), this);
    }
    
    private void initializeColimits() {
      this.colimits = new ColimitCollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getProofSection(),  getModelImpl(), this);
    }

/*    private void initializeURIs() {
      this.uris = new URICollection(this, getModelImpl(), members);
      //((Binding.Source)getRawBinding()).getProofSection(),  getModelImpl(), this);
    }*/
    
    protected SourceElementImpl findSource() {
        return this;
    }
    
    public Object readResolve() {
        return null;
    }
    
    protected Element cloneSelf() {
        return null;
    }
    
    protected boolean parentValid() {
        return isValid();
    }
    
    protected void notifyRemove() {
        Element[] allElems;
        
        allElems = members.getElements();
        for (int i = 0; i < allElems.length; i++) {
            ElementImpl impl = members.getElementImpl(allElems[i]);
            if (DEBUG) {
                Util.log("SourceElementImpl.notifyRemove calling notifyRemove on "+impl);
            }
            impl.notifyRemove();
        }
        super.notifyRemove();
    }
}

