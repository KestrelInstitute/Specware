/*
 * SourceElementImpl.java
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
 * Represents a source file. This element manages zero or more spec elements.
 * <B>This element has not any
 * Binding</B> since it has no (direct) properties.<P>
 * Although this implementation *does* implement entire SourceElement.Impl interface,
 * methods that have not anything to do with the model itself are <B>dummy</B> and
 * do nothing (parse, getStatus).
 */
public class SourceElementImpl extends MemberElementImpl implements SourceElement.Impl, ElementOrder {
    /** Reference keeping a collection of ElementImpls residing here.
     */
  private SpecCollection  specs;
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
        return getSpecs();
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
                if (operation != SpecElement.Impl.REMOVE && mms.length == 0)
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
	} else {
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
        
        if (specs != null) {
            allElems = members.getElements();
            for (int i = 0; i < allElems.length; i++) {
                ElementImpl impl = members.getElementImpl(allElems[i]);
		Util.log("SourceElementImpl.notifyRemove calling notifyRemove on "+impl);
                impl.notifyRemove();
            }
        }
        super.notifyRemove();
    }
}

