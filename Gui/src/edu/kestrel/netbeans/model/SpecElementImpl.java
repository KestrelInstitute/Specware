/*
 * SpecElementImpl
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

import java.beans.*;
import java.util.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;

/**
 * Models a spec in a source.
 *
 */
class SpecElementImpl extends MemberElementImpl implements SpecElement.Impl, ElementOrder {
    /** Uplink to the implementation of the source element. The link is made during
     * attaching the abstract Element to the implementation.
     */
    private SourceElementImpl       sourceImpl;
    
    private SortCollection    sorts;
    
    private OpCollection    ops;

    private MemberCollection        members;

    private static final long serialVersionUID = -7718381719188756697L;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////
    
    /**
     * Constructs a spec element from an external data source.
     * @param name name of the spec. The name must contain both simple name and
     * fully qualified name parts.
    SpecElementImpl(String name) {
        super(name);
    }
     */
    
    SpecElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected void createFromModel(Element model) throws SourceException {
        SpecElement element = (SpecElement)model;

        // PENDING: set these directly.
        super.createFromModel(model);

        // member elements need the Element already.
        changeSorts(element.getSorts(), SpecElement.Impl.ADD);
        changeOps(element.getOps(), SpecElement.Impl.ADD);
    }
    
    public final void setParent(ElementImpl impl) {
        super.setParent(impl);
        if (impl instanceof SourceElementImpl) {
            sourceImpl = (SourceElementImpl)impl;
        }
    }
    
    public void setBinding(Binding b) {
        super.setBinding(b);
        // initialize all members.
        members = new MemberCollection(this, (Binding.Container)b);
    }
        
    // Member management methods
    // - will delegate to collection helpers.
    ///////////////////////////////////////////////////////////////////////////////////
    public SortElement[] getSorts() {
        if (sorts == null)
            return SortCollection.EMPTY;
        return (SortElement[])sorts.getElements().clone();
    }
    
    public SortElement getSort(String name) {
        if (sorts == null)
            return null;
        return sorts.getSort(name);
    }
    
    public void changeSorts(SortElement[] elements, int operation) 
        throws SourceException {
        initializeSorts();
        Object token = takeMasterLock();
        try {
            sorts.changeMembers(elements, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }

    public OpElement[] getOps() {
        if (ops == null)
            return OpCollection.EMPTY;
        return (OpElement[])ops.getElements().clone();
    }

    public OpElement getOp(String str) {
        if (ops == null)
            return null;
        return ops.getOp(str);
    }
    
    public void changeOps(OpElement[] cons, int operation) 
        throws SourceException {
        initializeOps();
        Object token = takeMasterLock();
        try {
            ops.changeMembers(cons, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }

    // Utility methods
    ///////////////////////////////////////////////////////////////////////////////////
    
    /** Return the implementation for the SourceElement - directly, since all specs
     * have a link to the source.
     */
    protected final SourceElementImpl findSourceImpl() {
        return this.sourceImpl;
    }
    
    protected final Binding.Spec getSpecBinding() {
        return (Binding.Spec)getBinding();
    }
    
    public void updateMembers(String propName, Element[] els, int[] indices,
        int[] optMap) {
        if (propName == ElementProperties.PROP_SORTS) {
            initializeSorts();
            sorts.updateMembers(els, indices, optMap);
        } else if (propName == ElementProperties.PROP_OPS) {
	    initializeOps();
            ops.updateMembers(els, indices, optMap);
        }
	//Util.log("SpecElementimpl.updateMembers after PartialCollection.updateMembers members = "+members);
	//Util.log("SpecElementimpl.updateMembers after PartialCollection.updateMembers indices = "+Util.print(indices)
	//				 +" optMap = "+Util.print(optMap));

    }
    
    public void updateMemberOrder(Element[] ordered) {
        members.updateOrder(ordered);
    }
    
    private void initializeSorts() {
        if (sorts != null)
            return;
        synchronized (this) {
            if (sorts == null) {
                sorts = new SortCollection(this, getModelImpl(), members);
            }
        }
    }

    private void initializeOps() {
        if (ops != null)
            return;
        synchronized (this) {
            if (ops == null) {
                ops = new OpCollection(this, getModelImpl(), members);
            }
        }
    }

    protected final Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindSpec((SpecElement)el);
    }
    
    protected final void createAfter(Binding.Container cb, Binding refBinding)
    throws SourceException {
        Element[] els = members.getElements();
        ElementImpl impl;
        Binding ref = null;
        
        for (int i = 0; i < els.length; i++) {
            impl = members.getElementImpl(els[i]);
            impl.createAfter(getSpecBinding(), ref);
            ref = impl.getBinding();
        }
    }
    

    // Serialization support
    ///////////////////////////////////////////////////////////////////////////////////
    public Object readResolve() {
        return null;
    }
    
    ///////////////////////////////////////////////////////////////////////////////////
    public String toString() {
        StringBuffer sb = new StringBuffer();
        
        sb.append("SpecElement["); // NOI18N
        sb.append(getName());
        sb.append("]");
        return sb.toString();
    }
    
    /**
     * This implementation only clones the spec element itself, not its subitems.
     */
    protected Element cloneSelf() {
        SpecElement clone = new SpecElement();
        try {
            clone.setName(getName());
        } catch (SourceException ex) {
        }
        return clone;
    }
    
    protected void doSetName(String name) throws SourceException {
        super.doSetName(name);
    }
    
    protected Element getParent() {
        Element p = super.getParent();
        if (p == null)
            return ((SpecElement)getElement()).getSource();
        else 
            return p;
    }
    
    protected void checkRemove() throws SourceException {
        super.checkRemove();
        Element[] allElems = members.getElements();
        for (int i = 0; i < allElems.length; i++) {
            ElementImpl impl = members.getElementImpl(allElems[i]);
            impl.checkRemove();
        }
    }
    
    protected void notifyRemove() {
        super.notifyRemove();
        Element[] allElems = members.getElements();
        for (int i = 0; i < allElems.length; i++) {
            ElementImpl impl = members.getElementImpl(allElems[i]);
            impl.notifyRemove();
        }
    }
    
    protected void notifyCreate() {
        Element[] allElems = members.getElements();
        for (int i = 0; i < allElems.length; i++) {
            ElementImpl impl = members.getElementImpl(allElems[i]);
            impl.notifyCreate();
        }
        super.notifyCreate();
        members.sanityCheck();
        if (sorts != null)
            sorts.sanityCheck();
        if (ops != null)
            ops.sanityCheck();
    }
    
    public Element[] getElements() {
        return members.getElements();
    }
}
