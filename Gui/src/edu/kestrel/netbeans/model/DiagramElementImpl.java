package edu.kestrel.netbeans.model;

import java.beans.*;
import java.util.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;

/**
 * Models a diagram in a source.
 *
 */
class DiagramElementImpl extends MemberElementImpl implements DiagramElement.Impl, ElementOrder {
    /** Uplink to the implementation of the source element. The link is made during
     * attaching the abstract Element to the implementation.
     */
    private SourceElementImpl       sourceImpl;
    
    private DiagElemCollection      diagElems;

    private MemberCollection        members;

    private static final long serialVersionUID = -7718381719188756697L;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////
    
    /**
     * Constructs a diagram element from an external data source.
     * @param name name of the diagram. The name must contain both simple name and
     * fully qualified name parts.
    DiagramElementImpl(String name) {
        super(name);
    }
     */
    
    DiagramElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected void createFromModel(Element model) throws SourceException {
        DiagramElement element = (DiagramElement)model;

        // PENDING: set these directly.
        super.createFromModel(model);

        // member elements need the Element alreADD);
    }
    
    public final void setParent(ElementImpl impl) {
        super.setParent(impl);
        if (impl instanceof SourceElementImpl) {
            sourceImpl = (SourceElementImpl)impl;
        } else {
            sourceImpl = null;
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
    public DiagElemElement[] getDiagElems() {
        if (diagElems == null)
            return DiagElemCollection.EMPTY;
        return (DiagElemElement[])diagElems.getElements().clone();
    }
    
    public DiagElemElement getDiagElem(String name) {
        if (diagElems == null)
            return null;
        return diagElems.getDiagElem(name);
    }
    
    public void changeDiagElems(DiagElemElement[] elements, int operation) 
        throws SourceException {
        initializeDiagElems();
        Object token = takeMasterLock();
        try {
            diagElems.changeMembers(elements, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }


    // Utility methods
    ///////////////////////////////////////////////////////////////////////////////////
    
    /** Return the implementation for the SourceElement - directly, since all diagrams
     * have a link to the source.
     */
    protected final SourceElementImpl findSourceImpl() {
        return this.sourceImpl;
    }
    
    protected final Binding.Diagram getDiagramBinding() {
        return (Binding.Diagram)getBinding();
    }
    
    public void updateMembers(String propName, Element[] els, int[] indices,
        int[] optMap) {
        if (propName == ElementProperties.PROP_DIAG_ELEMS) {
	    initializeDiagElems();
            diagElems.updateMembers(els, indices, optMap);
        }
	//Util.log("DiagramElementimpl.updateMembers after PartialCollection.updateMembers members = "+members);
	//Util.log("DiagramElementimpl.updateMembers after PartialCollection.updateMembers indices = "+Util.print(indices)
	//				 +" optMap = "+Util.print(optMap));

    }
    
    public void updateMemberOrder(Element[] ordered) {
        members.updateOrder(ordered);
    }
    
    private void initializeDiagElems() {
        if (diagElems != null)
            return;
        synchronized (this) {
            if (diagElems == null) {
                diagElems = new DiagElemCollection(this, getModelImpl(), members);
            }
        }
    }


    protected final Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindDiagram((DiagramElement)el);
    }
    
    protected final void createAfter(Binding.Container cb, Binding refBinding)
    throws SourceException {
        Element[] els = members.getElements();
        ElementImpl impl;
        Binding ref = null;
        
        for (int i = 0; i < els.length; i++) {
            impl = members.getElementImpl(els[i]);
            impl.createAfter(getDiagramBinding(), ref);
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
        return "DiagramElementImpl[" + getName() + "]"; // NOI18N
    }
    
    /**
     * This implementation only clones the diagram element itself, not its subitems.
     */
    protected Element cloneSelf() {
        DiagramElement clone = new DiagramElement();
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
            return ((DiagramElement)getElement()).getSource();
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
        if (diagElems != null)
            diagElems.sanityCheck();
    }
    
    public Element[] getElements() {
        return members.getElements();
    }
}
