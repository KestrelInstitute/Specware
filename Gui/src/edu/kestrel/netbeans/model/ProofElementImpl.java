package edu.kestrel.netbeans.model;

import java.beans.*;
import java.util.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;

/**
 * Models a proof in a source.
 *
 */
class ProofElementImpl extends MemberElementImpl implements ProofElement.Impl, ElementOrder {
    /** Uplink to the implementation of the source element. The link is made during
     * attaching the abstract Element to the implementation.
     */
    private SourceElementImpl       sourceImpl;
    
//    private ImportCollection     imports;

    private MemberCollection        members;

    private static final long serialVersionUID = -7718381719188756697L;

    private String proofString;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////
    
    /**
     * Constructs a proof element from an external data source.
     * @param name name of the proof. The name must contain both simple name and
     * fully qualified name parts.
    ProofElementImpl(String name) {
        super(name);
    }
     */
    
    ProofElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected void createFromModel(Element model) throws SourceException {
        ProofElement element = (ProofElement)model;

        // PENDING: set these directly.
        super.createFromModel(model);

        // member elements need the Element already.
//        changeImports(element.getImports(), ADD);
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
/*    public ImportElement[] getImports() {
        if (imports == null)
            return ImportCollection.EMPTY;
        return (ImportElement[])imports.getElements().clone();
    }
    
    public ImportElement getImport(String name) {
        if (imports == null)
            return null;
        return imports.getImport(name);
    }
    
    public void changeImports(ImportElement[] elements, int operation) 
        throws SourceException {
        initializeImports();
        Object token = takeMasterLock();
        try {
            imports.changeMembers(elements, operation);
            commit();
        } finally {
            releaseLock(token);
        }
    }
*/

    // Utility methods
    ///////////////////////////////////////////////////////////////////////////////////
    
    /** Return the implementation for the SourceElement - directly, since all proofs
     * have a link to the source.
     */
    protected final SourceElementImpl findSourceImpl() {
        return this.sourceImpl;
    }
    
    protected final Binding.Proof getProofBinding() {
        return (Binding.Proof)getBinding();
    }
    
    public void updateMembers(String propName, Element[] els, int[] indices,
        int[] optMap) {
/*        if (propName == ElementProperties.PROP_IMPORTS) {
	    initializeImports();
            imports.updateMembers(els, indices, optMap);
        }
*/	//Util.log("ProofElementimpl.updateMembers after PartialCollection.updateMembers members = "+members);
	//Util.log("ProofElementimpl.updateMembers after PartialCollection.updateMembers indices = "+Util.print(indices)
	//				 +" optMap = "+Util.print(optMap));

    }
    
    public void updateMemberOrder(Element[] ordered) {
        members.updateOrder(ordered);
    }
    
/*    private void initializeImports() {
        if (imports != null)
            return;
        synchronized (this) {
            if (imports == null) {
                imports = new ImportCollection(this, getModelImpl(), members);
            }
        }
    }
*/

    protected final Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindProof((ProofElement)el);
    }
    
    protected final void createAfter(Binding.Container cb, Binding refBinding)
    throws SourceException {
        Element[] els = members.getElements();
        ElementImpl impl;
        Binding ref = null;
        
        for (int i = 0; i < els.length; i++) {
            impl = members.getElementImpl(els[i]);
            impl.createAfter(getProofBinding(), ref);
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
        
        sb.append("ProofElement["); // NOI18N
        sb.append(getName());
        sb.append("]");
        return sb.toString();
    }
    
    /**
     * This implementation only clones the proof element itself, not its subitems.
     */
    protected Element cloneSelf() {
        ProofElement clone = new ProofElement();
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
            return ((ProofElement)getElement()).getSource();
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
//        if (imports != null)
//            imports.sanityCheck();
    }
    
    public Element[] getElements() {
        return members.getElements();
    }
    
    public String getProofString() {
        return this.proofString;
    }
    
    public void setProofString(String proofString) throws SourceException {
        Util.log("ProofElementImpl.setProofString called with "+proofString);
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                /*if (proofString.equals(this.proofString)) {
                    Util.log("ProofElementImpl.setProofString returning because proofString hasn't changed");
                    return;
                }*/
                evt = new PropertyChangeEvent(getElement(), PROP_PROOFSTRING, this.proofString, proofString);
                // no constraings on the Initializer... only check vetoable listeners.
                checkVetoablePropertyChange(evt);
                getProofBinding().changeProofString(proofString);
                addPropertyChange(evt);
            }
            this.proofString = proofString;
            Util.log("ProofElementImpl.setProofString has this.proofString = "+this.proofString);
            commit();
        } finally {
            releaseLock(token);
        }    
    }
    
}
