package edu.kestrel.netbeans.model;

import java.beans.*;
import java.util.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;

/**
 * Models a morphism in a source.
 *
 */
class MorphismElementImpl extends MemberElementImpl implements MorphismElement.Impl, ElementOrder {
    /** Uplink to the implementation of the source element. The link is made during
     * attaching the abstract Element to the implementation.
     */
    private SourceElementImpl       sourceImpl;
    
//    private ImportCollection     imports;

    private MemberCollection        members;

    private UnitID                  sourceUnitID;
    
    private UnitID                  targetUnitID;
    
    private static final long serialVersionUID = -7718381719188756697L;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////
    
    /**
     * Constructs a morphism element from an external data source.
     * @param name name of the morphism. The name must contain both simple name and
     * fully qualified name parts.
    MorphismElementImpl(String name) {
        super(name);
    }
     */
    
    MorphismElementImpl(DefaultLangModel model) {
        super(model);
        sourceUnitID = null;
        targetUnitID = null;
    }
    
    protected void createFromModel(Element model) throws SourceException {
        MorphismElement element = (MorphismElement)model;
        super.createFromModel(model);
        setSourceUnitID(element.getSourceUnitID());
        setTargetUnitID(element.getTargetUnitID());
        
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
        
    /** Getter for the initial value.
    * @return initial value for the variable or empty string if it is not initialized
    */
    public UnitID getSourceUnitID() {
        return this.sourceUnitID;
    }

    /** Setter for the initial value.
    * @param value initial value for the variable
    */
    public void setSourceUnitID(UnitID sourceUnitID) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (sourceUnitID != this.sourceUnitID) {
                    evt = new PropertyChangeEvent(getElement(), PROP_SOURCE_UNIT_ID, this.sourceUnitID, sourceUnitID);
                    checkVetoablePropertyChange(evt);
                    getMorphismBinding().changeSourceUnitID(sourceUnitID);
                    fireOwnPropertyChange(evt);
                    //addPropertyChange(evt);
                }
            }
            this.sourceUnitID = sourceUnitID;
            commit();
        } finally {
            releaseLock(token);
        }
    }

    /** Getter for the initial value.
    * @return initial value for the variable or empty string if it is not initialized
    */
    public UnitID getTargetUnitID() {
        return this.targetUnitID;
    }

    /** Setter for the initial value.
    * @param value initial value for the variable
    */
    public void setTargetUnitID(UnitID targetUnitID) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (targetUnitID != this.targetUnitID) {
                    evt = new PropertyChangeEvent(getElement(), PROP_TARGET_UNIT_ID, this.targetUnitID, targetUnitID);
                    checkVetoablePropertyChange(evt);
                    getMorphismBinding().changeTargetUnitID(targetUnitID);
                    fireOwnPropertyChange(evt);
                    //addPropertyChange(evt);
                }
            }
            this.targetUnitID = targetUnitID;
            commit();
        } finally {
            releaseLock(token);
        }
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
    
    /** Return the implementation for the SourceElement - directly, since all morphisms
     * have a link to the source.
     */
    protected final SourceElementImpl findSourceImpl() {
        return this.sourceImpl;
    }
    
    protected final Binding.Morphism getMorphismBinding() {
        return (Binding.Morphism)getBinding();
    }
    
    public void updateMembers(String propName, Element[] els, int[] indices,
        int[] optMap) {
/*        if (propName == ElementProperties.PROP_IMPORTS) {
	    initializeImports();
            imports.updateMembers(els, indices, optMap);
        }
*/	//Util.log("MorphismElementimpl.updateMembers after PartialCollection.updateMembers members = "+members);
	//Util.log("MorphismElementimpl.updateMembers after PartialCollection.updateMembers indices = "+Util.print(indices)
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
        return getModelImpl().getBindingFactory().bindMorphism((MorphismElement)el);
    }
    
    protected final void createAfter(Binding.Container cb, Binding refBinding)
    throws SourceException {
        Element[] els = members.getElements();
        ElementImpl impl;
        Binding ref = null;
        
        for (int i = 0; i < els.length; i++) {
            impl = members.getElementImpl(els[i]);
            impl.createAfter(getMorphismBinding(), ref);
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
        
        sb.append("MorphismElement["); // NOI18N
        sb.append(getName());
        sb.append("]");
        return sb.toString();
    }
    
    /**
     * This implementation only clones the morphism element itself, not its subitems.
     */
    protected Element cloneSelf() {
        MorphismElement clone = new MorphismElement();
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
            return ((MorphismElement)getElement()).getSource();
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
}
