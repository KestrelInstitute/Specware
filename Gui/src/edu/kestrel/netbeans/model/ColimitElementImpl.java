package edu.kestrel.netbeans.model;

import java.beans.*;
import java.util.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;

/**
 * Models a colimit in a source.
 *
 */
class ColimitElementImpl extends MemberElementImpl implements ColimitElement.Impl, ElementOrder {
    /** Uplink to the implementation of the source element. The link is made during
     * attaching the abstract Element to the implementation.
     */
    private SourceElementImpl       sourceImpl;
    
//    private ImportCollection     imports;

    private MemberCollection        members;

    private static final long serialVersionUID = -7718381719188756697L;
    
    // Construction
    ///////////////////////////////////////////////////////////////////////////////////
    
    /**
     * Constructs a colimit element from an external data source.
     * @param name name of the colimit. The name must contain both simple name and
     * fully qualified name parts.
    ColimitElementImpl(String name) {
        super(name);
    }
     */
    
    ColimitElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected void createFromModel(Element model) throws SourceException {
        ColimitElement element = (ColimitElement)model;

        // PENDING: set these directly.
        super.createFromModel(model);

        // member elements need the Element already.
//        changeImports(element.getImports(), SpecElement.Impl.ADD);
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
    
    /** Return the implementation for the SourceElement - directly, since all colimits
     * have a link to the source.
     */
    protected final SourceElementImpl findSourceImpl() {
        return this.sourceImpl;
    }
    
    protected final Binding.Colimit getColimitBinding() {
        return (Binding.Colimit)getBinding();
    }
    
    public void updateMembers(String propName, Element[] els, int[] indices,
        int[] optMap) {
/*        if (propName == ElementProperties.PROP_IMPORTS) {
	    initializeImports();
            imports.updateMembers(els, indices, optMap);
        }
*/	//Util.log("ColimitElementimpl.updateMembers after PartialCollection.updateMembers members = "+members);
	//Util.log("ColimitElementimpl.updateMembers after PartialCollection.updateMembers indices = "+Util.print(indices)
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
        return getModelImpl().getBindingFactory().bindColimit((ColimitElement)el);
    }
    
    protected final void createAfter(Binding.Container cb, Binding refBinding)
    throws SourceException {
        Element[] els = members.getElements();
        ElementImpl impl;
        Binding ref = null;
        
        for (int i = 0; i < els.length; i++) {
            impl = members.getElementImpl(els[i]);
            impl.createAfter(getColimitBinding(), ref);
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
        
        sb.append("ColimitElement["); // NOI18N
        sb.append(getName());
        sb.append("]");
        return sb.toString();
    }
    
    /**
     * This implementation only clones the colimit element itself, not its subitems.
     */
    protected Element cloneSelf() {
        ColimitElement clone = new ColimitElement();
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
            return ((ColimitElement)getElement()).getSource();
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
