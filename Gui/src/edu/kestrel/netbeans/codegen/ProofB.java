package edu.kestrel.netbeans.codegen;

import java.util.*;

import javax.swing.text.Position;

import org.openide.text.CloneableEditorSupport;
import org.openide.text.PositionBounds;
import org.openide.text.PositionRef;
import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;

import edu.kestrel.netbeans.model.*;

/**
 * Specialized document binding for a ProofElement.
 *
 */
class ProofB extends Member implements Binding.Proof, TextBinding.Container {
    /**
     * Support for the containment of member elements.
     */
    ContainerSupport    container;
    
    public ProofB(ProofElement el, SourceText s) {
        super(el, s);
    }
    
    public TextBinding.Container getContainer() {
        return this;
    }
    
    public boolean isEmpty() {
        return container == null ||  container.isEmpty();
    }
    
    public void updateChildren(Collection c) {
        if (container == null && c.isEmpty())
            return;
        initializeContainer();
        container.updateChildren(c);
    }
    
    /** The clone implementation will clone, for efficiency reasons only the class itself,
     * not its children, as ProofElement.clone() normally does.
     */
    protected Element cloneElement() {
        ProofElement x = new ProofElement();
        ProofElement my = (ProofElement)getElement();
        try {
            x.setName(my.getName());
            x.setSource(my.getSource());
        } catch (SourceException ex) {
            // should NOT happen.
        }
        return x;
    }
    
    private ProofElement cloneProof() {
        return (ProofElement)cloneElement();
    }
    
    protected int classifyProperty(String name) {
        return CLASS_HEADER;
    }
    
    public ElementBinding findBindingAt(int pos) {
        ElementBinding b = super.findBindingAt(pos);
        if (b == this) {
            ElementBinding b2 = container.findBindingAt(pos);
            if (b2 != null)
                return b2;
        }
        return b;
    }

    /* ============== CONTAINER MANAGEMENT METHODS ================= */
    
    public boolean canInsertAfter(Binding b) {
        if (container == null) {
            return source.canWriteInside(bodyBounds);
        }
        return container.canInsertAfter(b);
    }

    /** The map contains mapping from target places to their new contents.
     */
    public void reorder(Map fromToMap) throws SourceException {
        container.reorder(fromToMap);
    }
    
    /** Replaces the slot contents with another element (different type permitted ?)
     */
    public void replace(Binding oldBinding, Binding newBinding) throws SourceException {
        container.replace(oldBinding, newBinding);
    }
    
    public void changeMembers(MultiPropertyChangeEvent evt) throws SourceException {
        if (container == null) {
            int etype = evt.getEventType();
            if (etype == evt.TYPE_ADD || etype == evt.TYPE_COMPOUND)
                initializeContainer();
            else
                return;
        }
        container.changeMembers(evt);
    }
    
    /**
     * Initializes a new binding for the element so the element is stored after the
     * `previous' binding, if that matters to the binding implementation.
     * @param toInitialize the binding that is being initialized & bound to the storage.
     * @param previous marker spot, the binding that should precede the new one.
     */
    public void insert(Binding toInitialize,Binding previous) throws SourceException {
        initializeContainer();
        container.insert(toInitialize, previous);
    }
    
    protected void initializeContainer() {
        if (container != null)
            return;
        container = new ContainerSupport(this.source, this);
    }
    
    public void regenerateWhole(Element el) {
    }
    
    PositionBounds findContainerBounds(TextBinding.Container cont) {
        return bodyBounds;
    }
    
    public void create(PositionBounds bounds) throws SourceException {
        ProofElement c = cloneProof();
        ProofElement orig = (ProofElement)getElement();

        wholeBounds = bounds;
        super.regenerateWhole(c, true);
        
        // initialize the container with the members:
        PositionRef r = bodyBounds.getBegin();
        boolean empty = true;
        ElementBinding prevBinding= null;
	Element[] models = null;

/*        for (int kind = 0; kind < 7; kind++) {
            
            switch (kind) {
                case 0:
                    models = orig.getSorts();
                    break;
                case 1:
                    models = orig.getOps();
                    break;
                case 2:
                    models = orig.getDefs();
                    break;                    
                case 3:
                    models = orig.getClaims();
                    break;
                case 4:
                    models = orig.getImports();
                    break;
            }
            if (empty && models.length > 0) {
                initializeContainer();
                empty = false;
            }
            
            for (int i = 0; i < models.length; i++) {
                ElementBinding b = source.findBinding(models[i]);
                container.insertChild(b, prevBinding, null);
                prevBinding = b;
            }
        }*/
    }
}
