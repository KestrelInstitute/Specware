package edu.kestrel.netbeans.model;

import java.beans.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/**
 * Implements properties specific to a diagElem declared in a diagram.
 *
 */
final class DiagElemElementImpl extends MemberElementImpl implements DiagElemElement.Impl {
    private static final long serialVersionUID = 6799964214013985830L;

    DiagElemElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindDiagElem((DiagElemElement)el);
    }

    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        DiagElemElement element = (DiagElemElement)el;
    }

    public Object readResolve() {
        return null;
    }
    
    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.DiagElem getDiagElemBinding() {
        return (Binding.DiagElem)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "DiagElemElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((DiagElemElement)getElement()).clone();
    }
}
