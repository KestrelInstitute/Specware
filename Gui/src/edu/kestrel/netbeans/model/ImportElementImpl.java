/*
 * ImportElementImpl.java
 *
 * Created on February 17, 2003, 5:45 PM
 */

package edu.kestrel.netbeans.model;

import java.beans.*;

import org.openide.nodes.Node;
import org.openide.src.SourceException;

/**
 *
 * @author  weilyn
 */
class ImportElementImpl extends MemberElementImpl implements ImportElement.Impl {
    
    private static final long serialVersionUID = 6799964214013985830L;
    
    ImportElementImpl(DefaultLangModel model) {
        super(model);
    }
    
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindImport((ImportElement)el);
    }

    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        ImportElement element = (ImportElement)el;
	//edu.kestrel.netbeans.Util.log("ImportElementImpl.createFromModel: name="+element.getName());
    }

    public Object readResolve() {
        return null;
    }
    
    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.Import getImportBinding() {
        return (Binding.Import)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "ImportElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((ImportElement)getElement()).clone();
    }
}
