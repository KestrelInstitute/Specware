/*
 * LangEnvImpl.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:18  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import org.openide.nodes.Node;

import java.util.WeakHashMap;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;

/**
 * Standard simple implementation of the language model environment.
 *
 */
public class LangEnvImpl implements LangModel.Env {
    WeakHashMap     cookieMap;
    DocumentBinding binding;
    WrapperFactory  wrapper;
    LangModel model;
    
    public LangEnvImpl(DocumentBinding docBinding) {
        this.binding = docBinding;
        this.wrapper = DefaultWrapper.getInstance();
        cookieMap = new WeakHashMap(57);
    }
    
    public void setModel(LangModel model) {
        this.model = model;
    }

    public BindingFactory getBindingFactory() {
        return binding;
    }
    
    public WrapperFactory getWrapperFactory() {
        return wrapper;
    }

    /**
     * Currently no-op implementation.
     */
    public void complete(Element scope, int informationKind) {
    }
    
    public Node.Cookie findCookie(Element el, Class requested) {
        return null;
    }
}
