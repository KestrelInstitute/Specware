/*
 * BaseElementInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:15  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.*;

import org.openide.nodes.Node;

import org.openide.text.PositionBounds;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

/**
 *
 */
public abstract class BaseElementInfo implements ElementFactory.Item {
    ElementFactory.Item parent;
    String              name;
    String              docText;
    Element             el;
    TextBinding         binding;
    String              bodyContent;
    
    PositionBounds      wholeBounds;
    PositionBounds      bodyBounds;
    PositionBounds      headerBounds;
    PositionBounds      docBounds;
    
    BaseElementInfo() {
        this(null);
    }
    
    BaseElementInfo(String name) {
        this.name = name;
    }
    
    public Element createModelElement(Element parent, LangModel.Updater model) 
    throws SourceException {
        Element el = createModelImpl(model, parent);
        updateElement(model, el);
        return this.el = el;
    }
    
    public int comparePositionTo(TextBinding b) {
        if (b == null)
            return -1;
        PositionBounds bounds = b.getElementRange(true);
        
        int begin = (headerBounds == null ? wholeBounds : headerBounds).getBegin().getOffset();
	Element element = b.getElement();
        int otherBegin = bounds.getBegin().getOffset();
        int end = wholeBounds.getEnd().getOffset();
        int otherEnd = bounds.getEnd().getOffset();
        
        if (otherBegin == otherEnd)
            // the binding is invalid - extinct ??
            return -1;
        
        if (begin < otherEnd && end > otherBegin)
            // MATCH!!
            return 0;
        if (end == otherBegin)
            return -1;
        return end - otherBegin;
    }
    
    public Node.Cookie getCookie(Class desiredClass) {
        return null;
    }
    
    protected abstract Element createModelImpl(LangModel.Updater model, Element parent);
    
    public void updateElement(LangModel.Updater model, Element el) throws SourceException {
        this.el = el;
        this.binding = (TextBinding)model.getElementBinding(el);
    }
    
    public void updateBindings(DocumentBinding updater) {
        updateBinding(updater, binding);
    }
    
    public void updateBinding(DocumentBinding updater, TextBinding b) {
        b.updateBounds(TextBinding.BOUNDS_ALL, wholeBounds);
        b.updateBounds(TextBinding.BOUNDS_HEADER, headerBounds);
        b.updateBounds(TextBinding.BOUNDS_BODY, bodyBounds);
    }
    
    protected static void updateChildren(DocumentBinding updater,
					 Collection infos, TextBinding.Container container) {
        List blist = new ArrayList(infos.size());
        for (Iterator it = infos.iterator(); it.hasNext(); ) {
            BaseElementInfo i = (BaseElementInfo)it.next();
            i.updateBindings(updater);
            blist.add(i.binding);
        }
        container.updateChildren(blist);
    }
    
    protected void updateBase(Element el) throws SourceException {
        this.el = el;
        MemberElement.Impl m = (MemberElement.Impl)el.getCookie(MemberElement.Impl.class);
        if (m != null) {
	    m.setName(name);
	}
    }

    public String toString() {
	return "["+getClass().getName()+"]"+name;
    }
    
    public static class NameFinder extends ElementMatch.AbstractFinder {
        protected boolean matches(BaseElementInfo info, Element old) {
            MemberElement oldMember = (MemberElement)old;
            return info.name.equals(oldMember.getName());
        }
    }
}
