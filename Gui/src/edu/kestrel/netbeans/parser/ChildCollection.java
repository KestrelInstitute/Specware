/*
 * ChildCollection.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.*;

import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;

/**
 *
 */
public class ChildCollection extends Object {
    Collection              children;
    ElementMatch.Finder[]   finders;
    int []                  ids;
    int []                  results;
    int                     idIndex;
    Class                   componentClass;
    
    private static final int MIN_IDS = 15;
    
    public ChildCollection(ElementMatch.Finder[] finders, Class componentClass) {
        this.finders = finders;
        this.componentClass = componentClass;
    }
    
    public int[] getIDs() {
        return ids;
    }
    
    public int[] getResultMap() {
        return results;
    }
    
    protected Element[] createArray(int size) {
        return (Element[])java.lang.reflect.Array.newInstance(componentClass, size);
    }
    
    public void addChild(BaseElementInfo el, int id) {
        if (children == null) {
            children = new LinkedList();
            if (id != -1)
                ids = new int[MIN_IDS];
        }
        children.add(el);
        if (ids != null) {
            if (ids.length == idIndex) {
                int[] newIDs = new int[ids.length * 2];
                System.arraycopy(ids, 0, newIDs, 0, ids.length);
                ids = newIDs;
            }
            ids[idIndex++] = id;
        }
    }
    
    private Element[] createAllChildren(Element parent, LangModel.Updater updater) 
        throws SourceException {
        Element[] newElements = createArray(children.size());
        int i = 0;
        for (Iterator it = children.iterator(); it.hasNext(); i++) {
            BaseElementInfo info = (BaseElementInfo)it.next();
            newElements[i] = info.createModelElement(parent, updater);
        }
        return newElements;
    }
    
    public Element[] updateChildren(Element parent, LangModel.Updater model, Element[] oldChildren)
    throws SourceException {
        if (oldChildren.length == 0) {
            return createAllChildren(parent, model);
        }
        ElementMatch match = new ElementMatch(oldChildren, this.children);
        for (int i = 0; i < finders.length; i++) {
            match.reset();
            finders[i].findMatches(match);
        }

        int[] mapping = match.getResultMap();
        Element[] oldElements = match.getOldElements();
        Element[] newElements = createArray(children.size());
        Collection current = match.getInfos();
        Iterator it = current.iterator();
        results = mapping;
        
        for (int i = 0; it.hasNext(); i++) {
            BaseElementInfo info = (BaseElementInfo)it.next();
            if (mapping == null || mapping[i] == -1) {
                // create the child element within its parent
                newElements[i] = info.createModelElement(parent, model);
            } else {
                newElements[i] = oldElements[mapping[i]];
                info.updateElement(model, newElements[i]);
            }
        }
        return newElements;
    }
    
    public void mapChildren(Element[] n, Element[] map) {
        for (int i = 0; i < n.length; i++) {
            map[ids[i]] = n[i];
        }
    }
    
    public Collection getChildren() {
        return this.children;
    }
}
