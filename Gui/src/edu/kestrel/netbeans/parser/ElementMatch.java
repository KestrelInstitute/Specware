/*
 * ElementMatch.java
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

import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;

import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.LangModel;
import edu.kestrel.netbeans.codegen.TextBinding;

/**
 *
 */
public class ElementMatch {
    Element[]   oldElements;
    BitSet      usedElements;
    BitSet      matchedInfos;
    Collection  currentInfos;
    int         currentIndex;
    int         matchedCount;
    LangModel.Updater model;

    Enumeration     enum;
    int[]           resultMap;
    BaseElementInfo nextElem;
    
    public ElementMatch(Element[] oldElements, Collection currentInfos 
        /*, LangModel.Updater model */) {
        this.currentInfos = currentInfos;
        this.oldElements = oldElements;
        this.matchedInfos = new BitSet(currentInfos.size());
        this.usedElements = new BitSet(oldElements.length);
        resultMap = new int[currentInfos.size()];

        java.util.Arrays.fill(resultMap, -1);
    }
    
    public int[]    getResultMap() {
        return resultMap;
    }
    
    public void reset() {
        enum = Collections.enumeration(currentInfos);
        currentIndex = -1;
        nextElem = null;
    }
    
    public Element[] getOldElements() {
        return oldElements;
    }
    
    public boolean hasMoreElements() {
        if (matchedCount == currentInfos.size())
            return false;
        if (nextElem != null)
            return true;
        
        while (true) {
            if (!enum.hasMoreElements())
                return false;
            ++currentIndex;
            BaseElementInfo i = (BaseElementInfo)enum.nextElement();
            if (!matchedInfos.get(currentIndex)) {
                nextElem = i;
                break;
            }
        }
        return nextElem != null;
    }
    
    public BaseElementInfo nextElement() {
        BaseElementInfo ret = nextElem;
        nextElem = null;
        return ret;
    }
    
    public Collection getInfos() {
        return currentInfos;
    }
    
    public boolean isUsed(int elementIndex) {
        return usedElements.get(elementIndex);
    }
    
    public void matchElement(int elementIndex) {
        matchedInfos.set(currentIndex);
        usedElements.set(elementIndex);
        resultMap[currentIndex] = elementIndex;
        matchedCount++;
    }

    /*
    public TextBinding findBinding(Element el) {
        return (TextBinding)model.getElementBinding(el);
    }
     */
    
    public interface Finder {
        public void findMatches(ElementMatch data);
    }
    
    public static abstract class AbstractFinder implements Finder {
        
        public void findMatches(ElementMatch data) {
            Element[] elems = data.getOldElements();
            
            while (data.hasMoreElements()) {
                BaseElementInfo info = data.nextElement();
                for (int i = 0; i < elems.length; i++) {
                    if (data.isUsed(i))
                        continue;
                    if (matches(info, elems[i])) {
                        data.matchElement(i);
                        break;
                    }
                }
            }
        }
        
        protected abstract boolean matches(BaseElementInfo info, Element old);
    }
}
