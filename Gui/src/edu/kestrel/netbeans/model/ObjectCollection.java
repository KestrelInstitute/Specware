package edu.kestrel.netbeans.model;

import java.beans.PropertyChangeEvent;
import java.util.*;

import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;
import org.netbeans.modules.java.model.IndexedPropertyBase;

import edu.kestrel.netbeans.Util;

/**
 *
 */
abstract class ObjectCollection extends IndexedPropertyBase implements ElementOrder {
    /**
     * Threshold for dump identity comparisons. If the avg number of compare ops *2 is
     * more than this value, faster hashing algorithm is used for discovering identities.
     * The value should balance the tradeoff between creating new objects and the comparisons.
     */
    public static final int SMALL_THRESHOLD = 500;
    
    /** Reference to the collection's container binding - manages contained objects.
     */
    Binding.Container       containerBinding;
    
    /** Interface used for broadcasting events
     */
    ElementEvents           events;
    
    /** The actual contents of the collection.
     */
    Element[]               elements;
    
    ElementCreator          creator;
    
    public ObjectCollection(Binding.Container container,
        ElementCreator creator, ElementEvents events, String propertyName) {
        super(propertyName);
        this.events = events;
        this.creator = creator;
        this.containerBinding = container;
    }
    
    public Element[] getElements() {
        if (elements == null)
            return createEmpty(0);
        return elements;
    }
    
    /** Attempts to find appropriate positions(s) for inserting the new element(s).
     * The method is expected to return array of elements that should precede the 
     * matching element being inserted. For insertion at the beginning of the collection,
     * the method should use a special tag value, Positioner.FIRST. If the method returns
     * null, elements are appended at the end of the collection.
     */
    protected abstract Element[] findPositions(Element[] elements);
    
    /**
     * Creates a copy of the passed element using local implementation and creates an
     * empty (uninitialized) binding for it.
     */
    protected abstract ElementImpl createElement(Element parent);
    
    /** The method is called for creation of array of exactly the specific element
     * type so that typecasts in collection's clients succeed.
     */
    protected abstract Element[] createEmpty(int size);
    
    protected Element copyElement(Element model) {
        ElementImpl impl = createElement((Element)events.getEventSource());
        try {
            impl.createFromModel(model);
        } catch (SourceException ex) {
        }
        return impl.getElement();
    }
    
    /** Adds the specified members to the collection. The implementation uses
     * Finder to find appropriate place(s) in the collection to insert the new
     * members.
     */
    public void addMembers(Element[] els) throws SourceException {
        Element[] insertingEls = new Element[els.length];
        Element[] elements = getElements();
	Util.log("*** ObjectCollection.addMembers: els="+Util.print(els));
	Util.log("*** ObjectCollection.addMembers: getElements()="+Util.print(elements));
        for (int i = 0; i < els.length; i++) {
            insertingEls[i] = copyElement(els[i]);
        }
        Element[] precedings = findPositions(insertingEls);
	Util.log("*** ObjectCollection.addMembers: precedings()="+Util.print(precedings));
        Element[] newElems = createEmpty(insertingEls.length + elements.length);
        int[] insertIndices = new int[newElems.length];
        // If an element wants to be inserted after another one, that another one
        // needs to be inserted first (if it is also new one)
        Map m = new HashMap(precedings.length * 4 / 3);
        for (int i = 0; i < precedings.length; i++) {
            // throw exception if prev is not a member of this class.
            Object o = m.get(precedings[i]);
            if (o != null) {
                Collection c;
                if (!(o instanceof Collection)) {
                    c = new LinkedList();
                    c.add(o);
                    m.put(precedings[i], c);
                } else {
                    c = (Collection)o;
                }
                c.add(insertingEls[i]);
            } else {
                m.put(precedings[i], insertingEls[i]);
            }
        }
        Element prevElem = Positioner.FIRST;
        int newPos = 0, oldPos = 0, inserted = 0;
        for (oldPos = 0; oldPos <= elements.length; oldPos++) {
            Object dependent = m.get(prevElem);
            if (dependent != null) {
                //Util.log("inserting after global item #" + oldGlobalPos); // NOI18N
                LinkedList toInsert = new LinkedList();
                do {
		    Util.log("*** ObjectCollection.addMembers: oldPos="+oldPos+" newPos="+newPos+" inserted="+inserted+" dependent="+Util.print(dependent));
                    if (dependent != null) {
                        if (dependent instanceof Collection)
                            toInsert.addAll((Collection)dependent);
                        else
                            toInsert.add(dependent);
                    }
                    Element newEl = (Element)toInsert.removeFirst();
		    Util.log("*** ObjectCollection.addMembers: newEl="+Util.print(newEl));
                    insertIndices[inserted] = newPos;
                    newElems[newPos] = newEl;
                    inserted++;
                    newPos++;

                    dependent = m.get(newEl);
                } while (!toInsert.isEmpty() || dependent != null);
                // inserted everything chained after prevElem
            }            
	    Util.log("*** ObjectCollection.addMembers: oldPos="+oldPos+" newPos="+newPos+" inserted="+inserted+" dependent="+Util.print(dependent));
            if (oldPos >= elements.length) break;            
            prevElem = elements[oldPos];
            newElems[newPos] = elements[oldPos];
            newPos++;
        }
	Util.log("*** ObjectCollection.addMembers: newElems="+Util.print(newElems));
        if (inserted < insertingEls.length)
            throw new IllegalArgumentException("Inconsistent insertion strategy"); // NOI18N        
        Change chng = new Change();
        chng.insertIndices = insertIndices;
        chng.inserted = Arrays.asList(insertingEls);
        chng.phaseCount = 1;
        chng.sizeDiff = insertingEls.length;
        doSetMembers(newElems, chng);
    }
    
    /**
     * Removes exactly the members specified in toRemove. Elements are matched against
     * the set of current members based on object identity; if an element is not found in
     * the current set, the implementation may throw IllegalArgumentException.
     */
    public void removeMembers(Element[] els) throws SourceException {
        Element[] elements = getElements();
        int[] removeIndices = createIdentityMap(els);
        // sanity check:
        for (int i = 0; i < removeIndices.length; i++) {
            if (removeIndices[i] == -1)
                throw new SourceException("Element does not exist"); // NOI18N
        }
        Element[] newElems = createEmpty(elements.length - els.length);
        int[] offsets = new int[elements.length];
        int newPos = 0;
        int removed = 0;
        int nextRemove = removeIndices[0];
        for (int i = 0; i < elements.length; i++) {
            if (i == nextRemove) {
                offsets[i] = -i -1;
                if (++removed < removeIndices.length)
                    nextRemove = removeIndices[removed];
                else
                    nextRemove = -1;
            } else {
                offsets[i] = newPos - i;
                newElems[newPos] = elements[i];
                newPos++;
            }
        }
        Change ch = new Change();
        ch.removed = Arrays.asList(els);
        ch.removeIndices = removeIndices;
        ch.offsets = offsets;
        ch.sizeDiff = - els.length;
        ch.phaseCount = 1;        
        // elements & positions will be updated from inside doSetMembers.
        doSetMembers(newElems, ch);
    }
    
    public void updateMembers(Element[] members, int[] map) {
        Collection newMembers = null;        
        if (this.elements != null) {
            Collection removedMembers;
            Element[] els = getElements();
            if (els != null) {
                if (map == null)
                    map = createIdentityMap(members);
                Change chng = computeChanges2(els, members, map);
                if (chng.phaseCount == 0) return;
                events.addPropertyChange(createPropertyEvent(chng, events.getEventSource(),
							     els, members));
                newMembers = chng.inserted;
                removedMembers = chng.removed;
            } else {
	      newMembers = Arrays.asList(members);
	      removedMembers = null;
            }
            ElementImpl parent = events.getElementImpl();
            boolean fire = parent.isValid();
            if (fire) {
	      if (removedMembers != null && !removedMembers.isEmpty()) {
		for (Iterator it = removedMembers.iterator(); it.hasNext(); ) {
		  Element el = (Element)it.next();
		  ElementImpl impl = getElementImpl(el);
		  impl.notifyRemove();
		}
	      }
	      if (newMembers != null && !newMembers.isEmpty()) {
		for (Iterator it = newMembers.iterator(); it.hasNext(); ) {
		  Element el = (Element)it.next();
		  ElementImpl impl = getElementImpl(el);
		  impl.notifyCreate();
		}
	      }
            }
        } else if (!events.getElementImpl().isCreated() && members.length > 0) {
	  ElementImpl parent = events.getElementImpl();
	  boolean fire = parent.isValid();
	  for (int i = 0; i < members.length; i++) {
	    Element el = members[i];
	    ElementImpl impl = getElementImpl(el);
	    impl.notifyCreate();
	  }
        }
        this.elements = members;
    }
    
    public void setMembers(Element[] members) throws SourceException {
        Change chng;   
        Element[] els = getElements();
        Element[] newEls = createEmpty(members.length);
        int[] map = createIdentityMap(members);
        int memberPos = 0;
        boolean copied = false;
        for (int i = 0; i < map.length; i++) {
            if (map[i] == -1) {
                newEls[i] = copyElement(members[i]);
                copied = true;
            } else {
                newEls[i] = members[i];
            }
        }        
        chng = computeChanges2(els, newEls, map);        
        doSetMembers(newEls, chng);
    }
    
    protected Binding getBinding(Object o) {
        return getBinding((Element)o);
    }
    
    protected Binding getBinding(Element el) {
        ElementImpl impl = getElementImpl(el);
        return impl == null ? null : impl.getBinding();
    }
    
    protected ElementImpl getElementImpl(Element el) {
        return (ElementImpl)el.getCookie(ElementImpl.class);
    }
    
    public void changeMembers(Element[] members, int operation) throws SourceException {
        switch (operation) {
            case Element.Impl.ADD:
                addMembers(members);
                break;
            case Element.Impl.SET:
                setMembers(members);
                break;
            case Element.Impl.REMOVE:
                removeMembers(members);
                break;
        }
    }
    
    /**
     * The actual worker method, that rewrites the collection's content and the associated
     * Bindings.
     */
    protected void doSetMembers(Element[] newMembers, Change chg) throws SourceException {
        if (chg.phaseCount == 0)
            return;

        Element[] elements = getElements();
        boolean deferredCreation = events.getElementImpl().isCreated();

        MultiPropertyChangeEvent evt;

        if (!deferredCreation) {
            if (events.getElementImpl().isConstrained() && (chg.removed != null)) {
                for (Iterator it = chg.removed.iterator(); it.hasNext(); ) {
                    getElementImpl((Element)it.next()).checkRemove();
                }
            }
            evt = createPropertyEvent(chg, events.getEventSource(), getElements(), newMembers);
            fireVetoableChange(evt);
            containerBinding.changeMembers(evt);

            if (chg.inserted != null)
                for (Iterator it = chg.inserted.iterator(); it.hasNext(); ) {
                    getElementImpl((Element)it.next()).notifyCreate();
                }
            if (chg.removed != null)
                for (Iterator it = chg.removed.iterator(); it.hasNext(); ) {
                    getElementImpl((Element)it.next()).notifyRemove();
                }
            addPropertyChange(evt);
        }

        this.elements = newMembers;
        
        /*
        if (!events.getElementImpl().isCreated() && chg.inserted != null) {
            insertIndices = chg.insertIndices;
            nextInsert = insertIndices[0];
            insertIt = chg.inserted.iterator();
        } else {
            nextInsert = -1;
            insertIt = null;
        }
        if (chg.removed != null)
            nextRemove = chg.removeIndices[0];
        else
            nextRemove = -1;
        if (chg.replacements != null) {
            nextReplace = chg.replaceIndices[0];
            replaceIt = chg.replacements.iterator();
        } else {
            nextReplace = -1;
            replaceIt = null;
        }

        int curPos = 0, newPos = 0;
        Iterator it = Arrays.asList(elements).iterator();
        
        while (nextInsert != -1 || nextReplace != -1 || nextRemove != -1 ||
            it.hasNext()) {
            if (curPos == nextReplace) {
                // replacing...
                Element newEl = (Element)replaceIt.next();
                
                Binding oldB, newB;
                oldB = getBinding(it.next());
                newB = getBinding(newEl);
                
                // replace old binding with the new one
                containerBinding.replace(oldB, newB);

                //Util.log("replacing from " + curPos + " to " + newPos); // NOI18N
                offsets[curPos] = newPos - curPos;
                curPos++; newPos++;
                if (replaceIt.hasNext()) 
                    nextReplace = chg.replaceIndices[++replacePos];
                else
                    nextReplace = -1;
                continue;
            } 
            if (newPos == nextInsert) {
                // check whether we can insert there...
                Binding b;

                //Util.log("inserting at pos " + newPos); // NOI18N
                if (nextInsert == 0) {
                    b = null;
                } else {
                    b  = getBinding(newMembers[newPos - 1]);
                }
                Element newElement = (Element)insertIt.next();
                ElementImpl newImpl = getElementImpl(newElement);
                newImpl.createAfter(containerBinding, b);
                events.getElementImpl().getModelImpl().notifyElementCreated(newElement);
                if (insertIt.hasNext()) {
                    nextInsert = insertIndices[++insertPos];
                } else {
                    nextInsert = -1;
                }
                //Util.log("next insert will be at " + nextInsert); // NOI18N
                newPos++;
                continue;
            } 
            if (curPos == nextRemove) {
                // removing...
                ElementImpl curImpl = getElementImpl((Element)it.next());
                offsets[curPos] = -curPos - 1;
                curImpl.notifyRemove();
                curPos++;
                if (++removePos < chg.removeIndices.length) {
                    nextRemove = chg.removeIndices[removePos];
                } else
                    nextRemove = -1;
                continue;
            } 
            if (it.hasNext()) {
                // just an ordinary element...

                offsets[curPos] = newPos - curPos;
                curPos++; newPos++;
            } else {
                Util.log("*** Confusion - nothing to do!"); // NOI18N
                Util.log("nextInsert = " + nextInsert); // NOI18N
                Util.log("nextReplace = " + nextReplace); // NOI18N
                Util.log("nextRemove = " + nextRemove); // NOI18N
                Util.log("curPos = " + curPos); // NOI18N
                Util.log("newPos = " + newPos); // NOI18N
                Util.log("it.hasNext = " + it.hasNext()); // NOI18N
                throw new InternalError("blah"); // NOI18N
            }
        }
         
        //Util.log("before reorder"); // NOI18N
        if (chg.reordered != null) {
            int[] reorder = chg.reordered;
            Map m = new HashMap(chg.reordered.length);
            for (int i = 0; i < reorder.length; i++) {
                if (reorder[i] == -1)
                    continue;
                int newIndex = reorder[i];
                Element src = elements[i];
                Element target = newMembers[newIndex];
                m.put(getBinding(target), getBinding(src));
            }
            // can fail --> rollback.
            containerBinding.reorder(m);
        }
        this.elements = newMembers;
        addPropertyChange(evt);
         */
    }
    
    protected void fireVetoableChange(PropertyChangeEvent evt) throws SourceException {
        events.fireVetoableChange(evt);
    }
    
    protected void addPropertyChange(PropertyChangeEvent evt) {
        events.addPropertyChange(evt);
    }
    
    protected int[] createIdentityMap(Element[] els) {
        Element[] olds = getElements();
        return super.createIdentityMap(els, olds);
    }

}
