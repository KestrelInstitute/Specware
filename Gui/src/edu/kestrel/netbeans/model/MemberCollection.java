/*
 * MemberCollection.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.model;

import java.util.*;

import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;

import org.netbeans.modules.java.model.IndexedPropertyBase;

import edu.kestrel.netbeans.Util;
    
/**
 * Main collection that holds all class members. The object also contain references to
 * partial collections made up from members of a specified type.
 * 
 * <B>MT note</B>: since the class is a helper implementation of a indexed property of some
 * model element, it assumes that the model synchronizes access to the property's access
 * operations.
 *
 */
class MemberCollection extends IndexedPropertyBase 
implements Positioner.Acceptor, ElementOrder {
    private static final Element[] EMPTY = new Element[0];
    
    /** All memebers of the declaring class.
     */
    Element[]   allMembers;
    
    /** Source that should be reported for events that are generated on behalf of
     * this object.
     */
    ElementEvents events;
    
    /** Binding to a container implementation
     */
    Binding.Container   containerBinding;
    
    /** Partial collection that should be informed about content changes to this object.
     */
    List partialCollections = new LinkedList();

    /** Interface that directs positioning of newly created Elements.
     */
    Positioner  positioner;
    
    private static final boolean DEBUG = false;
 
    public MemberCollection(ElementEvents events, Binding.Container containerBinding) {
        super(ElementProperties.PROP_MEMBERS);
        this.events = events;
        this.containerBinding = containerBinding;
        positioner = DefaultLangModel.DEFAULT_POSITIONER;
        allMembers = EMPTY;
    }

    public void setPositioner(Positioner pos) {
        this.positioner = pos;
    }
    
    /** Register partial collection (or view) that wants to cooperate with the members
     * collection. Partial views will be notified whenever a new slot is created or
     * an old one is removed from the main collection so they can update their data
     * structures.
     */
    public void addPartialCollection(PartialCollection col) {
        partialCollections.add(col);
    }
    
    /** Convenience method that calls, in turn, setMembers with a proper Change object.
     */
    void removeMembers(Collection toRemove, int[] indices) throws SourceException {
        Change ch = new Change();
        
        ch.removed = toRemove;
        ch.removeIndices = indices;
        ch.phaseCount = 1;
        ch.sizeDiff = toRemove.size();
        changeMembers(ch);
    }
    
    /** Attempts to find appropriate insert positions for the passed Elements.
     * The implementation may correct the returned data, if it finds that a returned
     * marker is not valid (belongs to another container, etc)
     */
  public Element[] findPositions(Element[] els) throws SourceException {
    try {
      events.getElementImpl().getModelImpl().notifyEventsDispatched(true);
      return positioner.findInsertPositions((Element)events.getEventSource(), els, this);
    } finally {
      events.getElementImpl().getModelImpl().notifyEventsDispatched(false);
    }
  }
    
    private ElementImpl getElement(Element el) {
        return (ElementImpl)el.getCookie(ElementImpl.class);
    }
    
    ElementImpl getElementImpl(Object o) {
        return getElement((Element)o);
    }
    
    public Element[] getElements() {
        if (allMembers == null) {
            return new Element[0];
        } else {
            return this.allMembers;
        }
    }
    
    public int[] changeMembers(IndexedPropertyBase.Change chg) throws SourceException {
        if (chg.phaseCount == 0) return null;
	Util.log("MemberCollection.changeMembers  this = "+this+" change = "+Util.print(chg));
	//Util.log("MemberCollection.changeMembers  allMembers = "+Util.print(allMembers));
        Element[] newMembers = new Element[allMembers.length + chg.sizeDiff]; 
        int nextInsert = -1, nextRemove = -1, nextReplace = -1; 
	int insertPos = 0, removePos = 0, replacePos = 0, curPos = 0, newPos = 0;
        Iterator insertIt = null, replaceIt = null; 
        ElementImpl[] newItems = null, removedItems = null;        
        boolean deferredCreation = false;
        int[] offsets = new int[allMembers.length];
        int offsetPos;
        int[] insertIndices = null;
        int indicePos = 0;
        Iterator it = Arrays.asList(allMembers).iterator();

        if (chg.inserted != null) {
	  insertIndices = chg.insertIndices;
	  nextInsert = insertIndices[0];
	  insertIt = chg.inserted.iterator();
	  // defer creation of children elements.
	  deferredCreation = events.getElementImpl().isCreated();
	  newItems = new ElementImpl[chg.inserted.size()];
        }
        if (chg.removed != null) {
	  nextRemove = chg.removeIndices[0];
	  removedItems = new ElementImpl[chg.removed.size()];
        }
        if (chg.replacements != null) {
	  nextReplace = chg.replaceIndices[0];
	  replaceIt = chg.replacements.iterator();
        }
        while (nextInsert != -1 || nextReplace != -1 || nextRemove != -1 || it.hasNext()) {
            if (newPos == nextInsert) {
                // check whether we can insert there...
                Element newElement = (Element)insertIt.next();
                Util.log("MemberCollection.changeMembers inserting "+newElement+" at pos " + newPos); // NOI18N
                newItems[insertPos] = getElementImpl(newElement);
                newMembers[newPos] = newElement;
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
                ElementImpl curImpl = getElementImpl(it.next());
                offsets[curPos] = -curPos - 1;
                // notify the element that is being removed;
                // can throw SourceException!
                curImpl.checkRemove();
                curPos++;
                removedItems[removePos] = curImpl;
                if (++removePos < chg.removeIndices.length) {
                    nextRemove = chg.removeIndices[removePos];
                } else
                    nextRemove = -1;
                continue;
            } 
            if (it.hasNext()) {
                // just an ordinary element...
                newMembers[newPos] = (Element)it.next();
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

        if (chg.reordered != null) {
	  int[] reorder = chg.reordered;
	  Map m = new HashMap(chg.reordered.length);
	  for (int i = 0; i < reorder.length; i++) {
	    int newIndex = reorder[i];
	    if (newIndex == -1) continue;
	    newMembers[newIndex] = allMembers[i];
	  }
            /*
            // can fail --> rollback.
            containerBinding.reorder(m);
             */
        }
        chg.offsets = offsets;
        chg.insertIndices = insertIndices;        
        if (!deferredCreation) {
            MultiPropertyChangeEvent evt = createPropertyEvent(chg, events.getEventSource(), getElements(), newMembers);
            events.fireVetoableChange(evt);
            containerBinding.changeMembers(evt);
            // we should also notify members that they were created or removed.
            if (newItems != null)
                for (int i = 0; i < newItems.length; i++) {
                    newItems[i].notifyCreate();
                }
            if (removedItems != null)
                for (int i = 0; i < removedItems.length; i++) {
                    removedItems[i].notifyRemove();
                }
            events.addPropertyChange(evt);
        } 
        this.allMembers = newMembers;
	Util.log("MemberCollection.changeMembers newMembers "+Util.print(newMembers) +" allMembers = "+Util.print(allMembers)); // NOI18N
	System.err.println("MemberCollection.changeMembers newMembers "+Util.print(newMembers)+" allMembers = "+Util.print(allMembers)); // NOI18N
        sanityCheck();
	fireContentSlotsChanged(offsets);
        return insertIndices;
    }

    /** Fires information about change(s) in content slots to registered partial
     * collections.
     */
    private void fireContentSlotsChanged(int[] offsets) {
        Iterator it = partialCollections.iterator();
        while (it.hasNext()) {
            ((PartialCollection)it.next()).contentSlotsChanged(offsets);
        }
    }
    
    /** Callback method that determines whether it is possible to insert after a particular
     * element (contained within this container). Delegates to the container binding and/or
     * the reference element binding. If the reference element is null, ability to insert
     * as the first contained element is tested.
     * @return true, if it is possible to introduce a new element after the reference one (or at
     * the beginning of the container, if the reference element is null).
     */
    public boolean canInsertAfter(Element el) {
        ElementImpl impl;
        
        // special case -- element is just being created.
        if (events.getElementImpl().isCreated())
            return true;
        
        if (el != null && el != Positioner.FIRST) {
            impl =  (ElementImpl)el.getCookie(ElementImpl.class);
            if (impl == null) {
                throw new IllegalArgumentException("Unsupported element implementation"); // NOI18N
            }
        } else
            impl = null;
        return containerBinding.canInsertAfter(impl == null ? null : impl.getBinding());
    }
    
    public void updateOrder(Element[] newEls) {
        Collection newMembers;
        Collection removedMembers;
        
        if (allMembers != null && allMembers.length > 0) {
            Element[] els = getElements();
            int[] map = createIdentityMap(newEls);
            Change chng = computeChanges2(els, newEls, map);
            if (chng.phaseCount == 0)
                return;
            MultiPropertyChangeEvent evt = createPropertyEvent(chng,     
                events.getEventSource(), els, newEls);
            events.addPropertyChange(evt);
            newMembers = chng.inserted;
            removedMembers = chng.removed;
        } else {
            newMembers = Arrays.asList(newEls);
            removedMembers = null;
        }
        if (newMembers != null && !newMembers.isEmpty()) {
            ElementImpl ownerImpl = events.getElementImpl();
            DefaultLangModel modelImpl = ownerImpl.getModelImpl();
            boolean notify = !ownerImpl.isCreated();
            
            for (Iterator it = newMembers.iterator(); it.hasNext(); ) {
                Element el = (Element)it.next();
                ElementImpl impl = getElement(el);
                impl.notifyCreate();
                if (notify)
                    modelImpl.notifyElementCreated(el);
            }
        }
        if (removedMembers != null && !removedMembers.isEmpty()) {
            for (Iterator it = removedMembers.iterator(); it.hasNext(); ) {
                Element el = (Element)it.next();
                ElementImpl impl = getElement(el);
                impl.notifyRemove();
            }
        }
        this.allMembers = newEls;
        if (DEBUG) {
            sanityCheck();
            for (Iterator it = partialCollections.iterator(); it.hasNext(); ) {
                PartialCollection p = (PartialCollection)it.next();
                p.sanityCheck();
            }
        }
    }

    protected int[] createIdentityMap(Element[] els) {
        Element[] olds = getElements();
        return super.createIdentityMap(els, olds);
    }

    public void updateMemberImpls(Collection members) {
        if (allMembers != null)
            throw new IllegalStateException("Updates not implemented yet"); // NOI18N
        
        this.allMembers = (Element[])members.toArray(new Element[0]);
    }
    
    void sanityCheck() {
        if (!DEBUG)
            return;
        
        Element[] allElements = getElements();
        
        HashMap m = new HashMap(allElements.length * 4 / 3);
        System.err.println("Sanity check " + this + " of " + events); // NOI18N
        for (int i = 0; i < allElements.length; i++) {
            if (allElements[i] == null) {
                System.err.println("element #" + i + " is null"); // NOI18N
                continue;
            }
            Integer x = (Integer)m.put(allElements[i], new Integer(i));
            if (x != null) {
                System.err.println("element #" + i + " and " + x.intValue() + " are identical"); // NOI18N
            }
        }
    }

    public String toString() {
	return "#MemberCollection"+Util.print(allMembers);
    }
}
