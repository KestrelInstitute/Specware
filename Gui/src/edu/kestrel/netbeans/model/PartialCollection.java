/*
 * PartialCollection.java
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
import javax.swing.undo.UndoableEdit;

import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;
import org.netbeans.modules.java.model.IndexedPropertyBase;
import org.openide.ErrorManager;

import edu.kestrel.netbeans.Util;

/**
 * Implementation class that holds elements of a single type and maps them to a collection
 * of all members. The class manages operations on the partial collection and maps
 * them to operations on the whole collection. Mechanisms inherited from IndexedPropertyBase
 * allows detection of changes.
 *
 * This collection works in conjunction with {@link #MemberCollection}
 *
 */
abstract class PartialCollection extends IndexedPropertyBase {
    /**
     * Threshold for dump identity comparisons. If the avg number of compare ops *2 is
     * more than this value, faster hashing algorithm is used for discovering identities.
     * The value should balance the tradeoff between creating new objects and the comparisons.
     */
    public static final int SMALL_THRESHOLD = 500;
    
    /** Interface that performs event firing and provides basic information for
     * events (e.g. source of the event).
     */
    ElementEvents   events;
    
    /** Holds positions of individual elements in the ordered collection of all
     *  members.
     */
    private int[]   positions;
    
    /** Cached array of references to the wrapper Elements. This array is invalidated
     * after each modifying operation and constructed whenever some code asks
     * for
     */
    Element[]  elements;
    
    /** Reference to a collection that contains all members.
     */
    MemberCollection    allMembers;
    
    /** Model used for creation of new elements.
     */
    ElementCreator      creator;
    
    /** State variable -- causes this partial collection to ignore changes in
     * slot positions broadcasted by allMembers collection.
     */
    boolean             ignoreContentChange;
    
    private static final int[] EMPTY_POSITIONS = new int[0];
    
    protected static final boolean DEBUG = false;
    
    /** Constructs a new collection of elements of a particular type and binds
     * it to a owner's property.
     * @param ownerImpl implementation object of the collection's owner
     * @param allMembers collection of all members of that owner
     * @param propertyName name of the property this collection represents.
     */
    public PartialCollection(ElementEvents events, ElementCreator creator,
    MemberCollection allMembers, String propertyName) {
        super(propertyName);
        this.events = events;
        this.allMembers = allMembers;
        this.creator = creator;
        this.positions = EMPTY_POSITIONS;
        // tell the member collection about this partial one:
        allMembers.addPartialCollection(this);
    }
    
    /** Returns the Class object for element impls contained within the collection.
     */
    public abstract Class getElementImplClass();
    
    
    protected abstract ElementImpl createElement(Element parent);
    
    /** Creates empty array of the collection element's type for array-creation
     * operations.
     */
    protected abstract Object[] createEmpty();
    
    protected abstract Element[] createEmpty(int size);
    
    /** Returns indexes to collection of all members for individual
     * members of this collection/view.
     */
    public int[] getPositions() {
        return positions;
    }
    
    /** Returns array of Element objects for members contained within this collection.
     * The method optimizes read access in that it caches results of the query; the results
     * are invalidated by the first write operation.
     */
    public final Element[] getElements() {
        if (this.elements == null)
            return (Element[])createEmpty();
        else
            return this.elements;
    }
    
    public boolean isEmpty() {
        return this.elements == null || this.elements.length == 0;
    }
    
    /** Adds new members to the collection of elements and to the member collection
     * as well. The method fires VetoablePropertyChange on the property the collection
     * represents and it have the members collection fire VetoablePropertyChange on the
     * whole elements as well.<P>
     * This method is *only* responsible for translating the request into
     * desired insert positions in the whole collection, then delegating to the
     * MemberCollection to do the actual work.
     */
    public void addMembers(Element[] els) throws SourceException {
        if (els.length == 0) return;
        Util.log("PartialCollection.addMembers "+this+" els to be added "+els.length);
        Element[] insertingEls = new Element[els.length];
        Element[] elements = getElements();
        for (int i = 0; i < els.length; i++) {
            insertingEls[i] = copyElement(els[i]);
        }
        Element[] allElems = allMembers.getElements();
        Element[] precedings = allMembers.findPositions(insertingEls);
        Element[] newElems = createEmpty(insertingEls.length + elements.length);
        int[] insertIndices = new int[els.length];
        int[] newPositions = new int[newElems.length];
        
        // If an element wants to be inserted after another one, that another one
        // needs to be inserted first (if it is also new one)
        Map m = new HashMap(precedings.length * 4 / 3);

        Util.log("PartialCollection.addMembers "+this+" allMembers.length = "+allElems.length+" precedings.length =  "+precedings.length);
        for (int i = 0; i < precedings.length; i++) {
            // throw exception if prev is not a member.
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
                System.err.println("*** PartialCollection.addMembers: insert "+((MemberElement)insertingEls[i]).getName()+" after "+((MemberElement)precedings[i]).getName());
                m.put(precedings[i], insertingEls[i]);
            }
        }
        Element prevElem = Positioner.FIRST;
        int newPos = 0, oldPos = 0, inserted = 0;
        int newGlobalPos = 0, oldGlobalPos = 0;
        int[] newGlobalIndices = new int[els.length];
        for (oldGlobalPos = 0; oldGlobalPos <= allElems.length; oldGlobalPos++) {
            Object dependent = m.get(prevElem);
            if (dependent != null) {
                //System.err.println("*** PartialCollection.addMembers: inserting after global item #" + oldGlobalPos); // NOI18N
                LinkedList toInsert = new LinkedList();
                do {
                    if (dependent instanceof Collection)
                        toInsert.addAll((Collection)dependent);
                    else
                        toInsert.add(dependent);
                    Element newEl = (Element)toInsert.removeFirst();
                    newGlobalIndices[inserted] = newGlobalPos;
                    insertIndices[inserted] = newPos;
                    newElems[newPos] = newEl;
                    newPositions[newPos] = newGlobalPos;
                    
                    Util.log("*** PartialCollection.addMembers: newGlobalIndices["+inserted+"]="+newGlobalPos); // NOI18N
                    Util.log("*** PartialCollection.addMembers: insertIndices["+inserted+"]="+newPos); // NOI18N
                    Util.log("*** PartialCollection.addMembers: newElems["+newPos+"]="+((MemberElement)newEl).getName()); // NOI18N
                    Util.log("*** PartialCollection.addMembers: newPositions["+newPos+"]="+newGlobalPos); // NOI18N
                    
                    inserted++;
                    newPos++;
                    newGlobalPos++;
                    dependent = m.get(newEl);
                } while (dependent != null);
                // inserted everything chained after prevElem
            } else {
                Util.log("*** PartialCollection.addMembers: dependent is null inserted = "+inserted); // NOI18N
            }
            if (oldGlobalPos >= allElems.length)  break;
            prevElem = allElems[oldGlobalPos];
            // won't transfer.
            if (oldPos < elements.length && prevElem == elements[oldPos]) {
                // we processed our OWN element.
                newPositions[newPos] = newGlobalPos;
                //Util.log("*** PartialCollection.addMembers: newElems["+newPos+"]="+((MemberElement)elements[oldPos]).getName()); // NOI18N
                //Util.log("*** PartialCollection.addMembers: newPositions["+newPos+"]="+newGlobalPos); // NOI18N
                newElems[newPos++] = elements[oldPos++];
            }
            newGlobalPos++;
        }
        if (inserted < insertingEls.length){
            Util.log("PartialCollection.addMembers inserted "+inserted+" < insertingElements.length "+insertingEls.length);
            throw new IllegalArgumentException("Inconsistent insertion strategy"); // NOI18N
        }
        
        
        Change chng = new Change();
        chng.insertIndices = insertIndices;
        chng.inserted = Arrays.asList(insertingEls);
        chng.phaseCount = 1;
        chng.sizeDiff = insertingEls.length;
        
        MultiPropertyChangeEvent evt = createInsertionEvent(events.getEventSource(),
        elements, newElems, chng.inserted, insertIndices);
        
        chng.insertIndices = newGlobalIndices;
        // are we allowed to do that ??
        events.fireVetoableChange(evt);
        try {
            ignoreContentChange = true;
            Util.log("PartialCollection.addMembers Before MemberCollection change members this = "+this+" allMembers = "+allMembers.getElements().length);
            allMembers.changeMembers(chng);
            Util.log("PartialCollection.addMembers After MemberCollection change Memberss this = "+this+" allMembers = "+allMembers.getElements().length);
        } finally {
            ignoreContentChange = false;
        }
        events.addPropertyChange(evt);
        this.elements = newElems;
        Util.log("PartialCollection.addMembers this = "+this+" Setting positions to "+Util.print(newPositions));
        this.positions = newPositions;
        sanityCheck();
    }
    
    public void removeMembers(Element[] els) throws SourceException {
        Util.log("PartialCollection.removeMembers "+this+" els to be removed "+Util.print(els));
        Element[] elements = getElements();
        int[] removeIndices = createIdentityMap(els);
        // sanity check:
        for (int i = 0; i < removeIndices.length; i++) {
            if (removeIndices[i] == -1){
                String errorMessage = "";
                for (int j = 0 ; j < elements.length ; j++) {
                    errorMessage += ("\n"+elements[j].toString());
                    Util.log("PartialCollection.removeMembers element ["+j+"] = "+ elements[j]);
                } // end of for (int j = 0 ; j < elements.length ; j++)
                Util.log("PartialCollection.removeMembers element ["+i+"] = "+ elements[i]+" does not exist");
                throw new SourceException("PartialCollection.removeMembers \n Element \n"+elements[i].toString()+" \n does not exist"); // NOI18N
            }
        }
        Element[] newElems = createEmpty(elements.length - els.length);
        //Util.log("newElems = " + newElems.length); // NOI18N
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
    
    /** Sets the members to be *exactly* the members in the array. The operation is
     * in fact performed as a sequence of remove-add-reorder operations and fires exactly
     * one (possibly compound) property change event. This is probably the most complex
     * method, because it must handle arbitrary changes made to the whole set of elements
     * public void setMembers(Element[] els) throws SourceException {
     * // work on identities.
     * int[] mapping = createIdentityMap(els);
     * ElementImpl[] impls = getElements();
     * Change chng = computeChanges2(impls, els, mapping);
     * doSetMembers(createImplList(mapping, els), mapping, impls, chng);
     * }
     */
    
    public void updateMembers(Element[] members, int[] indices, int[] map) {
      //Util.log("PartialCollection.updateMembers "+this+" els to be updated "+Util.print(members));
      if (this.elements != null) {
	Element[] els = getElements();
	Element[] newEls = createEmpty(members.length);
	if (map == null)
	  map = createIdentityMap(members);
	Change chng = computeChanges2(els, newEls, map);
	if (chng.phaseCount > 0) {
	  events.addPropertyChange(createPropertyEvent(chng, events.getEventSource(),
						       els, members));
	}
      } else if (!events.getElementImpl().isCreated()) {
	int[] indexes = new int[members.length];
	Collection insert = new ArrayList(members.length);
	for (int i = 0; i < members.length; i++) {
	  indexes[i] = i;
	  insert.add(members[i]);
	}
	events.addPropertyChange(createInsertionEvent(events.getEventSource(),
						      createEmpty(), members, insert, indexes));
      }
      this.elements = members;
      //Util.log("PartialCollection.updateMembers this = "+this+" Setting positions to "+indices);
      this.positions = indices;
    }
    
    /** Copies an element over to this collection, creating a local implementation of
     * the element.
     */
    protected Element copyElement(Element el) {
        ElementImpl impl = createElement((Element)events.getEventSource());
        try {
            impl.createFromModel(el);
        } catch (SourceException ex) {
        }
        return impl.getElement();
    }
    
    public void setMembers(Element[] members) throws SourceException {
        Util.log("PartialCollection.setMember elements = "+members.length);
        Change chng;
        Element[] els = getElements();
        Element[] newEls = createEmpty(members.length);
        int[] map = createIdentityMap(members);
        int memberPos = 0;
        boolean copied = false;
        for (int i = 0; i < map.length; i++) {
            if (map[i] == -1) {
                Util.log("PartialCollection.SetMembers before Copy Element element to be copied "+members[i]);
                newEls[i] = copyElement(members[i]);
                Util.log("PartialCollection.SetMembers after copyElement new element = "+newEls[i]);
                copied = true;
            } else {
                newEls[i] = members[i];
            }
        }
        chng = computeChanges2(els, newEls, map);
        doSetMembers(newEls, chng);
    }
    
    /** Helper function, that tries to map insert indices from the partial collection to
     * the global one so that they can be used to update of the global collection.
     * The problem is, that there can be one or more 'foreign' elements in the global collection
     * between an element and the one that immediatelly follows in the partial collection.
     * Another problem is, that some of the elements may be in removal during the set operation.
     * The helper method tries to find a place that can accept the element.
     */
    private void mapInsertIndices(Change chng, int[] newPositions) throws SourceException {
        int[] iindices = chng.insertIndices;
        int[] offsets = chng.offsets;
        
        /*
        for (int i = 0; i < iindices.length; i++) {
            Util.log("insertion at " + iindices[i]); // NOI18N
        }
         
        for (int i = 0; i < newPositions.length; i++) {
            Util.log("newPosition[" + i + "] = " + newPositions[i]); // NOI18N
        }
         */
        
        int nextInsert = iindices[0];;
        int oldIndex = 0;
        int prevOldIndex = -1;
        Element[] all = allMembers.getElements();
        Element[] elements = getElements();
        
        // there IS insert operation, offsets are always != null.
        int newIndex;
        int iPos = 0;
        int globalPrecedingPos = -1;
        
        while (iPos < iindices.length) {
            // the while condition skips -1, too.
            if (oldIndex < offsets.length) {
                //Util.log("oldIndex = " + oldIndex + ", nextInsert = " + nextInsert); // NOI18N
                while ((newIndex = oldIndex + offsets[oldIndex]) < nextInsert) {
                    //Util.log("old slot #" + oldIndex + " -> slot #" + newIndex); // NOI18N
                    if (newIndex != -1) {
                        prevOldIndex = oldIndex;
                    }
                    oldIndex++;
                    if (oldIndex >= offsets.length) {
                        oldIndex = -1;
                        newIndex = newPositions.length;
                        break;
                    }
                }
                //Util.log("prevOld = " + prevOldIndex + ", afterOld = " + oldIndex); // NOI18N
                // now: oldIndex = index of old element AFTER the inserted run,
                // prevOldIndex == index of old element BEFORE the inserted run.
                // we must collect (old) elements in <prevOldIndex, oldIndex) from
                // the whole collection and ask whether it is possible to insert after
                // any of them.
                
                int globalBarrier;
                int testPos;
                int myPos;
                
                if (prevOldIndex == -1) {
                    globalPrecedingPos = testPos = -1;
                    myPos = 0;
                } else {
                    testPos = positions[prevOldIndex];
                    myPos = prevOldIndex + 1;
                    globalPrecedingPos = testPos + offsets[prevOldIndex];
                }
                if (oldIndex == -1) {
                    globalBarrier = all.length;
                } else {
                    globalBarrier = positions[oldIndex];
                }
                
                //Util.log("starting search from (new) global pos " + globalPrecedingPos); // NOI18N
                //Util.log("myPos = " + myPos + ", globalPrevPos = " + globalPrecedingPos + ", globalAfterPos = " + globalBarrier); // NOI18N
                while (true) {
                    if (testPos >= globalBarrier) {
                        throw new SourceException("cannot insert"); // NOI18N
                    }
                    Element ref = testPos < 0 ? null : all[testPos];
                    //Util.log("testing canInsertAfter(" + testPos + ")"); // NOI18N
                    if (allMembers.canInsertAfter(ref)) {
                        // got it!!  globalPrevPos is the element we want to insert
                        // after.
                        break;
                    }
                    if (myPos < elements.length && positions[myPos] != testPos) {
                        // the element is NOT being removed. Record for the case we will
                        globalPrecedingPos++;
                        //Util.log("changing prev global pos = " + globalPrecedingPos); // NOI18N
                    } else {
                        myPos++;
                    }
                    testPos++;
                }
            } else {
                newIndex = nextInsert + 1;
            }
            //Util.log("nextInsert = " + nextInsert + ", newIndex = " + newIndex); // NOI18N
            while (nextInsert < newIndex) {
                globalPrecedingPos++;
                //Util.log("Mapping iindices[" + iPos + "] to " + globalPrecedingPos); // NOI18N
                iindices[iPos] = globalPrecedingPos;
                newPositions[nextInsert] = globalPrecedingPos;
                iPos++;
                if (iPos < iindices.length)
                    nextInsert = iindices[iPos];
                else
                    break;
            }
        }
        /*
        for (int i = 0; i < newPositions.length; i++) {
            Util.log("newPosition[" + i + "] = " + newPositions[i]); // NOI18N
        }
         */
        
    }
    
    private void doSetMembers(Element[] newElements, Change chng) throws SourceException {
        int[] newPositions = new int[newElements.length];
        Element[] els = getElements();
        int[] offsets = chng.offsets;
        // removed, inserted, replacements are Elements
        //Util.log("change object= " + chng); // NOI18N
        MultiPropertyChangeEvent multiEvt = createPropertyEvent(chng, events.getEventSource(),
        getElements(), newElements);
        // special case for no-ops
        if (multiEvt == null) return;
        // notifies Vetoable listeners about the change, possibly failing with a SourceException
        events.fireVetoableChange(multiEvt);
        if (offsets != null) {
            for (int i = 0; i < els.length; i++) {
                int newPos = i + offsets[i];
                if (newPos >= 0) {
                    int newGlobPos = positions[i] + offsets[i];
                    //Util.log("slot #" + i + " moving to " + newPos); // NOI18N
                    newPositions[newPos] = newGlobPos;
                }
            }
        } else {
            // maintain the position array
            System.arraycopy(positions, 0, newPositions, 0, els.length);
        }
        if (chng.inserted != null) {
            mapInsertIndices(chng, newPositions);
        }
        mapIndices(chng.removeIndices, positions);
        mapIndices(chng.replaceIndices, positions);
        mapReorderIndices(chng, newPositions);
        try {
            ignoreContentChange = true;
            // delegate the actual change to the MemberCollection. Change object now
            Util.log("PartialCollection.doSetMembers "+this+"\n change = "+chng+"\n allMembers = "+allMembers.getElements().length);
            allMembers.changeMembers(chng);
            Util.log("PartialCollection.doSetMembers after calling changeMembers allMembers = "+allMembers.getElements().length);
            System.err.println("PartialCollection.doSetMembers after calling changeMembers allMembers = "+allMembers.getElements().length);
        } catch (SourceException ex){
            Util.log("PartialCollection.doSetMembers Source Exception in changeMembers for "+allMembers);
            ErrorManager.getDefault().notify(ex);
        } finally {
            ignoreContentChange = false;
        }
        Util.log("PartialCollection.doSetMembers this = "+this+" Setting positions to "+newPositions);
        this.positions = newPositions;
        // revalidate the cached element array.
        this.elements = newElements;
        Util.log("PartialCollection.doSetMembers  newElements "+newElements.length +" this.elements = "+this.elements.length); // NOI18N
        System.err.println("PartialCollection.doSetMembers  newElements "+newElements.length +" this.elements = "+this.elements.length); // NOI18N
        sanityCheck();
        events.addPropertyChange(multiEvt);
    }
    
    /** Maps reorder indices to the collection of all elements. All the required positions
     * are known in advance (except new members, but those do not appear in the reorder
     * operation. The method uses change object, and overwrites its reordered member.
     */
    private void mapReorderIndices(Change chng, int[] newPositions) {
        if (chng.reordered == null)
            return;
        int[] mainReorder = new int[allMembers.getElements().length];
        int[] myOrder = chng.reordered;
        Arrays.fill(mainReorder, -1);
        
        for (int i = 0; i < myOrder.length; i++) {
            // old position = index -> mapped by current positions.
            // new position = value -> mapped by the new positions.
            if (myOrder[i] == -1)
                continue;
            mainReorder[positions[i]] = newPositions[myOrder[i]];
            //Util.log("reorder-map: from " + positions[i] + " to "  + mainReorder[positions[i]]); // NOI18N
        }
        chng.reordered = mainReorder;
    }
    
    /* package private */
    void contentSlotsChanged(int[] offsets) {
        if (ignoreContentChange)
            return;
        int l = getElements().length;
        Util.log("PartialCollection.contentSlotsChanged Current Collection = "+this);
        Util.log("PartialCollection.contentSlotsChanged size of elements = "+l);
        Util.log("PartialCollection.contentSlotsChanged positions = "+positions +" offsets = "+offsets);
        Util.log("PartialCollection.contentSlotsChanged positions = "+positions.length +" offsets = "+offsets.length);
        for (int i = 0; i < l; i++) {
            Util.log("PartialCollection.contentSlotsChanged positions["+i+"] = "+positions[i]);
            //Util.log("PartialCollection.contentSlotsChanged offsets = "+offsets[positions[i]]);
            //if (offsets.length > positions[i]) {
	    Util.log("PartialCollection.contentSlotsChanged offsets = "+offsets[positions[i]]);
	    positions[i] += offsets[positions[i]];
	    //}
        }
        sanityCheck();
    }
    
    private static void mapIndices(int[] indices, int[] positions) {
        if (indices == null)
            return;
        for (int i = 0; i < indices.length; i++ ) {
            if (indices[i] == -1)
                continue;
            indices[i] = positions[indices[i]];
        }
    }
    
    /** Creates mapping from els to the currently held elements in the format that
     * computeChanges2() expects. The method implements a dumb n^2 algorithm for small
     * data sets -- that are smaller than {@link #SMALL_THRESHOLD}. HashMap is used
     * for larger data, provided that the ElementImpls' equals() and hashCode() are appropriate
     * for object identity tests (true for all elements).
     */
    protected int[] createIdentityMap(Element[] els) {
        Element[] olds = getElements();
        return super.createIdentityMap(els, olds);
    }
    
    protected final Object getSource(ElementImpl impl) {
        return impl.getElement();
    }
    
    public void changeMembers(Element[] items, int operation) throws SourceException {
        Util.log("PartialCollection.changeMembers "+this+" Element "+items.length+" operation = "+operation);
        for (int i = 0 ; i < items.length; i++){
            Util.log("PartialCollection.changeMembers Element ["+i+"]"+items[i]);
        }
        
        switch (operation) {
            case SpecElementImpl.ADD:
                addMembers(items);
                break;
            case SpecElementImpl.REMOVE:
                removeMembers(items);
                break;
            case SpecElementImpl.SET:
                Util.log("PartialCollection.changeMembers Setting Items");
                setMembers(items);
                break;
            default:
                throw new InternalError("Unknown/unsupported operation: " + operation); // NOI18N
        }
    }
    
    protected void sanityCheck() {
        if (!DEBUG)
            return;
        Element[] els = getElements();
        int[] indices = positions;
        Element[] allElements = allMembers.getElements();
        
        Util.log("Sanity check " + getClass() + " of " + events); // NOI18N
        if (els.length > 0) {
            if (indices.length < els.length) {
                Util.log("positions.length = " // NOI18N
                + positions.length + ", elements = " + els.length); // NOI18N
            }
        }
        ElementImpl parent = events.getElementImpl();
        boolean parentValid = parent.isValid();
        
        for (int i = 0; i < els.length; i++) {
            if (els[i] == null) {
                System.err.println("Element #" + i + " is null"); // NOI18N
                continue;
            }
            ElementImpl impl = (ElementImpl)els[i].getCookie(ElementImpl.class);
            if (impl == null) {
                System.err.println("memberimpl #" + i + // NOI18N
                " is null"); // NOI18N
                continue;
            }
            if (parentValid && !impl.isValid()) {
                System.err.println("element #" + i +  // NOI18N
                " is invalid"); // NOI18N
                continue;
            }
            int mainPos = indices[i];
            if (mainPos < 0 || mainPos >= allElements.length) {
                System.err.println("element #" + i + // NOI18N
                " has invalid position: "+ mainPos); // NOI18N
                continue;
            }
            if (allElements[mainPos] != els[i]) {
                System.err.println("element #" + i + " has incosistent position: " + // NOI18N
                mainPos + " -> " + allElements[mainPos]);
            }
        }
    }

    public String toString() {
	return "#PartialCollection"+Util.print(elements);
    }
}
