/*
 * ContainerSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.util.*;
import javax.swing.text.Position;

import org.openide.text.*;
import org.openide.src.SourceException;
import org.openide.src.MultiPropertyChangeEvent;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;

/**
 */
class ContainerSupport implements TextBinding.Container, ContainerImpl {
    /** Sorted set of children Bindings, sorted by their text position.
     */
    TreeSet     children;
    
    ElementBinding  parent;
    
    SourceText      source;
    
    /**
     * True, if the container should attempt to separate its members using blank newlines.
     */
    boolean         separateMembers;
    
    private static final Comparator CHILD_COMPARATOR = new PositionComparator();
    
    private static final boolean DEBUG = false;
    
    public ContainerSupport(SourceText s, ElementBinding parent) {
        this.source = s;
        this.parent = parent;
        children = createSet(null);
        // standard behaviour: separate member elements by newlines.
        separateMembers = true;
    }
    
    private Element getElement() {
        return parent.getElement();
    }
    
    public boolean isEmpty() {
        return children == null || children.isEmpty();
    }
    
    protected TreeSet createSet(Collection c) {
        TreeSet s = new TreeSet(CHILD_COMPARATOR);
        if (c != null)
            s.addAll(c);
        return s;
    }
    
    /**
     * Returns the first position occupied by the container, or null
     * if the container is empty.
     */
    public PositionRef getFirstPosition() {
        ElementBinding first;
        synchronized (this) {
            if (children.isEmpty())
                return null;
            
            first = (ElementBinding)children.first();
        }
        return first.wholeBounds.getBegin();
    }
    
    /**
     * Returns the last position occupied by the container, or null,
     * if the container is empty.
     */
    public PositionRef getLastPosition() {
        ElementBinding last;
        synchronized (this) {
            if (children.isEmpty())
                return null;
            
            last = (ElementBinding)children.last();
        }
        return last.wholeBounds.getEnd();
    }
    
    protected PositionBounds getContainerBounds() {
        //Util.log("ContainerSupport.getContainerBounds before findContainerBounds parent = "+parent);
        return parent.findContainerBounds(this);
    }    
    public void updateChildren(Collection c) {
        ElementBinding last = null;
        ElementBinding first = null;
        
        for (Iterator it = c.iterator(); it.hasNext(); ) {
            ElementBinding b = ((ElementBinding)it.next());
            if (first == null) {
                first = b;
            }
            b.containerRef = this;
            last = b;
        }
        children = createSet(c);
    }
    
    /**
     * Finds the next binding, given some anchor one.
     * @return binding, that follows b, or the first one if b is null.
     */
    public synchronized ElementBinding findNext(ElementBinding b) {
        SortedSet s;
        
        if (b == null) {
            if (children.isEmpty())
                return null;
            return (ElementBinding)children.first();
        }
        synchronized (source.getTreeLock()) {
            s = children.tailSet(b);
        }
        if (s.size() < 2)
            return null;
        Iterator it = s.iterator();
        it.next();
        return (ElementBinding)it.next();
    }
    
    public synchronized ElementBinding findPrevious(ElementBinding b) {
        SortedSet s;
        
        if (b == null) {
            if (children.isEmpty())
                return null;
            return (ElementBinding)children.last();
        }
        synchronized (source.getTreeLock()) {
            s = children.headSet(b);
        }
        if (s.size() < 1)
            return null;
        return (ElementBinding)s.last();
    }
    
    /**
     * Attempts to find a binding at the given location.
     */
    public ElementBinding findBindingAt(int pos) {
        Integer posObj = new Integer(pos);
        SortedSet s = children.tailSet(posObj);
        if (s == null || s.isEmpty())
            return null;
        return ((ElementBinding)s.iterator().next()).findBindingAt(pos);
    }
    
    public ElementBinding findParent() {
        return parent;
    }
    
    /** Determines, if the executing code is allowed to insert after the specified
     * binding.
     */
    public boolean canInsertAfter(Binding b) {
        if (!source.isAtomicAsUser())
            return true;
        
        ElementBinding previous = (ElementBinding)b;
        ElementBinding next;
        PositionRef first;
        PositionRef last;
        PositionBounds cb = getContainerBounds();
        
        if (!source.isGeneratorEnabled() || cb == null)
            return true;
        
        if (previous == null) {
            // b is the first member of the class (?) --> begin is the class body start.
            first = source.createPos(cb.getBegin().getOffset(),
            Position.Bias.Forward);
            if (children.isEmpty())
                next = null;
            else
                next = (ElementBinding)children.first();
        } else {
            // element binding can override the default (textual) behaviour.
            if (!previous.canInsertAfter())
                return false;
            first = source.createPos(previous.wholeBounds.getEnd().getOffset(),
            Position.Bias.Forward);
            SortedSet s = children.tailSet(previous);
            Iterator it = s.iterator();
            it.next();
            if (it.hasNext()) {
                next = (ElementBinding)it.next();
            } else {
                next = null;
            }
        }
        
        if (next != null) {
            last = source.createPos(next.wholeBounds.getBegin().getOffset() - 1,
            Position.Bias.Forward);
        } else {
            int endOffset = cb.getEnd().getOffset();
            
            if (endOffset != 0)
                endOffset--;
            last = source.createPos(endOffset,Position.Bias.Forward);
        }
        
        return source.canWriteInside(new PositionBounds(first, last));
    }
    
    public void reorder(Map fromToMap) throws SourceException {
        // disabled
    }
    public void replace(Binding oldBinding, Binding newBinding) throws SourceException {
        // disabled
    }
    public void insert(Binding toInitialize, Binding previous) throws SourceException {
        // disabled
    }
    
    /**
     * Attempts to insert an element between after binding "p"
     */
    public void insertChild(ElementBinding n, ElementBinding previous, ElementBinding next,
    PositionBounds bounds) throws SourceException {
        boolean emptyBefore, emptyAfter;
        
        /*
        if (separateMembers) {
            emptyBefore = emptyAfter = true;
        } else {
            emptyBefore = previous == null;
            emptyAfter = next == null;
        }
         */
        emptyBefore = emptyAfter = separateMembers;
        if (DEBUG) {
            System.err.println("Trying to insert " + n + " after " + previous + ", before " + next + " container bounds = " + // NOI18N
            bounds);
        }
        Util.log("ContainerSupport.insertChild before n.create n = "+n);
        n.create(this, previous, next, bounds, emptyBefore, emptyAfter);
    }
    
    public void insertChild(ElementBinding n, ElementBinding previous, ElementBinding next)
    throws SourceException {
        Util.log("ContainerSupport.insertChild(n,previous,next)  n = "+n);
        PositionBounds cb = getContainerBounds();
        Util.log("ContainerSupport.insertChild before n.create containerBounds is null "+(cb == null));
        if (cb == null) {
            PositionRef upperBound = parent.getEndPosition();
            cb = new PositionBounds(upperBound, upperBound);
        }
        Util.log("ContainerSupport.insertChild before next call to insertChild containerBounds = "+(cb==null));
        insertChild(n, previous, next, cb);
    }
    
    private void doReorder(Map reorderMap) throws SourceException {
        Collection refPositions = new ArrayList(reorderMap.size());
        
        for (Iterator it = reorderMap.keySet().iterator(); it.hasNext(); ) {
            ElementBinding impl = (ElementBinding)it.next();
            refPositions.add(impl.prepareInsert(null, false));
        }
        
        Iterator it2 = refPositions.iterator();
        for (Iterator it = reorderMap.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry en = (Map.Entry)it.next();
            ElementBinding b2 = (ElementBinding)en.getValue();
            
            PositionRef refPos = (PositionRef)it2.next();
            //b2.moveTo(refPos);
        }
    }
    
    protected void performRemove(MultiPropertyChangeEvent evt)
    throws SourceException {
        if (evt == null)
            return;
        Collection elems = evt.getAffectedItems();
        int[] removeIndices = evt.getIndices();
        boolean empty = ((Object[])evt.getNewValue()).length == 0;
        int pos = 0;
        for (Iterator it = elems.iterator(); it.hasNext(); pos++) {
            Element e = (Element)it.next();
            ElementBinding victim = source.findBinding(e);
            boolean collapse;
            
            if (this.separateMembers)
                collapse = true;
            else
                collapse = empty;
            victim.remove(collapse, collapse);
        }
    }
    
    private void performReorder(MultiPropertyChangeEvent evt, int[] offsets)
    throws SourceException {
        if (evt == null)
            return;
        
        Element[] oldEls = (Element[])evt.getOldValue();
        Element[] newEls = (Element[])evt.getNewValue();
        int[] indices = evt.getIndices();
        Collection refPositions = new ArrayList(oldEls.length);
        Collection items = new ArrayList(oldEls.length);
        
        ElementBinding[] toMove = new ElementBinding[newEls.length];
        int count = 0;
        
        ElementBinding refBinding = null;
        for (int i = 0; i < indices.length; i++) {
            if (indices[i] == -1)
                // no change in relative pos, or the element was removed.
                continue;
            toMove[indices[i]] = source.findBinding(oldEls[i]);
            /*
            System.err.println("moving " + oldEls[i] + " from index " + i +  // NOI18N
                " to index " + indices[i]); // NOI18N
             */
            count++;
        }
        
        //System.err.println("Moving elements..."); // NOI18N
        for (int i = 0; i < newEls.length; i++) {
            if (toMove[i] == null)
                continue;
            
            ElementBinding previous, next;
            ElementBinding moving = toMove[i];
            if (i > 0)
                previous = source.findBinding(newEls[i - 1]);
            else
                previous = null;
            if (i < newEls.length - 1)
                next = source.findBinding(newEls[i + 1]);
            else
                next = null;
            
            moving.moveTo(previous, next);
        }
    }
    
    private void performInsert(MultiPropertyChangeEvent evt)
    throws SourceException {
        if (evt == null)
            return;
        //Util.log("ContainerSupport.performInsert evt = "+evt);
        Collection inserted = evt.getAffectedItems();
        int[] indexes = evt.getIndices();
        Iterator it = inserted.iterator();
        Element[] newEls = (Element[])evt.getNewValue();
        int indexPos = 0;
        int existingPos = -1;
        Element[] allElems = (Element[])evt.getNewValue();
        PositionRef upperBound;
        ElementBinding nextBinding;
        
        for (int i = 0; i < inserted.size(); i++) {
            Element n = (Element)it.next();
            ElementBinding b = source.findBinding(n);
            ElementBinding previous;
            int idx = indexes[indexPos++];
            
            if (existingPos < idx) {
                int tempIndex = indexPos;
                existingPos = idx + 1;
                while (existingPos < allElems.length &&
                tempIndex < indexes.length &&
                existingPos == indexes[tempIndex]) {
                    existingPos++;
                    tempIndex++;
                }
            }
            if (existingPos >= allElems.length) {
                nextBinding = null;
            }
            else {
                nextBinding = source.findBinding(allElems[existingPos]);
                upperBound = nextBinding.wholeBounds.getBegin();
            }
            if (idx == 0)
                previous = null;
            else {
                Element ref = newEls[idx - 1];
                previous = source.findBinding(ref);
            }
            Util.log("ContainerSupport.performInsert before insert child binding = "+b+" previous "+previous+" nextBinding = "+nextBinding);
            insertChild(b, previous, nextBinding);
            Util.log("ContainerSupport.performInsert after insert child");
        }
    }
    
    public static final int OP_REORDER = 0;
    public static final int OP_INSERT = 1;
    public static final int OP_REPLACE = 2;
    public static final int OP_REMOVE = 3;
    
    public void changeMembers(final MultiPropertyChangeEvent evt)
    throws SourceException {
        if (!source.isGeneratorEnabled())
            // no changes -- code generation is disabled.
            return;
        //Util.log("ContainerSupport.changeMembers parent.GetElement() = "+parent.getElement());
        source.runAtomic(parent.getElement(), new ExceptionRunnable() {
            public void run() throws Exception {
                performChangeMembers(evt);
            }
        });
    }
    
    /**
     * Inserts, removes, reorders or replaces individual items as ordered in the
     * property change event.
     * If the operation fails, it *should* rollback the changes.
     */
    private void performChangeMembers(MultiPropertyChangeEvent evt)
    throws SourceException {
        
        // assumption: a head of an "insertion run" either starts right from the beginning
        // of the container, or follows another (non-inserted) element. We need to perform
        // all other operations BEFORE the insert.
        MultiPropertyChangeEvent removeEv, reorderEv, insertEv;
        
        Collection evs;
        int[] offsets;
        
        if (evt.getEventType() == evt.TYPE_COMPOUND) {
            evs = evt.getComponents();
            offsets = evt.getIndices();
        } else {
            evs = Collections.singletonList(evt);
            offsets = null;
        }
        removeEv = reorderEv = insertEv = null;
        for (Iterator it = evs.iterator(); it.hasNext(); ) {
            MultiPropertyChangeEvent tmp;
            
            tmp = (MultiPropertyChangeEvent)it.next();
            switch (tmp.getEventType()) {
                case MultiPropertyChangeEvent.TYPE_ADD:
                    insertEv = tmp;
                    break;
                case MultiPropertyChangeEvent.TYPE_REMOVE:
                    removeEv = tmp;
                    break;
                case MultiPropertyChangeEvent.TYPE_REORDER:
                    reorderEv = tmp;
                    break;
                default:
                    throw new IllegalArgumentException("Unknown operation " +  // NOI18N
                    tmp.getEventType());
            }
        }
        // remove & insert adjust slot positions to the new state.
        performRemove(removeEv);
        performInsert(insertEv);
        performReorder(reorderEv, offsets);
        computeChildren((Element[])evt.getNewValue());
    }
    
    private void computeChildren(Element[] els) {
        ElementBinding[] bindings = new ElementBinding[els.length];
        
        for (int i = 0; i < els.length; i++) {
            bindings[i] = source.findBinding(els[i]);
        }
        updateChildren(Arrays.asList(bindings));
    }
    
    
    private class Writer implements ExceptionRunnable {
        int operation;
        Map reorderMap;
        ElementBinding previous, current;
        
        Writer(Map reorder) {
            this.operation = OP_REORDER;
            this.reorderMap = reorder;
        }
        
        Writer(ElementBinding prev, ElementBinding toinsert) {
            this.previous = prev;
            this.current = toinsert;
            this.operation = OP_INSERT;
        }
        
        public void run() throws Exception {
            if (!source.isGeneratorEnabled())
                return;
            switch (operation) {
                case OP_INSERT:
                    /*
                    doInsert(current, previous);
                    break;
                     */
                case OP_REORDER:
                    doReorder(reorderMap);
                    break;
                default:
                    throw new UnsupportedOperationException("Unknown operation :" + operation); // NOI18N
            }
        }
    }
}
