/*
 * EventQueue.java
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

import java.beans.PropertyChangeEvent;
import java.util.*;

/**
 * Event/change queue that collects modification events made to a model in one locked
 * level of operations. After the model is unlocked, the events are merged up to the
 * parent. Upon unlocking the model entirely, the top-level queue will contain
 * both PropertyChangeEvents generated during the model locked operation and summary
 * changes that should be fired to CommitListeners.
 *
 */
class EventQueue extends Object {
    /**
     * The queue contains a stream of PropertyChangeEvents fired from locked operation(s), in the
     * order of their creation/firing.
     */
    Collection  eventQueue;
    /**
     * Map of elements -> event queue. Events are sorted by their creation time in the
     * queue; new elements are appended at the end.
     */
    Map     sourceMap;

    /**
     * Map that collects elements that have been changes and their corresponding
     * original properties (in a form of cloned element).
     */
    Map     changedElements;
    
    /**
     * Set that collects new elements.
     */
    Set     newElements;
    
    /**
     * Set that collects elements that have been removed.
     */
    Set     removedElements;
    
    /**
     * The parent event queue that collects events originating in the outer lock.
     */
    EventQueue      parent;
    
    private boolean firingEvents;
    
    /** Constructs an event queue, optionally linking it to a parent event queue.
     */
    public EventQueue(EventQueue parent) {
        this.parent = parent;
    }

    /**
     * Creates a notice that an element was changed. If the element is not registered
     * with the event queue, it is cloned to obtain the old version and put into the
     * element queue.
     */
    public void elementChanged(Element el, Element oldVersion) {
        if (containsChanges(el))
            return;
        if (changedElements == null) 
            changedElements = new HashMap(17);
        changedElements.put(el, oldVersion);
    }

    /**
     * Helper method that creates a notice that an element was changed. The passed
     * impl is asked to clone itself, if the element is not found in the changed
     * map already.
     */
    public void elementChanged(ElementImpl impl) {
        Element el = impl.getElement();
        if (containsChanges(el))
            return;
        if (changedElements == null) 
            changedElements = new HashMap(17);
        changedElements.put(el, impl.cloneSelf());
    }
    
    /**
     * Creates a notice that an element was created.
     */
    public void elementCreated(Element el) {
        if (newElements == null)
            newElements = new HashSet(17);
        newElements.add(el);
    }
    
    /**
     * Creates a notice that the element was removed.
     */
    public void elementRemoved(Element el) {
        if (newElements != null)
            newElements.remove(el);
        if (removedElements == null)
            removedElements = new HashSet(17);
        removedElements.add(el);
    }
    
    /**
     * Determines whether there's already a change notification for the passed element.
     * @return true, if the element was already reported as changed.
     */
    public boolean containsChanges(Element el) {
        if (newElements != null &&
            newElements.contains(el))
            return true;
        if (changedElements != null && 
            changedElements.containsKey(el))
            return true;
        // PENDING: investigate efficiency of the cloning in nested transaction. If
        // the cost is too high, then the parent need to be checked for the same conditions
        // too before returning false.
        return false;
    }
    
    /**
     * Records a property change event that occurs on a particular element. The change
     * is recorded into the element's queue.
     */
    public synchronized void addPropertyChange(ElementImpl impl, PropertyChangeEvent evt) {
        Object source = impl;        
        Collection queue = getQueue(source);        
        queue.add(evt);
        if (eventQueue == null)
            eventQueue = new LinkedList();
        eventQueue.add(impl);
        eventQueue.add(evt);
    }
    
    /**
     * Master method that fires PropertyChange events from the queues collected so far.
     */
    public void fireEvents() {
        synchronized (this) {
            if (firingEvents)
                return;
            firingEvents = true;
        }
        for (Collection col = pollEventQueue(); col != null && !col.isEmpty(); col = pollEventQueue()) {
            for (Iterator it = col.iterator(); it.hasNext(); ) {
                ElementImpl impl = (ElementImpl)it.next();
                PropertyChangeEvent evt = (PropertyChangeEvent)it.next();
                impl.firePropertyChangeEvent(evt);
            }
        }
        synchronized (this) {
            firingEvents = false;
        }
    }
    
    private void fireElementEvents(ElementImpl impl, Collection eventQueue) {
        for (Iterator it = eventQueue.iterator(); it.hasNext(); ) {
            PropertyChangeEvent evt = (PropertyChangeEvent)it.next();
            impl.firePropertyChangeEvent(evt);
        }
    }
    
    private synchronized Map pollEvents() {
        Map m = sourceMap;
        sourceMap = null;
        return m;
    }
    
    private synchronized Collection pollEventQueue() {
        Collection c = eventQueue;
        eventQueue = null;
        sourceMap = null;
        return c;
    }
    
    private synchronized Collection getQueue(Object source) {
        Collection c;
        
        if (sourceMap == null) {
            sourceMap = new HashMap(17);
            c = null;
        } else {
            c = (Collection)sourceMap.get(source);
        }
        
        if (c != null)
            return c;
        c = new LinkedList();
        sourceMap.put(source, c);
        return c;
    }
    
    /**
     * Fixates change events - for each changed element, it creates a snapshot of it to
     * record its exact state at the time of unlock for the reference of listeners that
     * are contacted out of the locked exec region.
     */
    public void fixupChanges() {
        if (changedElements == null)
            return;
        for (Iterator it = changedElements.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry en = (Map.Entry)it.next();
            Element source = (Element)en.getKey();
            Element oldSnapshot = (Element)en.getValue();
            
            ElementImpl impl = (ElementImpl)source.getCookie(ElementImpl.class);
            // impl != null!
            Element newSnapshot = impl.cloneSelf();
            
            en.setValue(new Object[] { oldSnapshot, newSnapshot });
        }
    }
    
    private void mergeChild(EventQueue other) {
        if (other.removedElements != null) {
            // discard any information about elements that were previously 
            // created. Discard all such elements from the removed set
            if (newElements != null) {
                Collection copy = new HashSet(other.removedElements);
                other.removedElements.removeAll(newElements);
                newElements.removeAll(copy);
            }
            if (removedElements == null)
                removedElements = other.removedElements;
            else
                removedElements.addAll(other.removedElements);
        }
        if (other.newElements != null) {
            if (newElements == null)
                newElements = other.newElements;
            else
                newElements.addAll(other.newElements);
        }
        if (other.changedElements != null) {
            if (newElements != null) {
                other.changedElements.keySet().removeAll(newElements);
            }
            if (changedElements != null)
                other.changedElements.putAll(changedElements);
            changedElements = other.changedElements;
        }
        if (other.sourceMap != null) {
            mergePropertyEventMaps(other.sourceMap);
        }
        if (other.eventQueue != null) {
            if (eventQueue == null)
                eventQueue = other.eventQueue;
            else
                eventQueue.addAll(other.eventQueue);
        }
    }

    /**
     * Merges the otherMap of property changes events into this one; the events are
     * merged so that they are appended at the end of the existing queue, if the
     * element's queue already exists, or the whole queue for an element is copied
     * into out map.
     */
    private synchronized void mergePropertyEventMaps(Map otherMap) {
        if (sourceMap == null) {
            sourceMap = otherMap;
            return;
        }
        for (Iterator otherIterator = otherMap.entrySet().iterator();
            otherIterator.hasNext(); ) {
            Map.Entry otherEntry = (Map.Entry)otherIterator.next();
            Object otherKey = otherEntry.getKey();
            Collection myQueue = (Collection)sourceMap.get(otherKey);

            if (myQueue == null)
                sourceMap.put(otherKey, otherEntry.getValue());
            else
                myQueue.addAll((Collection)otherEntry.getValue());
        }
    }

    /**
     * Merges all information in this queue into the parent one, if there's any.
     * The operation is destructive for this instance.
     */
    public void mergeToParent() {
        if (parent == null)
            return;
        parent.mergeChild(this);
    }
    
    public final Map getChangedElements() {
        return this.changedElements;
    }
    
    public final Set getCreatedElements() {
        return this.newElements;
    }
    
    public final Set getRemovedElements() {
        return this.removedElements;
    }
    
    public final EventQueue getParent() {
        return this.parent;
    }
    
    public void clearSummary() {
        newElements = removedElements = null;
        changedElements = null;
    }
    
    public boolean isEmpty() {
        if (newElements != null && !newElements.isEmpty())
            return false;
        if (changedElements != null && !changedElements.isEmpty())
            return false;
        return removedElements == null || removedElements.isEmpty();
    }
}
