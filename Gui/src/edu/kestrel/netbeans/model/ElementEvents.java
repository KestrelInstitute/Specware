/*
 * ElementEvents.java
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
import java.beans.PropertyVetoException;

import javax.swing.undo.UndoableEdit;

import org.openide.src.SourceException;

/**
 *
 */
interface ElementEvents {
    /** Adds a PropertyChangeEvent to be fired. The event is not necessarily fired
     * immediately, but may be queued and fired after a lock on the element/model is
     * released. The method may throw IllegalArgumentException, if the event source
     * reported in the event does not match the return value of {@link #getSource}
     * @param evt the event to be fired
     */
    public void addPropertyChange(PropertyChangeEvent evt);
    
    /** Fires a property change event to Vetoable listeners. If a listener cancels
     * the ongoing change, its response is wrapped into a SourceException object which
     * is thrown from the method. The method may throw IllegalArgumentException, if the event source
     * reported in the event does not match the return value of {@link #getSource}
     * @param evt the event to be fired
     */
    public void fireVetoableChange(PropertyChangeEvent evt) throws SourceException;
    
    /** Adds another UndoableEdit. Generally there should be an edit for each partial
     * operation on any data structure. Those edits are grouped such that edits generated
     * during one particular change operation are always undone as a group.
     * @param edit the edit that should be queued in the undo queue
    public void addUndoableEdit(UndoableEdit edit);
     */
    
    /** Returns the event source for events that should be fired on this interface.
     * @return object representing the event source.
     */
    public Object getEventSource();
    
    /** Returns the implementation of the element.
     */
    public ElementImpl getElementImpl();
}
