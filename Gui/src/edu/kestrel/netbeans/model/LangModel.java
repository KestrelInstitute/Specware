/*
 * LangModel.java
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

import org.openide.nodes.Node;
import org.openide.src.SourceException;
import org.netbeans.modules.java.model.CommitListener;

import edu.kestrel.netbeans.model.Element;
import edu.kestrel.netbeans.model.SourceElement;

public interface LangModel extends ElementCreator {
    /** Acquires a read lock on the model. There can be no changes until the
     * lock is released. The same thread that has acquired the write lock may choose
     * to acquire a read lock as well. The opposite is true as well, as long there's only
     * a single reader - the current thread.
     */
    public void readLock();
    
    /** Releases the read lock.
     */
    public void releaseReadLock();
    
    /**
     * Returns true, if the model is write-locked currently. However, this method does not
     * guarantee, that, should it return false, writeLock called subsequently will not
     * block.
     */
    public boolean isWriteLocked();

    /**
     * Adds a listener that will be notified before the commit phase is over - that is
     * before the write lock is released. Please, use this type of listener with extreme
     * caution and do not make global changes from it and avoid event firing if possible.
     */
    public void addPreCommitListener(CommitListener l);

    /**
     * Removes pre-commit listener from the model.
     */
    public void removePreCommitListener(CommitListener l);
    
    /**
     * Attaches a CommitListener to the model. Post-commit listener gets a list of
     * changes after the lock is released. The listener can make further operations on the model,
     * risking that further events may be delayed.
     */
    public void addPostCommitListener(CommitListener l);

    /**
     * Removes the post-commit listener from the model.
     */
    public void removePostCommitListener(CommitListener l);
    
    /**
     * Executes an atomic action.
     */
    public void runAtomic(Runnable r) throws SourceException;

    public void commitChanges();
    
    /**
     * Acquires a write lock on the model and returns an opaque handle. There may be
     * at most *one* write lock active at any given time. Other threads asking for
     * a lock will be blocked.
     * @return handle for the write lock.
     */
    public Object writeLock();

    /**
     * Tries to acquire a write lock; if someone is holding the lock right now,
     * the method returns immediately null. You can use this method as a nonblocking
     * attempt to acquire the write lock.
     *
     * @return handle for the write lock, or null if the model is currently locked.
     */
    public Object tryWriteLock();
    
    /** Releases the write lock from the model. Requires the handle returned by
     * the prior call to writeLock(). If the handle is invalid, the method does not
     * unlock and throws IllegalArgumentException.
     * @param handle for unlocking.
     * @throws SourceException, if something goes wrong during the commit phase.
     * @throws IllegalArgumentException if the lock handle is invalid.
     */
    public void releaseWriteLock(Object handle) throws SourceException;

    /** Environmental interface that helps interaction between the model and its
     * environment. Virtually any services required by the model from outside should
     * be performed, or obtained from, this interface.
     */
    public static interface Env {
        /**
         * Callback function that will create a binding for an Element. The method can
         * return null, in which case it can be invoked later for that particular Impl,
         * or the Element will be assigned NullBinding, eventually.
         * @param impl implementation instance of the model's Element.
         * @return binding between the Element and its storage.
         */
        public BindingFactory getBindingFactory();
        
        /** Factory, that "wraps" element with the abstract layer fom the openide, optionally
         * providing some levels of indirection to an element.
         */
        public WrapperFactory getWrapperFactory();
        
        /** Asks the environment to feed back information local to the given scope.
         * Some Elements throughout the model support "lazy" evaluation. They will
         * ask the environment for the informations to be filled on the first 
         * operation on the local data. The element can, if it chooses, keep the
         * local data using WeakReferences, so it can ask for completion multiple
         * times.
         */
        public void complete(Element scope, int informationKind);
        
        /**
         * Since the model does not care for cookies, it needs to be supported by the
         * environment if somebody asks for a cookie on the Element.
         */
        public Node.Cookie findCookie(Element el, Class requestedClass);
        
        /**
         * Environment should remap the `markCurrent' call to some insertion
         * strategy.
	 public void markCurrentElement(Element marker, boolean beforeAfter);
	*/
    }
    
    public interface Updater extends LangModel, ElementProperties {
        public void updateMembers(Element target, String propertyName, 
				  Element[] els, int[] orderIndices, int[] optionalMap);

        /**
	 * Updates members in a specified container of a target element. In general,
	 * container types correspond with indexed property names.
	 */
        public void updateMemberOrder(Element target, String containerType,
				      Element[] orderedMembers);
        
        public Binding getElementBinding(Element target);
        
        /**
         * Special method that explicitly makes an element active. Inactive elements do not
         * fire property changes etc. Elements become automatically active, when inserted
         * into active container or when the container is activated.
         */
        public void activate(Element target);
        
        /**
         * Makes the whole model contents invalid.
         */
        public void invalidateModel(SourceElement el);

        /**
         * Runs the supplied runnable object in a special execution mode that can disable
         * property veto checks
         */
        public boolean runUpdate(Runnable r, boolean disableVetos) throws SourceException;

        /**
         * Fires some property change event on behalf of some element managed by
         * this model. Note that this <B>is a hack</B> method provided mostly
         * for PROP_COOKIES property change as most of the properties are
         * provided by the model's environment.
         */
        public void firePropertyChange(Element el, PropertyChangeEvent evt);
        
        /**
         * Updates a body property on the specified element, firing a property change
         * event when necessary.
         * @param contentHash must be a CRC-32 hash of the body content.
         */
        //public void updateBody(Element el, String bodyContent) throws UnsupportedOperationException;
    }
}
