/*
 * Storable.java
 *
 * Created on November 27, 2002, 10:43 PM
 */

package edu.kestrel.graphs.io;

/**
 * Interface used to read from and transform to instances of <code>ElementProperties</code>. This is used in io operation to
 * saved/load storable items.
 *
 * Important: all storable items must have a default constructor, i.e. a constructor with an empty argument list;
 * otherwise runtime errors will occur, if a saved Storable object has to be re-created.
 * @author  ma
 */
public interface Storable {
    
    public ElementProperties getElementProperties(ReadWriteOperation wop);
    
    public void initFromElementProperties(ReadWriteOperation rop, ElementProperties props);
    
}
