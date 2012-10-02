/*
 * ModelException.java
 *
 * Created on November 26, 2002, 5:31 PM
 */

package edu.kestrel.graphs.spec;

/**
 * Instances of this class are used whenever an operation has been carried out that does not conform to the rules
 * implemented in the model node and edge classes. (E.g. an edge has been connected to a node which is not allowed to
 * be source or target of this edge.)
 * @author  ma
 */
public class ModelException extends java.lang.Exception {
    
    /**
     * Creates a new instance of <code>ModelException</code> without detail message.
     */
    public ModelException() {
    }
    
    
    /**
     * Constructs an instance of <code>ModelException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public ModelException(String msg) {
        super(msg);
    }
}
