/*
 * VetoException.java
 *
 * Created on January 30, 2003, 3:14 PM
 */

package edu.kestrel.graphs.spec;

/**
 * Exception used to issue vetos against certain actions, e.g. removing of elements
 * @author  ma
 */
public class VetoException extends Exception {
    
    /** Creates a new instance of VetoException */
    public VetoException(String msg) {
        super(msg);
    }
    
}
