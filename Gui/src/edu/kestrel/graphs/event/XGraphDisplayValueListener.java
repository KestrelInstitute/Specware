/*
 * XGraphDisplayValueListener.java
 *
 * Created on December 2, 2002, 5:00 PM
 */

package edu.kestrel.graphs.event;

import edu.kestrel.graphs.*;
/**
 * Interface for listeners of changes of the value of a graph
 *
 * @author  ma
 */
public interface XGraphDisplayValueListener {
    
    void graphValueChanged(XGraphDisplay graph, Object oldValue, Object newValue);
    
}
