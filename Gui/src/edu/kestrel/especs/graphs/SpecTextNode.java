/*
 * SpecTextNode.java
 *
 * Created on January 24, 2003, 6:30 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.graphs.*;

/**
 *
 * @author  ma
 */
public class SpecTextNode extends XTextNode {
    
    /** Creates a new instance of SpecTextNode */
    public SpecTextNode() {
    }
    /** sets some initial node value using a counter variable.
     */

    protected void setInitialValue() {
        setUserObject("spec"+System.getProperty("line.separator")+"end-spec");
    }
    
    
}
