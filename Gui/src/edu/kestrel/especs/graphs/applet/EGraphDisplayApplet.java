/*
 * EGraphDisplayApplet.java
 *
 * Created on November 18, 2002, 3:10 PM
 */

package edu.kestrel.especs.graphs.applet;

import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.applet.*;
import edu.kestrel.graphs.*;

/**
 *
 * @author  ma
 */
public class EGraphDisplayApplet extends XGraphDisplayApplet {
    
    /** Creates a new instance of EGraphDisplayApplet */
    public EGraphDisplayApplet() {
    }
    
    /** this method can be overwritten by sub-classers in order to create an instance of a sub-class
     * of <code>XGraphDisplay</code>
     *
     */
    public XGraphDisplay createXGraphDisplay() {
        return new EGraphDisplay("");
    }
    
}
