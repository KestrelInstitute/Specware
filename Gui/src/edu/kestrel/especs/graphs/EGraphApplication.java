/*
 * EGraphApplication.java
 *
 * Created on November 25, 2002, 4:20 PM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.*;

/**
 *
 * @author  ma
 */
public class EGraphApplication extends XGraphApplication {
    
    /** Creates a new instance of EGraphApplication */
    public EGraphApplication() {
        super();
    }

    protected XGraphDisplay createXGraphDisplay(Object value) {
        XGraphSpec spec = createXGraphSpec();
        EGraphDisplay graph = new EGraphDisplay(value,spec);
        return graph;
    }
    
    
    public XGraphSpec createXGraphSpec() {
        return new EGraphSpec();
    }
    
    public static void main(String[] args) {
        EGraphApplication appl = new EGraphApplication();
        EGraphDesktop dt = new EGraphDesktop(appl);
        XGraphApplication.startApplication(args,"Graphical Especs Environment",dt);
    }
    
}
