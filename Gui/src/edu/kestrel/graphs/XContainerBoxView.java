/*
 * XContainerBoxView.java
 *
 * Created on November 1, 2002, 7:29 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.geom.*;
import java.awt.*;

/**
 * Implements the view of a boxed-shaped container node.
 *
 * @author  ma
 */
public class XContainerBoxView extends XContainerView {
    
    /** Creates a new instance of XContainerBoxView */
    public XContainerBoxView(XContainerNode element, XGraphDisplay graph, CellMapper cm) {
        super(element,graph,cm);
        setRenderer(new XContainerBoxRenderer(this));
    }
    
    protected class XContainerBoxRenderer extends XContainerRenderer {
        
        public XContainerBoxRenderer(XContainerBoxView view) {
            super(view);
        }
        
        protected Shape getShape(RectangularShape b) {
            return new Rectangle2D.Double(b.getX(),b.getY(),b.getWidth(),b.getHeight());
        }
        
        
    }
    
}
