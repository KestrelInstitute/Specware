/*
 * EllipseView.java
 *
 * Created on October 24, 2002, 7:00 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.geom.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XEllipseView extends XNodeView {
    
    /** Creates a new instance of SimpleEllipseView */
    
    public XEllipseView(XNode element, XGraphDisplay graph, CellMapper cm) {
        super(element,graph,cm);
        setRenderer(new XEllipseRenderer(this));
    }
    
    public CellViewRenderer getRenderer() {
        return renderer;
    }
    
    protected class XEllipseRenderer extends XNodeRenderer {
        
        public XEllipseRenderer(XEllipseView view) {
            super(view);
        }
        
        protected Shape getShape(RectangularShape b) {
            return new Ellipse2D.Double(b.getX(),b.getY(),b.getWidth(),b.getHeight());
        }
    }
    
}
