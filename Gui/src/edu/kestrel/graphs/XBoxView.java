/*
 * SimpleBoxView.java
 *
 * Created on October 24, 2002, 2:13 PM
 */

package edu.kestrel.graphs;

import com.jgraph.graph.*;
import java.awt.geom.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XBoxView extends XNodeView {
    
    /** Creates a new instance of SimpleBoxView */
    
    public XBoxView(XNode element, XGraphDisplay graph, CellMapper cm) {
        super(element,graph,cm);
        //System.out.println("creating a simple box view...");
        setRenderer(new XBoxRenderer(this));
    }
    
    protected class XBoxRenderer extends XNodeRenderer {
        
        public XBoxRenderer(XBoxView view) {
            super(view);
        }
        
        protected Shape getShape(RectangularShape b) {
            return new Rectangle2D.Double(b.getX(),b.getY(),b.getWidth(),b.getHeight());
        }
        
       
    }
    
}
