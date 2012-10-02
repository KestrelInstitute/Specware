/*
 * DrawingModeAddBezierEdge.java
 *
 * Created on October 31, 2002, 2:05 AM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import javax.swing.ImageIcon;

/**
 *
 * @author  ma
 */
public class DrawingModeAddBezierEdge extends DrawingModeAddEdge {
    
    /** Creates a new instance of DrawingModeAddBezierEdge */
    public DrawingModeAddBezierEdge() {
        super();
        id = "AddBezierEdge";
    }
    
    protected XEdge createXEdge() {
        return new XBezierEdge();
    }
    
    /** returns the icon image to be used in tool bars etc. for this drawing mode.
     *
     */
    public ImageIcon getImageIcon() {
        return IconImageData.bezierIcon;
    }
    
    /** returns the string to be used in menus, tool tips etc. for this drawing mode.
     *
     */
    public String getMenuString() {
        return "Add Bezier Edge";
    }
    
}
