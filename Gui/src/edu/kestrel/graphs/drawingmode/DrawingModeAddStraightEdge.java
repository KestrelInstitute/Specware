/*
 * DrawingModeAddStraightEdge.java
 *
 * Created on October 31, 2002, 1:52 AM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import javax.swing.ImageIcon;

/**
 *
 * @author  ma
 */
public class DrawingModeAddStraightEdge extends DrawingModeAddEdge {
    
    /** Creates a new instance of DrawingModeAddStraightEdge */
    public DrawingModeAddStraightEdge() {
        id = "AddStraightEdge";
    }
    /** returns the icon image to be used in tool bars etc. for this drawing mode.
     *
     */
    public ImageIcon getImageIcon() {
        return IconImageData.straightIcon;
    }
    
    /** returns the string to be used in menus, tool tips etc. for this drawing mode.
     *
     */
    public String getMenuString() {
        return "Add Straight Edge";
    }
    
    
    protected XEdge createXEdge() {
        return new XStraightEdge();
    }
    
}
