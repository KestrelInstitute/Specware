/*
 * DrawingMode.java
 *
 * Created on October 23, 2002, 3:27 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import javax.swing.ImageIcon;

/**
 * A drawing mode describes a mode of the XGraphDisplay. The mode determines, for instance,
 * the actions to be triggered when mouse events occur. Typical drawing modes are: "add node"
 * where new nodes are added when the mouse is pressed; "select" where nodes and edges are selected when
 * mouse buttons are pressed, etc. The modes can define their own marquee handler which can then
 * take care of the different actions for the mouse in the specific mode. To change a mode in the
 * corresponding XGraphDisplay, the method "XGraphDisplay.switchMode" is called which first executes exit()
 * current mode, then sets the current mode to the new mode, and finally calls enter() for the new mode.
 * New drawing modes are added using XGraphDisplay.addDrawingMode. For a given XGraphDisplay the id's for
 * the drawing modes must be unique.
 */

public abstract class DrawingMode implements java.io.Serializable {
    /**
     * returns the id of the drawing mode.
     */
    public abstract String getId();
    
    /**
     * returns the string to be used in menus, tool tips etc. for this drawing mode.
     */
    public abstract String getMenuString();
    
    /**
     * returns the icon image to be used in tool bars etc. for this drawing mode.
     */
    public abstract ImageIcon getImageIcon();
    
    /**
     * contains code that is executed when the GraphDisplay switches to this drawing mode.
     * @param graph the XGraphDisplay that enters the this mode
     */
    public abstract void enter(XGraphDisplay graph);
    
    /**
     * contains code that is executed just before the GraphDisplay switches to another drawing mode.
     * @param graph the XGraphDisplay that exits the this mode
     */
    public abstract void exit(XGraphDisplay graph);
    
    /**
     * two drawing modes are equal, if they have the same id. If the argument is a String, it
     * is compared with the id of the drawing mode.
     */
    
    final public boolean equals(Object o) {
        if (o == null) return false;
        if (o instanceof DrawingMode) {
            DrawingMode dm = (DrawingMode) o;
            return getId().equals(dm.getId());
        } else
            if (o instanceof String) {
                String str = (String) o;
                return getId().equals(str);
            } else {
                return false;
            }
    }
    
    public String toString() {
        return getId();
    }
    
}
