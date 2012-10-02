/*
 * DrawingModeAddStepEdge.java
 *
 * Created on October 31, 2002, 1:52 AM
 */

package edu.kestrel.especs.graphs.drawingmode;

import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.drawingmode.*;
import edu.kestrel.graphs.*;
import javax.swing.ImageIcon;

/**
 *
 * @author  ma
 */
public class DrawingModeAddImportEdge extends DrawingModeAddEdge {
    
    /** Creates a new instance of DrawingModeAddImportEdge */
    public DrawingModeAddImportEdge() {
        id = "AddImportEdge";
    }
    /** returns the icon image to be used in tool bars etc. for this drawing mode.
     *
     */
    public ImageIcon getImageIcon() {
        return EConstants.import24Icon;
    }
    
    /** returns the string to be used in menus, tool tips etc. for this drawing mode.
     *
     */
    public String getMenuString() {
        return "Add Import Edge";
    }
    
    
    protected XEdge createXEdge() {
        return new ImportEdge();
    }
    
}

