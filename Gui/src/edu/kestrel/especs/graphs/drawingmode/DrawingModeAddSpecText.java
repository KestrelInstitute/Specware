/*
 * DrawingModeAddSpecText.java
 *
 * Created on January 24, 2003, 6:33 PM
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
public class DrawingModeAddSpecText extends DrawingModeAddText {
    
    /** Creates a new instance of DrawingModeAddSpecText */
    public DrawingModeAddSpecText() {
        super();
        id = "AddSpecText";
    }
    
    protected XNode createXNode(XGraphDisplay graph) {
        return new SpecTextNode();
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.text24Icon;
    }
    
    public String getMenuString() {
        return "Add Spec Text";
    }
    
}
