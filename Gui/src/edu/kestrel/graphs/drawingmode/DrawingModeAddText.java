/*
 * DrawingModeAddText.java
 *
 * Created on October 24, 2002, 6:44 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;

/**
 *
 * @author  ma
 */
public class DrawingModeAddText extends DrawingModeAddNode {
    
    /** Creates a new instance of DrawingModeAddText */
    public DrawingModeAddText() {
        super();
        id = "AddText";
    }
    
    protected XNode createXNode(XGraphDisplay graph) {
        return new XTextNode();
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.text24Icon;
    }
    
    public String getMenuString() {
        return "Add Text";
    }
    
}
