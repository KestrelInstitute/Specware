/*
 * DrawingModeAddBox.java
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
public class DrawingModeAddBox extends DrawingModeAddNode {
    
    /** Creates a new instance of DrawingModeAddBox */
    public DrawingModeAddBox() {
        super();
        id = "AddBox";
    }
    
    protected XNode createXNode(XGraphDisplay graph) {
        return new XBoxNode();
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.box24Icon;
    }
    
    public String getMenuString() {
        return "Add Box";
    }
    
}
