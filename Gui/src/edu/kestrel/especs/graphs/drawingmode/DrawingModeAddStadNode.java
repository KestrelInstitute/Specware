/*
 * DrawingModeAddStadNode.java
 *
 * Created on November 15, 2002, 1:02 PM
 */

package edu.kestrel.especs.graphs.drawingmode;

import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.drawingmode.*;
import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;

/**
 *
 * @author  ma
 */
public class DrawingModeAddStadNode extends DrawingModeAddContainerBox {
    
    /** Creates a new instance of DrawingModeAddStadNode */
    public DrawingModeAddStadNode() {
        super();
        id = "AddStadNode";
    }

    protected XNode createXNode(XGraphDisplay graph) {
        XContainerNode node = new StadNode();
        CellView cv = graph.getView().getMapping(node,true);
        graph.getView().toBack(new CellView[]{cv});
        return node;
    }
    
    public ImageIcon getImageIcon() {
        return EConstants.stad24Icon;
    }
    
    public String getMenuString() {
        return "Add Stad Node";
    }
    
    
}
