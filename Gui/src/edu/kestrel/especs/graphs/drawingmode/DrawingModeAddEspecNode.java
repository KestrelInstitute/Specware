/*
 * DrawingModeAddEspecNode.java
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
public class DrawingModeAddEspecNode extends DrawingModeAddContainerBox {
    
    /** Creates a new instance of DrawingModeAddEspecNode */
    public DrawingModeAddEspecNode() {
        super();
        id = "AddEspecNode";
    }

    protected XNode createXNode(XGraphDisplay graph) {
        XContainerNode node = new EspecNode();
        CellView cv = graph.getView().getMapping(node,true);
        graph.getView().toBack(new CellView[]{cv});
        return node;
    }
    
    public ImageIcon getImageIcon() {
        return EConstants.e24Icon;
    }
    
    public String getMenuString() {
        return "Add ESpec Node";
    }
    
    
}
