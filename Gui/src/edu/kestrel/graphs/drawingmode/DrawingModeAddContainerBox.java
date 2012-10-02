/*
 * DrawingModeAddContainerBox.java
 *
 * Created on October 24, 2002, 6:44 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.tree.MutableTreeNode;
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class DrawingModeAddContainerBox extends DrawingModeAddNode {
    
    /** Creates a new instance of DrawingModeAddContainerBox */
    public DrawingModeAddContainerBox() {
        super();
        id = "AddContainerBox";
    }
    
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        //System.out.println("creating new mhandler for mode add node...");
        return new MarqueeHandler(graph);
    }
    
    
    protected XNode createXNode(XGraphDisplay graph) {
        XContainerNode node = new XContainerBoxNode();
        CellView cv = graph.getView().getMapping(node,true);
        graph.getView().toBack(new CellView[]{cv});
        return node;
    }
    
    public ImageIcon getImageIcon() {
        return IconImageData.container24Icon;
    }
    
    public String getMenuString() {
        return "Add Container Box";
    }
    
    public class MarqueeHandler extends DrawingModeAddNode.MarqueeHandler implements java.io.Serializable {
        
        protected int collapsedBoundsWidth;
        protected int collapsedBoundsHeight;
        
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
            collapsedBoundsWidth = collapsedBoundsHeight = 40;
        }
        
        public void setCollapsedBoundsWidth(int width) {
            this.collapsedBoundsWidth = width;
        }
        
        public void setCollapsedBoundsHeight(int height) {
            this.collapsedBoundsHeight = height;
        }
        
        public void mouseDragged(MouseEvent e0) {
            super.mouseDragged(e0);
            if (node != null) {
                CellView cv = graph.getView().getMapping(node,false);
                if (cv != null) {
                    if (cv instanceof XContainerView) {
                        ((XContainerView)cv).enableAddingOfContainedNodes(false);
                        ((XContainerView)cv).toBack();
                    }
                }
            }
        }
        
        public void mouseReleased(MouseEvent e0) {
            super.mouseReleased(e0);
            if (node == null) return;
            if (!(node instanceof XContainerNode)) return;
            XContainerNode cont = (XContainerNode) node;
            XContainerView contview = cont.getXContainerView(graph.getView());
            if (contview != null) {
                contview.addContainedNodes(true);
                contview.enableAddingOfContainedNodes(true);
                contview.setCollapsedBounds(new Rectangle(0,0,collapsedBoundsWidth,collapsedBoundsHeight));
                contview.addContainedNodes(true);
            }
        }
        
    }
    
}
