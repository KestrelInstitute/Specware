/*
 * DrawingModeAddNode.java
 *
 * Created on October 23, 2002, 3:31 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.ImageIcon;
import java.awt.*;
import java.awt.event.*;
import java.util.*;


/**
 * The default drawing mode for adding nodes.
 * @author  ma
 */
public abstract class DrawingModeAddNode extends DrawingModeWithMarqueeHandler {
    
    protected String id;
    
    /** Creates a new instance of DrawingModeAddBox */
    public DrawingModeAddNode() {
        super();
    }
    
    
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        //System.out.println("creating new mhandler for mode add node...");
        return new MarqueeHandler(graph);
    }
    
    public void enter(XGraphDisplay graph) {
        //System.out.println("entering mode add box...");
        super.enter(graph);
    }
    
    public void exit(XGraphDisplay graph) {
        //System.out.println("exiting mode add box...");
        super.exit(graph);
    }
    
    public abstract String getMenuString();
    
    public abstract ImageIcon getImageIcon();
    
    public String getId() {
        return id;
    }
    
    protected abstract XNode createXNode(XGraphDisplay graph);
    
    protected class MarqueeHandler extends XMarqueeHandler implements java.io.Serializable {
        
        protected XNode node;
        protected XContainerView possibleParentView;
        protected int initialWidth;
        protected int initialHeight;
        
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
            node = null;
            possibleParentView = null;
            initialWidth = initialHeight = 40;
        }
        
        public void setInitialWidth(int width) {
            this.initialWidth = width;
        }
        
        public void setInitialHeight(int height) {
            this.initialHeight = height;
        }
        
        public boolean isForceMarqueeEvent(MouseEvent e) {
            return (getMouseButton(e) == 1);
            //return true;
        }
        
        
        public void mousePressed(MouseEvent e0) {
            MouseEvent e = fromScreenSnap(e0);
            CellView cv = graph.getNextViewAt(null,e.getX(),e.getY());
            possibleParentView = null;
            if (getMouseButton(e) == 3) {
                super.mousePressed(e0);
                return;
            }
            node = null;
            if (cv != null) {
                if (cv instanceof XContainerView) {
                    possibleParentView = (XContainerView) cv;
                    if (!possibleParentView.isExpanded()) {
                        super.mousePressed(e0);
                        possibleParentView = null;
                        node = null;
                        return;
                    }
                    //possibleParentView.expand();
                } else {
                    super.mousePressed(e0);
                    node = null;
                    return;
                }
            }
            node = createXNode(graph);
            startPoint = new Point(e.getX(),e.getY());
            //graph.insertNode(node, new Rectangle(e.getX(),e.getY(),40,40));
            graph.insertNode(node, new Rectangle(e.getX(),e.getY(),initialWidth,initialHeight));

            if (possibleParentView != null) {
                Map viewMap = new Hashtable();
                ParentMap pm = new ParentMap();
                pm.addEntry(node,possibleParentView.getCell());
                graph.getModel().insert(null,null,pm,null);
                possibleParentView = null;
            }
            
        }
        
        public void mouseReleased(MouseEvent e0) {
            mouseDragged(e0);
            e0.consume();
            if (possibleParentView != null) {
                Map viewMap = new Hashtable();
                ParentMap pm = new ParentMap();
                pm.addEntry(node,possibleParentView.getCell());
                graph.getModel().insert(null,null,pm,null);
            }
            //node = null;
            ((XGraphDisplay)graph).switchToInitialDrawingMode();
        }
        
        public void mouseDragged(MouseEvent e0) {
            if (getMouseButton(e0) == 3) {
                super.mouseDragged(e0);
                return;
            }
            MouseEvent e = fromScreenSnap(e0);
            currentPoint = new Point(e.getX(),e.getY());
            int x = currentPoint.x;
            int y = currentPoint.y;
            if (node != null) {
                int w = Math.max(Math.abs(x-startPoint.x),initialWidth);
                int h = Math.max(Math.abs(y-startPoint.y),initialHeight);
                int x0 = Math.min(x,startPoint.x);
                int y0 = Math.min(y,startPoint.y);
                graph.setBoundsOfGraphElement(node, new Rectangle(x0,y0,w,h));
                return;
            }
            super.mouseDragged(e0);
        }
        
    }
}
