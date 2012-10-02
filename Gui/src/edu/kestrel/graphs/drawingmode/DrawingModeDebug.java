/*
 * DrawingModeDebug.java
 *
 * Created on October 31, 2002, 5:20 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import edu.kestrel.especs.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class DrawingModeDebug extends DrawingModeWithMarqueeHandler {
    
    String id;
    
    /** Creates a new instance of DrawingModeDebug */
    public DrawingModeDebug() {
        super();
        id = "InternalDebug";
    }
    
    /** sub classes must provide this method for creating a MarqueeHandler that is used
     * when this drawing mode is active in the given graph.
     *
     */
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        return new MarqueeHandler(graph);
    }
    
    /** returns the icon image to be used in tool bars etc. for this drawing mode.
     *
     */
    public ImageIcon getImageIcon() {
        return IconImageData.information24Icon;
    }
    
    /** returns the string to be used in menus, tool tips etc. for this drawing mode.
     *
     */
    public String getMenuString() {
        return "Debug (internal)";
    }
    
    public String getId() {
        return id;
    }
    
    protected class MarqueeHandler extends XMarqueeHandler {
        
        GraphView view;
        XGraphModel model;
        
        
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
            view = graph.getView();
            model = graph.getXGraphModel();
        }
        
        private void printCell(String msg, Object obj) {
            if (obj == null) return;
            if (obj instanceof DefaultGraphCell) {
                DefaultGraphCell v = (DefaultGraphCell) obj;
                Dbg.pr(msg+v.getUserObject());
            }
        }
        
        public boolean isForceMarqueeHandler(MouseEvent e0) {
            return true;
        }
        
        public void mousePressed(MouseEvent e0) {
            e0.consume();
            MouseEvent e = fromScreenSnap(e0);
            
            /*
            JFrame f = ((XGraphDisplay)graph).getApplication().getDesktop().getFrame();
            Dbg.pr("desktop size: "+f.getSize());
            int answ1 = JOptionPane.showConfirmDialog(null,"Resize Desktop to (500,500)?","Resize?",JOptionPane.YES_NO_OPTION);
            if (answ1 == JOptionPane.YES_OPTION) {
                Dbg.pr("ok.");
                f.setSize(500,500);
            }
            */
            
            //Dbg.pr("children are selectable? "+graph.getSelectionModel().isChildrenSelectable());
            
            CellView[] roots = view.getRoots();
            
            //Dbg.pr("found #"+roots.length+" root views:");
            CellView[] sel = graph.getView().getMapping(graph.getSelectionCells());
            if (getMouseButton(e0) == 1) {
                //Dbg.pr(model.dump());
                //Dbg.pr(graph.getSelectionCount()+" elements selected.");
                //graph.translateAllViews(20,20,true);
                //graph.getView().translateViews(sel,20,20);
                //Dbg.pr("moving all views to origin...");
                //graph.moveAllViewsToOrigin();
                //graph.repaint();
                CellView cv = graph.getNextViewAt(null,e.getX()-20,e.getY());
                Dbg.pr("cv="+cv);
                if (cv instanceof XContainerView) {
                    XContainerView ccv = (XContainerView) cv;
                    ccv.collapse();
                    graph.repaint();
                    XNodeView clcv = ccv.cloneView(50,50,false);
                    if (clcv instanceof XContainerView) {
                        ((XContainerView)clcv).expand();
                    }
                }
            } else {
                //graph.translateAllViews(-20,-20, true);
                //XGraphView.translateViews(sel,-20,-20);
                int answ = JOptionPane.showConfirmDialog(e.getComponent(),"add nodes?","",JOptionPane.YES_NO_OPTION);
                if (answ == JOptionPane.YES_OPTION) {
                    StadNode stad1 = new StadNode();
                    StadNode stad2 = new StadNode();
                    StadNode stad3 = new StadNode();
                    EspecNode espec1 = new EspecNode("A");
                    EspecNode espec2 = new EspecNode("B");
                    graph.insertNode(stad1,new Rectangle(10,10,40,40));
                    graph.insertNode(stad2,new Rectangle(60,60,40,40));
                    graph.insertNode(stad3,new Rectangle(130,130,40,40));
                    graph.insertNode(espec1,new Rectangle(10,10,40,40));
                    graph.insertNode(espec2,new Rectangle(10,10,40,40));
                    StepEdge edge1 = new StepEdge();
                    StepEdge edge2 = new StepEdge();
                    graph.insertEdge(edge2,stad1,stad3, new Point[]{new Point(30,150)});
                    espec1.addChildNodes(graph,new XNode[] {stad1,stad2});
                    espec2.addChildNodes(graph,new XNode[] {espec1,stad3});
                    graph.insertEdge(edge1,stad1,stad2,new Point[]{new Point(80,30)});
                    espec1.collapse(graph);
                    espec2.collapse(graph);
                    graph.translateAllViews(50,50,true);
                }
                graph.repaint();
            }
            for(int i=0;i<roots.length;i++) {
                CellView cv = roots[i];
                Object obj = roots[i].getCell();
                //printCell("   ",obj);
            }
            
        }
        
        public void mouseMoved(MouseEvent e0) {
            MouseEvent e = fromScreenSnap(e0);
            Object obj = graph.getFirstCellForLocation(e0.getX(),e0.getY());
            //printCell("at cell: ",obj);
            CellView[] cvs = view.getMapping(new Object[]{obj});
            //Dbg.pr("cell is mapped to "+cvs.length+" view object(s).");
            for(int i=0;i<cvs.length;i++) {
                CellView cv = cvs[i];
                if (cv != null) {
                    view.toFront(new CellView[] {cv});
                }
            }
        }
        
    }
    
}
