/*
 * DrawingModeAddEdge.java
 *
 * Created on October 25, 2002, 3:27 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.*;
import java.awt.event.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public abstract class DrawingModeAddEdge extends DrawingModeWithMarqueeHandler {
    
    protected String id;
    
    /** Creates a new instance of DrawingModeAddEdge */
    public DrawingModeAddEdge() {
        super();
        id = "AddEdge";
    }
    
    
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        return new MarqueeHandler(graph);
    }
    
    /** returns the id of the drawing mode.
     *
     */
    public String getId() {
        return id;
    }
    
    protected abstract XEdge createXEdge();
    
    protected class MarqueeHandler extends XMarqueeHandler {
        
        /** the edge object that is used during drawing */
        protected XEdge edge;
        
        /** start and end ports of the new edge */
        protected Port startPort, endPort;
        
        /** the point array of the new edge */
        protected ArrayList edgePoints;
        
        protected Rectangle highlightRectangle = null;
        
        /** flag showing the current mode */
        protected boolean isDrawingEdge = false;
        
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
        }
        
        
        public boolean isForceMarqueeEvent(MouseEvent e0) {
            MouseEvent e = fromScreenSnap(e0);
            if (isDrawingEdge) return true;
            if (getAndHighlightPortViewAt(e.getX(), e.getY()) != null) {
                return true;
            }
            return super.isForceMarqueeEvent(e0);
            //return true;
        }
        
        /** returns the port view, if there is one a position (x,y); the port will also be highlighted
         * by calling XDisplayGraph.setHighlightedPortView(). */
        protected PortView getAndHighlightPortViewAt(int x, int y) {
            try {
                PortView pv = graph.getPortViewAt(x,y);
                if (pv == null) {
                    //System.out.println("no port found at("+x+","+y+")");
                    graph.unsetHighlightedPortView();
                } else {
                    Map map = pv.getParentView().getAttributes();
                    if (GraphConstants.isVisible(map)) {
                        graph.setHighlightedPortView(pv);
                    } else {
                        graph.unsetHighlightedPortView();
                        pv = null;
                    }
                }
                //System.out.println("port view found at ("+x+","+y+")");
                graph.repaint();
                return pv;
            } catch (Exception e1) {
                return null;
            }
        }
        
        
        public void mousePressed(MouseEvent e0) {
            //System.out.println("mouse pressed in mode draw edge ...");
            //ignore, during drawing
            //e0.consume();
            if (isDrawingEdge) {
                if (getMouseButton(e0) == 3) {
                    cancelDrawing();
                }
                return;
            }
            MouseEvent e = fromScreenSnap(e0);
            int x = e.getX(), y = e.getY();
            PortView pv = getAndHighlightPortViewAt(x,y);
            if (pv == null) {
                edge = null;
                super.mousePressed(e0);
                return;
            }
            startPort = (Port) pv.getCell();
            startPoint = graph.snap(new Point(x,y));
            Map viewMap = new Hashtable();
            edge = createXEdge();
            edgePoints = new ArrayList();
            edgePoints.add(startPoint); edgePoints.add(startPoint);
            graph.insertEdge(edge, edgePoints);
            super.mousePressed(e0);
        }
        
        /** method called when the mouse is moved/dragged while the edge is drawn. */
        protected void mouseMovedWhileDrawing(MouseEvent e0) {
            if (edge == null) return;
            MouseEvent e = fromScreenSnap(e0);
            int x = e.getX(), y = e.getY();
            PortView pv = getAndHighlightPortViewAt(x,y);
            currentPoint = new Point(x,y);
            Map edgeMap = GraphConstants.createMap();
            if (edgePoints == null) return;
            edgePoints.set(edgePoints.size()-1,currentPoint);
            //GraphConstants.setPoints(edgeMap, edgePoints);
            //Map viewMap = new Hashtable();
            //viewMap.put(edge,edgeMap);
            //graph.getModel().insert(new Object[]{edge},null,null,viewMap);
            graph.setPointsOfEdge(edge, edgePoints);
            e0.consume();
        }
        
        /** method called when the drawing of the edge is finished; start and end point are stored in
         * the local variables startPoint and endPoint. */
        protected void connectEdge() {
            if ((edge != null) && (startPort != null) && (endPort != null)) {
                //ConnectionSet cs = new ConnectionSet(edge,startPort,endPort);
                //graph.getModel().insert(null,cs,null,null);
                //graph.getModel().edit(cs,null,null,null);
                graph.connectEdge(edge,startPort,endPort);
                EdgeView ev = (EdgeView) graph.getView().getMapping(edge,false);
                if (ev instanceof XEdgeView) {
                    //System.out.println("straightening edge...");
                    ((XEdgeView) ev).straightenEdge();
                    //System.out.println("straightening edge done.");
                }
            }
        }
        
        /** method called when the drawing of the edge is canceled, i.e. either the user has clicked with the right mouse
         * button, or startPort is equal to endPort */
        protected void cancelDrawing() {
            if (edge != null) {
                graph.getModel().remove(new Object[]{edge});
                isDrawingEdge = false;
                edge = null;
                Dbg.pr("drawing edge canceled.");
            }
        }
        
        public void mouseDragged(MouseEvent e0) {
            mouseMovedWhileDrawing(e0);
        }
        
        public void mouseReleased(MouseEvent e0) {
            if (edge == null) {
                super.mouseReleased(e0);
                return;
            }
            MouseEvent e = fromScreenSnap(e0);
            int x = e.getX(), y = e.getY();
            PortView pv = getAndHighlightPortViewAt(x,y);
            e0.consume();
            if (pv == null) {
                // add the edge with only a start port
                // can be continued to an end port
                currentPoint = new Point(x,y);
                Map edgeMap = GraphConstants.createMap();
                edgePoints.add(currentPoint);
                GraphConstants.setPoints(edgeMap, edgePoints);
                Map viewMap = new Hashtable();
                viewMap.put(edge, edgeMap);
                ConnectionSet cs = null; //new ConnectionSet(edge,startPort,null);
                graph.getModel().insert(new Object[]{edge},cs,null,viewMap);
                //graph.setSelectionCell(edge);
                Dbg.pr("added intermediate point.");
                isDrawingEdge = true;
                return;
            }
            isDrawingEdge = false;
            endPort = (Port) pv.getCell();
            if (endPort == startPort) {
                Dbg.pr("start port = end port");
                cancelDrawing();
                return;
            }
            connectEdge();
        }
        
        public void mouseMoved(MouseEvent e0) {
            if (isDrawingEdge) {
                mouseMovedWhileDrawing(e0);
            } else {
                MouseEvent e = fromScreenSnap(e0);
                highlightRectangle = null;
                PortView pv = getAndHighlightPortViewAt(e.getX(),e.getY());
                if (pv == null) return;
                e0.consume();
            }
        }
        
        
    }
}
