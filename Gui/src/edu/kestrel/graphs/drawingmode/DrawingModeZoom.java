/*
 * DrawingModeZoom.java
 *
 * Created on October 30, 2002, 1:01 AM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import javax.swing.ImageIcon;
import java.awt.event.*;
import java.awt.*;
/**
 *
 * @author  ma
 */
public class DrawingModeZoom extends DrawingModeWithMarqueeHandler {
    
    String id;
    
    /** Creates a new instance of DrawingModeZoom */
    public DrawingModeZoom() {
        super();
        id = "Zoom";
    }
    
    /** contains code that is executed when the GraphDisplay switches to this drawing mode.
     * @param graph the XGraphDisplay that enters the this mode
     *
     */
    public void enter(XGraphDisplay graph) {
        super.enter(graph);
    }
    
    /** contains code that is executed just before the GraphDisplay switches to another drawing mode.
     * @param graph the XGraphDisplay that exits the this mode
     *
     */
    public void exit(XGraphDisplay graph) {
        super.exit(graph);
    }
    
    /** returns the id of the drawing mode.
     *
     */
    public String getId() {
        return id;
    }
    
    /** returns the icon image to be used in tool bars etc. for this drawing mode.
     *
     */
    public ImageIcon getImageIcon() {
        return IconImageData.zoom24Icon;
    }
    
    /** returns the string to be used in menus, tool tips etc. for this drawing mode.
     *
     */
    public String getMenuString() {
        return "Zoom";
    }
    
    /** sub classes must provide this method for creating a MarqueeHandler that is used
     * when this drawing mode is active in the given graph.
     *
     */
    protected XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph) {
        return new MarqueeHandler(graph);
    }
    protected class MarqueeHandler extends XMarqueeHandler {
        
        int startX;
        protected Point startPointOnScreen;
        protected int eventX, eventY;
        double startScale;
        protected ZoomThread zoomThread;
        
        public MarqueeHandler(XGraphDisplay graph) {
            super(graph);
        }
        
        
        public boolean isForceMarqueeEvent(MouseEvent e) {
            return true;
        }
        
        protected void terminateZooming() {
            if (zoomThread != null) {
                zoomThread.stopZooming();
            }
        }
        
        protected void setScaleAndAdjustView(double scale, boolean allowNegativeCoordinates) {
            graph.setScale(scale);
            Point newp = graph.fromScreen(new Point(eventX,eventY));
            //Dbg.pr("new point at start position: "+newp);
            //Point trans = new Point(eventX-newp.x,eventY-newp.y);
            //trans = graph.fromScreen(trans);
            graph.translateAllViews(newp.x-startPoint.x,newp.y-startPoint.y,allowNegativeCoordinates);
            startPoint = graph.fromScreen(new Point(eventX,eventY));
            graph.repaint();
        }
        
        public void mousePressed(MouseEvent e0) {
            MouseEvent e = fromScreenSnap(e0);
            terminateZooming();
            eventX = e0.getX();
            eventY = e0.getY();
            startPoint = new Point(e.getX(), e.getY());
            if (e.getClickCount() == 2) {
                setScaleAndAdjustView(1.0,true);
                graph.moveAllViewsToOrigin();
            } else {
                int inOrOut = (getMouseButton(e)==1?ZoomThread.ZOOM_IN:ZoomThread.ZOOM_OUT);
                zoomThread = new ZoomThread(inOrOut);
                zoomThread.start();
            }
            e.consume();
        }
        
        public void mouseDragged(MouseEvent e0) {
            e0.consume();
            eventX = e0.getX();
            eventY = e0.getY();
        }
        
        public void mouseReleased(MouseEvent e) {
            terminateZooming();
            e.consume();
        }
        
        protected class ZoomThread extends Thread {
            private boolean zooming;
            final static public int ZOOM_IN = 0;
            final static public int ZOOM_OUT = 1;
            private int inOrOut;
            private double scale;
            private double speed = 1.03;
            public ZoomThread(int inOrOut) {
                super();
                zooming = true;
                this.inOrOut = inOrOut;
                this.scale = graph.getScale();
            }
            public void stopZooming() {
                zooming = false;
            }
            public void run() {
                while (zooming) {
                    if (inOrOut == ZOOM_IN) {
                        scale = scale*speed;
                    } else {
                        scale = scale/speed;
                    }
                    //Dbg.pr("scale="+scale);
                    try {
                        setScaleAndAdjustView(scale,true);
                    } catch (Exception e) {
                    }
                    
                    try {
                        sleep(10);
                    } catch (InterruptedException e1) {}
                    
                }
            }
        }
    }
}
