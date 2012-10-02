/*
 * DrawingModeWithMarqueeHandler.java
 *
 * Created on October 23, 2002, 4:15 PM
 */

package edu.kestrel.graphs.drawingmode;

import edu.kestrel.graphs.*;
import com.jgraph.graph.*;
import java.awt.event.*;
import java.util.*;
/**
 * This class represents the superclass for all drawing modes that provide their own marquee handler.
 * On class instance creation, an marquee handler is initialized; the enter and exit methods take
 * care of storing and restoring the exisiting marquee handler of the XGraphDisplay.
 *
 * @author  ma
 */
public abstract class DrawingModeWithMarqueeHandler extends DrawingMode {
    
    protected Map modeLocalMarqueeHandler;
    protected Map savedMarqueeHandler;
    protected XGraphDisplay graph = null;
    
    public DrawingModeWithMarqueeHandler() {
        modeLocalMarqueeHandler = new Hashtable();
        savedMarqueeHandler = new Hashtable();
    }
    
    /** sub classes must provide this method for creating a MarqueeHandler that is used
     * when this drawing mode is active in the given graph.
     */
    protected abstract XMarqueeHandler createLocalMarqueeHandler(XGraphDisplay graph);
    
    /**
     * takes care of switching to the MarqueeHandler, which is local to this mode by calling
     * createLocalMarqueeHandler(). For each graph one instance of the local marquee handler is
     * created; this method takes care of storing and restoring the instances of the local
     * marwuee handler.
     */
    public void enter(XGraphDisplay graph) {
        // save the current marquee handler of the graph
        // so that we can restore it, when we exit the mode
        this.graph = graph;
        BasicMarqueeHandler oldmh = graph.getMarqueeHandler();
        if (oldmh != null) {
            savedMarqueeHandler.put(graph,oldmh);
        }
        // check whether we have already created a local handler for this graph
        // if no, create a new one and store in in the modeLocalMarqueeHandler map
        XBasicMarqueeHandler localmh = (XBasicMarqueeHandler) modeLocalMarqueeHandler.get(graph);
        if (localmh == null) {
            localmh = createLocalMarqueeHandler(graph);
            modeLocalMarqueeHandler.put(graph,localmh);
        }
        graph.setMarqueeHandler(localmh);
        try {
            EventListener[] listener = graph.getListeners(Class.forName("java.awt.event.KeyListener"));
            for(int i=0;i<listener.length;i++) {
                graph.removeKeyListener((KeyListener)listener[i]);
            }
        } catch (Exception ee) {}
        graph.addKeyListener(localmh);
    }
    
    /** exists this mode in the graph display. Restores the marquee handler saved for this
     * graph, when the mode has been entered.
     */
    public void exit(XGraphDisplay graph) {
        BasicMarqueeHandler savedmh = (BasicMarqueeHandler) savedMarqueeHandler.get(graph);
        if (savedmh != null) {
            graph.setMarqueeHandler(savedmh);
        }
        this.graph = null;
    }
    
}
