package edu.kestrel.graphs;

import edu.kestrel.graphs.io.*;
import com.jgraph.graph.*;
import java.util.*;
import java.awt.*;

public interface XGraphElement extends Storable {
    
    /** method for initializing the graph element, when it is inserted in the XGraphDisplay <code>graph</code>
     * and it's associated view element is <code>viewObject</code>
     */
    public void insertHook(XGraphDisplay graph, XGraphElementView viewObject);
    
    /** called after the initial bounds of a graph element have been set.
     */
    public void setBoundsHook(XGraphDisplay graph, XGraphElementView viewObject, Rectangle bounds);
    
    /** method for creating the view object for a graph element. */
    public XGraphElementView createView(XGraphDisplay graph, CellMapper cm);
    
    /** called during a clone-operation on the graph element; used for performing customized cloning
     * action on this node/edge. 
     * @param mgr the instance of XCLoneManager that represents the current clone operation
     * @param original the original object of which the current object is a clone
     */
    public void cloneHook(XCloneManager mgr, Object original);
    
    /** returns a clone of the graph element.
     */
    public XGraphElement cloneGraphElement();
    
    public void setUserObject(Object obj);
    
    public Object getUserObject();
    
    /** removes the element and all its inner nodes and edges from the given model.
     */
    public void remove(GraphModel model);
    
    /** method to update the relevant data stored in the view object in this object. This method is called by the
     * view object whenever it is updated.
     */
    public void updateViewData(XGraphElementView view);
    
    public void setGraph(XGraphDisplay graph);
    
    public XGraphDisplay getGraph();
    
}
