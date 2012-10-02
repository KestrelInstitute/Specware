/*
 * ImportManager.java
 *
 * Created on January 30, 2003, 12:01 AM
 */

package edu.kestrel.especs.graphs;

import edu.kestrel.especs.graphs.spec.*;
import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.*;
import java.util.*;

/**
 *
 * @author  ma
 */
public class ImportManager extends XCloneManager {
    
    /** Creates a new instance of ImportManager */
    public ImportManager(XGraphDisplay graph, Object[] cells, XGraphDisplay destGraph, boolean readonly, boolean isCopy) {
        super(graph,cells,destGraph,readonly,isCopy);
    }
    
    public ImportManager(XGraphDisplay graph, Object[] cells, XGraphDisplay destGraph) {
        this(graph,cells,destGraph,false,false);
    }
    
    /** called when model edges are copied; calls <copy>copy.copyHook(orig)</code> by default.
     *
     */
    protected void copyModelEdge(ModelEdge orig, ModelEdge copy) {
        if ((orig instanceof StepModelEdge) && (copy instanceof StepModelEdge)) {
            ((StepModelEdge)copy).importHook((StepModelEdge)orig);
        } else {
            super.copyModelEdge(orig,copy);
        }
    }
    
    /** called when model nodes are copied; calls <copy>copy.copyHook(orig)</code> by default.
     *
     */
    protected void copyModelNode(ModelNode orig, ModelNode copy) {
        if ((orig instanceof StadModelNode) && (copy instanceof StadModelNode)) {
            ((StadModelNode)copy).importHook((StadModelNode)orig);
        } else if ((orig instanceof EspecModelNode) && (copy instanceof EspecModelNode)) {
            ((EspecModelNode)copy).importHook((EspecModelNode)orig);
        } else {
            super.copyModelNode(orig,copy);
        }
    }
    
    /** called when a graph element is copied/cloned; subclasser should always call <code>super.cloneXGraphElement()</code>.
     *
     */
    protected void cloneXGraphElement(Object orig, XGraphElement copy) {
        super.cloneXGraphElement(orig,copy);
    }
    /** called after completion of a copy operation for all copied model elements.
     */
    protected void modelElementPostCopyAction(Map modelElementMap, ModelElement orig, ModelElement copy) {
        if ((orig instanceof EspecModelNode) && (copy instanceof EspecModelNode)) {
            ((EspecModelNode)copy).postImportAction(modelElementMap,(EspecModelNode)orig);
        } else {
            super.modelElementPostCopyAction(modelElementMap,orig,copy);
        }
    }
    
    
}
