/*
 * ModelEdge.java
 *
 * Created on November 26, 2002, 5:15 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import java.util.*;
/**
 *
 * @author  ma
 */
public class ModelEdge extends ModelElement {
    
    protected ModelNode src;
    protected ModelNode trg;
    
    public ModelEdge() {
        super();
    }
    
    /** to be overwritten by sub-classers.
     */
    public boolean acceptsSource(ModelNode n) {
        return true;
    }
    
    /** to be overwritten by sub-classers.
     */
    public boolean acceptsTarget(ModelNode n) {
        return true;
    }
    
    /** returns the source node as <code>ModelNode</code> instance.
     */
    public ModelNode getSource() {
        return src;
    }
    /** returns the target node as <code>ModelNode</code> instance.
     */
    public ModelNode getTarget() {
        return trg;
    }
    
    public void setSource(ModelNode n) throws ModelException {
        if (!acceptsSource(n)) {
            throw new ModelException("cannot add node \""+n+"\" as source of this edge.");
        }
        if (src != null) {
            if (src.equals(n)) return;
            src.removeOutgoingEdge(this);
        }
        src = n;
        if (n != null) {
            n.addOutgoingEdge(this);
        }
        fireModelChange(null);
        Dbg.pr("new source of model edge "+this+" set to "+src);
    }
    
    public void setTarget(ModelNode n) throws ModelException {
        if (!acceptsTarget(n)) {
            throw new ModelException("cannot add node \""+n+"\" as target of this edge.");
        }
        if (trg != null) {
            if (trg.equals(n)) return;
            trg.removeIncomingEdge(this);
        }
        trg = n;
        if (n != null) {
            n.addIncomingEdge(this);
        }
        fireModelChange(null);
        Dbg.pr("new target of model edge "+this+" set to "+trg);
    }
    
    /** removes the model element.  */
    public void removeModelElement() {
        //super.removeModelElement();
        if (src != null) {
            src.removeOutgoingEdge(this);
        }
        if (trg != null) {
            trg.removeIncomingEdge(this);
        }
        src = null;
        trg = null;
        Dbg.pr("*********************** ModelEdge "+this+" removed.");
    }
    
    protected void fireModelChange(XTreeModelEvent e) {
        if (src != null) src.fireModelChange(null);
        if (trg != null) trg.fireModelChange(null);
    }
    
    /** inserts a freshly created representation element into the given graph.
     *
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem, Map elemReprMap) {
        if (elemReprMap.containsKey(getSource()) && elemReprMap.containsKey(getTarget())) {
            super.insertIntoGraph(graph,elem,elemReprMap);
            //XEdge edge = ((XEdge) reprExemplar).cloneEdge();
            XEdge edge = (XEdge)elem;
            XNode srcnode = (XNode) elemReprMap.get(getSource());
            XNode trgnode = (XNode) elemReprMap.get(getTarget());
            graph.insertEdge(edge,srcnode,edge.getSavedSrcPort(),trgnode,edge.getSavedTrgPort(), edge.getSavedIntermediatePoints());
            addRepr(edge);
            elemReprMap.put(this,edge);
            return edge;
        }
        return null;
    }
    
    /** sets this edge as model edge of all representations.
     */
    protected void setModelElementOfReprs() {
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XEdge edge = (XEdge) iter.nextElement();
            edge.setModelEdge(this);
        }
    }
    
    
    protected static String SourceNode = "SourceNode";
    protected static String TargetNode = "TargetNode";
    
    /** returns an element properties object representing this edge for the use in io operations.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        Dbg.pr("{ getElementProperties for ModelEdge "+this+"...");
        props.setValueProperty(getValue());
        ModelNode srcnode = getSource();
        ModelNode trgnode = getTarget();
        Dbg.pr("ModelEdge "+this+": source: "+srcnode+", target: "+trgnode);
        if (srcnode != null) {
            props.addChildObjectAsReference(SourceNode,srcnode);
        }
        if (trgnode != null) {
            props.addChildObjectAsReference(TargetNode,trgnode);
        }
        if (trgnode == null && srcnode == null) {
            props.setBooleanProperty("DELETE",true);
        }
        Dbg.pr("}");
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        String srcid = props.getChildObjectAsReference(SourceNode);
        if (srcid != null) {
            Storable obj = rwop.getObjectForId(srcid);
            if (obj instanceof ModelNode) {
                try {
                    setSource((ModelNode)obj);
                } catch (ModelException me) {}
            }
        }
        String trgid = props.getChildObjectAsReference(TargetNode);
        if (trgid != null) {
            Storable obj = rwop.getObjectForId(trgid);
            if (obj instanceof ModelNode) {
                try {
                    setTarget((ModelNode)obj);
                } catch (ModelException me) {}
            }
        }
    }
    
}
