/*
 * ModelElement.java
 *
 * Created on November 26, 2002, 5:55 PM
 */

package edu.kestrel.graphs.spec;

import edu.kestrel.graphs.*;
import edu.kestrel.graphs.event.*;
import edu.kestrel.graphs.io.*;
import java.util.*;

/**
 * Superclass for ModelNode and ModelEdge.
 * @author  ma
 */
public abstract class ModelElement implements Storable {
    
    /** counter for model elements; mainly used for debugging purposes.
     */
    static protected int elementCnt = 0;
    
    /** unique id for this model element; mainly used for debugging purposes.
     */
    protected int id;
    
    /** the parent of this element
     */
    protected ModelContainerNode parent;
    
    /** vector containing all representation objects currently existing for this model node.
     * The elements of this vector are of type XNode for ModelNode and XEdge for ModelEdge
     */
    protected Vector reprs;
    
    /** the representation exemplar that is kept if no actual representation element exists.
     */
    protected XGraphElement reprExemplar;
    
    /** the value of the node/edge; this is the only "builtin" property for all model elements.
     */
    protected Object value;
    
    public ModelElement() {
        this.value = null;
        initModelElement();
    }
    
    protected void initModelElement() {
        reprs = new Vector();
        id = elementCnt++;
        Dbg.pr("initModelElement: new model element \""+this+"\" created");
    }
    
    /** this method determines whether the model element must have at least one representation element or not;
     * subclassers can overwrite this method to control the behaviour in case the last representation element
     * of this model element is removed: if this method returns true, it will exist without having a representation;
     * if it returns false, the node/edge will be removed, if no representation element for it exists.
     */
    protected boolean existsWithoutRepresentation() {
        return false;
    }
    
    /** adds the first representation object, which is used to initialize the element's value.
     */
    public void addFirstRepr(XGraphElement xelem) {
        if (xelem != null) {
            addRepr(xelem);
            setValue(xelem.getUserObject());
        }
    }
    
    /** adds a new representation element to the list of representations.
     */
    public void addRepr(XGraphElement repr) {
        if (!reprs.contains(repr)) {
            reprs.add(repr);
            if (reprExemplar == null) {
                reprExemplar = repr;
            }
            Dbg.pr("new representation node added to "+value);
        }
        else Dbg.pr("'new' representation already exists for element "+this);
    }
    
    /** sets this element as model element of all representations.
     */
    protected abstract void setModelElementOfReprs();
    
    
    /** removes the given representation element from the list of representations.
     */
    public void removeRepr(XGraphElement repr) {
        reprs.remove(repr);
        Dbg.pr("repr of "+this+" removed.");
        if (!existsWithoutRepresentation()) {
            // throw away if no representation element is left
            if (reprs.size() == 0) {
                Dbg.pr("removing model element \""+this+"\", because the last representation object has been removed...");
                removeModelElement();
            }
        }
    }
    
    /** if representations currently exist in one of the graph displays of the application, this method returns an
     * enumeration of those (the ones that are store in the reprs field);
     * if no such representations exist, the reprExemplar field is checked, and -- if != null -- the enumeration jst
     * consisting of reprExemplar is returned;
     * if reprExemplar is null, this method returns null.
     */
    protected Enumeration getReprs() {
        if (reprs.size()>0)
            return reprs.elements();
        if (reprExemplar == null) return null;
        Vector v = new Vector();
        v.add(reprExemplar);
        return v.elements();
    }
    
    /** returns the saved representation exemplar. */
    public XGraphElement getReprExemplar() {
        return reprExemplar;
    }
    
    public abstract void removeModelElement();
    
    /** removes the model element and all representations in all graph displays of the application.
     */
    public void removeModelElement(XGraphApplication appl) {
        removeModelElement();
        Vector rem = new Vector();
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XGraphElement elem = (XGraphElement)iter.nextElement();
            rem.add(elem);
        }
        Enumeration iter0 = rem.elements();
        while(iter0.hasMoreElements()) {
            XGraphElement elem = (XGraphElement) iter0.nextElement();
            appl.removeXGraphElement(elem);
        }
    }
    
    /** returns the value field of this model element. */
    public Object getValue() {
        return value;
    }
    
    /** sets the value field of this model element. */
    public void setValue(Object value) {
        Dbg.pr("setValue("+value+")");
        this.value = value;
    }
    
    /** returns a short representation of the element's value as string to be used in popup windows etc.
     */
    public String getShortName() {
        if (getValue() == null) return "";
        String name = getValue().toString();
        if (name.length() > XGraphConstants.maxShortNameLength) {
            name = name.substring(0,XGraphConstants.maxShortNameLength) + "...";
        }
        return name;
    }
    
    
    
    /** inserts a freshly created representation element into the given graph.
     * @paran elem the graph element that is used as representation element
     * @param elemReprMap data structure mapping model elements to representations in the context of this
     * insertion operation
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem, Map elemReprMap) {
        if (elem == null)
            throw new IllegalArgumentException("displaying this element failed; no representation information found.");
        return elem;
    }
    
    /** inserts the model element into graph using elem as representation object
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, XGraphElement elem) {
        return insertIntoGraph(graph,elem,new Hashtable());
    }
    
    /** insert the model element into the graph using a copy of reprExemplar as representation object; elemReprMap contains
     * mappings from ModelElements to XGraphElement in the context of a insertion operation.
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph, Map elemReprMap) {
        XGraphElement repr = reprExemplar.cloneGraphElement();
        return insertIntoGraph(graph,repr,elemReprMap);
    }
    
    /** inserts the model element into the graph using a copy of reprExemplar as representation object.
     */
    public XGraphElement insertIntoGraph(XGraphDisplay graph) {
        XGraphElement repr = reprExemplar.cloneGraphElement();
        return insertIntoGraph(graph,repr);
    }
    
    /** synchronize this model element with all its representation objects by updating the representation objects
     * according to changed properties.
     */
    public void sync() {
        Enumeration iter = reprs.elements();
        while(iter.hasMoreElements()) {
            XGraphElement n = (XGraphElement) iter.nextElement();
            sync(n);
            n.repaintGraph();
        }
    }
    
    /** fires a model change to all listeners of this model element.
     */
    protected abstract void fireModelChange(XTreeModelEvent e);
    
    /** synchronizes this model element with the given representation element, which is part of the reprs. This method is called
     * from within sync() and can be used by subclassers to implement customized synch operations without iterating over the
     * list of representations.
     */
    protected void sync(XGraphElement n) {
        n.setFullUserObject(getValue());
    }
    
    protected static String Representation = "Representation";
    
    /** returns the instance of <code>ElementProperties</code> that is used in io operations as a representation of this
     * element.
     */
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = wop.createElementProperties(this);
        Enumeration iter = getReprs();
        if (iter != null) {
            while(iter.hasMoreElements()) {
                Storable obj = (Storable)iter.nextElement();
                props.addChildObject(Representation,obj);
            }
        }
        return props;
    }
    
    /** initializes a freshly created element of this class using the information stored in the given
     * ElementProperties instance. Used during io operations.
     */
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        initModelElement();
        Dbg.pr("{adding representations for model element "+this+"...");
        Dbg.pr(" #existing reprs: "+reprs.size());
        Enumeration iter = props.getChildObjectEnumeration(Representation);
        while(iter.hasMoreElements()) {
            ElementProperties cprops = (ElementProperties)iter.nextElement();
            XGraphElement elem = (XGraphElement) rwop.getObjectForId(cprops.getId());
            addRepr(elem);
        }
        //setModelElementOfReprs();
        Dbg.pr("}");
    }
    
    /** returns the string representation of this model elment, which is the string representation of the model element's value.
     */
    public String toString() {
        String res;
        if (value != null) {
            res = value.toString();
        } else {
            String cname = getClass().getName();
            int index = cname.lastIndexOf('.');
            String name;
            if (index<0)
                name = cname;
            else
                name = cname.substring(index+1);
            res = name+id;
        }
        int cnt = reprs.size();
        return res;// + "("+ String.valueOf(cnt) + ")";
    }
    
}
