/*
 * ReadWriteOperation.java
 *
 * Created on November 27, 2002, 9:55 PM
 */

package edu.kestrel.graphs.io;

import edu.kestrel.graphs.*;
import java.io.*;
import java.util.*;
/**
 * Instances of this class represent a read or write operation of graph and model elements.
 * The usage is as follows:
 * <ul>
 * <li> For <b>writing</b> a new instance of this class is created with the toplevel object,
 * which should be stored. Writing is carried out with a call to the method <code>computeAllElementProperties</code>,
 * which stores everything that is needed to recreate the toplevel object in this read-write-operation instance.
 * <li> For reading the toplevel object, i.e. re-creating a new instance of the toplevel object's class and its dependents,
 * the <code>createObject</code> method is used.
 * </ul>
 * @author  ma
 */
public class ReadWriteOperation implements Serializable {
    
    protected Map objectToIdMap;
    protected Map idToObjectMap;
    
    protected Map elementPropertiesMap;
    protected Map elementPropertiesIdMap;
    
    protected int objCnt = 0;
    
    protected Storable toplevelObject;
    protected ElementProperties toplevelProps;
    
    protected java.util.List graphlist;
    
    protected XGraphApplication appl;
    
    /** Creates a new instance of ReadWriteOperation */
    public ReadWriteOperation(XGraphApplication appl, Storable toplevelObject) {
        this.appl = appl;
        this.toplevelObject = toplevelObject;
        elementPropertiesMap = new Hashtable();
        elementPropertiesIdMap = new Hashtable();
        objectToIdMap = new Hashtable();
        idToObjectMap = new Hashtable();
        graphlist = new ArrayList();
    }
    
    public ReadWriteOperation(XGraphApplication appl) {
        this(appl,null);
    }
    
    public void initAfterRead(XGraphApplication appl) {
        this.appl = appl;
        elementPropertiesMap = new Hashtable();
        objectToIdMap = new Hashtable();
        idToObjectMap = new Hashtable();
        graphlist = new ArrayList();
        toplevelObject = null;
        setToplevelProps();
    }
    
    public XGraphApplication getAppl() {
        return appl;
    }
    
    /** returns a new instance of <code>ElementProperties</code> and registers it for the given object.
     * @param obj the object that is represented by the new ElementProperties instance
     * @param parentProps if the element properties instance is created as a child of some parent properties, this parameter
     * represents the parent properties object, if not, this field is empty.
     */
    public ElementProperties createElementProperties(Storable obj) {//, ElementProperties parentProps) {
        ElementProperties props = new ElementProperties(obj,this/*parentProps*/);
        addElementProperties(obj,props);
        return props;
    }
    
    /** returns a new instance of <code>ElementProperties</code> and registers it for the given object.
     * @param obj the object that is represented by the new ElementProperties instance
     */
    //public ElementProperties createElementProperties(Storable obj) {
    //    return createElementProperties(obj,null);
    //}
    
    /** initializes the object for a new read operation, that means that new onjects will be created during the
     * read operation. Therefore the objecttoid maps have to be re-initialized.
     */
    protected void initForReadOperation() {
        objectToIdMap = new Hashtable();
        idToObjectMap = new Hashtable();
        graphlist = new ArrayList();
        toplevelObject = null;
    }
    
    /** creates the toplevelObject using the stored element properties.
     */
    public Storable createObject() {
        initForReadOperation();
        if (toplevelProps == null) {
            Dbg.pr("nothing stored in here...");
            return null;
        }
        String id = toplevelProps.getId();
        Storable res = getObjectForId(id);
        return res;
    }
    
    /* register graph during a read operation; this information is used to carry out some update operations
     * after all element are added to a graph.
     */
    public void registerGraphDuringRead(XGraphDisplay graph) {
        if (graphlist == null) {
            graphlist = new ArrayList();
        }
        if (!graphlist.contains(graph)) {
            graphlist.add(graph);
            startReadingGraph(graph);
        }
    }
    
    /** the initial actions to be carried out before things are added to a graph during a read operation.
     */
    public void startReadingGraph(XGraphDisplay graph) {
        //graph.getXGraphView().startGroupTranslate();
    }
    
    /** the action to be carried out, after all elements have been added to a graph during a read operation.
     */
    protected void endReadingGraph(XGraphDisplay graph) {
        //graph.getXGraphView().endGroupTranslate();
    }
    
    /** call the endReadingGraph method for all registered graphs as last step of a read operation.
     */
    protected void endReadingRegisteredGraphs() {
        if (graphlist == null) return;
        Iterator iter = graphlist.iterator();
        while(iter.hasNext()) {
            XGraphDisplay graph = (XGraphDisplay)iter.next();
            endReadingGraph(graph);
        }
    }
    
    /** gets the next object the element properties of which hasn't been determined yet; this is used in the
     * context of a write operation.
     */
    protected Storable getNextObject() {
        Iterator iter = objectToIdMap.keySet().iterator();
        while(iter.hasNext()) {
            Object obj = iter.next();
            if (!elementPropertiesMap.containsKey(obj)) {
                return (Storable) obj;
            }
        }
        return null;
    }
    
    /** computes all the element properties that contain the information needed to represent the given objs.
     */
    public void computeAllElementProperties() {
        getIdForObject(toplevelObject);
        Storable obj;
        while ((obj = getNextObject()) != null) {
            Dbg.pr("{ computeAllElementProperties: processing "+obj+" of class "+obj.getClass().getName()+"...");
            obj.getElementProperties(this);
            Dbg.pr("}");
        }
        if (elementPropertiesMap.containsKey(toplevelObject)) {
            toplevelProps = (ElementProperties) elementPropertiesMap.get(toplevelObject);
            toplevelProps.setBooleanProperty("IsToplevel",true);
        }
        removeDeletedElementProperties();
    }
    
    /** set the toplevel prop by iterating over the entries of the elementPropertiesIdMap after a readFromFile operation.
     */
    public void setToplevelProps() {
        Iterator iter = elementPropertiesIdMap.values().iterator();
        while (iter.hasNext()) {
            ElementProperties props = (ElementProperties) iter.next();
            if (props.getBooleanProperty("IsToplevel")) {
                toplevelProps = props;
                return;
            }
        }
        toplevelProps = null;
    }
    
    /** returns a unique identifier in the context of this read/write operation
     */
    protected String generateId(Storable obj) {
        String cname = obj.getClass().getName();
        int index = cname.lastIndexOf('.');
        String id;
        if (index<0)
            id = cname;
        else
            id = cname.substring(index+1);
        id += "_"+objCnt++;
        return id;
    }
    
    static int ERRORIDCNT=0;
    /** returns the id for the given Storable in the context of this ReadWriteOperation; if no id is stored
     * for the given object, a fresh id is generated and stored for the object.
     */
    public String getIdForObject(Storable obj) {
        if (obj == null) {
            Dbg.pr("**** ERROR: trying to get an id for null object, throwing exception...");
            return "ERRORID"+(ERRORIDCNT++);
            //throw new IllegalArgumentException("trying to get an id for null object");
        }
        if (objectToIdMap.containsKey(obj)) {
            return (String) objectToIdMap.get(obj);
        }
        String id = generateId(obj);
        //Dbg.pr("id "+id+" generated for obj "+obj+".");
        objectToIdMap.put(obj,id);
        idToObjectMap.put(id,obj);
        return id;
    }
    
    /** returns the Storable that is associated with the given id; if no entry for the object exists, it's created using
     * the element properties map. This method is used in the context of a read operation
     */
    public Storable getObjectForId(String id, StorableInitActions actions) {
        Dbg.pr("{ getObjectForId("+id+")...");
        try {
            if (idToObjectMap.containsKey(id)) {
                Storable obj = (Storable) idToObjectMap.get(id);
                Dbg.pr("returning already created object "+obj+"}");
                if (actions != null) {
                    actions.preinitAction(obj);
                }
                return obj;
            }
            if (elementPropertiesIdMap.containsKey(id)) {
                ElementProperties props = (ElementProperties) elementPropertiesIdMap.get(id);
                Storable obj = props.createObject(this,actions);
                Dbg.pr("getObjectForId: new object "+obj+" created for id "+id);
                Dbg.pr("}");
                return obj;
            }
            Dbg.pr("*************** no object with id "+id+" found!");
        } catch (Exception ex) {
            ex.printStackTrace(new java.io.PrintStream(System.out));
        }
        Dbg.pr("}");
        return null;
    }
    
    public Storable getObjectForId(String id) {
        return getObjectForId(id,null);
    }
    
    /** returns the ElementProperties object that is stored for the given id, or null if it cannot be found.
     */
    public ElementProperties getElementPropertiesForId(String id) {
        if (elementPropertiesIdMap.containsKey(id)) {
            return (ElementProperties) elementPropertiesIdMap.get(id);
        }
        return null;
    }
    
    public void putObjectIdRelation(Storable obj, String id) {
        if (obj != null) {
            idToObjectMap.put(id,obj);
            objectToIdMap.put(obj,id);
            Dbg.pr("-----> object "+obj+" stored in idToObjectMap with id "+id);
        }
    }
    
    /** registers the given <code>ElementProperties</code> for the given Object.
     * The mapping is saved in the elementPropertiesMap with the object as key; also the
     * elementsPropertiesIdMap is actualized with a mapping from the props id field to the props.
     */
    protected void addElementProperties(Storable obj, ElementProperties props) {
        elementPropertiesMap.put(obj,props);
        addElementPropertiesWithId(props);
    }
    
    /** adds a mapping from the props' id to the props in the elementPropertiesIdMap.
     */
    public void addElementPropertiesWithId(ElementProperties props) {
        elementPropertiesIdMap.put(props.getId(),props);
    }
    
    protected void removeDeletedElementProperties() {
        Vector removeKeys = new Vector();
        Iterator iter = elementPropertiesMap.keySet().iterator();
        while(iter.hasNext()) {
            Object key = iter.next();
            ElementProperties props = (ElementProperties) elementPropertiesMap.get(key);
            if (props.getBooleanProperty("DELETED")) {
                removeKeys.add(key);
                elementPropertiesIdMap.remove(props.getId());
            }
        }
        Enumeration iter1 = removeKeys.elements();
        while(iter1.hasMoreElements()) {
            Object key = iter1.nextElement();
            elementPropertiesMap.remove(key);
        }
    }
    
    /** the string representing the line separator as returned by <code>System.getProperty("line.separator")</code>
     */
    static public String newline = System.getProperty("line.separator");
    
    /** returns the XML representation of the collected map of element properties.
     */
    public String toXml() {
        StringBuffer buf = new StringBuffer();
        String tag = "Model";
        buf.append("<?xml version=\"1.0\"?>"+newline);
        buf.append("<"+tag+">"+newline);
        Iterator iter = elementPropertiesMap.values().iterator();
        while(iter.hasNext()) {
            ElementProperties props = (ElementProperties) iter.next();
            if (!props.isChild()) {
                buf.append(props.toXml(" "));
            }
        }
        buf.append("</"+tag+">"+newline);
        return buf.toString();
    }
    
    
    /** prepare this object for writing into a file, i.e. all reference object will be removed.
     */
    protected void prepareForWrite() {
        elementPropertiesMap = null;
        objectToIdMap = null;
        idToObjectMap = null;
        appl = null;
        graphlist = null;
        toplevelObject = null;
        Iterator iter = elementPropertiesIdMap.keySet().iterator();
        while(iter.hasNext()) {
            ElementProperties props = (ElementProperties) elementPropertiesIdMap.get(iter.next());
            props.prepareForWrite();
        }
    }
    
    /** writes this object and the contained element properties to a file.
     */
    public void writeToFile(String filename) throws IOException {
        prepareForWrite();
        ObjectOutputStream ostream = new ObjectOutputStream(new FileOutputStream(filename));
        ostream.writeObject(this);
        ostream.close();
    }
    
    public static ReadWriteOperation createFromFile(XGraphApplication appl, String filename) throws IOException {
        ObjectInputStream istream = new ObjectInputStream(new FileInputStream(filename));
        try {
            ReadWriteOperation rwop = (ReadWriteOperation)istream.readObject();
            rwop.initAfterRead(appl);
            return rwop;
        } catch (ClassNotFoundException cnf) {
            throw new IOException("illegal file format: "+cnf.getMessage());
        }
    }
    
}
