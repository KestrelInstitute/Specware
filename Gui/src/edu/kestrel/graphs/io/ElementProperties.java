/*
 * ElementSaveInfo.java
 *
 * Created on November 27, 2002, 9:47 PM
 */

package edu.kestrel.graphs.io;

import edu.kestrel.graphs.*;
import java.util.*;
import java.awt.*;
/**
 * Instances of this class contain generic information about any kind of model
 * elements that can be used to save them into a file etc.
 * @author  ma
 */
public class ElementProperties implements java.io.Serializable {
    
    protected String className;
    protected String id;
    protected Object valueProperty;
    
    /** map from String -> Object for storing value attributes. */
    protected Map propertyMap;
    /** map from String -> Vector of ElementProperties for storing dependent children. */
    protected Map childMap;
    
    /** map from String -> Vector of String representing references children using their ids. */
    protected Map childRefMap;
    
    protected ReadWriteOperation rwop;
    protected Storable obj;
    
    /** the field is != null, if this instance of ElementProperties has been created as a child of this parent.
     */
    protected ElementProperties parentProps = null;
    
    /** flag used when generating XML output: if true, the toplevel element is not generated, only the child nodes
     * are present in the XML output.
     */
    protected boolean xmlHideToplevel = false;
    
    /** Creates a new instance of ElementProperties in the context of a ReadWriteOperation
     * @param obj the object that is represented by this ElementProperties instance
     * @param rwop the context of the properties element, used to retrieve information about other storable objects
     * @param parentProps if this instance is created as a child of some parent properties, this parameter
     * represents the parent properties object, if not, this field is empty.
     */
    protected ElementProperties(Storable obj, ReadWriteOperation rwop, ElementProperties parentProps) {
        this.obj = obj;
        this.rwop = rwop;
        this.parentProps = parentProps;
        propertyMap = new Hashtable();
        childMap = new Hashtable();
        childRefMap = new Hashtable();
        if (obj != null) {
            className = obj.getClass().getName();
            id = rwop.getIdForObject(obj);
        }
    }
    
    /** Creates a new instance of ElementProperties in the context of a ReadWriteOperation; calls the constructor with
     * parentProps = null.
     */
    public ElementProperties(Storable obj, ReadWriteOperation rwop) {
        this(obj,rwop,null);
    }
    
    public void setClassName(String className) {this.className = className;}
    public String getClassName() {return className;}
    public void setId(String id) {this.id = id;}
    public String getId() {return id;}
    
    /** sets the parent properties of this object; this method is used by an enclosing element properties instance
     * to mark it as a child.
     */
    public void setParent(ElementProperties parentProps) {
        this.parentProps = parentProps;
    }
    
    /** sets the flags that signals whether the toplevel element should be hidden or not when XML
     * output is generated.
     */
    public void setXmlHideToplevel(boolean b) {
        xmlHideToplevel = b;
    }
    
    /** returns true, if this element properties are embedded as child properties in its parent properties.
     */
    public boolean isChild() {
        return (parentProps != null);
    }
    
    public void setProperty(String name, Object value) {
        Object val = value;
        if (value == null) val = "";
        if (propertyMap.containsKey(name)) {
            propertyMap.remove(name);
        }
        propertyMap.put(name,val);
    }
    
    /** stores the property <code>name</code> using the id for the storable as determined using the <code>getIdForObject</code>
     * method of the <code>ReadWriteOperation</code> associated with this <code>ElementProperties</code> object.
     * Property names must be unique for an instance of ElementProperties
     */
    public void setProperty(String name, Storable value) {
        String valueId = rwop.getIdForObject(value);
        setProperty(name,(Object)valueId);
    }
    
    public Object getProperty(String name) {
        return propertyMap.get(name);
    }
    
    /** convenience method for setting a rectangle property.
     */
    public void setRectangleProperty(String name, Rectangle b) {
        if (b == null) return;
        setProperty(name+"XPos",String.valueOf(b.x));
        setProperty(name+"YPos",String.valueOf(b.y));
        setProperty(name+"Width",String.valueOf(b.width));
        setProperty(name+"Height",String.valueOf(b.height));
    }
    
    /** returns the rectangle that is stored as properties name+"XPos", name+"YPos", name+"Width", and name+"Height";
     * any missing properties will be set to 0.
     */
    public Rectangle getRectangleProperty(String name) {
        Point p = getPointProperty(name);
        Dimension dim = getDimenstionProperty(name);
        return new Rectangle(p.x,p.y,dim.width,dim.height);
    }
    
    /** returns true, if a rectangle property with key name is stored in this object.
     */
    public boolean hasRectangleProperty(String name) {
        return (hasPointProperty(name) && hasDimensionProperty(name));
    }
    
    /** convenience method for setting a point property.
     */
    public void setPointProperty(String name, Point p) {
        if (p == null) return;
        setProperty(name+"XPos",String.valueOf(p.x));
        setProperty(name+"YPos",String.valueOf(p.y));
    }
    
    /** returns the Point property stored as name+"XPos" and name+"YPos" property; if a property doesn't exist,
     * it will be set to 0.
     */
    public Point getPointProperty(String name) {
        int xpos = getIntProperty(name+"XPos");
        int ypos = getIntProperty(name+"YPos");
        return new Point(xpos,ypos);
    }
    
    /** returns true, if a point property with key name is stored in this object.
     */
    public boolean hasPointProperty(String name) {
        return ((getProperty(name+"XPos")!=null) && (getProperty(name+"YPos")!=null));
    }
    
    /** sets the dimension dim as property name+"Width" and name+"Height"
     */
    public void setDimensionProperty(String name, Dimension dim) {
        setProperty(name+"Width",String.valueOf(dim.width));
        setProperty(name+"Height",String.valueOf(dim.height));
    }
    
    /** returns the Dimension property stored as name+"Width" and name+"Height"; if a property doesn't exist,
     * it will be set to 0.
     */
    public Dimension getDimenstionProperty(String name) {
        int width = getIntProperty(name+"Width");
        int height = getIntProperty(name+"Height");
        return new Dimension(width,height);
    }
    
    /** returns true, if a dimension property with key name is stored in this object.
     */
    public boolean hasDimensionProperty(String name) {
        return ((getProperty(name+"Width")!=null) && (getProperty(name+"Height")!=null));
    }
    
    /** returns the property name as int number; if the property doesn't exist or cannot be transformed to an int number
     * 0 is returned.
     */
    public int getIntProperty(String name) {
        Object obj = getProperty(name);
        if (obj == null) return 0;
        if (obj instanceof String) {
            try {
                return (new Integer((String)obj)).intValue();
            } catch (NumberFormatException e) {
                return 0;
            }
        }
        return 0;
    }
    
    /** convenience method for setting a boolean property.
     */
    public void setBooleanProperty(String name, boolean b) {
        setProperty(name,String.valueOf(b));
    }
    
    public boolean getBooleanProperty(String name) {
        Object val = getProperty(name);
        if (val instanceof String) {
            Boolean b = new Boolean((String)val);
            return b.booleanValue();
        }
        return false;
    }
    
    /** sets the value property, which gets special treatment in the XML output: if the string representation
     * of the value object contains a newline, then the value will be added as CData, otherwise it will be
     * added as attribute with name "value".
     */
    public void setValueProperty(Object value) {
        valueProperty = value;
    }
    
    public Object getValueProperty() {
        return valueProperty;
    }
    
    /** returns the string representation of the property value; if the value is not found or equal to null, it returns
     * the empty String.
     */
    public String getPropertyAsString(String name) {
        Object val = getProperty(name);
        if (val == null) return "";
        return val.toString();
    }
    
    /** returns the String representation of the value property; if no value property is stored, returns the empty string
     */
    protected String getValuePropertyAsString() {
        if (hasValueProperty())
            return getValueProperty().toString();
        return "";
    }
    
    /** returns true, if the value property exists and if it's string representation contains newlines.
     */
    protected boolean valueContainsNewline() {
        if (!hasValueProperty()) return false;
        return (getValuePropertyAsString().indexOf(newline) >= 0);
    }
    
    public boolean hasValueProperty() {
        return getValueProperty() != null;
    }
    
    public Iterator propertyNames() {
        return propertyMap.keySet().iterator();
    }
    
    
    /** add the object as child of this element properties instance, which means that it is
     * nested within this object when printed e.g. as XML String.
     * Tags of children doesn't need to be unique.
     */
    public void addChildObject(String childTag, Storable obj) {
        ElementProperties childProps = obj.getElementProperties(rwop);
        childProps.setParent(this);
        Vector prev = (Vector) childMap.get(childTag);
        if (prev == null) {
            prev = new Vector();
        }
        prev.add(childProps);
        childMap.put(childTag,prev);
    }
    
    /** returns an enumeration of all children stored with childTag */
    public Enumeration getChildObjectEnumeration(String childTag) {
        Vector v = (Vector) childMap.get(childTag);
        if (v == null) {
            return (new Vector()).elements();
        }
        return v.elements();
    }
    
    /** add the object as child of this element properties instance; reference the child using its id rather than
     * using its properties itself (as it is the case when it's added using <code>addChildObject</code>.
     * Tags of children doesn't need to be unique.
     */
    public void addChildObjectAsReference(String childTag, Storable obj) {
        String childId = rwop.getIdForObject(obj);
        Vector prev = (Vector) childRefMap.get(childTag);
        if (prev == null) {
            prev = new Vector();
        }
        prev.add(childId);
        childRefMap.put(childTag,prev);
    }
    
    /** returns an enumeration of all referenced children stored with childTag */
    public Enumeration getChildObjectAsReferenceEnumeration(String childTag) {
        Vector v = (Vector) childRefMap.get(childTag);
        if (v == null) {
            Dbg.pr("getChildObjectAsReferenceEnumeration: no children found with tag "+childTag);
            return (new Vector()).elements();
        }
        Dbg.pr("getChildObjectAsReferenceEnumeration: "+v.size()+" children found with tag "+childTag);
        return v.elements();
    }
    
    /** returns the first child object reference id with the given tag; this method should only be used,
     * if only one child with the given tag can exist.
     */
    public String getChildObjectAsReference(String childTag) {
        Enumeration iter = getChildObjectAsReferenceEnumeration(childTag);
        if (iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof String)
                return (String) obj;
        }
        return null;
    }
    
    /** the string representing the line separator as returned by <code>System.getProperty("line.separator")</code>
     */
    static public String newline = System.getProperty("line.separator");
    
    /** returns the XmlString representing this object; indents the generated text
     */
    public String toXml(String indent) {
        StringBuffer buf = new StringBuffer();
        String tag = "Object";
        String lindent = indent+" ";
        if (xmlHideToplevel) {
            lindent = indent;
        } else {
            buf.append(indent+"<"+tag);
            if (className != null) {
                buf.append(" class=\""+className+"\"");
            }
            buf.append(" id=\""+id+"\"");
            boolean valueContainsNewline = valueContainsNewline();
            if (!valueContainsNewline) {
                buf.append(" value=\""+getValuePropertyAsString()+"\"");
            }
            Iterator iter = propertyNames();
            while (iter.hasNext()) {
                String pname = (String)iter.next();
                String val = getPropertyAsString(pname);
                buf.append(" "+pname+"=\""+val+"\"");
            }
            buf.append(">"+newline);
            if (valueContainsNewline) {
                String valStr = getValueProperty().toString();
                buf.append(valStr+newline);
            }
        }
        Iterator iter1 = childMap.entrySet().iterator();
        while(iter1.hasNext()) {
            Map.Entry entry = (Map.Entry) iter1.next();
            String childName = (String) entry.getKey();
            Enumeration iter0 = ((Vector) entry.getValue()).elements();
            while(iter0.hasMoreElements()) {
                ElementProperties childProps = (ElementProperties) iter0.nextElement();
                buf.append(lindent+"<"+childName+">"+newline);
                buf.append(childProps.toXml(indent+"  "));
                buf.append(lindent+"</"+childName+">"+newline);
            }
        }
        Iterator iter2 = childRefMap.entrySet().iterator();
        while(iter2.hasNext()) {
            Map.Entry entry = (Map.Entry) iter2.next();
            String childTag = (String) entry.getKey();
            Enumeration iter0 = ((Vector) entry.getValue()).elements();
            while(iter0.hasMoreElements()) {
                String childId = (String) iter0.nextElement();
                buf.append(lindent+"<"+childTag+" id=\""+childId+"\"/>"+newline);
            }
        }
        if (!xmlHideToplevel)
            buf.append(indent+"</"+tag+">"+newline);
        return buf.toString();
    }
    
    /** returns the XmlString representing this object
     */
    public String toXml() {
        return toXml("");
    }
    
    
    /** creates the object that is represented by this element properties instance. It uses the className field
     * to generate a new instance; it is assumed that the class has an empty constructor. In case an exception is
     * caught during the instance creation, or if the stored className field is null, the returned value is null.
     */
    public Storable createObject(ReadWriteOperation rwop, StorableInitActions action) {
        if (className == null) return null;
        // check whether we need to use a stored instance of the class:
        Object obj0 = rwop.getAppl().getClassExemplar(className);
        if (obj0 != null) {
            if (obj0 instanceof Storable) {
                Dbg.pr("returning class exemplar stored in application for class "+className+"...");
                rwop.putObjectIdRelation((Storable)obj,getId());
                if (action != null) action.preinitAction((Storable)obj0);
                ((Storable)obj0).initFromElementProperties(rwop,this);
                return (Storable)obj0;
            }
        }
        try {
            Dbg.pr("looking for class "+className+"...");
            Class cl = Class.forName(className);
            Dbg.pr("creating new instance...");
            Storable obj = (Storable) cl.newInstance();
            rwop.putObjectIdRelation(obj,getId());
            Dbg.pr("calling initFromElementProperties for new instance...");
            obj.initFromElementProperties(rwop,this);
            return obj;
        } catch (Exception ex) {
            ex.printStackTrace(new java.io.PrintStream(System.out));
            System.err.println("Exception while creating object of class \""+className+"\":"+newline+ex.getMessage());
            return null;
        }
    }
    
    public Storable createObject(ReadWriteOperation rwop) {
        return createObject(rwop,null);
    }

    /** prepares this object for writing into a file, i.e. remove all object references ecept those to other
     * ElementProperties instances.
     */
    public void prepareForWrite() {
        if (valueProperty != null) {
            setValueProperty(valueProperty.toString());
        }
        // exchange all values in the property map by their string representation
        Map propertyMap0 = new Hashtable();
        Iterator iter0 = propertyMap.entrySet().iterator();
        while(iter0.hasNext()) {
            Map.Entry entry = (Map.Entry) iter0.next();
            propertyMap0.put(entry.getKey(),entry.getValue().toString());
        }
        propertyMap = propertyMap0;
        // recursively prepare child entries for write operation
        Iterator iter1 = childMap.values().iterator();
        while(iter1.hasNext()) {
            Vector v = (Vector) iter1.next();
            Enumeration iter = v.elements();
            while(iter.hasMoreElements()) {
                ElementProperties props = (ElementProperties)iter.nextElement();
                props.prepareForWrite();
            }
        }
        obj = null;
    }
    
    
}
