/*
 * StadModelNode.java
 *
 * Created on December 5, 2002, 9:49 PM
 */

package edu.kestrel.especs.graphs.spec;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.*;
import java.util.*;
/**
 *
 * @author  ma
 */
public class StadModelNode extends ModelContainerNode {
    
    protected StadModelNode derivedFrom;
    protected Vector derivedStads;
    
    protected interface StadAction {
        public void execute(StadModelNode s);
    }
    
    /** Creates a new instance of StadModelNode */
    public StadModelNode() {
        super();
    }

    public void setDerivedFromNode(StadModelNode m0) {
        Dbg.pr("setting derived from node of "+this+" to "+m0+"...");
        derivedFrom = m0;
        m0.addDerived(this);
    }
    
    /** returns the stad from which this one is derived.
     */
    public StadModelNode getDerivedFrom() {
        return derivedFrom;
    }
    
    
    /** adds an derived stad.
     */
    public void addDerived(StadModelNode stad) {
        if (derivedStads == null) {
            derivedStads = new Vector();
        }
        if (!derivedStads.contains(stad)) {
            derivedStads.add(stad);
        }
    }
    
    /** removes the stad from the list of derived stads.
     */
    public void removeDerived(StadModelNode stad) {
        if (derivedStads != null) {
            derivedStads.remove(stad);
        }
    }
    
    public void removeModelElement() {
        if (isDerived()) {
            derivedFrom.removeDerived(this);
        }
        super.removeModelElement();
    }
    
    
    public boolean isDerived() {
        return (derivedFrom != null);
    }

    public boolean removeOk(boolean throwException) throws VetoException {
        if (derivedStads == null) return true;
        boolean ok = derivedStads.size() == 0;
        if (ok) return true;
        if (throwException) {
            throw new VetoException("Stad \""+getShortName()+"\" cannot be removed, because other stads are derived from this one.");
        }
        return false;
    }
    
    public boolean renameOk(boolean throwException) throws VetoException {
        if (!isDerived()) return true;
        if (throwException) {
            throw new VetoException("Stad \""+getShortName()+"\" cannot be renamed, because it's derived from another stad.");
        }
        return false;
    }
    
    protected static String DerivedFrom = "DerivedFrom";
    
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        if (derivedFrom != null) {
            props.addChildObjectAsReference(DerivedFrom, derivedFrom);
        }
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        String id = props.getChildObjectAsReference(DerivedFrom);
        if (id != null) {
            Storable obj = rwop.getObjectForId(id);
            if (obj instanceof StadModelNode) {
                setDerivedFromNode((StadModelNode)obj);
            }
        }
    }
    

    public void importHook(StadModelNode orig) {
        copyHook(orig);
        setDerivedFromNode(orig);
    }

    /** called after a copy action. */
    synchronized public void postCopyAction(Map modelElementMap, ModelElement original) {
        Dbg.pr("postCopyAction: ModelNode "+getShortName()+"...");
        StadModelNode mnode0 = (StadModelNode)original;
        StadModelNode derived0 = mnode0.getDerivedFrom();
        if (derived0 != null) {
            Dbg.pr("updating derivedFrom information...");
            Object obj = modelElementMap.get(derived0);
            if (obj instanceof StadModelNode) {
                Dbg.pr(" --------------------- derivedFrom stad has also been copied.");
                setDerivedFromNode((StadModelNode)obj);
            } else {
                setDerivedFromNode(derived0);
            }
        }
    }
    
    protected void forallDerivedStads(StadAction action) {
        if (derivedStads == null) return;
        Enumeration iter = derivedStads.elements();
        while(iter.hasMoreElements()) {
            Object obj = iter.nextElement();
            if (obj instanceof StadModelNode) {
                action.execute((StadModelNode)obj);
            }
        }
    }
    
    /** sets the value also for all derived stads.
     */
    public void setValue(final Object val) {
        super.setValue(val);
        forallDerivedStads(new StadAction() {
            public void execute(StadModelNode s) {
                s.setValue(val);
                s.sync();
            }
        });
    }
    
}
