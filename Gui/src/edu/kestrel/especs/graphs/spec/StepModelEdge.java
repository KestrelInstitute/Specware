/*
 * StepModelEdge.java
 *
 * Created on December 5, 2002, 9:49 PM
 */

package edu.kestrel.especs.graphs.spec;

import edu.kestrel.graphs.spec.*;
import edu.kestrel.especs.lang.*;
import edu.kestrel.graphs.io.*;
import edu.kestrel.graphs.util.*;
import edu.kestrel.graphs.*;
import java.util.*;
/**
 *
 * @author  ma
 */
public class StepModelEdge extends ModelEdge {
    
    protected String stepName;
    protected String stepParams;
    /** holds the condition given as list of conjuntive terms, element type: Term (see below) */
    protected java.util.List conditionTerms;
    
    /** holds the list of updates; element type: Term (see below) */
    protected java.util.List updates;
    
    /** contains the direct "parent" edge, i.e. the edge from which this one is
     * derived from.
     */
    protected StepModelEdge derivedFrom;
    
    /** list containing the model edges that are directly derived from this one.
     */
    protected Vector derivedSteps;
    
    /** Creates a new instance of StepModelEdge */
    public StepModelEdge() {
        super();
    }
    
    
    public String getStepName() {
        if (isDerived()) {
            return derivedFrom.getStepName();
        }
        return stepName;
    }
    
    public void setStepName(String stepName) {
        if (isDerived()) return;
        this.stepName = stepName;
        refreshValue();
    }
    
    public String getStepParams() {
        if (isDerived()) {
            return derivedFrom.getStepParams();
        }
        return stepParams;
    }
    
    public void setStepParams(String params) {
        if (isDerived()) return;
        this.stepParams = stepParams;
        refreshValue();
    }
    
    /** returns a copy of the list by creating new Term instances for every element.
     */
    private java.util.List getFreshTermList(java.util.List list) {
        if (list == null) return null;
        ArrayList res = new ArrayList();
        Iterator iter = list.iterator();
        while(iter.hasNext()) {
            Term t = new Term((Term)iter.next());
            res.add(t);
        }
        return res;
    }
    
    /** removes readonly Terms from the list; doesn't create new Term instances.
     */
    private java.util.List removeReadonlyTerms(java.util.List list) {
        if (list == null) return null;
        ArrayList res = new ArrayList();
        Iterator iter = list.iterator();
        while(iter.hasNext()) {
            Term t = (Term)iter.next();
            if (!t.isReadonly) {
                res.add(t);
            }
        }
        return res;
    }

    /** makes the terms in the list readonly; creates new Term instances.
     */
    private java.util.List makeTermsReadonly(java.util.List list) {
        if (list == null) return null;
        ArrayList res = new ArrayList();
        Iterator iter = list.iterator();
        while(iter.hasNext()) {
            Term t = new Term((Term)iter.next());
            t.isReadonly = true;
            res.add(t);
        }
        return res;
    }
    
    public void setConditionTerms(java.util.List conditionTerms) {
        this.conditionTerms = getFreshTermList(removeReadonlyTerms(conditionTerms));
        refreshValue();
    }
    
    public java.util.List getConditionTerms() {
        if (isDerived()) {
            ArrayList res = new ArrayList();
            java.util.List dlist = makeTermsReadonly(derivedFrom.getConditionTerms());
            if (dlist != null) res.addAll(dlist);
            if (conditionTerms != null) res.addAll(conditionTerms);
            return res;
        }
        return conditionTerms;
    }
    
    public void setUpdates(java.util.List updates) {
        this.updates = getFreshTermList(removeReadonlyTerms(updates));
        refreshValue();
    }
    
    public java.util.List getUpdates() {
        if (isDerived()) {
            ArrayList res = new ArrayList();
            java.util.List dlist = makeTermsReadonly(derivedFrom.getUpdates());
            if (dlist != null) res.addAll(dlist);
            if (updates != null) res.addAll(updates);
            return res;
        }
        return updates;
    }
    
    public void setDerivedFromEdge(StepModelEdge m0) {
        derivedFrom = m0;
        if (m0 != null) {
            m0.addDerived(this);
        }
    }
    
    /** returns the edge from which this one is derived.
     */
    public StepModelEdge getDerivedFrom() {
        return derivedFrom;
    }
    
    
    /** adds an derived edge.
     */
    public void addDerived(StepModelEdge edge) {
        if (derivedSteps == null) {
            derivedSteps = new Vector();
        }
        if (!derivedSteps.contains(edge)) {
            derivedSteps.add(edge);
        }
    }
    
    /** removes the edge from the list of derived edges.
     */
    public void removeDerived(StepModelEdge edge) {
        if (derivedSteps != null) {
            derivedSteps.remove(edge);
        }
    }
    
    public void removeModelElement() {
        if (isDerived()) {
            derivedFrom.removeDerived(this);
        }
        super.removeModelElement();
    }
    
    public boolean removeOk(boolean throwException) throws VetoException {
        if (derivedSteps == null) return true;
        boolean ok = derivedSteps.size() == 0;
        if (ok) return true;
        if (throwException) {
            throw new VetoException("Step \""+getShortName()+"\" cannot be removed, because other steps are derived from this one.");
        }
        return false;
    }
    
    public boolean renameOk(boolean throwException) throws VetoException {
        if (!isDerived()) return true;
        if (throwException) {
            throw new VetoException("Step \""+getShortName()+"\" cannot be renamed, because it's derived from another step.");
        }
        return false;
    }
    
    
    public boolean isDerived() {
        return (derivedFrom != null);
    }
    
    protected void refreshValueForDerived() {
        if (derivedSteps != null) {
            Enumeration iter = derivedSteps.elements();
            while(iter.hasMoreElements()) {
                StepModelEdge edge = (StepModelEdge)iter.nextElement();
                edge.refreshValue();
            }
        }
    }
    
    public void refreshValue() {
        StringBuffer buf = new StringBuffer();
        java.util.List clist = getConditionTerms();
        java.util.List ulist = getUpdates();
        String cont = ":\n";
        buf.append(getStepName()+(ListUtils.containsSomething(clist)||ListUtils.containsSomething(ulist)?cont:""));
        String sep = "  ";
        if (clist != null) {
            Iterator iter = clist.iterator();
            while(iter.hasNext()) {
                Term t = (Term) iter.next();
                buf.append(sep+" "+t.term+"\n");
                sep = "& ";
            }
        }
        sep = "|-";
        if (ulist != null) {
            Iterator iter = ulist.iterator();
            while(iter.hasNext()) {
                Term t = (Term) iter.next();
                buf.append(sep+" "+t.term+"\n");
                sep = ", ";
            }
        }
        setValue(buf.toString());
        sync();
        refreshValueForDerived();
    }
    
    public void copyHook(ModelElement orig) {
        super.copyHook(orig);
        if (orig instanceof StepModelEdge) {
            StepModelEdge medge = (StepModelEdge)orig;
            setStepName(medge.getStepName());
            setStepParams(medge.getStepParams());
            setConditionTerms(medge.getConditionTerms());
            setUpdates(medge.getUpdates());
        }
    }
    
    private void makeTermsReadOnly(java.util.List list) {
        Iterator iter = list.iterator();
        while(iter.hasNext()) {
            Term t = (Term)iter.next();
            t.isReadonly = true;
        }
    }
    
    public void importHook(StepModelEdge orig) {
        copyHook(orig);
        setDerivedFromEdge(orig);
        if (getConditionTerms() != null) {
            makeTermsReadOnly(getConditionTerms());
        }
        if (getUpdates() != null) {
            makeTermsReadOnly(getUpdates());
        }
    }
    
    
    /** called after a copy action. */
    public void postCopyAction(Map modelElementMap, ModelElement original) {
        Dbg.pr("postCopyAction: ModelEdge "+getShortName()+"...");
        StepModelEdge medge0 = (StepModelEdge)original;
        StepModelEdge derived0 = medge0.getDerivedFrom();
        if (derived0 != null) {
            Dbg.pr("updating derivedFrom information...");
            Object obj = modelElementMap.get(derived0);
            if (obj instanceof StepModelEdge) {
                Dbg.pr(" --------------------- derivedFrom step has also been copied.");
                setDerivedFromEdge((StepModelEdge)obj);
            } else {
                setDerivedFromEdge(derived0);
            }
        }
    }
    
    
    protected static String StepName = "StepName";
    protected static String StepParams = "StepParams";
    protected static String ConditionTerms = "ConditionTerms";
    protected static String UpdateTerms = "UpdateTerms";
    protected static String DerivedFrom = "DerivedFrom";
    
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = super.getElementProperties(wop);
        props.setProperty(StepName,getStepName());
        props.setProperty(StepParams,getStepParams());
        props.setStorableListProperty(ConditionTerms, getConditionTerms());
        props.setStorableListProperty(UpdateTerms,getUpdates());
        if (derivedFrom != null) {
            props.addChildObjectAsReference(DerivedFrom, derivedFrom);
        }
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rwop, ElementProperties props) {
        super.initFromElementProperties(rwop,props);
        String n = props.getPropertyAsString(StepName);
        Dbg.pr("StepModelEdge.initFromElementProperties: setting step name to "+n+"...");
        setStepName(n);
        setStepParams(props.getPropertyAsString(StepParams));
        setConditionTerms(props.getStorableListProperty(ConditionTerms));
        setUpdates(props.getStorableListProperty(UpdateTerms));
        String id = props.getChildObjectAsReference(DerivedFrom);
        if (id != null) {
            Storable obj = rwop.getObjectForId(id);
            if (obj instanceof StepModelEdge) {
                setDerivedFromEdge((StepModelEdge)obj);
            }
        }
    }
    
    
    
}
