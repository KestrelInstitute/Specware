package edu.kestrel.especs.lang;


import edu.kestrel.graphs.io.*;


public class Term implements Storable {
    
    public String term;
    
    public boolean isReadonly = false;
    
    public Term() {
    }
    
    public Term(String term) {
        this.term = term;
    }
    
    public Term(Term t) {
        this.isReadonly = t.isReadonly;
        this.term = t.term;
    }
    
    public String toString() {
        return term;
    }
    
    public boolean isDerived() {
        return isReadonly;
    }
    
    protected static String IsReadOnly = "IsReadOnly";
    
    public ElementProperties getElementProperties(ReadWriteOperation wop) {
        ElementProperties props = wop.createElementProperties(this);
        props.setValueProperty(term);
        props.setBooleanProperty(IsReadOnly,isReadonly);
        return props;
    }
    
    public void initFromElementProperties(ReadWriteOperation rop, ElementProperties props) {
        term = props.getValueProperty().toString();
        isReadonly = props.getBooleanProperty(IsReadOnly);
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Term)
            return ((Term)obj).term.equals(term);
        else
            return false;
    }
    
}

