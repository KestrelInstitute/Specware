/*
 * ParserAnnontation.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:24  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import org.openide.text.Annotation;
import org.openide.text.Line;
import org.openide.text.Annotatable;
import org.openide.text.Line.Set;

/**
 *
 */
public class ParserAnnotation extends Annotation implements PropertyChangeListener {
    
    private final String error;
    private final int line,column;
    private int state;
    private Line docline;
    private ParserAnnotation chained;
    
    private static final int STATE_NEW=1;
    private static final int STATE_ATTACHED = 2;
    private static final int STATE_DETACHED = 3;
    
    /** Creates a new instance of ParserAnnontation */
    ParserAnnotation(int l, int c,String err) {
        line=l;
        column=c;
        error = err;
        state = STATE_NEW;
    }
    
    public String getAnnotationType() {
        return "org-netbeans-modules-java-parser_annotation";       // NOI18N
    }
    
    public String getShortDescription() {
        // Localize this with NbBundle:
        if (chained!=null)
            return error+"\n\n"+chained.getShortDescription();
        return error;
    }
    
    int getLine() {
        return line;
    }
    
    int getColumn() {
        return column;
    }
    
    String getError() {
        return error;
    }
    
    void chain(ParserAnnotation anno) {
        if (chained!=null)
            chained.chain(anno);
        else
            chained=anno;
    }
    
    private int getState() {
        return state;
    }
    
    protected void notifyAttached(final Annotatable toAnno) {
        super.notifyAttached(toAnno);
        docline.addPropertyChangeListener(this);
        state = STATE_ATTACHED;
    }
    
    protected void notifyDetached(Annotatable fromAnno) {
        super.notifyDetached(fromAnno);
        docline.removePropertyChangeListener(this);
        state=STATE_DETACHED;
    }
    
    public boolean equals(Object obj) {
        boolean eq=shallowEquals(obj);
        
        if (!eq)
            return false;
        if (chained!=null)
            return chained.equals(((ParserAnnotation)obj).chained);
        return true;
    }
           
    private boolean shallowEquals(Object obj) {
        if (obj instanceof ParserAnnotation) {
            ParserAnnotation ann=(ParserAnnotation)obj;
            
            if (this==obj)
                return true;
            if (line!=ann.getLine())
                return false;
            if (column!=ann.getColumn())
                return false;
            if (!error.equals(ann.getError()))
                return false;
            if (getState()==STATE_DETACHED || ann.getState()==STATE_DETACHED)
                return false;
            return true;
        }
        return false;
    }
    
    public void attachToLineSet(Set lines) {
        char string[];
        int start,end;
        Line.Part part;

        docline=lines.getCurrent(line-1);
        string=docline.getText().toCharArray();
        start=0;
        end=string.length-1;
        while (start<=end && string[start]<=' ') {
            start++;
        }
        while (start<=end && string[end]<=' ') {
            end--;
        }
        if (start<=end)
            part=docline.createPart(start,end-start+1);
        else
            part=docline.createPart(0,string.length);
        attach(part);
    }
    
    public void propertyChange(PropertyChangeEvent ev) {
        String type = ev.getPropertyName();
        if (type == null || type == Annotatable.PROP_TEXT) {    // User edited the line, assume error should be cleared.
            detach();
        }
    }
}
