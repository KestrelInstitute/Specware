/*
 * Member.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:43  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import org.openide.src.SourceException;

import edu.kestrel.netbeans.model.*;

/**
 *
 */
class Member extends ElementBinding implements Binding.Member {
    /** Creates new Member */
    public Member(MemberElement me, SourceText s) {
        super(me, s);
    }
    
    protected Element cloneElement() {
        try {
            return (MemberElement)((MemberElement)getElement()).clone();
        } catch (CloneNotSupportedException ex) {
            throw new InternalError("Cannot clone element."); // NOI18N
        }
    }

    /**
     * Requests a change of member's name.
     */
    public void changeName(String name) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        
        MemberElement el = (MemberElement)cloneElement();
        el.setName(name);
        regenerateHeader(el);
    }
    
    /**
     * Updates the storage binding object from an external SourceText.
     */
    public void updateFrom(Binding other) {
    }
}
