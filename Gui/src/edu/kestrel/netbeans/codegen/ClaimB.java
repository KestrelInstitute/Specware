/*
 * ClaimB.java
 *
 * Created on February 12, 2003, 2:24 PM
 */

package edu.kestrel.netbeans.codegen;

import java.io.*;
import javax.swing.text.*;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.codegen.Member;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.model.Element;
/**
 *
 * @author  weilyn
 */
class ClaimB extends Member implements Binding.Claim {
    
    /** Creates a new instance of ClaimB */
    public ClaimB(ClaimElement el, SourceText s) {
        super(el, s);
    }
    
    private ClaimElement cloneClaim() {
        return (ClaimElement)cloneElement();
    }
    
    protected Element cloneElement() {
        ClaimElement el = new ClaimElement();
        copyProperties(el);
        return el;
    }

    protected void copyProperties(ClaimElement target) {
        ClaimElement my = (ClaimElement)getElement();
        try {
            target.setName(my.getName());
            target.setClaimKind(my.getClaimKind());
        } catch (SourceException ex) {
            // should NOT happen
        }
    }
    
    /**
     * Requests a change of member's name.
     */
    public void changeName(final String name) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        
	super.changeName(name);
    }
    
    /** Changes claimKind for the claim.
     */
    public void changeClaimKind(String claimKind) throws SourceException {
        if (!source.isGeneratorEnabled())
            return;
        ClaimElement el = (ClaimElement)cloneElement();
        el.setClaimKind(claimKind);
        regenerateHeader(el);
    }
}
