/*
 * ClaimInfo.java
 *
 * Created on February 12, 2003, 2:14 PM
 */

package edu.kestrel.netbeans.parser;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

/**
 *
 * @author  weilyn
 */
public class ClaimInfo extends BaseElementInfo {
    String   claimKind;
    
    /** Creates a new instance of ClaimInfo */
    public ClaimInfo(String name, String claimKind) {
        super(name);
	this.claimKind = claimKind;
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createClaim((SpecElement)parent)).getElement();
    }

    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        ClaimElement element = (ClaimElement)target;
        element.setClaimKind(claimKind);
    }

    public String toString() {
	return claimKind+" "+name;
    }
}
