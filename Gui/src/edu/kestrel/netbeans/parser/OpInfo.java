/*
 * OpInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:22  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import org.openide.text.*;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.codegen.TextBinding;

public class OpInfo extends BaseElementInfo {
    String   sort;
    OpInfo   nextOp;
    
    public OpInfo(String name, String sort) {
        super(name);
	this.sort = sort;
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createOp((SpecElement)parent)).getElement();
    }
    
    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        OpElement element = (OpElement)target;
        element.setSort(sort);
        // PENDING: update binding with op link information.
    }

    public String toString() {
	return "op "+name+": "+sort;
    }
}
