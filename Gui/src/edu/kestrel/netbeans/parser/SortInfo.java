/*
 * SortInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
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

public class SortInfo extends BaseElementInfo {
    String[]      parameters;

    public SortInfo(String name, String[] parameters) {
        super(name);
	this.parameters = parameters;
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createSort((SpecElement)parent)).getElement();
    }
    
    public void updateBinding(DocumentBinding doc, TextBinding target) {
        super.updateBinding(doc, target);
    }
    
    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        SortElement element = (SortElement)target;
        element.setParameters(parameters);
        // PENDING: update binding with sort link information.
    }

    public String toString() {
	return "sort " + name + ((parameters == null) ? "" : Util.print(parameters, true));
    }
}
