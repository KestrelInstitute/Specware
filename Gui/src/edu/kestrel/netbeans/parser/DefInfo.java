/*
 * DefInfo.java
 *
 * Created on February 15, 2003, 4:53 PM
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
public class DefInfo extends BaseElementInfo {
    String[]      parameters;

    public DefInfo(String name, String[] parameters) {
        super(name);
	this.parameters = parameters;
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createDef((SpecElement)parent)).getElement();
    }
    
    public void updateBinding(DocumentBinding doc, TextBinding target) {
        super.updateBinding(doc, target);
    }
    
    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        DefElement element = (DefElement)target;
        element.setParameters(parameters);
        // PENDING: update binding with def link information.
    }

    public String toString() {
	return "def " + name + ((parameters == null) ? "" : Util.print(parameters, true));
    }
}
