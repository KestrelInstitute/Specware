/*
 * ImportInfo.java
 *
 * Created on February 17, 2003, 6:09 PM
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
public class ImportInfo extends BaseElementInfo {
    
    public ImportInfo(String name) {
        super(name);
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createImport((SpecElement)parent)).getElement();
    }
    
    public void updateBinding(DocumentBinding doc, TextBinding target) {
        super.updateBinding(doc, target);
    }
    
    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        ImportElement element = (ImportElement)target;
        // TODO:handle things other than infile references
        SourceElement src = element.findSource();
	SpecElement unitImported = src.getSpec(name);
        if (unitImported != null) {
            element.setUnitImported((MemberElement)unitImported);
        }
    }

    public String toString() {
	return "import " + name;
    }
}
