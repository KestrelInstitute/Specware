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
public class DiagElemInfo extends BaseElementInfo {
    
    public DiagElemInfo(String name) {
        super(name);
    }
    
    protected Element createModelImpl(LangModel.Updater model, Element parent) {
        return ((ElementImpl)model.createDiagElem((DiagramElement)parent)).getElement();
    }
    
    public void updateBinding(DocumentBinding doc, TextBinding target) {
        super.updateBinding(doc, target);
    }
    
    public void updateElement(LangModel.Updater model, Element target) 
    throws SourceException {
        super.updateElement(model, target);
        super.updateBase(target);
        
        DiagElemElement element = (DiagElemElement)target;
       // PENDING: update binding with diagElem link information.
    }

    public String toString() {
	return name;
    }
}
