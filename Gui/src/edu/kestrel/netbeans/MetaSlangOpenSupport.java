/*
 * MetaSlangOpenSupport.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:35  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans;

import java.io.IOException;

import org.openide.ErrorManager;
import org.openide.TopManager;
import org.openide.cookies.*;
import org.openide.loaders.*;
import org.openide.windows.CloneableTopComponent;
import org.openide.util.Task;

import edu.kestrel.netbeans.editor.MetaSlangEditorSupport;
import edu.kestrel.netbeans.model.SourceElement;

public class MetaSlangOpenSupport extends OpenSupport implements OpenCookie, CloseCookie {
    
    public MetaSlangOpenSupport(MultiDataObject.Entry entry) {
        super(entry);
        //Util.trace("*** Entering MetaSlangOpenSupport constructor.");
    }
    
    // For access from MetaSlangEditorSupport:
    public boolean isOpen() {
        return !allEditors.isEmpty();
    }
    
    protected boolean canClose() {
        if (!super.canClose()) {
            return false;
        }
        DataObject dob = entry.getDataObject();
        if (!dob.isModified()) {
            return true;
        }
        MetaSlangEditorSupport mes = (MetaSlangEditorSupport)dob.getCookie(MetaSlangEditorSupport.class);
        if (mes == null) {
            // Should not happen.
            ErrorManager.getDefault().log(ErrorManager.WARNING, "WARNING: closing modified file, cannot save");
            return true;
        }
        if (mes.getOpenedPanes() != null) {
            return true;
        }
        boolean mesCanClose = mes.superCanClose();
        if (mesCanClose) mes.close();
        return mesCanClose;
    }

    protected CloneableTopComponent createCloneableTopComponent() {
        //Util.trace("*** Entering MetaSlangOpenSupport.createCloneableTopComponent.");
        return new MetaSlangPanel(entry);
    }

    public void open () {
	// Do parsing outside of the AWT/SWING event-dispatching thread
	SourceElement source = ((MetaSlangDataObject)entry.getDataObject()).getSource();
	if (source.getStatus() != SourceElement.STATUS_OK) {
	    Task task = source.prepare();
	    task.waitFinished();
	}
	// GUI done in the AWT/SWING event-dispatching thread
	super.open();
    }
}
