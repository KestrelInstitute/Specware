/*
 * DocumentModelUpdater.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:17  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import org.openide.src.SourceException;

import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.model.LangModel;
import edu.kestrel.netbeans.model.SourceElement;

public interface DocumentModelUpdater {
    public void updateBindings(DocumentBinding updater);

    public void updateModel(LangModel.Updater updater, SourceElement src, 
			    SourceElement.Impl impl) throws SourceException;

}

