/*
 * DocumentModelUpdater.java
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

import org.openide.src.SourceException;

import edu.kestrel.netbeans.codegen.DocumentBinding;
import edu.kestrel.netbeans.model.LangModel;
import edu.kestrel.netbeans.model.SourceElement;

public interface DocumentModelUpdater {
    public void updateBindings(DocumentBinding updater);

    public void updateModel(LangModel.Updater updater, SourceElement src, 
			    SourceElement.Impl impl) throws SourceException;

}

