/*
 * MetaSlangDocument.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:46  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import org.netbeans.editor.BaseDocument;
import org.netbeans.editor.BaseKit;
import org.netbeans.editor.Formatter;
import org.netbeans.editor.SettingsChangeEvent;
import org.netbeans.modules.editor.NbEditorDocument;


/**
 * NbEditorDocument extension specifying formatter/indent engine
 *
 */

public class MetaSlangDocument extends NbEditorDocument {

    /** Formatter being used. */
    private Formatter formatter;

    private Class kitClass;

    public MetaSlangDocument(Class kitClass) {
        super(kitClass);
	this.kitClass = kitClass;
    }

    public void settingsChange(SettingsChangeEvent evt) {
        super.settingsChange(evt);

        // Check whether the mimeType is set
        Object o = getProperty(MIME_TYPE_PROP);
        if (!(o instanceof String)) {
            BaseKit kit = BaseKit.getKit(getKitClass());
            putProperty(MIME_TYPE_PROP, kit.getContentType());
        }

        // Fill in the indentEngine property
        putProperty(INDENT_ENGINE,
            new BaseDocument.PropertyEvaluator() {

                private Object cached;

                public Object getValue() {
                    if (cached == null) {
                        cached = new MetaSlangIndentEngine();
                    }
                    
                    return cached;
                }
            }
        );
    }

    public Formatter getFormatter() {
        if (formatter == null) {
            formatter = new MetaSlangFormatter(kitClass);
        }

        return formatter;
    }



}
