/*
 * MetaSlangEditorKit.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.editor;

import java.awt.event.ActionEvent;
import javax.swing.Action;
import javax.swing.text.Document;
import javax.swing.text.TextAction;
import javax.swing.text.JTextComponent;

import org.netbeans.editor.BaseDocument;
import org.netbeans.editor.Formatter;
import org.netbeans.editor.Syntax;
import org.netbeans.editor.SyntaxSupport;
import org.netbeans.modules.editor.NbEditorKit;

/**
* Editor kit implementation for MetaSlang content type
*
*/

public class MetaSlangEditorKit extends NbEditorKit {

    public static final String META_SLANG_MIME_TYPE = "text/x-meta-slang"; // NOI18N

    public MetaSlangEditorKit() {
	super();
	MetaSlangSettingsInitializer.init();
    }

    public String getContentType() {
        return META_SLANG_MIME_TYPE;
    }

    /** Create new instance of syntax coloring scanner
    * @param doc document to operate on. It can be null in the cases the syntax
    *   creation is not related to the particular document
    */
    public Syntax createSyntax(Document doc) {
        return new MetaSlangSyntax();
    }

    /** Create syntax support */
    public SyntaxSupport createSyntaxSupport(BaseDocument doc) {
        return new MetaSlangSyntaxSupport(doc);
    }

    public Document createDefaultDocument() {
        return new MetaSlangDocument(this.getClass());
    }


    /* Not yet implemented.
    public Completion createCompletion(ExtEditorUI extEditorUI) {
        return new MetaSlangCompletion(extEditorUI);
    }

    /* This is not used by NetBeans.
    public Formatter createFormatter() {
        return new MetaSlangFormatter(this.getClass());
    }
    */

}
