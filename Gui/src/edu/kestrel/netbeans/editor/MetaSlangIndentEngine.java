/*
 * MetaSlangIndentEngine.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:49  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import java.io.*;
import javax.swing.text.Document;
import org.netbeans.editor.ext.ExtFormatter;
import org.netbeans.modules.editor.EditorModule;
import org.netbeans.modules.editor.FormatterIndentEngine;
import org.openide.text.IndentEngine;

/**
* MetaSlang indentation engine that delegates to MetaSlang formatter
*
*/

public class MetaSlangIndentEngine extends FormatterIndentEngine {

    public static final String META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT_PROP
        = "metaSlangFormatLeadingSpaceInComment"; // NOI18N

    static final long serialVersionUID = 5111817948403221232L;

    public MetaSlangIndentEngine() {
        setAcceptedMimeTypes(new String[] { MetaSlangEditorKit.META_SLANG_MIME_TYPE });
    }

    protected ExtFormatter createFormatter() {
        return new MetaSlangFormatter(MetaSlangEditorKit.class);
    }

    public boolean getMetaSlangFormatLeadingSpaceInComment() {
        Boolean b = (Boolean)getValue(MetaSlangSettingsNames.META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT);
        if (b == null) {
            b = MetaSlangSettingsDefaults.defaultMetaSlangFormatLeadingSpaceInComment;
        }
        return b.booleanValue();
    }        
    public void setMetaSlangFormatLeadingSpaceInComment(boolean b) {
        setValue(MetaSlangSettingsNames.META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT, b ? Boolean.TRUE : Boolean.FALSE);
    }

    // Serialization ------------------------------------------------------------

    private static final ObjectStreamField[] serialPersistentFields = {
        new ObjectStreamField(META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT_PROP, Boolean.TYPE)
    };
    
    private void readObject(java.io.ObjectInputStream ois)
    throws IOException, ClassNotFoundException {
        ObjectInputStream.GetField fields = ois.readFields();
        setMetaSlangFormatLeadingSpaceInComment(fields.get(META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT_PROP,
            getMetaSlangFormatLeadingSpaceInComment()));
    }

    private void writeObject(java.io.ObjectOutputStream oos)
    throws IOException, ClassNotFoundException {
        ObjectOutputStream.PutField fields = oos.putFields();
        fields.put(META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT_PROP, getMetaSlangFormatLeadingSpaceInComment());
        oos.writeFields();
    }

}

