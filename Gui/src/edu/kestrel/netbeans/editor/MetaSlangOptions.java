/*
 * MetaSlangOptions.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:50  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import java.util.Enumeration;
import java.util.List;
import java.awt.Color;
import java.awt.Dimension;
import org.openide.TopManager;
import org.openide.ServiceType;
import org.openide.util.HelpCtx;

import org.netbeans.editor.ext.ExtSettingsNames;
import org.netbeans.modules.editor.NbEditorUtilities;
import org.netbeans.modules.editor.options.BaseOptions;

/**
 * Options for the meta-slang editor kit
 *
 */
public class MetaSlangOptions extends BaseOptions {

    //static final long serialVersionUID =-7951549840240159575L;

    public static final String META_SLANG = "meta-slang"; // NOI18N

    public static final String FORMAT_SPACE_BEFORE_PARENTHESIS_PROP = "formatSpaceBeforeParenthesis"; // NOI18N

    static final String[] META_SLANG_PROP_NAMES = new String[] {FORMAT_SPACE_BEFORE_PARENTHESIS_PROP};

    public boolean getFormatSpaceBeforeParenthesis() {
        return ((Boolean)getSettingValue(MetaSlangSettingsNames.META_SLANG_FORMAT_SPACE_BEFORE_PARENTHESIS)).booleanValue();
    }

    public void setFormatSpaceBeforeParenthesis(boolean v) {
        setSettingBoolean(MetaSlangSettingsNames.META_SLANG_FORMAT_SPACE_BEFORE_PARENTHESIS, v,
			  FORMAT_SPACE_BEFORE_PARENTHESIS_PROP);
    }

    public MetaSlangOptions() {
        this(MetaSlangEditorKit.class, META_SLANG);
    }

    public MetaSlangOptions(Class kitClass, String typeName) {
        super(kitClass, typeName);
    }

    protected Class getDefaultIndentEngineClass() {
        return MetaSlangIndentEngine.class;
    }

}
