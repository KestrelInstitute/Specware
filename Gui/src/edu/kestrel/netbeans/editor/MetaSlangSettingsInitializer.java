/*
 * MetaSlangSettingsInitializer.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:01:51  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.editor;

import java.util.Map;
import org.netbeans.editor.Settings;
import org.netbeans.editor.SettingsUtil;
import org.netbeans.editor.SettingsNames;
import org.netbeans.editor.BaseKit;
import org.netbeans.editor.TokenContext;
import org.netbeans.editor.ext.ExtSettingsNames;

/**
* Extended settings for MetaSlang.
*
*/

public class MetaSlangSettingsInitializer extends Settings.AbstractInitializer {

    /** Name assigned to initializer */
    public static final String NAME = "meta-slang-settings-initializer";

    private static boolean inited = false;

    public static void init() {
        if (!inited) {
            inited = true;
            Settings.addInitializer(new MetaSlangSettingsInitializer(MetaSlangEditorKit.class));
            Settings.reset();
        }
    }

    private Class metaSlangKitClass;

    /** Construct new meta-slang-settings-initializer.
    * @param metaSlangKitClass the real kit class for which the settings are created.
    *   It's unknown here so it must be passed to this constructor.
    */
    public MetaSlangSettingsInitializer(Class metaSlangKitClass) {
        super(NAME);
        this.metaSlangKitClass = metaSlangKitClass;
    }

    /** Update map filled with the settings.
    * @param kitClass kit class for which the settings are being updated.
    *   It is always non-null value.
    * @param settingsMap map holding [setting-name, setting-value] pairs.
    *   The map can be empty if this is the first initializer
    *   that updates it or if no previous initializers updated it.
    */
    public void updateSettingsMap(Class kitClass, Map settingsMap) {

        // Update meta-slang colorings
        if (kitClass == BaseKit.class) {

            new MetaSlangSettingsDefaults.MetaSlangTokenColoringInitializer().updateSettingsMap(kitClass, settingsMap);
            new MetaSlangSettingsDefaults.MetaSlangLayerTokenColoringInitializer().updateSettingsMap(kitClass, settingsMap);

        }

        if (kitClass == metaSlangKitClass) {
            
            SettingsUtil.updateListSetting(settingsMap, SettingsNames.KEY_BINDING_LIST,
                MetaSlangSettingsDefaults.getMetaSlangKeyBindings());

            SettingsUtil.updateListSetting(settingsMap, SettingsNames.TOKEN_CONTEXT_LIST,
                new TokenContext[] {
                    MetaSlangTokenContext.context,
                    MetaSlangLayerTokenContext.context
                }
            );

            settingsMap.put(SettingsNames.INDENT_SHIFT_WIDTH, MetaSlangSettingsDefaults.defaultMetaSlangIndentShiftWidth);

            settingsMap.put(SettingsNames.ABBREV_MAP, MetaSlangSettingsDefaults.getMetaSlangAbbrevMap());

            settingsMap.put(SettingsNames.MACRO_MAP, MetaSlangSettingsDefaults.getMetaSlangMacroMap());

            settingsMap.put(ExtSettingsNames.CARET_SIMPLE_MATCH_BRACE,
                            MetaSlangSettingsDefaults.defaultCaretSimpleMatchBrace);

            settingsMap.put(ExtSettingsNames.HIGHLIGHT_MATCH_BRACE,
                            MetaSlangSettingsDefaults.defaultHighlightMatchBrace);

            settingsMap.put(SettingsNames.IDENTIFIER_ACCEPTOR,
                            MetaSlangSettingsDefaults.defaultIdentifierAcceptor);

            settingsMap.put(SettingsNames.ABBREV_RESET_ACCEPTOR,
                            MetaSlangSettingsDefaults.defaultAbbrevResetAcceptor);

            settingsMap.put(SettingsNames.WORD_MATCH_MATCH_CASE,
                            MetaSlangSettingsDefaults.defaultWordMatchMatchCase);

            settingsMap.put(SettingsNames.WORD_MATCH_STATIC_WORDS,
                            MetaSlangSettingsDefaults.defaultWordMatchStaticWords);

            // Formatting settings
            settingsMap.put(MetaSlangSettingsNames.META_SLANG_FORMAT_SPACE_BEFORE_PARENTHESIS,
                            MetaSlangSettingsDefaults.defaultMetaSlangFormatSpaceBeforeParenthesis);

            settingsMap.put(MetaSlangSettingsNames.META_SLANG_FORMAT_SPACE_AFTER_COMMA,
                            MetaSlangSettingsDefaults.defaultMetaSlangFormatSpaceAfterComma);

            settingsMap.put(MetaSlangSettingsNames.META_SLANG_FORMAT_NEWLINE_BEFORE_BRACE,
                            MetaSlangSettingsDefaults.defaultFormatNewlineBeforeBrace);

            settingsMap.put(MetaSlangSettingsNames.META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT,
                            MetaSlangSettingsDefaults.defaultMetaSlangFormatLeadingSpaceInComment);

            settingsMap.put(MetaSlangSettingsNames.INDENT_HOT_CHARS_ACCEPTOR,
                            MetaSlangSettingsDefaults.defaultIndentHotCharsAcceptor);

            settingsMap.put(ExtSettingsNames.REINDENT_WITH_TEXT_BEFORE,
                            Boolean.FALSE);
        }

    }

}
