/*
 * MetaSlangSettingsDefaults
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

import java.awt.event.KeyEvent;
import java.awt.event.InputEvent;
import java.awt.Font;
import java.awt.Color;
import javax.swing.KeyStroke;
import java.util.Map;
import java.util.HashMap;
import java.util.TreeMap;
import org.netbeans.editor.Acceptor;
import org.netbeans.editor.AcceptorFactory;
import org.netbeans.editor.Coloring;
import org.netbeans.editor.Settings;
import org.netbeans.editor.SettingsDefaults;
import org.netbeans.editor.SettingsUtil;
import org.netbeans.editor.TokenCategory;
import org.netbeans.editor.TokenContextPath;
import org.netbeans.editor.MultiKeyBinding;
import org.netbeans.editor.ext.ExtSettingsDefaults;
import org.netbeans.editor.ext.ExtKit;

/**
 * Default settings values for MetaSlang.
 *
 */

public class MetaSlangSettingsDefaults extends ExtSettingsDefaults {

    public static final Boolean defaultCaretSimpleMatchBrace = Boolean.FALSE;
    public static final Boolean defaultHighlightMatchingBracket = Boolean.TRUE;

    public static final Acceptor defaultIdentifierAcceptor = AcceptorFactory.JAVA_IDENTIFIER;
    public static final Acceptor defaultAbbrevResetAcceptor = AcceptorFactory.NON_JAVA_IDENTIFIER;
    public static final Boolean defaultWordMatchMatchCase = Boolean.TRUE;

    // Formatting
    public static final Boolean defaultMetaSlangFormatSpaceBeforeParenthesis = Boolean.FALSE;
    public static final Boolean defaultMetaSlangFormatSpaceAfterComma = Boolean.TRUE;
    public static final Boolean defaultMetaSlangFormatNewlineBeforeBrace = Boolean.FALSE;
    public static final Boolean defaultMetaSlangFormatLeadingSpaceInComment = Boolean.FALSE;

    public static final Integer defaultMetaSlangIndentShiftWidth = new Integer(3);


    /** @deprecated */
    public static final Boolean defaultFormatSpaceBeforeParenthesis = defaultMetaSlangFormatSpaceBeforeParenthesis;
    /** @deprecated */
    public static final Boolean defaultFormatSpaceAfterComma = defaultMetaSlangFormatSpaceAfterComma;
    /** @deprecated */
    public static final Boolean defaultFormatNewlineBeforeBrace = defaultMetaSlangFormatNewlineBeforeBrace;
    /** @deprecated */
    public static final Boolean defaultFormatLeadingSpaceInComment = defaultMetaSlangFormatLeadingSpaceInComment;

    public static final Acceptor defaultIndentHotCharsAcceptor
        = new Acceptor() {
            public boolean accept(char ch) {
                switch (ch) {
                    case '{':
                    case '}':
                        return true;
                }

                return false;
            }
        };


    public static final String defaultWordMatchStaticWords
    = "Exception IntrospectionException FileNotFoundException IOException" // NOI18N
      + " ArrayIndexOutOfBoundsException ClassCastException ClassNotFoundException" // NOI18N
      + " CloneNotSupportedException NullPointerException NumberFormatException" // NOI18N
      + " SQLException IllegalAccessException IllegalArgumentException"; // NOI18N

    public static Map getMetaSlangAbbrevMap() {
        Map metaSlangAbbrevMap = new TreeMap();
        //metaSlangAbbrevMap.put("ct", "constant "); // NOI18N

        return metaSlangAbbrevMap;
    }

    public static MultiKeyBinding[] getMetaSlangKeyBindings() {
        return new MultiKeyBinding[] {
                   new MultiKeyBinding(
                       new KeyStroke[] {
                           KeyStroke.getKeyStroke(KeyEvent.VK_J, InputEvent.CTRL_MASK),
                           KeyStroke.getKeyStroke(KeyEvent.VK_D, 0)
                       },
                       "macro-debug-var"
                   ),
                   new MultiKeyBinding(
                       KeyStroke.getKeyStroke(KeyEvent.VK_T, InputEvent.CTRL_MASK | InputEvent.SHIFT_MASK),
                       ExtKit.commentAction
                   ),
                  new MultiKeyBinding(
                      KeyStroke.getKeyStroke(KeyEvent.VK_D, InputEvent.CTRL_MASK | InputEvent.SHIFT_MASK),
                      ExtKit.uncommentAction
                  )
               };
    }
    
    public static Map getMetaSlangMacroMap() {
        Map metaSlangMacroMap = new HashMap();
        metaSlangMacroMap.put( "debug-var", "select-identifier copy-to-clipboard " +
                "caret-up caret-end-line insert-break \"System.err.println(\\\"\"" + 
                "paste-from-clipboard \" = \\\" + \" paste-from-clipboard \" );" );
        
        return metaSlangMacroMap;
    }

    static class MetaSlangTokenColoringInitializer
    extends SettingsUtil.TokenColoringInitializer {

        Font boldFont = SettingsDefaults.defaultFont.deriveFont(Font.BOLD);
        Font italicFont = SettingsDefaults.defaultFont.deriveFont(Font.ITALIC);
        Settings.Evaluator boldSubst = new SettingsUtil.FontStylePrintColoringEvaluator(Font.BOLD);
        Settings.Evaluator italicSubst = new SettingsUtil.FontStylePrintColoringEvaluator(Font.ITALIC);
        Settings.Evaluator lightGraySubst = new SettingsUtil.ForeColorPrintColoringEvaluator(Color.lightGray);

        Coloring commentColoring = new Coloring(italicFont, Coloring.FONT_MODE_APPLY_STYLE,
                            new Color(115, 115, 115), null);

        Coloring numbersColoring = new Coloring(null, new Color(120, 0, 0), null);

        public MetaSlangTokenColoringInitializer() {
            super(MetaSlangTokenContext.context);
        }

        public Object getTokenColoring(TokenContextPath tokenContextPath,
        TokenCategory tokenIDOrCategory, boolean printingSet) {
            if (!printingSet) {
                switch (tokenIDOrCategory.getNumericID()) {
                    case MetaSlangTokenContext.WHITESPACE_ID:
                    case MetaSlangTokenContext.IDENTIFIER_ID:
                    case MetaSlangTokenContext.OPERATORS_ID:
                        return SettingsDefaults.emptyColoring;

                    case MetaSlangTokenContext.ERRORS_ID:
                        return new Coloring(null, Color.white, Color.red);

                    case MetaSlangTokenContext.KEYWORDS_ID:
                        return new Coloring(boldFont, Coloring.FONT_MODE_APPLY_STYLE,
					    new Color(0, 0, 153), null);


                    case MetaSlangTokenContext.LINE_COMMENT_ID:
                    case MetaSlangTokenContext.BLOCK_COMMENT_ID:
                    case MetaSlangTokenContext.LATEX_COMMENT_ID:
                        return commentColoring;

                    case MetaSlangTokenContext.CHAR_LITERAL_ID:
                        return new Coloring(null, new Color(0, 111, 0), null);

                    case MetaSlangTokenContext.STRING_LITERAL_ID:
                        return new Coloring(null, new Color(153, 0, 107), null);

                    case MetaSlangTokenContext.NUMERIC_LITERALS_ID:
                        return numbersColoring;

                }

            } else { // printing set
                switch (tokenIDOrCategory.getNumericID()) {
                    case MetaSlangTokenContext.LINE_COMMENT_ID:
                    case MetaSlangTokenContext.BLOCK_COMMENT_ID:
                         return lightGraySubst; // print fore color will be gray

                    default:
                         return SettingsUtil.defaultPrintColoringEvaluator;
                }

            }

            return null;

        }

    }

    static class MetaSlangLayerTokenColoringInitializer
	extends SettingsUtil.TokenColoringInitializer {

        Font boldFont = SettingsDefaults.defaultFont.deriveFont(Font.BOLD);
        Settings.Evaluator italicSubst = new SettingsUtil.FontStylePrintColoringEvaluator(Font.ITALIC);

        public MetaSlangLayerTokenColoringInitializer() {
            super(MetaSlangLayerTokenContext.context);
        }

        public Object getTokenColoring(TokenContextPath tokenContextPath,
				       TokenCategory tokenIDOrCategory,
				       boolean printingSet) {
            if (printingSet) {
		return SettingsUtil.defaultPrintColoringEvaluator;
            }

            return null;
        }

    }

}
