/*
 * MetaSlangSettingsNames.java
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

import org.netbeans.editor.ext.ExtSettingsNames;

/**
* Names of the meta-slang editor settings.
*
*/

public class MetaSlangSettingsNames extends ExtSettingsNames {

    /** Whether insert extra space before the parenthesis or not.
    * Values: java.lang.Boolean instances
    * Effect: function(a)
    *           becomes (when set to true)
    *         function (a)
    */
    public static final String META_SLANG_FORMAT_SPACE_BEFORE_PARENTHESIS
    = "meta-slang-format-space-before-parenthesis"; // NOI18N

    /** Whether insert space after the comma inside the parameter list.
    * Values: java.lang.Boolean instances
    * Effect: function(a,b)
    *           becomes (when set to true)
    *         function(a, b)
    *
    */
    public static final String META_SLANG_FORMAT_SPACE_AFTER_COMMA
    = "meta-slang-format-space-after-comma"; // NOI18N

    /** Whether insert extra new-line before the compound bracket or not.
    * Values: java.lang.Boolean instances
    * Effect: if (test) {
    *           function();
    *         }
    *           becomes (when set to true)
    *         if (test)
    *         {
    *           function();
    *         }
    */
    public static final String META_SLANG_FORMAT_NEWLINE_BEFORE_BRACE
    = "meta-slang-format-newline-before-brace"; // NOI18N

    /** Add one more space to the begining of each line
    * in the multi-line comment if it's not already there.
    * Values: java.lang.Boolean
    * Effect: For example in meta-slang:
    *
    *        (* this is
    *         multiline comment
    *        *)
    *
    *            becomes (when set to true)
    *
    *         (* this is
    *            multiline comment
    *          *)
    */
    public static final String META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT
    = "meta-slang-format-leading-space-in-comment"; // NOI18N

}
