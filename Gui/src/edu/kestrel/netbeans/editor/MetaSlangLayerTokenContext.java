/*
 * MetaSlangLayerTokenContext.java
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

import org.netbeans.editor.BaseTokenCategory;
import org.netbeans.editor.BaseTokenID;
import org.netbeans.editor.TokenContext;
import org.netbeans.editor.TokenContextPath;

/**
 * Various extensions to the displaying of the meta-slang tokens
 * is defined here. The tokens defined here are used
 * by the meta-slang-drawing-layer.
 *
 */

public class MetaSlangLayerTokenContext extends TokenContext {

    // Token category-ids

    // Token-categories
//    public static final BaseTokenCategory KEYWORDS
//    = new BaseTokenCategory("keywords", KEYWORDS_ID);


    // Context instance declaration
    public static final MetaSlangLayerTokenContext context = new MetaSlangLayerTokenContext();

    public static final TokenContextPath contextPath = context.getContextPath();


    private MetaSlangLayerTokenContext() {
        super("meta-slang-layer-");

        try {
            addDeclaredTokenIDs();
        } catch (Exception e) {
            if (Boolean.getBoolean("netbeans.debug.exceptions")) { // NOI18N
                e.printStackTrace();
            }
        }

    }

}

