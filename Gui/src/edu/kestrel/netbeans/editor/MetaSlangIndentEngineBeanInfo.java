/*
 * MetaSlangIndentEngineBeanInfo.java
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

import java.beans.BeanDescriptor;
import java.util.MissingResourceException;
import org.netbeans.modules.editor.FormatterIndentEngineBeanInfo;
import org.netbeans.modules.editor.NbEditorUtilities;
import org.openide.util.NbBundle;

/**
 * Beaninfo for MetaSlangIndentEngine.
 *
 */

public class MetaSlangIndentEngineBeanInfo extends FormatterIndentEngineBeanInfo {

    private BeanDescriptor beanDescriptor;

    public MetaSlangIndentEngineBeanInfo() {
    }

    public BeanDescriptor getBeanDescriptor () {
        if (beanDescriptor == null) {
            beanDescriptor = new BeanDescriptor(getBeanClass());
            beanDescriptor.setDisplayName(getString("LAB_MetaSlangIndentEngine"));
            beanDescriptor.setShortDescription(getString("HINT_MetaSlangIndentEngine"));
            beanDescriptor.setValue("global", Boolean.TRUE); // NOI18N
        }
        return beanDescriptor;
    }

    protected Class getBeanClass() {
        return MetaSlangIndentEngine.class;
    }

    protected String[] createPropertyNames() {
        return NbEditorUtilities.mergeStringArrays(super.createPropertyNames(),
            new String[] {
                MetaSlangIndentEngine.META_SLANG_FORMAT_LEADING_SPACE_IN_COMMENT_PROP
            }
        );
    }

    protected String getString(String key) {
        try {
            return NbBundle.getBundle(MetaSlangIndentEngineBeanInfo.class).getString(key);
        } catch (MissingResourceException e) {
            return super.getString(key);
        }
    }

}

