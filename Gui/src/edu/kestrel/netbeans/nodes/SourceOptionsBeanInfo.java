/*
 * SourceOptionsBeanInfo.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.*;
import java.awt.Image;
import java.util.ResourceBundle;

import org.openide.TopManager;
import org.openide.util.NbBundle;
import org.openide.util.Utilities;
import org.openide.ErrorManager;

/** BeanInfo for source options.
*
*/
public final class SourceOptionsBeanInfo extends SimpleBeanInfo {
    /** Prefix of the icon location. */

    public BeanDescriptor getBeanDescriptor() {
        ResourceBundle bundle = NbBundle.getBundle(SourceOptionsBeanInfo.class);
        BeanDescriptor desc = new BeanDescriptor(SourceOptions.class);
        desc.setDisplayName(bundle.getString("MSG_sourceOptions"));
        /* for Post-FCS desc.setShortDescription(bundle.getString("HINT_sourceOptions")); */
        return desc;
    }

    /*
    * @return Returns an array of PropertyDescriptors
    * describing the editable properties supported by this bean.
    */
    public PropertyDescriptor[] getPropertyDescriptors () {
        try {
    	    ResourceBundle bundle = NbBundle.getBundle(SourceOptionsBeanInfo.class);
            PropertyDescriptor[] descriptors = new PropertyDescriptor[6];
            for (int i = 0; i < 6; i++) {
                descriptors[i] = new PropertyDescriptor(SourceOptions.PROP_NAMES[i], SourceOptions.class);
                descriptors[i].setDisplayName(bundle.getString("PROP_"+SourceOptions.PROP_NAMES[i]));
                descriptors[i].setShortDescription(bundle.getString("HINT_"+SourceOptions.PROP_NAMES[i]));
            }
            //        descriptors[6] = new PropertyDescriptor(SourceOptions.PROP_CATEGORIES_USAGE, SourceOptions.class);
            //        descriptors[6].setDisplayName(bundle.getString("PROP_"+SourceOptions.PROP_CATEGORIES_USAGE));
            //        descriptors[6].setShortDescription(bundle.getString("HINT_"+SourceOptions.PROP_CATEGORIES_USAGE));
    	    return descriptors;
        } catch (IntrospectionException e) {
	    ErrorManager.getDefault().notify(e);
	    return null;
        }
    }

    /* @param type Desired type of the icon
    * @return returns the Java loader's icon
    */
    public Image getIcon(final int type) {
        if ((type == BeanInfo.ICON_COLOR_16x16) || (type == BeanInfo.ICON_MONO_16x16)) {
	    return Utilities.loadImage("/edu/kestrel/resources/src/sourceOptions.gif"); // NOI18N
        }
        else {
            return Utilities.loadImage("/edu/kestrel/resources/src/sourceOptions32.gif"); // NOI18N
        }
    }
}
