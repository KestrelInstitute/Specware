/*
 * SpecsWizardData.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */


package edu.kestrel.netbeans.wizard;

import java.util.*;

import org.openide.filesystems.FileObject;
import org.openide.loaders.DataObject;
import org.openide.util.NbBundle;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.cookies.SourceCookie;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.parser.*;

/**
 * The class encapsulates a state of Java Wizard's iterator shared among various
 * wizard components.
 */
public class SpecsWizardData extends Object {
    /** Template object that is to be customized.
     */
    private DataObject obj;

    private SourceElement customizedSource;

    private SpecElement[] originalSpecs;

    private String[] originalSpecNames;

    //private List customizedSpecs;

    /** Creates new SpecsWizardData */
    public SpecsWizardData() {
    }

    void setTemplate(DataObject obj) {
	if (obj.equals(this.obj)) {
	    return;
	}
        this.obj = obj;
        SourceCookie cookie = (SourceCookie)obj.getCookie(SourceCookie.class);
	SourceElement source = null;

        if (cookie != null) {
            source = cookie.getSource();
            source.prepare().waitFinished();
	    originalSpecs = source.getSpecs();
	    originalSpecNames = new String[originalSpecs.length];
	    for (int i = 0; i < originalSpecs.length; i++) {
		originalSpecNames[i] = originalSpecs[i].getName();
	    }
	    Util.log("SpecsWizardData.setTemplate(): originalSpecs="+Util.print(originalSpecs));
	    Util.log("SpecsWizardData.setTemplate(): originalSpecNames="+Util.print(originalSpecNames));
        }
	customizedSource = source;
    }

    void restoreSource() {
	Util.log("SpecsWizardData.restoreSource(): originalSpecs="+Util.print(originalSpecs));
	Util.log("SpecsWizardData.restoreSource(): originalSpecNames="+Util.print(originalSpecNames));
	try {
	    if (customizedSource != null) {
		for (int i = 0; i < originalSpecs.length; i++) {
		    originalSpecs[i].setName(originalSpecNames[i]);
		}
		customizedSource.setSpecs(originalSpecs);
	    }
	} catch (SourceException e) {
	}
    }
		
    /** Copy properties of a customized class (model) to the target class.
     * Only class own properties, methods, constructors and fields are copied.
     * Inner classes are not handled by this method.
     * No methods are removed or replaced from/in the original class
     * @param target the target class in the source being newly created.
     */
    void applyChanges(SourceElement target) throws SourceException {
        if (target == null || customizedSource == null)
            return;
	SpecElement[] specs = customizedSource.getSpecs();
	for (int i = 0; i < specs.length; i++) {
	    Util.log("*** SpecWizardData.applyChanges: i="+i+" spec="+specs[i].getName());
	}
        target.setSpecs(specs);
	restoreSource();
    }

    public SpecElement[] getOriginalSpecs() {
        return originalSpecs;
    }

    public DataObject getDataObject() {
        return obj;
    }

    public SourceElement getCustomizedSource() {
        return customizedSource;
    }

}
