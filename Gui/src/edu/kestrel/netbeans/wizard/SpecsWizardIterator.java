/*
 * SpecsWizardIterator.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:31  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.wizard;

import java.io.IOException;
import java.text.MessageFormat;
import java.util.ResourceBundle;

import java.awt.Component;
import java.awt.event.ActionEvent;
import javax.swing.event.ChangeListener;

import org.openide.ErrorManager;
import org.openide.WizardDescriptor;
import org.openide.filesystems.FileObject;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataFolder;
import org.openide.loaders.TemplateWizard;
import org.openide.util.NbBundle;
import org.openide.src.SourceException;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.MetaSlangDataLoader;
import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.cookies.SourceCookie;

public class SpecsWizardIterator implements TemplateWizard.Iterator {
    private static final long serialVersionUID = -1987345873459L;

    /** Array of panels that form the Wizard.
     */
    private transient WizardDescriptor.Panel[] panels;

    /**
     * Names for panels used in the Wizard.
     */
    private static String[] panelNames;
    
    /** Total number of panels that can be displayed.
     */
    private static final int PANEL_COUNT = 2;
    
    private static final int SPECS_PANEL = 1;
    
    /** Singleton instance of SpecsWizardIterator, should it be ever needed.
     */
    private static SpecsWizardIterator instance;
    
    /** Index of the current panel. Panels are numbered from 0 to PANEL_COUNT - 1.
     */
    private transient int panelIndex = 0;
    
    /** Reference to Wizard's private data structures.
     */
    private transient SpecsWizardData myData;

    /**
     * Holds a reference to the instance of TemplateWizard we are communicating with.
     */
    private transient TemplateWizard wizardInstance;
    
    /** Preferred size of each panel computed from expected largest one
     */
    private transient java.awt.Dimension prefSize;
    
    /**
     * True, if the iterator was already initialized from the Wizard's
     * input fields.
     */
    private transient boolean initialized;
    
    public SpecsWizardIterator() {
    }
    
    /** Returns SpecsWizardIterator singleton instance. This method is used
     * for constructing the instance from filesystem.attributes.
     */
    public static synchronized SpecsWizardIterator singleton() {
        if (instance == null) {
            instance = new SpecsWizardIterator();
        }
        instance.initialized = false;
        return instance;
    }
    // ========================= TemplateWizard.Iterator ============================

    /** Instantiates the template using informations provided by
     * the wizard.
     *
     * @param wiz the wizard
     * @return set of data objects that has been created (should contain
     *  at least one
     * @exception IOException if the instantiation fails
    */
    public java.util.Set instantiate(TemplateWizard wiz) throws IOException,
        IllegalArgumentException {
	Util.trace("SpecWizardIterator.instantiate(): Entering");
        // dig out file from the template.
        if (!initialized) {
	    initializeTemplateData(wiz.getTemplate());
            initializeTargetData(wiz.getTemplate(), wiz.getTargetFolder(), wiz.getTargetName());
        } else {
            updateTargetData(wiz.getTemplate(), wiz.getTargetFolder(), wiz.getTargetName());
        }
        DataObject obj = instantiateTemplate(wiz.getTemplate(), wiz.getTargetFolder(), wiz.getTargetName());
        
        SourceCookie src = (SourceCookie)obj.getCookie(SourceCookie.class);
        if (src == null) {
            return java.util.Collections.singleton(obj);
        }
	SourceElement source = src.getSource();
        try {
	    Util.log("SpecWizardIterator.instantiate(): applyChanges");
	    myData.applyChanges(source);
        } catch (SourceException e) {
            obj.delete();
            throw new IOException(e.getLocalizedMessage());
        }


        // run default action (hopefully should be here)
        org.openide.nodes.Node node = obj.getNodeDelegate ();
        org.openide.util.actions.SystemAction sa = node.getDefaultAction ();
        if (sa != null) {
            sa.actionPerformed (new ActionEvent (node, ActionEvent.ACTION_PERFORMED, "")); // NOI18N
        }
	Util.log("SpecWizardIterator.instantiate(): Exiting");
        return java.util.Collections.singleton(obj);
    }
    
    /** Get the current panel.
     * @return the panel
    */
    public WizardDescriptor.Panel current() {
        return panels[panelIndex];
    }
    
    /** Get the name of the current panel.
     * @return the name
    */
    public String name() {
        return ""; // NOI18N
    }
    
    /** Test whether there is a next panel.
     * @return <code>true</code> if so
    */
    
    public boolean hasNext() {
        return panelIndex < PANEL_COUNT - 1;
    }
    
    /** Test whether there is a previous panel.
     * @return <code>true</code> if so
    */
    public boolean hasPrevious() {
        return panelIndex > 0;
    }
    
    /** Move to the next panel.
     * I.e. increment its index, need not actually change any GUI itself.
     * @exception NoSuchElementException if the panel does not exist
    */
    public void nextPanel() {
	panelIndex++;
    }
    
    /** Move to the previous panel.
     * I.e. decrement its index, need not actually change any GUI itself.
     * @exception NoSuchElementException if the panel does not exist
    */
    public void previousPanel() {
	panelIndex--;
    }
    
    /** Add a listener to changes of the current panel.
     * The listener is notified when the possibility to move forward/backward changes.
     * @param l the listener to add
    */
    public void addChangeListener(ChangeListener l) {
    }
    
    /** Remove a listener to changes of the current panel.
     * @param l the listener to remove
    */
    public void removeChangeListener(ChangeListener l) {
    }

    public void initialize(TemplateWizard wizard) {
        this.wizardInstance = wizard;
        
	if (panels == null) {
            
            myData = new SpecsWizardData();
	    initializeTemplateData(wizard.getTemplate());
            initialize();
            
            Component panel = wizard.targetChooser().getComponent();
            panelNames[0] = panel.getName();
            if (panel instanceof javax.swing.JComponent) {
                ((javax.swing.JComponent)panel).putClientProperty(
                    "WizardPanel_contentData", panelNames); // NOI18N
            }
            panels = new WizardDescriptor.Panel[] {
                wizardInstance.targetChooser(),
                new DelegatingPanel(SpecsPanel.class, true),
            };
	}
        reset();
    }
    
    public void uninitialize(TemplateWizard wiz) {
	panels = null;
	myData = null;
        initialized = false;
    }

    // ========================= IMPLEMENTATION ============================
    
    private Object readResolve() {
        initialize();
        reset();
        return this;
    }
    
    /** Instantiates the template. Currently it just delegates to the template DataObject's
     * createFromTemplate method.
     */
    private DataObject instantiateTemplate(DataObject tpl, DataFolder target, String targetName) throws IOException {
        checkTargetName(target, targetName);
        return tpl.createFromTemplate(target, targetName);
    }
    
    protected void reset() {
        panelIndex = 0;
    }

    /** Initializes the Wizard with array of panels.
     */
    protected void initialize() {
	panelNames = new String[2];
        panelNames[0] = "";
	panelNames[1] = getString("TIT_AddSpecsWizardPanel");
    }
    
    private void checkTargetName(DataFolder folder, String desiredName) {
        if (!MetaSlangSyntax.isMetaSlangIdentifier(desiredName)) {
            String msg = MessageFormat.format(getString("FMTERR_IllegalTargetName"),
            new Object[] {
                desiredName
            });
            IllegalStateException x = 
                (IllegalStateException)ErrorManager.getDefault().annotate(
            new IllegalStateException(msg),
            ErrorManager.USER, null, msg,
            null, null
            );
            throw x;
        }
        FileObject f = folder.getPrimaryFile();
        // check whether the name already exists:
        if (f.getFileObject(desiredName, MetaSlangDataLoader.META_SLANG_EXTENSION) != null) { // NOI18N
            String msg = MessageFormat.format(getString("FMTERR_TargetExists"),
            new Object[] {
                desiredName
            });
            throw new IllegalStateException(msg);
        }
    }

    private void initializeTemplateData(DataObject template) throws IllegalStateException {
        if (template == null) {
            throw new IllegalStateException("Expected template, got null"); // NOI18N
        }

        myData.setTemplate(template);
    }
    
    private void initializeTargetData(DataObject template, DataFolder targetFolder, String desiredName) 
        throws IllegalStateException {
        if (template == null || targetFolder == null) {
            throw new IllegalStateException("Expected template & target folder, got null(s)"); // NOI18N
        }
        updateTargetData(template, targetFolder, desiredName);
        prefSize = panels[1].getComponent().getPreferredSize();
        initialized = true;
    }
    
    private void updateTargetData(DataObject template, DataFolder targetFolder, String desiredName) 
        throws IllegalStateException {
        FileObject folder = targetFolder.getPrimaryFile();
        if (desiredName == null) {
            // make up an name using the Template's name
            desiredName = org.openide.filesystems.FileUtil.findFreeFileName(folder,
                template.getName(), MetaSlangDataLoader.META_SLANG_EXTENSION);
        } else {
            checkTargetName(targetFolder, desiredName);
        }
    }

    private class DelegatingPanel implements WizardDescriptor.Panel, 
        WizardDescriptor.FinishPanel {

        private Class   panelClass;
        private boolean init;
        private WizardDescriptor.Panel  instance;
        
        DelegatingPanel(Class c, boolean initData) {
            panelClass = c;
            init = initData;
        }
        
        private WizardDescriptor.Panel getInstance() {
            if (instance != null)
                return instance;
            try {
                instance = (WizardDescriptor.Panel)panelClass.newInstance();
                if (instance instanceof SpecsPanel) {
                    ((SpecsPanel)instance).initialize(myData);
                }
            } catch (Exception ex) {
                ex.printStackTrace();
            }
            return instance;
        }
        
        public org.openide.util.HelpCtx getHelp() {
            return getInstance().getHelp();
        }
        
        public void storeSettings(Object s) {
            getInstance().storeSettings(s);
        }
        
        public void addChangeListener(ChangeListener l) {
            getInstance().addChangeListener(l);
        }
        
        public void removeChangeListener(ChangeListener l) {
            getInstance().removeChangeListener(l);
        }
        
        public boolean isValid() {
            return getInstance().isValid();
        }
        
        public Component getComponent() {
            //return (Component)instance;
            ((javax.swing.JComponent) getInstance()).setPreferredSize(prefSize);
            if (panelIndex == panelNames.length) {
                ((javax.swing.JComponent) getInstance())
                    .putClientProperty("WizardPanel_contentSelectedIndex",  // NOI18N
                        new Integer(panelNames.length - 1)); //NOI18N
            }
            return getInstance().getComponent();
        }
        
        public void readSettings(Object settings) {
            if (!init || !(settings instanceof TemplateWizard)) {
                return;
            }
            TemplateWizard wizardInstance = (TemplateWizard)settings;
            
            DataFolder target = null;
            DataObject template = null;
            
            try {
                target = wizardInstance.getTargetFolder();
                template = wizardInstance.getTemplate();
            } catch (java.io.IOException ex) {
                // PENDING: provide better message / annotate through error manager.
                throw new IllegalStateException("Illegal settings"); // NOI18N
            }

            initializeTargetData(template, target, wizardInstance.getTargetName());
            
            getInstance().readSettings(settings);
        }
    }

    private static ResourceBundle bundle;

    static String getString(String key) {
        if (bundle == null)
             bundle = org.openide.util.NbBundle.getBundle(SpecsWizardIterator.class);
        return bundle.getString(key);
    }
    
    static char getMnemonic(String key) {
	if (bundle == null)
	    bundle = org.openide.util.NbBundle.getBundle(SpecsWizardIterator.class);
	    return bundle.getString(key).charAt(0);
    }
}
