package edu.kestrel.netbeans.nodes;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.MorphismElement;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.model.SpecElement;
import edu.kestrel.netbeans.model.UnitID;
import edu.kestrel.netbeans.nodes.MemberCustomizer;
import edu.kestrel.netbeans.nodes.SourceEditSupport.ExceptionalRunnable;

import edu.kestrel.netbeans.lisp.LispProcessManager;

import java.io.IOException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.ResourceBundle;
import javax.swing.*;
import javax.swing.border.*;

import org.openide.ErrorManager;
import org.openide.filesystems.Repository;
import org.openide.filesystems.FileObject;
import org.openide.filesystems.FileSystem;
import org.openide.loaders.DataObject;
import org.openide.loaders.DataObjectNotFoundException;
import org.openide.src.SourceException;
import org.openide.util.NbBundle;
import org.openide.util.Task;
import org.openide.util.Utilities;

/**
 *
 * @author  weilyn
 */
public class MorphismCustomizer extends javax.swing.JPanel {
    private static final boolean DEBUG = false;
    
    private static final String currentFileText = "<current file>";
    
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(MorphismCustomizer.class);
        
    private MorphismElement element;
    private SourceElement srcElement;
    private String packageName = null;
    
    private HashMap dataObjects = new HashMap();
    
    boolean isOK = true;
        
    /** Creates new customizer MorphismCustomizer */
    public MorphismCustomizer(MorphismElement newMorphismElem, SourceElement srcElement) {
        initComponents();

        this.element = newMorphismElem;
        this.srcElement = srcElement;
        
        if (this.element != null) {
	    nameTextField.setText(element.getName());
            initComboBoxes();
	}
        
        //borders
        setBorder (new CompoundBorder(
                       new TitledBorder(bundle.getString("CTL_MorphismFrame")),
                       new EmptyBorder(new java.awt.Insets(5, 5, 5, 5)))
                       );
    }
    
    private void initComboBoxes() {
        String swpath = System.getProperty("Env-SWPATH");
        if (DEBUG) {
            Util.log("MorphismCustomizer.initComboBoxes: swpath is "+swpath);
        }
        
        String[] paths;
        if (Utilities.isWindows()) {
            paths = swpath.split(";");
        } else {
            paths = swpath.split(":");
        }
        FileObject fo = null;
                
        Repository rep = Repository.getDefault();       

        // First, iterate through the mounted filesystems, then check whether any
        // of the SWPATHs are a substring
        
        for (Enumeration allFS = rep.getFileSystems(); allFS.hasMoreElements(); ) {
            FileSystem fs = (FileSystem)allFS.nextElement();
            
            for (int i=0; i<paths.length; i++) {
                String onePath = paths[i];
                
                if (DEBUG) {
                    Util.log("onePath is "+onePath);
                }
                
                if (Utilities.isWindows()) {
                    // TODO: make more robust if possible...these are kidna dumb checks 
                    // for things that could be wrong with SWPATH...
                    // note: it looks like mounted jar files' system names use '\', but 
                    // mounted local directories use '/' in their system names
                    //onePath = onePath.replace('/', '\\');
                    onePath = onePath.replace('\\', '/');
                    onePath = onePath.replaceAll("Progra~1", "Program Files");
                    if (!onePath.startsWith("C:")) {
                        onePath = "C:" + onePath;
                    }
                }
                
//                FileSystem fs = rep.findFileSystem(onePath);
                
                if (fs.getDisplayName().indexOf(onePath) != -1) {
                
//                if (fs != null) {
                    FileObject rootFolder = fs.getRoot();
                    if (rootFolder != null) {
                        if (DEBUG) {
                            Util.log("MorphismCustomizer.initComboBoxes: found filesystem "+fs.getDisplayName()+" with rootFolder="+rootFolder.getName());
                        }
                        
                        for (Enumeration e = rootFolder.getData(true); e.hasMoreElements(); ) {
                            FileObject data = (FileObject)e.nextElement();
                            try {
                                DataObject obj = DataObject.find(data);
                                if (obj instanceof MetaSlangDataObject) {
                                    MetaSlangDataObject msDataObj = (MetaSlangDataObject)obj;
                                    SourceElement source = msDataObj.getSource();
                                    prepareSource(source);
                                    
                                    // now only display those files with specs in them
                                    if (source.getSpecs().length != 0) {
                                        if (msDataObj.getSource().equals(this.srcElement)) {
                                            this.packageName = data.getPackageName('/');
                                            sourceFileComboBox.insertItemAt(currentFileText, 0);
                                            targetFileComboBox.insertItemAt(currentFileText, 0);
                                            dataObjects.put(this.packageName, msDataObj);
                                        } else {
                                            sourceFileComboBox.addItem(data.getPackageName('/'));
                                            targetFileComboBox.addItem(data.getPackageName('/'));
                                            dataObjects.put(data.getPackageName('/'), msDataObj);
                                        }
                                    }
                                }
                            } catch (DataObjectNotFoundException ex) {}
                        }
                        if (sourceFileComboBox.getItemCount() != 0) {
                            sourceFileComboBox.setSelectedIndex(0);
                            setSpecs((String)sourceFileComboBox.getSelectedItem(), sourceComboBox);
                        }
                        if (targetFileComboBox.getItemCount() != 0) {
                            targetFileComboBox.setSelectedIndex(0);
                            setSpecs((String)targetFileComboBox.getSelectedItem(), targetComboBox);
                        }
                    }
                }
            }
        }
    }
    
    private void prepareSource(SourceElement source) {
        Task parsingTask = source.prepare();
        if (parsingTask.isFinished()) {
            return;
        } else {
            parsingTask.addTaskListener(new org.openide.util.TaskListener() {
                public void taskFinished(Task t) {
                    t.removeTaskListener(this);
                }
            });
        }
    }    
    
    private void setSpecs(String fileName, final JComboBox whichBox) {
        MetaSlangDataObject msdo;

        if (fileName.equals(currentFileText)) { //then add a relative inner spec unitid
            msdo = (MetaSlangDataObject)dataObjects.get(this.packageName);
        } else {
            msdo = (MetaSlangDataObject)dataObjects.get(fileName);
        }
        if (msdo != null) {
            final SourceElement source = msdo.getSource();

            addSpecsToComboBox(source, whichBox);
        }
    }
    
    private void addSpecsToComboBox(SourceElement source, JComboBox whichBox) {
        whichBox.removeAllItems();
        SpecElement[] specs = source.getSpecs();
        for (int j=0; j<specs.length; j++) {
            whichBox.addItem(specs[j].getName());
        }
        if (specs.length > 0) {
            whichBox.setSelectedIndex(0);
        }
    }
    
    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the FormEditor.
     */
    private void initComponents() {//GEN-BEGIN:initComponents
        java.awt.GridBagConstraints gridBagConstraints;

        nameLabel = new javax.swing.JLabel();
        sourceLabel = new javax.swing.JLabel();
        targetLabel = new javax.swing.JLabel();
        nameTextField = new javax.swing.JTextField();
        sourceFileComboBox = new javax.swing.JComboBox();
        targetFileComboBox = new javax.swing.JComboBox();
        sourceComboBox = new javax.swing.JComboBox();
        targetComboBox = new javax.swing.JComboBox();
        jLabel1 = new javax.swing.JLabel();
        jLabel2 = new javax.swing.JLabel();

        setLayout(new java.awt.GridBagLayout());

        nameLabel.setText("Name:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        add(nameLabel, gridBagConstraints);

        sourceLabel.setText("From spec:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        add(sourceLabel, gridBagConstraints);

        targetLabel.setText("To spec:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        add(targetLabel, gridBagConstraints);

        nameTextField.setText("newMorphism");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridwidth = 3;
        gridBagConstraints.ipadx = 121;
        gridBagConstraints.ipady = 8;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(nameTextField, gridBagConstraints);

        sourceFileComboBox.setEditable(true);
        sourceFileComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                sourceFileComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(sourceFileComboBox, gridBagConstraints);

        targetFileComboBox.setEditable(true);
        targetFileComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                targetFileComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(targetFileComboBox, gridBagConstraints);

        sourceComboBox.setEditable(true);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 3;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 75;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(sourceComboBox, gridBagConstraints);

        targetComboBox.setEditable(true);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 3;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 75;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(targetComboBox, gridBagConstraints);

        jLabel1.setText("#");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 2;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 4;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(jLabel1, gridBagConstraints);

        jLabel2.setText("#");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 2;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 4;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(jLabel2, gridBagConstraints);

    }//GEN-END:initComponents

    private void targetFileComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_targetFileComboBoxActionPerformed
        setSpecs((String)targetFileComboBox.getSelectedItem(), targetComboBox);
    }//GEN-LAST:event_targetFileComboBoxActionPerformed

    private void sourceFileComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_sourceFileComboBoxActionPerformed
        setSpecs((String)sourceFileComboBox.getSelectedItem(), sourceComboBox);
    }//GEN-LAST:event_sourceFileComboBoxActionPerformed

    private void nameTextFieldFocusLost (java.awt.event.FocusEvent evt) {
        if (evt != null && evt.isTemporary())
            return;

        final String newName = nameTextField.getText();
        String oldName = element.getName();
        boolean ok = false;
        Exception x = null;

        if (oldName == null || !oldName.equals(newName)) {
            try {
                SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                    public void run() throws SourceException {
                        element.setName(newName);
                    }
                });
                ok = true;
            }
            catch (SourceException e) {
                x = e;
            }
        } else
            return;
        isOK = ok;
        if (!ok) {
            nameTextField.setText(oldName);
        }
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }
   
    private void setSourceSpec() {
        String innerRef = "";
        if (sourceComboBox.getItemCount() != 0) {
            innerRef = (String)sourceComboBox.getSelectedItem();
        }
        
        String fileName = (String)sourceFileComboBox.getSelectedItem();
        
        String pound = (fileName.equals(currentFileText) || innerRef.equals("")) ? "" : "#";

        // for now, only allow same file, inner references to be relative
        String swpathBased = (fileName.equals(currentFileText) && !innerRef.equals("")) ? "" : "/";
        
        if (fileName.equals(currentFileText)) fileName = "";
        final String newSourceSpec = swpathBased + fileName + pound + innerRef;
        
        boolean ok = false;
        Exception x = null;

        try {
            SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                public void run() throws SourceException {
                    UnitID unit = UnitID.get(newSourceSpec);
                    if (unit == null) {
                        UnitID.addInstance(newSourceSpec);
                        unit = UnitID.get(newSourceSpec);
                    }
                    if (DEBUG) {
                        Util.log("sourceunitid is "+unit);
                    }
                    element.setSourceUnitID(unit);
                }
            });
            ok = true;
        }
        catch (SourceException e) {
            Util.log("MorphismCustomizer.setSourceSpec caught exception: "+e.getMessage());
            x = e;
        }
        isOK = ok;
        
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }
    
    private void setTargetSpec() {
        String innerRef = "";
        if (targetComboBox.getItemCount() != 0) {
            innerRef = (String)targetComboBox.getSelectedItem();
        }
        
        String fileName = (String)targetFileComboBox.getSelectedItem();
        
        String pound = (fileName.equals(currentFileText) || innerRef.equals("")) ? "" : "#";

        // for now, only allow same file, inner references to be relative
        String swpathBased = (fileName.equals(currentFileText) && !innerRef.equals("")) ? "" : "/";
        
        if (fileName.equals(currentFileText)) fileName = "";
        final String newTargetSpec = swpathBased + fileName + pound + innerRef;
        
//        final String newTargetSpec = (String)targetFileComboBox.getSelectedItem() + innerRef;
        
        boolean ok = false;
        Exception x = null;

        try {
            SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                public void run() throws SourceException {
                    UnitID unit = UnitID.get(newTargetSpec);
                    if (unit == null) {
                        UnitID.addInstance(newTargetSpec);
                        unit = UnitID.get(newTargetSpec);
                    }
                    if (DEBUG) {
                        Util.log("targetunitid is "+unit);
                    }
                    element.setTargetUnitID(unit);
                }
            });
            ok = true;
        }
        catch (SourceException e) {
            Util.log("MorphismCustomizer.setTargetSpec caught exception: "+e.getMessage());
            x = e;
        }
        isOK = ok;
        
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }
    
    public boolean isOK() {
        nameTextFieldFocusLost(null);
        setSourceSpec();
        setTargetSpec();
        return isOK;
    }    
    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel nameLabel;
    private javax.swing.JTextField nameTextField;
    private javax.swing.JComboBox sourceComboBox;
    private javax.swing.JComboBox sourceFileComboBox;
    private javax.swing.JLabel sourceLabel;
    private javax.swing.JComboBox targetComboBox;
    private javax.swing.JComboBox targetFileComboBox;
    private javax.swing.JLabel targetLabel;
    // End of variables declaration//GEN-END:variables
    
}
