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
        String[] paths = swpath.split(";");
        FileObject fo = null;
                
        Repository rep = Repository.getDefault();       

        for (int i=0; i<paths.length; i++) {
            String onePath = paths[i];
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
            FileSystem fs = rep.findFileSystem(onePath);
            if (fs != null) {
                FileObject rootFolder = fs.getRoot();
                if (fs != null) {
                    for (Enumeration e = rootFolder.getData(true); e.hasMoreElements(); ) {
                        FileObject data = (FileObject)e.nextElement();
                        try {
                            DataObject obj = DataObject.find(data);
                            if (obj instanceof MetaSlangDataObject) {
                                MetaSlangDataObject msDataObj = (MetaSlangDataObject)obj;
                                if (msDataObj.getSource().equals(this.srcElement)) {
                                    this.packageName = data.getPackageName('/');
                                    sourceFileComboBox.insertItemAt("", 0);
                                    sourceFileComboBox.setSelectedIndex(0);
                                    targetFileComboBox.insertItemAt("", 0);
                                    targetFileComboBox.setSelectedIndex(0);
                                    dataObjects.put(this.packageName, msDataObj);
                                } else {
                                    sourceFileComboBox.addItem(data.getPackageName('/'));
                                    targetFileComboBox.addItem(data.getPackageName('/'));
                                    dataObjects.put(data.getPackageName('/'), msDataObj);
                                }
                            }
                        } catch (DataObjectNotFoundException ex) {}
                    }
                    initSpecs();
                }
            }
        }
    }
    
    private void initSpecs() {
        String selected = (String)sourceFileComboBox.getSelectedItem();
        if (selected.equals("")) selected = this.packageName;
        MetaSlangDataObject msdo = (MetaSlangDataObject)dataObjects.get(selected);
        if (msdo != null) {
            final SourceElement source = msdo.getSource();

            Task parsingTask = source.prepare();
            if (parsingTask.isFinished()) {
                addSpecsToComboBox(source, sourceComboBox);
                addSpecsToComboBox(source, targetComboBox);
            } else {
                parsingTask.addTaskListener(new org.openide.util.TaskListener() {
                    public void taskFinished(Task t) {
                        t.removeTaskListener(this);
                        addSpecsToComboBox(source, sourceComboBox);
                        addSpecsToComboBox(source, targetComboBox);
                    }
                });
            }        
        }
    }
    
    private void setSpecs(String fileName, final JComboBox whichBox) {
        MetaSlangDataObject msdo;
        if (fileName.equals("")) { //then add a relative inner spec unitid
            msdo = (MetaSlangDataObject)dataObjects.get(this.packageName);
        } else {
            msdo = (MetaSlangDataObject)dataObjects.get(fileName);
        }
        if (msdo != null) {
            final SourceElement source = msdo.getSource();

            Task parsingTask = source.prepare();
            if (parsingTask.isFinished()) {
                addSpecsToComboBox(source, whichBox);
            } else {
                parsingTask.addTaskListener(new org.openide.util.TaskListener() {
                    public void taskFinished(Task t) {
                        t.removeTaskListener(this);
                        addSpecsToComboBox(source, whichBox);
                    }
                });
            }
        }
    }
    
    private void addSpecsToComboBox(SourceElement source, JComboBox whichBox) {
        whichBox.removeAllItems();
        SpecElement[] specs = source.getSpecs();
        for (int j=0; j<specs.length; j++) {
            whichBox.addItem(specs[j].getName());
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
        sourceComboBox = new javax.swing.JComboBox();
        targetComboBox = new javax.swing.JComboBox();
        sourceFileComboBox = new javax.swing.JComboBox();
        targetFileComboBox = new javax.swing.JComboBox();
        jLabel1 = new javax.swing.JLabel();
        jLabel2 = new javax.swing.JLabel();

        setLayout(new java.awt.GridBagLayout());

        nameLabel.setText("Name:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(nameLabel, gridBagConstraints);

        sourceLabel.setText("From spec:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(sourceLabel, gridBagConstraints);

        targetLabel.setText("To spec:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 20;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.insets = new java.awt.Insets(2, 0, 2, 0);
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(targetLabel, gridBagConstraints);

        nameTextField.setText("newMorphism");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridwidth = 3;
        gridBagConstraints.ipadx = 121;
        gridBagConstraints.ipady = 8;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(nameTextField, gridBagConstraints);

        sourceComboBox.setEditable(true);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(sourceComboBox, gridBagConstraints);

        targetComboBox.setEditable(true);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(targetComboBox, gridBagConstraints);

        sourceFileComboBox.setEditable(true);
        sourceFileComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                sourceFileComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 3;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 75;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(sourceFileComboBox, gridBagConstraints);

        targetFileComboBox.setEditable(true);
        targetFileComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                targetFileComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 3;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 75;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        gridBagConstraints.weightx = 1.0;
        add(targetFileComboBox, gridBagConstraints);

        jLabel1.setText("in");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 2;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.ipadx = 4;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(jLabel1, gridBagConstraints);

        jLabel2.setText("in");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 2;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.ipadx = 4;
        gridBagConstraints.ipady = 2;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.WEST;
        add(jLabel2, gridBagConstraints);

    }//GEN-END:initComponents

    private void sourceFileComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_sourceFileComboBoxActionPerformed
        setSpecs((String)sourceFileComboBox.getSelectedItem(), sourceComboBox);
    }//GEN-LAST:event_sourceFileComboBoxActionPerformed

    private void targetFileComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_targetFileComboBoxActionPerformed
        setSpecs((String)targetFileComboBox.getSelectedItem(), targetComboBox);
    }//GEN-LAST:event_targetFileComboBoxActionPerformed

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
        
        String pound = (fileName.equals("") || innerRef.equals("")) ? "" : "#";

        // for now, only allow same file, inner references to be relative
        String swpathBased = (fileName.equals("") && !innerRef.equals("")) ? "" : "/";
        
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
                    LispProcessManager.writeToOutput("sourceunitid is "+unit);
                    element.setSourceUnitID(unit);
                }
            });
            ok = true;
        }
        catch (SourceException e) {
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
        
        final String newTargetSpec = (String)targetFileComboBox.getSelectedItem() + innerRef;
        
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
                    LispProcessManager.writeToOutput("targetunitid is "+unit);
                    element.setTargetUnitID(unit);
                }
            });
            ok = true;
        }
        catch (SourceException e) {
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
    private javax.swing.JComboBox sourceFileComboBox;
    private javax.swing.JLabel sourceLabel;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JComboBox sourceComboBox;
    private javax.swing.JComboBox targetComboBox;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel nameLabel;
    private javax.swing.JComboBox targetFileComboBox;
    private javax.swing.JLabel targetLabel;
    private javax.swing.JTextField nameTextField;
    // End of variables declaration//GEN-END:variables
    
}
