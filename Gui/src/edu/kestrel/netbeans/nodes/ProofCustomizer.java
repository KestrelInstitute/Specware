/*
 * ProveCustomizer.java
 *
 * Created on February 19, 2003, 3:09 PM
 */

package edu.kestrel.netbeans.nodes;

import edu.kestrel.netbeans.MetaSlangDataObject;
import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.ClaimElement;
import edu.kestrel.netbeans.model.ProofElement;
import edu.kestrel.netbeans.model.SourceElement;
import edu.kestrel.netbeans.model.SpecElement;
import edu.kestrel.netbeans.nodes.MemberCustomizer;
import edu.kestrel.netbeans.nodes.SourceEditSupport.ExceptionalRunnable;

import java.util.ResourceBundle;

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
public class ProofCustomizer extends javax.swing.JPanel {
    
    private static final boolean DEBUG = true;
    
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(ProofCustomizer.class);
    
    public static final String USE_ALL_CLAIMS = "--- All Claims ---";
    public static final String USE_NO_CLAIMS = "--- No Other Claims ---";
    public static final String USE_RESOLUTION_YES = "Yes";
    public static final String USE_RESOLUTION_NO = "No";
    public static final String USE_RESOLUTION_DEFAULT = "Use default";
    
    private static final String currentFileText = "<current file>";   
    
    private ProofElement element;
    private SourceElement srcElement;
    private String packageName = null;
    
    private HashMap dataObjects = new HashMap();    
    
    boolean isOK = true;
        
    /** Creates new customizer ProveCustomizer */
    public ProofCustomizer(ProofElement newProofElem, SourceElement srcElement) {
        initComponents();

        this.element = newProofElem;
        this.srcElement = srcElement;
        
        if (this.element != null) {
	    nameTextField.setText(element.getName());
            
            initComboBoxes();
            
            /*ClaimElement[] allClaims = parentSpecElem.getClaims();
            //String[] allClaimNames = new String[allClaims.length];
            if (allClaims.length > 1) {
                usingComboBox.addItem(USE_ALL_CLAIMS);
            } else {
                usingComboBox.addItem(USE_NO_CLAIMS);
            }
            for (int i=0; i<allClaims.length; i++) {
                if (!allClaims[i].getName().equals(claimElement.getName())) {
                    usingComboBox.addItem(allClaims[i].getName());
                }
                //allClaimNames[i] = allClaims[i].getName();
            }*/
            
            //usingList.setListData(allClaimNames);
            useResolutionComboBox.addItem(USE_RESOLUTION_DEFAULT);
            useResolutionComboBox.addItem(USE_RESOLUTION_YES);
            useResolutionComboBox.addItem(USE_RESOLUTION_NO);
	}
        
        //borders
        setBorder (new CompoundBorder(
                       new TitledBorder(bundle.getString("CTL_ProofFrame")),
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
                       
                        for (Enumeration e = rootFolder.getData(true); e.hasMoreElements(); ) {
                            FileObject data = (FileObject)e.nextElement();
                            try {
                                DataObject obj = DataObject.find(data);
                                if (obj instanceof MetaSlangDataObject) {
                                    MetaSlangDataObject msDataObj = (MetaSlangDataObject)obj;
                                    SourceElement source = msDataObj.getSource();
                                    prepareSource(source);
                                    
                                    // now, display only those files with claims somewhere in them
                                    if (hasClaims(source)) {
                                        if (source.equals(this.srcElement)) {
                                            this.packageName = data.getPackageName('/');
                                            sourceFileComboBox.insertItemAt(currentFileText, 0);
                                            dataObjects.put(this.packageName, msDataObj);
                                        } else {
                                            sourceFileComboBox.addItem(data.getPackageName('/'));
                                            dataObjects.put(data.getPackageName('/'), msDataObj);
                                        }
                                    }
                                }
                            } catch (DataObjectNotFoundException ex) {}
                        }
                        if (!dataObjects.isEmpty()) {
                            sourceFileComboBox.setSelectedIndex(0);
                            setSpecsAndClaims(false);
                        }
                    }
                }
            }
        }
    }
    
    private boolean hasClaims(SourceElement source) {
        SpecElement[] specs = source.getSpecs();
        for (int i=0; i<specs.length; i++) {
            if (specs[i].getClaims().length != 0) {
                return true;
            }
        }
        return false;
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
    
    private void setSpecsAndClaims(boolean setClaimsOnly) {
        MetaSlangDataObject msdo;
        String fileName = (String)sourceFileComboBox.getSelectedItem();
        if (fileName.equals(currentFileText)) { //then add a relative inner spec unitid
            msdo = (MetaSlangDataObject)dataObjects.get(this.packageName);
        } else {
            msdo = (MetaSlangDataObject)dataObjects.get(fileName);
        }
        if (msdo != null) {
            final SourceElement source = msdo.getSource();

            if (!setClaimsOnly) {
                addSpecsToComboBox(source);
            }
            addClaimsToComboBox(source);
        }
    }

    private void addSpecsToComboBox(SourceElement source) {
        specComboBox.removeAllItems();
        SpecElement[] specs = source.getSpecs();
        for (int i=0; i<specs.length; i++) {
            if (specs[i].getClaims().length != 0) {
                specComboBox.addItem(specs[i].getName());
            }
        }
        if (specs.length > 0)
            specComboBox.setSelectedIndex(0);
    }
    
    private void addClaimsToComboBox(SourceElement source) {
        claimComboBox.removeAllItems();
        usingComboBox.removeAllItems();
        SpecElement elem = source.getSpec((String)specComboBox.getSelectedItem());
        if (elem != null) {
            ClaimElement[] claims = elem.getClaims();
            for (int j=0; j<claims.length; j++) {
                claimComboBox.addItem(claims[j].getName());
            }
            if (claims.length > 0) {
                claimComboBox.setSelectedIndex(0);
            }
            if (claims.length > 1) {
                usingComboBox.addItem(USE_ALL_CLAIMS);
            } else {
                usingComboBox.addItem(USE_NO_CLAIMS);
            }
        }
/*        for (int i=0; i<claims.length; i++) {
            if (!caims[i].getName().equals(claimElement.getName())) {
                usingComboBox.addItem(claims[i].getName());
            }
        }
 **/
    }
        
    
    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the FormEditor.
     */
    private void initComponents() {//GEN-BEGIN:initComponents
        java.awt.GridBagConstraints gridBagConstraints;

        nameLabel = new javax.swing.JLabel();
        nameTextField = new javax.swing.JTextField();
        claimLabel = new javax.swing.JLabel();
        claimComboBox = new javax.swing.JComboBox();
        jLabel3 = new javax.swing.JLabel();
        sourceFileComboBox = new javax.swing.JComboBox();
        jLabel4 = new javax.swing.JLabel();
        specComboBox = new javax.swing.JComboBox();
        usingLabel = new javax.swing.JLabel();
        usingComboBox = new javax.swing.JComboBox();
        optionsLabel = new javax.swing.JLabel();
        resolutionLabel = new javax.swing.JLabel();
        useResolutionComboBox = new javax.swing.JComboBox();
        jLabel1 = new javax.swing.JLabel();
        timeLimitTextField = new javax.swing.JTextField();
        jLabel2 = new javax.swing.JLabel();

        setLayout(new java.awt.GridBagLayout());

        setMinimumSize(new java.awt.Dimension(1000, 200));
        setPreferredSize(new java.awt.Dimension(1000, 200));
        nameLabel.setText("Name");
        nameLabel.setVerticalAlignment(javax.swing.SwingConstants.TOP);
        nameLabel.setMaximumSize(new java.awt.Dimension(150, 15));
        nameLabel.setMinimumSize(new java.awt.Dimension(150, 15));
        nameLabel.setPreferredSize(new java.awt.Dimension(150, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 0;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.ipadx = 5;
        gridBagConstraints.ipady = 5;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(nameLabel, gridBagConstraints);

        nameTextField.setText("newProof");
        nameTextField.setMinimumSize(new java.awt.Dimension(150, 20));
        nameTextField.setPreferredSize(new java.awt.Dimension(150, 20));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridwidth = 2;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(nameTextField, gridBagConstraints);

        claimLabel.setText("Claim to prove");
        claimLabel.setVerticalAlignment(javax.swing.SwingConstants.TOP);
        claimLabel.setMaximumSize(new java.awt.Dimension(500, 15));
        claimLabel.setMinimumSize(new java.awt.Dimension(150, 15));
        claimLabel.setPreferredSize(new java.awt.Dimension(150, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(claimLabel, gridBagConstraints);

        claimComboBox.setMinimumSize(new java.awt.Dimension(200, 25));
        claimComboBox.setPreferredSize(new java.awt.Dimension(200, 25));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.gridwidth = 2;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(claimComboBox, gridBagConstraints);

        jLabel3.setText("in");
        jLabel3.setMinimumSize(new java.awt.Dimension(10, 15));
        jLabel3.setPreferredSize(new java.awt.Dimension(10, 15));
        jLabel3.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 3;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(jLabel3, gridBagConstraints);

        sourceFileComboBox.setMinimumSize(new java.awt.Dimension(300, 25));
        sourceFileComboBox.setPreferredSize(new java.awt.Dimension(300, 25));
        sourceFileComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                sourceFileComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 4;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.gridwidth = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(sourceFileComboBox, gridBagConstraints);

        jLabel4.setText("#");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 7;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(4, 4, 4, 4);
        add(jLabel4, gridBagConstraints);

        specComboBox.setMinimumSize(new java.awt.Dimension(150, 25));
        specComboBox.setPreferredSize(new java.awt.Dimension(150, 25));
        specComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                specComboBoxActionPerformed(evt);
            }
        });

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 8;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.gridwidth = java.awt.GridBagConstraints.REMAINDER;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        add(specComboBox, gridBagConstraints);

        usingLabel.setText("Prove Using");
        usingLabel.setVerticalAlignment(javax.swing.SwingConstants.TOP);
        usingLabel.setMaximumSize(new java.awt.Dimension(150, 15));
        usingLabel.setMinimumSize(new java.awt.Dimension(150, 15));
        usingLabel.setPreferredSize(new java.awt.Dimension(150, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.anchor = java.awt.GridBagConstraints.SOUTH;
        gridBagConstraints.weightx = 1.0;
        add(usingLabel, gridBagConstraints);

        usingComboBox.setMinimumSize(new java.awt.Dimension(225, 25));
        usingComboBox.setPreferredSize(new java.awt.Dimension(225, 25));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.gridwidth = 2;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(usingComboBox, gridBagConstraints);

        optionsLabel.setText("Options:");
        optionsLabel.setMaximumSize(new java.awt.Dimension(150, 15));
        optionsLabel.setMinimumSize(new java.awt.Dimension(150, 15));
        optionsLabel.setPreferredSize(new java.awt.Dimension(150, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.anchor = java.awt.GridBagConstraints.SOUTH;
        gridBagConstraints.weightx = 1.0;
        add(optionsLabel, gridBagConstraints);

        resolutionLabel.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
        resolutionLabel.setText("Use Resolution");
        resolutionLabel.setMaximumSize(new java.awt.Dimension(500, 15));
        resolutionLabel.setMinimumSize(new java.awt.Dimension(100, 15));
        resolutionLabel.setPreferredSize(new java.awt.Dimension(100, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 1;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(resolutionLabel, gridBagConstraints);

        useResolutionComboBox.setMinimumSize(new java.awt.Dimension(150, 25));
        useResolutionComboBox.setPreferredSize(new java.awt.Dimension(150, 25));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 2;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        gridBagConstraints.weightx = 1.0;
        add(useResolutionComboBox, gridBagConstraints);

        jLabel1.setHorizontalAlignment(javax.swing.SwingConstants.LEFT);
        jLabel1.setText("Time Limit");
        jLabel1.setMaximumSize(new java.awt.Dimension(150, 15));
        jLabel1.setMinimumSize(new java.awt.Dimension(100, 15));
        jLabel1.setPreferredSize(new java.awt.Dimension(100, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 4;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        add(jLabel1, gridBagConstraints);

        timeLimitTextField.setText("0");
        timeLimitTextField.setMaximumSize(new java.awt.Dimension(10, 20));
        timeLimitTextField.setMinimumSize(new java.awt.Dimension(50, 25));
        timeLimitTextField.setPreferredSize(new java.awt.Dimension(50, 25));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 5;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        add(timeLimitTextField, gridBagConstraints);

        jLabel2.setText("Seconds");
        jLabel2.setMaximumSize(new java.awt.Dimension(500, 15));
        jLabel2.setMinimumSize(new java.awt.Dimension(100, 15));
        jLabel2.setPreferredSize(new java.awt.Dimension(100, 15));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 6;
        gridBagConstraints.gridy = 3;
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.insets = new java.awt.Insets(5, 5, 5, 5);
        add(jLabel2, gridBagConstraints);

    }//GEN-END:initComponents

    private void specComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_specComboBoxActionPerformed
        setSpecsAndClaims(true);
    }//GEN-LAST:event_specComboBoxActionPerformed

    private void sourceFileComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_sourceFileComboBoxActionPerformed
        setSpecsAndClaims(false);
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

    public boolean isOK() {
        nameTextFieldFocusLost(null);
        
        String claimToProve = (String)claimComboBox.getSelectedItem() + " in ";
        
        String innerRef = "";
        if (sourceFileComboBox.getItemCount() != 0) {
            innerRef = (String)sourceFileComboBox.getSelectedItem();
        }
        
        String fileName = (String)sourceFileComboBox.getSelectedItem();
        
        String pound = (fileName.equals(currentFileText) || innerRef.equals("")) ? "" : "#";

        // for now, only allow same file, inner references to be relative
        String swpathBased = (fileName.equals(currentFileText) && !innerRef.equals("")) ? "" : "/";
        
        if (fileName.equals(currentFileText)) fileName = "";
        final String sourceSpec = swpathBased + fileName + pound + innerRef;        

        //TODO: String usingClaim = getSelectedUsingClaim();
        String useResolution = getSelectedUseResolution();
        String timeLimit = getTimeLimit();
        String options = "";
/*TODO        if (!usingClaim.equals(ProveCustomizer.USE_ALL_CLAIMS) &&
            !usingClaim.equals(ProveCustomizer.USE_NO_CLAIMS)) {
            usingClaim = " using " + getSelectedUsingClaim();
        }*/
        if (!(useResolution.equals(ProveCustomizer.USE_RESOLUTION_DEFAULT) &&
              timeLimit.equals("0"))) {
              options = " options \"";
              if (useResolution.equals(ProveCustomizer.USE_RESOLUTION_YES)) {
                  options += "(USE-RESOLUTION T)";
              } else if (useResolution.equals(ProveCustomizer.USE_RESOLUTION_NO)) {
                  options += "(USE-RESOLUTION NIL)";
              }
              if (!timeLimit.equals("0")) {
                  options += "(RUN-TIME-LIMIT " + timeLimit + ")";
              }
              options += "\"";
        }

        final String proofString = claimToProve + sourceSpec + options;
        
        if (DEBUG) {
            Util.log("ProofCustomizer.isOK created proofString: "+proofString);
        }
        try {
            SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                public void run() throws SourceException {
                    element.setProofString(proofString);
                }
            });   
            isOK = true;
        }
        catch (SourceException e) {
            Util.log("ProofCustomizer.isOK() caught exception: "+e.getMessage());
            isOK = false;
        }     
        return isOK;
    }    
        
    public String getSelectedUsingClaim() {
        return (String)usingComboBox.getSelectedItem();
    }
    
    public String getSelectedUseResolution() {
        return (String)useResolutionComboBox.getSelectedItem();
    }
    
    public String getTimeLimit() {
        return (String)timeLimitTextField.getText();
    }
    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JComboBox claimComboBox;
    private javax.swing.JLabel claimLabel;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    private javax.swing.JLabel nameLabel;
    private javax.swing.JTextField nameTextField;
    private javax.swing.JLabel optionsLabel;
    private javax.swing.JLabel resolutionLabel;
    private javax.swing.JComboBox sourceFileComboBox;
    private javax.swing.JComboBox specComboBox;
    private javax.swing.JTextField timeLimitTextField;
    private javax.swing.JComboBox useResolutionComboBox;
    private javax.swing.JComboBox usingComboBox;
    private javax.swing.JLabel usingLabel;
    // End of variables declaration//GEN-END:variables
    
}
