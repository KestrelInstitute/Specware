package edu.kestrel.netbeans.nodes;

import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.MorphismElement;
import edu.kestrel.netbeans.nodes.MemberCustomizer;
import edu.kestrel.netbeans.nodes.SourceEditSupport.ExceptionalRunnable;

import java.util.ResourceBundle;

import javax.swing.*;
import javax.swing.border.*;

import org.openide.ErrorManager;
import org.openide.util.NbBundle;
import org.openide.src.SourceException;

/**
 *
 * @author  weilyn
 */
public class MorphismCustomizer extends javax.swing.JPanel {
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(MorphismCustomizer.class);
        
    MorphismElement element;
    
    boolean isOK = true;
        
    /** Creates new customizer MorphismCustomizer */
    public MorphismCustomizer(MorphismElement newMorphismElem) {
        initComponents();

        this.element = newMorphismElem;
        
        if (this.element != null) {
	    nameTextField.setText(element.getName());
/*            if (allClaims.length > 1) {
                usingComboBox.addItem(USE_ALL_CLAIMS);
            } else {
                usingComboBox.addItem(USE_NO_CLAIMS);
            }
            for (int i=0; i<allClaims.length; i++) {
                if (!allClaims[i].getName().equals(claimElement.getName())) {
                    usingComboBox.addItem(allClaims[i].getName());
                }
                //allClaimNames[i] = allClaims[i].getName();
            }
            //usingList.setListData(allClaimNames);
            useResolutionComboBox.addItem(USE_RESOLUTION_DEFAULT);
            useResolutionComboBox.addItem(USE_RESOLUTION_YES);
            useResolutionComboBox.addItem(USE_RESOLUTION_NO);
*/	}
        
        //borders
        setBorder (new CompoundBorder(
                       new TitledBorder(bundle.getString("CTL_MorphismFrame")),
                       new EmptyBorder(new java.awt.Insets(5, 5, 5, 5)))
                       );
    }
    
    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the FormEditor.
     */
    private void initComponents() {//GEN-BEGIN:initComponents
        jPanel1 = new javax.swing.JPanel();
        nameLabel = new javax.swing.JLabel();
        sourceLabel = new javax.swing.JLabel();
        targetLabel = new javax.swing.JLabel();
        jPanel2 = new javax.swing.JPanel();
        nameTextField = new javax.swing.JTextField();
        sourceComboBox = new javax.swing.JComboBox();
        targetComboBox = new javax.swing.JComboBox();

        setLayout(new java.awt.BorderLayout());

        setPreferredSize(new java.awt.Dimension(300, 200));
        jPanel1.setLayout(new java.awt.GridLayout(3, 1, 10, 10));

        jPanel1.setPreferredSize(new java.awt.Dimension(125, 200));
        nameLabel.setText("Name");
        jPanel1.add(nameLabel);

        sourceLabel.setText("Source");
        jPanel1.add(sourceLabel);

        targetLabel.setText("Target");
        jPanel1.add(targetLabel);

        add(jPanel1, java.awt.BorderLayout.WEST);

        jPanel2.setLayout(new java.awt.GridLayout(3, 1, 10, 10));

        jPanel2.setPreferredSize(new java.awt.Dimension(150, 200));
        nameTextField.setText("newMorphism");
        jPanel2.add(nameTextField);

        sourceComboBox.setEditable(true);
        jPanel2.add(sourceComboBox);

        targetComboBox.setEditable(true);
        jPanel2.add(targetComboBox);

        add(jPanel2, java.awt.BorderLayout.EAST);

    }//GEN-END:initComponents

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

    private void sourceComboBoxFocusLost (java.awt.event.FocusEvent evt) {
        if (evt != null && evt.isTemporary())
            return;

        final String newSourcePath = (String)sourceComboBox.getSelectedItem();
        String oldSourcePath = element.getSourceURI().getPath();
        boolean ok = false;
        Exception x = null;

        if (oldSourcePath == null || !oldSourcePath.equals(newSourcePath)) {
            try {
                SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                    public void run() throws SourceException {
                        element.getSourceURI().setPath(newSourcePath);
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
            sourceComboBox.setSelectedItem(oldSourcePath);
        }
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }
    
    private void targetComboBoxFocusLost (java.awt.event.FocusEvent evt) {
        if (evt != null && evt.isTemporary())
            return;

        final String newTargetPath = (String)targetComboBox.getSelectedItem();
        String oldTargetPath = element.getDestinationURI().getPath();
        boolean ok = false;
        Exception x = null;

        if (oldTargetPath == null || !oldTargetPath.equals(newTargetPath)) {
            try {
                SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                    public void run() throws SourceException {
                        element.getDestinationURI().setPath(newTargetPath);
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
            targetComboBox.setSelectedItem(oldTargetPath);
        }
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }
    
    public boolean isOK() {
        nameTextFieldFocusLost(null);
        sourceComboBoxFocusLost(null);
        targetComboBoxFocusLost(null);
        return isOK;
    }    
        
    public String getSelectedSource() {
        return (String)sourceComboBox.getSelectedItem();
    }
    
    public String getSelectedTarget() {
        return (String)targetComboBox.getSelectedItem();
    }
    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel sourceLabel;
    private javax.swing.JComboBox sourceComboBox;
    private javax.swing.JComboBox targetComboBox;
    private javax.swing.JLabel nameLabel;
    private javax.swing.JPanel jPanel2;
    private javax.swing.JLabel targetLabel;
    private javax.swing.JPanel jPanel1;
    private javax.swing.JTextField nameTextField;
    // End of variables declaration//GEN-END:variables
    
}
