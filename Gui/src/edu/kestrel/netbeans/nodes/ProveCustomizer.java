/*
 * ProveCustomizer.java
 *
 * Created on February 19, 2003, 3:09 PM
 */

package edu.kestrel.netbeans.nodes;

import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.ClaimElement;
import edu.kestrel.netbeans.model.SpecElement;
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
public class ProveCustomizer extends javax.swing.JPanel {
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(ProveCustomizer.class);
    
    /*Prove*/SpecElement element;
    
    boolean isOK = true;
        
    /** Creates new customizer ProveCustomizer */
    public ProveCustomizer(/*Prove*/SpecElement newProveElem, SpecElement specElem) {
        initComponents();

        this.element = newProveElem;
        
        if (this.element != null) {
	    nameTextField.setText(element.getName());
            ClaimElement[] allClaims = specElem.getClaims();
            //String[] allClaimNames = new String[allClaims.length];
            for (int i=0; i<allClaims.length; i++) {
                usingComboBox.addItem(allClaims[i].getName());
                //allClaimNames[i] = allClaims[i].getName();
            }
            //usingList.setListData(allClaimNames);
	}
        
        //borders
        setBorder (new CompoundBorder(
                       new TitledBorder(bundle.getString("CTL_ProveFrame")),
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
        usingLabel = new javax.swing.JLabel();
        optionsLabel = new javax.swing.JLabel();
        jPanel2 = new javax.swing.JPanel();
        nameTextField = new javax.swing.JTextField();
        usingComboBox = new javax.swing.JComboBox();
        optionsComboBox = new javax.swing.JComboBox();

        setLayout(new java.awt.BorderLayout());

        setPreferredSize(new java.awt.Dimension(300, 120));
        jPanel1.setLayout(new java.awt.GridLayout(3, 1, 10, 10));

        jPanel1.setPreferredSize(new java.awt.Dimension(75, 120));
        nameLabel.setText("Name");
        jPanel1.add(nameLabel);

        usingLabel.setText("Prove Using");
        jPanel1.add(usingLabel);

        optionsLabel.setText("Options");
        jPanel1.add(optionsLabel);

        add(jPanel1, java.awt.BorderLayout.WEST);

        jPanel2.setLayout(new java.awt.GridLayout(3, 1, 10, 10));

        jPanel2.setPreferredSize(new java.awt.Dimension(200, 120));
        nameTextField.setText("newProof");
        jPanel2.add(nameTextField);

        jPanel2.add(usingComboBox);

        jPanel2.add(optionsComboBox);

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

    public boolean isOK() {
        nameTextFieldFocusLost(null);
        return isOK;
    }    
        
    public String getSelectedUsingClaim() {
        return (String)usingComboBox.getSelectedItem();
    }
    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JComboBox optionsComboBox;
    private javax.swing.JComboBox usingComboBox;
    private javax.swing.JLabel nameLabel;
    private javax.swing.JLabel optionsLabel;
    private javax.swing.JPanel jPanel2;
    private javax.swing.JLabel usingLabel;
    private javax.swing.JPanel jPanel1;
    private javax.swing.JTextField nameTextField;
    // End of variables declaration//GEN-END:variables
    
}
