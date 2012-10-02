/*
 * OpCustomizer.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:09  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.nodes;

import java.beans.Customizer;
import java.beans.PropertyEditor;
import java.util.ResourceBundle;

import javax.swing.*;
import javax.swing.border.*;

import org.openide.src.SourceException;
import org.openide.explorer.propertysheet.*;
import org.openide.*;
import org.openide.util.Utilities;
import org.openide.util.NbBundle;
import org.openide.util.HelpCtx;

import edu.kestrel.netbeans.Util;
import edu.kestrel.netbeans.editor.MetaSlangSyntax;
import edu.kestrel.netbeans.model.OpElement;
import edu.kestrel.netbeans.nodes.SourceEditSupport.ExceptionalRunnable;

/** Customizer for OpElement
 *
 */
public class OpCustomizer extends JPanel {
    /** Source of the localized human presentable strings. */
    static ResourceBundle bundle = NbBundle.getBundle(OpCustomizer.class);

    /** The edited op */
    OpElement element;

    /** Predefined sorts in the sort combo */
    private static final String[] COMMON_SORTS = {
        "String", // NOI18N
        "Boolean", // NOI18N
        "Char", // NOI18N
        "Int", // NOI18N
    };
    
    boolean isOK = true;

    /** Create new OpCustomizer component
    * @param element The op to be customized
    */
    public OpCustomizer(OpElement element) {
        this.element = element;

        initComponents ();
        
        //borders
        nameSortPanel.setBorder (new CompoundBorder(
                                     new TitledBorder(bundle.getString("CTL_OpFrame")),
                                     new EmptyBorder(new java.awt.Insets(5, 5, 5, 5)))
                                );
        // name
        nameTextField.setText(element.getName());

        // sort
        sortCombo.setSelectedItem(element.getSort());

        HelpCtx.setHelpIDString (this, "metaslang.op.customizer"); // NOI18N
        //mnemonics
        jLabel1.setDisplayedMnemonic(bundle.getString("CTL_Name_Mnemonic").charAt(0));
        jLabel2.setDisplayedMnemonic(bundle.getString("CTL_Sort_Mnemonic").charAt(0));
        initAccessibility();
    }

    public void addNotify() {
        super.addNotify();

        // select the name
        int l = nameTextField.getText().length();
        nameTextField.setCaretPosition(0);
        nameTextField.moveCaretPosition(l);
        nameTextField.requestFocus();
        SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                nameTextField.requestFocus();
            }
        });
    }
    
    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the FormEditor.
     */
    private void initComponents() {//GEN-BEGIN:initComponents
        nameSortPanel = new javax.swing.JPanel();
        jLabel1 = new javax.swing.JLabel();
        nameTextField = new javax.swing.JTextField(30);
        jLabel2 = new javax.swing.JLabel();
        sortCombo = new javax.swing.JComboBox(COMMON_SORTS);
        jPanel1 = new javax.swing.JPanel();
        
        setLayout(new java.awt.GridBagLayout());
        java.awt.GridBagConstraints gridBagConstraints1;
        
        setBorder(new javax.swing.border.EmptyBorder(new java.awt.Insets(6, 6, 6, 6)));
        nameSortPanel.setLayout(new java.awt.GridBagLayout());
        java.awt.GridBagConstraints gridBagConstraints2;
        
        jLabel1.setText(bundle.getString("CTL_Name"));
        jLabel1.setLabelFor(nameTextField);
        gridBagConstraints2 = new java.awt.GridBagConstraints();
        gridBagConstraints2.insets = new java.awt.Insets(10, 0, 0, 8);
        gridBagConstraints2.anchor = java.awt.GridBagConstraints.EAST;
        nameSortPanel.add(jLabel1, gridBagConstraints2);
        
        nameTextField.addFocusListener(new java.awt.event.FocusAdapter() {
            public void focusLost(java.awt.event.FocusEvent evt) {
                nameTextFieldFocusLost(evt);
            }
        });
        
        gridBagConstraints2 = new java.awt.GridBagConstraints();
        gridBagConstraints2.gridwidth = java.awt.GridBagConstraints.REMAINDER;
        gridBagConstraints2.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints2.insets = new java.awt.Insets(10, 0, 0, 0);
        gridBagConstraints2.weightx = 1.0;
        nameSortPanel.add(nameTextField, gridBagConstraints2);
        
        jLabel2.setText(bundle.getString("CTL_Sort"));
        jLabel2.setLabelFor(sortCombo);
        gridBagConstraints2 = new java.awt.GridBagConstraints();
        gridBagConstraints2.insets = new java.awt.Insets(8, 0, 0, 8);
        gridBagConstraints2.anchor = java.awt.GridBagConstraints.EAST;
        nameSortPanel.add(jLabel2, gridBagConstraints2);
        
        sortCombo.setEditable(true);
        sortCombo.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jComboBox1ActionPerformed(evt);
            }
        });
        
        gridBagConstraints2 = new java.awt.GridBagConstraints();
        gridBagConstraints2.gridwidth = java.awt.GridBagConstraints.REMAINDER;
        gridBagConstraints2.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints2.insets = new java.awt.Insets(8, 0, 0, 0);
        gridBagConstraints2.weightx = 1.0;
        nameSortPanel.add(sortCombo, gridBagConstraints2);
        
        gridBagConstraints2 = new java.awt.GridBagConstraints();
        gridBagConstraints2.weighty = 1.0;
        nameSortPanel.add(jPanel1, gridBagConstraints2);
        
        gridBagConstraints1 = new java.awt.GridBagConstraints();
        gridBagConstraints1.gridx = 0;
        gridBagConstraints1.gridy = 0;
        gridBagConstraints1.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints1.weightx = 1.0;
        add(nameSortPanel, gridBagConstraints1);
        
    }//GEN-END:initComponents

    private void jComboBox1ActionPerformed (java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jComboBox1ActionPerformed
        Object selItem = sortCombo.getSelectedItem();
        String oldValue = element.getSort();
        boolean ok = false;
        
        if (selItem != null) {
            try {
                final String newValue = selItem.toString();
                if (oldValue == null || !oldValue.equals(newValue)) {
                    try {
                        SourceEditSupport.runAsUser(element, new ExceptionalRunnable() {
                            public void run() throws SourceException {
                                element.setSort(newValue);
                            }
                        });
                        ok = true;
                    }
                    catch (SourceException e) {
                        ErrorManager.getDefault().notify(e);
                    }
                } else
                    return;
            }
            catch (IllegalArgumentException e) {
                ErrorManager.getDefault().annotate(
                    e, ErrorManager.USER, null, 
                    bundle.getString("MSG_Not_Valid_Sort"),
                    null, null);
                ErrorManager.getDefault().notify(e);
            }
        }
        isOK = ok;
        if (!ok)
            sortCombo.setSelectedItem(oldValue);
    }//GEN-LAST:event_jComboBox1ActionPerformed

    private void nameTextFieldFocusLost (java.awt.event.FocusEvent evt) {//GEN-FIRST:event_nameTextFieldFocusLost
        if (evt != null && evt.isTemporary())
            return;

        final String newName = nameTextField.getText();
        String oldName = element.getName();
        boolean ok = false;
        Exception x = null;

        if (MetaSlangSyntax.isMetaSlangIdentifier(newName)) {
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
        } else {
            x = new IllegalArgumentException("Invalid name"); // NOI18N
            ErrorManager.getDefault().annotate(
                x, ErrorManager.USER, null, 
                bundle.getString("MSG_Not_Valid_Identifier"),
                null, null);
        }
        isOK = ok;
        if (!ok) {
            nameTextField.setText(oldName);
        }
        if (x != null) {
            ErrorManager.getDefault().notify(x);
        }
    }//GEN-LAST:event_nameTextFieldFocusLost


    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JPanel nameSortPanel;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JTextField nameTextField;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JComboBox sortCombo;
    private javax.swing.JPanel jPanel1;
    // End of variables declaration//GEN-END:variables

    private void initAccessibility() {
        nameTextField.getAccessibleContext().setAccessibleName(bundle.getString("ACS_OpNameTextField"));
        nameTextField.getAccessibleContext().setAccessibleDescription(bundle.getString("ACS_OpNameTextField"));
        this.getAccessibleContext().setAccessibleDescription("ACSD_OpCustomizerDialog");
    }
    
    public boolean isOK() {
        nameTextFieldFocusLost(null);
        jComboBox1ActionPerformed(null);
        return isOK;
    }
    
}
