/*
 * StepEditor.java
 *
 * Created on January 28, 2003, 8:00 PM
 */

package edu.kestrel.especs.graphs.editor;

import edu.kestrel.graphs.editor.*;
import edu.kestrel.especs.graphs.*;
import edu.kestrel.graphs.*;

import javax.swing.*;
import java.awt.event.*;
import java.util.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class StepEditor extends JPanel implements XElementEditor {
    
    protected StepEdge stepEdge;
    protected static String unnamed = "unnamed";
    
    protected JPanel condPanel;
    
    protected JTextField nameTextField = null;
    
    protected int condCnt = 0;
    
    protected Map conditionMap;
    
    protected Map updateMap;
    
    /** Creates a new instance of StepEditor */
    public StepEditor(StepEdge stepEdge) {
        this.stepEdge = stepEdge;
        initGui();
    }
    
    private String getNameString() {
        String n = stepEdge.getStepName();
        if (n == null) return unnamed;
        n = n.trim();
        if (n.length() == 0) return unnamed;
        return n;
    }
    
    protected void initGui() {
        setLayout(new GridBagLayout());
        // command button
        JToolBar cmdp = new JToolBar(JToolBar.VERTICAL);
        cmdp.setFloatable(false);
        cmdp.setBorder(new javax.swing.border.EmptyBorder(0,0,0,0));
        JButton newConditionBtn = new JButton(EConstants.and24Icon);
        newConditionBtn.setToolTipText("add new conjuntive term to condition");
        JButton newUpdateBtn = new JButton(EConstants.assign24Icon);
        newUpdateBtn.setToolTipText("add new update");
        newConditionBtn.setMargin(new Insets(0,0,0,0));
        newUpdateBtn.setMargin(new Insets(0,0,0,0));
        cmdp.add(newConditionBtn);
        cmdp.add(newUpdateBtn);
        
        newConditionBtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                StepEdge.Term term = new StepEdge.Term("true");
                JTextArea ta = addConditionTerm(term);
                conditionMap.put(term,ta);
            }
        });
        
        GridBagConstraints c = new GridBagConstraints();
        c.ipadx = 5; c.ipady = 5;
        c.anchor = c.NORTHWEST;
        c.fill = c.NONE;
        c.weightx = 0; c.weighty = 0;
        //add(cmdp,BorderLayout.EAST);
        c.gridx = 0; c.gridy = 0;
        add(new JLabel("step name:"),c);
        c.gridx = 1; c.gridy = 0;
        nameTextField = new JTextField(25);
        nameTextField.setText(getNameString());
        c.fill = c.HORIZONTAL;
        c.gridwidth = 1;
        add(nameTextField,c);
        
        condPanel = new JPanel();
        condPanel.setLayout(new GridBagLayout());
        c.gridx = 0; c.gridy = 1;
        c.fill = c.NONE;
        c.fill = c.BOTH;
        c.gridwidth = 2;
        c.insets = new Insets(10,0,0,0);
        add(condPanel,c);
        
        c.gridwidth = 1;
        c.gridx = 20; c.gridy = 0;
        c.insets = new Insets(0,20,0,0);
        c.fill = c.NONE;
        c.gridheight = GridBagConstraints.REMAINDER;
        add(cmdp,c);
        
        initConditionFromStepEdge();
        
    }
    
    protected JTextArea addConditionTerm(final StepEdge.Term term) {
        final int index = condCnt++;
        GridBagConstraints c = new GridBagConstraints();
        JLabel wedgeIcon = new JLabel((index==0?"   ":"and"));
        JTextArea ta = new JTextArea(1,25);
        JButton deleteBtn = new JButton(IconImageData2.xdelete24Icon);
        deleteBtn.setMargin(new Insets(0,0,0,0));
        deleteBtn.setToolTipText("delete this term");
        //deleteBtn.setBorder(new javax.swing.border.EmptyBorder(0,0,0,0));
        deleteBtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                int answ = JOptionPane.showConfirmDialog(StepEditor.this,"Delete this term?","Delete?",JOptionPane.OK_CANCEL_OPTION);
                if (answ == JOptionPane.OK_OPTION) {
                    conditionMap.remove(term);
                    refreshConditionTerms();
                }
            }
        });
        ta.setBorder(new javax.swing.border.EtchedBorder());
        ta.setText(term.term);
        c.weightx = 0;
        c.weighty = 0;
        c.fill = c.NONE;
        c.anchor = c.EAST;
        c.ipadx = 5; c.ipady = 5;
        c.gridx = 0; c.gridy = index;
        condPanel.add(wedgeIcon,c);
        c.fill = c.BOTH;
        c.anchor = c.WEST;
        c.gridx = 1;
        condPanel.add(ta,c);
        c.gridx = 2;
        c.ipadx = 5; c.ipady = 0;
        condPanel.add(deleteBtn,c);
        return ta;
    }
    
    /** initializes the condition from the step edge.
     */
    protected void initConditionFromStepEdge() {
        condPanel.removeAll();
        condCnt = 0;
        conditionMap = new Hashtable();
        java.util.List cterms = stepEdge.getConditionTerms();
        Dbg.pr("cterms="+cterms);
        if (cterms == null) return;
        Iterator iter = cterms.iterator();
        while (iter.hasNext()) {
            StepEdge.Term t = (StepEdge.Term)iter.next();
            JTextArea ta = addConditionTerm(t);
            conditionMap.put(t,ta);
        }
    }
    
    /** refreshes the condition terms using the internally stored conditionTextAreas.
     */
    protected void refreshConditionTerms() {
        if (conditionMap == null) return;
        condPanel.removeAll();
        condCnt = 0;
        Map newConditionMap = new Hashtable();
        Iterator iter = conditionMap.keySet().iterator();
        while(iter.hasNext()) {
            StepEdge.Term term = (StepEdge.Term)iter.next();
            String t = ((JTextArea)(conditionMap.get(term))).getText();
            JTextArea ta = addConditionTerm(term);
            ta.setText(t);
            newConditionMap.put(term,ta);
        }
        conditionMap = newConditionMap;
    }
    
    protected void applyConditionTerms() {
        if (conditionMap == null) {
            stepEdge.setConditionTerms(null);
        }
        ArrayList res = new ArrayList();
        Iterator iter = conditionMap.keySet().iterator();
        while(iter.hasNext()) {
            StepEdge.Term t = (StepEdge.Term)iter.next();
            String term = ((JTextArea)(conditionMap.get(t))).getText().trim();
            if (term.length() > 0 && (!term.equals("true"))) {
                res.add(new StepEdge.Term(term));
            }
        }
        stepEdge.setConditionTerms(res);
    }
    
    protected void applyName() {
        String s = nameTextField.getText().trim();
        if (s.length() > 0 && (!s.equals(unnamed))) {
            stepEdge.setStepName(s);
        } else {
            stepEdge.setStepName("");
        }
    }
    
    /** applies the changes made in the editor.  */
    public void apply() {
        applyName();
        applyConditionTerms();
    }
    
    /** actions that need to be performed in the context of a cancel operation.
     *
     */
    public void cancel() {
    }
    
    /** returns the panel that is actually embedded into the frame; implementors might embed the actual editor instance
     * into a JScrollPane, for instance, using this method.
     *
     */
    public javax.swing.JComponent getPanel() {
        return /*new JScrollPane*/(this);
    }
    
    public String getTitleText() {
        return "step "+getNameString();
    }
    
    /** returns true, if the frame containing the editor shall constantly update its size according to
     * changed size of this editor.
     *
     */
    public boolean autoUpdateFrameSize() {
        return true;
    }
    
}
