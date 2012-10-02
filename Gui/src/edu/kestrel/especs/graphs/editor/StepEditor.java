/*
 * StepEditor.java
 *
 * Created on January 28, 2003, 8:00 PM
 */

package edu.kestrel.especs.graphs.editor;

import edu.kestrel.graphs.editor.*;
import edu.kestrel.especs.graphs.*;
import edu.kestrel.especs.lang.*;
import edu.kestrel.graphs.*;

import javax.swing.text.*;
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
    protected JPanel updatePanel;
    
    protected XElementEditorFrame editorFrame;
    
    protected JTextField nameTextField = null;
    
    //protected int condCnt = 0;
    
    protected Map conditionMap;
    protected Vector conditionMapKeys;
    protected LabelSpec conditionLabelSpec;
    
    protected Map updateMap;
    protected Vector updateMapKeys;
    protected LabelSpec updateLabelSpec;
    
    /** Creates a new instance of StepEditor */
    public StepEditor(StepEdge stepEdge) {
        this.stepEdge = stepEdge;
        initGui();
    }
    
    /** inner class used to represent labels in panels for adding line of terms. The first label is
     * used only in the first line, the next label for all additional lines. For instance, in case
     * of the condition panel, the first label would be the empty string and the next label "and"
     * The type of the labels may either be <code>String</code> or <code>ImageIcon</code>
     */
    protected class LabelSpec {
        public Object firstLabel;
        public Object nextLabel;
        public LabelSpec(Object firstLabel, Object nextLabel) {
            this.firstLabel = firstLabel;
            this.nextLabel = nextLabel;
        }
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
                Term term = new Term("true");
                JTextArea ta = addTerm(condPanel,term,conditionMap,conditionMapKeys,conditionLabelSpec);
            }
        });
        
        newUpdateBtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                Term term = new Term("");
                JTextArea ta = addTerm(updatePanel,term,updateMap,updateMapKeys,updateLabelSpec);
            }
        });
        
        GridBagConstraints c = new GridBagConstraints();
        c.ipadx = 5; c.ipady = 5;
        c.anchor = c.NORTHWEST;
        c.fill = c.NONE;
        c.weightx = 0; c.weighty = 0;
        c.gridx = 0; c.gridy = 0;
        add(new JLabel("step name:"),c);
        c.gridx = 1; c.gridy = 0;
        nameTextField = new JTextField(25);
        nameTextField.setText(getNameString());
        if (stepEdge.isDerived()) {
            setReadonlyFlags(nameTextField);
        }
        c.fill = c.HORIZONTAL;
        c.gridwidth = 1;
        nameTextField.addKeyListener(new KeyListener() {
            public void keyPressed(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                    if (editorFrame != null) {
                        editorFrame.okAction();
                    }
                }
            }
            public void keyReleased(KeyEvent e) {}
            public void keyTyped(KeyEvent e) {}
        });
        add(nameTextField,c);
        
        condPanel = new JPanel();
        condPanel.setLayout(new GridBagLayout());
        c.gridx = 0; c.gridy = 1;
        c.fill = c.NONE;
        c.fill = c.BOTH;
        c.gridwidth = 2;
        c.insets = new Insets(10,0,0,0);
        add(condPanel,c);
        
        updatePanel = new JPanel();
        updatePanel.setLayout(new GridBagLayout());
        c.gridx = 0; c.gridy = 2;
        c.fill = c.NONE;
        c.fill = c.BOTH;
        c.gridwidth = 2;
        c.insets = new Insets(10,0,0,0);
        add(updatePanel,c);
        
        c.gridwidth = 1;
        c.gridx = 20; c.gridy = 0;
        c.insets = new Insets(0,20,0,0);
        c.fill = c.NONE;
        c.gridheight = GridBagConstraints.REMAINDER;
        add(cmdp,c);
        
        initConditionFromStepEdge();
        initUpdatesFromStepEdge();
        
    }
    
    protected void setReadonlyFlags(JTextComponent tc) {
        tc.setEditable(false);
        tc.setBackground(new Color(210,210,210));
    }
    
    /** adds an entry to the panel p to edit a term.
     */
    protected JTextArea addTerm(final JPanel p, final Term term, final Map m, final Vector keys, final LabelSpec lblspec) {
        final int index = (keys==null?0:keys.size());
        GridBagConstraints c = new GridBagConstraints();
        Object lbl = (index==0?lblspec.firstLabel:lblspec.nextLabel);
        JLabel wedgeIcon;
        if (lbl instanceof String) {
            wedgeIcon = new JLabel((String)lbl);
        }
        else if (lbl instanceof ImageIcon) {
            wedgeIcon = new JLabel((ImageIcon)lbl);
        }
        else {
            wedgeIcon = new JLabel();
        }
        final JTextArea ta = new JTextArea(1,25);
        if (term.isReadonly) {
            setReadonlyFlags(ta);
        }
        JButton deleteBtn = new JButton(IconImageData2.xdelete16Icon);
        deleteBtn.setMargin(new Insets(0,0,0,0));
        deleteBtn.setToolTipText("delete this term");
        //deleteBtn.setBorder(new javax.swing.border.EmptyBorder(0,0,0,0));
        deleteBtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                int answ = JOptionPane.OK_OPTION;
                if (ta.getText().trim().length() > 0) {
                    answ = JOptionPane.showConfirmDialog(StepEditor.this,"Delete this term?","Delete?",JOptionPane.OK_CANCEL_OPTION);
                }
                if (answ == JOptionPane.OK_OPTION) {
                    //m.remove(term);
                    //keys.remove(term);
                    keys.remove(index);
                    refreshTerms(p,m,keys,lblspec);
                }
            }
        });
        JButton upBtn = new JButton(IconImageData2.uparrow16Icon);
        upBtn.setMargin(new Insets(0,0,0,0));
        upBtn.setToolTipText("move this term up");
        //deleteBtn.setBorder(new javax.swing.border.EmptyBorder(0,0,0,0));
        upBtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (index>0) {
                    Object k0 = keys.elementAt(index-1);
                    keys.setElementAt(term,index-1);
                    keys.setElementAt(k0,index);
                    refreshTerms(p,m,keys,lblspec);
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
        p.add(wedgeIcon,c);
        c.fill = c.BOTH;
        c.anchor = c.WEST;
        c.gridx = 1;
        p.add(ta,c);
        c.gridx = 2;
        c.ipadx = 5; c.ipady = 0;
        p.add(upBtn,c);
        
        c.gridx = 3;
        if (!term.isReadonly) {
            p.add(deleteBtn,c);
        }
        
        m.put(term,ta);
        keys.add(term);
        
        return ta;
    }
    
    /** initializes the condition from the step edge.
     */
    protected void initConditionFromStepEdge() {
        conditionLabelSpec = new LabelSpec("",EConstants.wedgeIcon);
        condPanel.removeAll();
        //condCnt = 0;
        conditionMap = new Hashtable();
        conditionMapKeys = new Vector();
        java.util.List cterms = stepEdge.getConditionTerms();
        //Dbg.pr("cterms="+cterms);
        if (cterms == null) return;
        Iterator iter = cterms.iterator();
        while (iter.hasNext()) {
            Term t = (Term)iter.next();
            JTextArea ta = addTerm(condPanel,t,conditionMap,conditionMapKeys,conditionLabelSpec);
        }
    }
    
    /** initializes the update terms from the step edge.
     */
    protected void initUpdatesFromStepEdge() {
        updateLabelSpec = new LabelSpec(EConstants.vdashIcon,"");
        updatePanel.removeAll();
        //condCnt = 0;
        updateMap = new Hashtable();
        updateMapKeys = new Vector();
        java.util.List cterms = stepEdge.getUpdates();
        //Dbg.pr("cterms="+cterms);
        if (cterms == null) return;
        Iterator iter = cterms.iterator();
        while (iter.hasNext()) {
            Term t = (Term)iter.next();
            JTextArea ta = addTerm(updatePanel,t,updateMap,updateMapKeys,updateLabelSpec);
        }
    }
    
    /** refreshes the condition terms using the internally stored conditionTextAreas.
     */
    protected void refreshTerms(JPanel p, final Map m, final Vector keys, LabelSpec lblspec) {
        if (m == null || keys == null) return;
        p.removeAll();
        Map oldMap = new Hashtable();
        oldMap.putAll(m);
        Vector oldMapKeys = new Vector();
        oldMapKeys.addAll(keys);
        m.clear();
        keys.removeAllElements();
        Enumeration iter = oldMapKeys.elements();
        while(iter.hasMoreElements()) {
            Term term = (Term)iter.nextElement();
            String t = ((JTextArea)(oldMap.get(term))).getText();
            JTextArea ta = addTerm(p,term,m,keys,lblspec);
            ta.setText(t);
        }
    }
    
    protected void refreshConditionTerms() {
        refreshTerms(condPanel, conditionMap, conditionMapKeys, conditionLabelSpec);
    }
    
    protected void applyConditionTerms() {
        if (conditionMap == null || conditionMapKeys == null) {
            stepEdge.setConditionTerms(null);
        }
        ArrayList res = new ArrayList();
        Enumeration iter = conditionMapKeys.elements();
        while(iter.hasMoreElements()) {
            Term t = (Term)iter.nextElement();
            String str = ((JTextArea)(conditionMap.get(t))).getText().trim();
            t.term = str;
            if (str.length() > 0 && (!str.equals("true"))) {
                res.add(new Term(t));
            }
        }
        stepEdge.setConditionTerms(res);
    }
    
    protected void applyUpdates() {
        if (updateMap == null || updateMapKeys == null) {
            stepEdge.setUpdates(null);
        }
        ArrayList res = new ArrayList();
        Enumeration iter = updateMapKeys.elements();
        while(iter.hasMoreElements()) {
            Term t = (Term)iter.nextElement();
            String str = ((JTextArea)(updateMap.get(t))).getText().trim();
            t.term = str;
            if (str.length() > 0) {
                res.add(new Term(t));
            }
        }
        stepEdge.setUpdates(res);
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
        applyUpdates();
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
    
    public void setFrame(XElementEditorFrame editorFrame) {
        this.editorFrame = editorFrame;
    }
    
}
