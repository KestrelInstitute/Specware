/*
 * XTextEditorInternalFrame.java
 *
 * Created on January 23, 2003, 6:56 PM
 */

package edu.kestrel.graphs.editor;

import edu.kestrel.graphs.*;
import javax.swing.*;
import javax.swing.event.*;
import java.awt.event.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XTextEditorInternalFrame extends JInternalFrame {
    
    protected XElementEditor editorPane;
    protected Thread resizeThread = null;
    protected boolean stopResizeThread = false;
    
    /** Creates a new instance of XTextEditorInternalFrame */
    public XTextEditorInternalFrame() {
        super("",true,true,true,true);
        editorPane = new XTextEditor();
        initGui();
    }
    
    public XTextEditorInternalFrame(XTextEditorEditable elem) {
        super("",true,true,true,true);
        editorPane = elem.createEditorPane();
        initGui();
    }
    
    protected void setTitle() {
        String title = "";
        if (editorPane != null) {
            title = editorPane.getTitleText();
        }
        setTitle(title);
    }
    
    public void setFont(Font f) {
        editorPane.setFont(f);
    }
    
    protected void closeFrame() {
        JDesktopPane dt = getDesktopPane();
        dt.remove(this);
        dt.repaint();
        if (resizeThread != null) {
            stopResizeThread = true;
        }
    }
    
    protected void initGui() {
        addInternalFrameListener(new InternalFrameAdapter() {
            public void internalFrameClosing(InternalFrameEvent e) {
                //Dbg.pr("internal frame closing...");
                closeFrame();
            }
        });
        setTitle();
        getContentPane().setLayout(new BorderLayout());
        JPanel cmdp = new JPanel();
        cmdp.setLayout(new FlowLayout());
        JButton okbtn = new JButton("ok");
        okbtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                editorPane.apply();
                closeFrame();
            }
        });
        JButton cancelbtn = new JButton("cancel");
        cancelbtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                closeFrame();
            }
        });
        JButton applybtn = new JButton("apply");
        applybtn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                editorPane.apply();
                setTitle();
            }
        });
        cmdp.add(okbtn);
        cmdp.add(applybtn);
        cmdp.add(cancelbtn);
        //getContentPane().add(new JScrollPane(editorPane));
        getContentPane().add(editorPane.getPanel());
        getContentPane().add(cmdp,BorderLayout.SOUTH);
        updateSize();
        if (editorPane != null) {
            if (editorPane.autoUpdateFrameSize()) {
                resizeThread = new Thread(new ResizeThread());
                resizeThread.start();
            }
        }
    }
    
    public void updateSize() {
        Dimension initSize = new Dimension(400,400);
        if (editorPane != null) {
            Dimension psize = editorPane.getPreferredSize();
            initSize.width = Math.max(250,psize.width + 50);
            initSize.height = Math.max(150,psize.height + 100);
        }
        setSize(initSize);
    }
    
    protected class ResizeThread implements Runnable {
        
        /** When an object implementing interface <code>Runnable</code> is used
         * to create a thread, starting the thread causes the object's
         * <code>run</code> method to be called in that separately executing
         * thread.
         * <p>
         * The general contract of the method <code>run</code> is that it may
         * take any action whatsoever.
         *
         * @see     java.lang.Thread#run()
         *
         */
        public void run() {
            while (!stopResizeThread) {
                try {
                    updateSize();
                    Thread.sleep(500);
                } catch (Exception ee) {}
            }
        }
        
    }
    
}
