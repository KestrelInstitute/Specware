/*
 * XDesktopPane.java
 *
 * Created on November 25, 2002, 12:08 PM
 */

package edu.kestrel.graphs;

import edu.kestrel.graphs.io.*;
import javax.swing.filechooser.FileFilter;
import javax.swing.tree.*;
import javax.swing.*;
import java.io.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;

/**
 * This class implements the desktop panel for XGraphDisplays
 * @author  ma
 */
public class XGraphDesktop extends JPanel {
    
    protected JMenuBar menuBar;
    protected JToolBar toolBar;
    protected JDesktopPane desktopPane;
    
    protected XGraphApplication appl;
    
    protected String currentdir = System.getProperty("user.dir");
    
    /** the toplevel frame.
     */
    protected JFrame frame = null;
    
    /** the suffix used for files.
     */
    protected String defaultFileSuffix = ".xgraph";
    
    /** Creates a new instance of XGraphDesktop */
    public XGraphDesktop(XGraphApplication appl) {
        this.toolBar = createToolBar(JToolBar.HORIZONTAL);
        this.desktopPane = createDesktopPane();
        this.appl = appl;
        appl.setDesktop(this);
        //desktopPane.setBackground(new Color(237,235,218));
        setLayout(new BorderLayout());
        add(desktopPane,"Center");
        initMenuBar();
        JPanel topPanel = new JPanel();
        topPanel.setLayout(new GridLayout(2,1));
        topPanel.add(menuBar);
        topPanel.add(toolBar);
        add(topPanel,"North");
    }
    
    protected void initMenuBar() {
        menuBar = new JMenuBar();
        JMenu m = new JMenu("File");
        JMenuItem item;
        item = new JMenuItem("New");
        item.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                newAction();
            }
        });
        m.add(item);
        item = new JMenuItem("Open...");
        item.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                openAction(null);
            }
        });
        m.add(item);
        item = new JMenuItem("Save...");
        item.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                saveAction();
            }
        });
        m.add(item);
        item = new JMenuItem("Save As...");
        item.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                saveAsAction(null);
            }
        });
        m.add(item);
        m.addSeparator();
        item = new JMenuItem("Exit");
        item.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                exitAction(true);
            }
        });
        m.add(item);
        menuBar.add(m);
    }
    
    /** returns the file filter that is used in open/save operations.
     */
    protected FileFilter createXmlFileFilter() {
        return new FileFilter() {
            public boolean accept(File f) {
                if (f.isDirectory()) return true;
                String fname = f.getName();
                return fname.endsWith(".xml");
            }
            public String getDescription() {
                return "Graph Model XML Files";
            }
        };
    }
    
    /** sets the toplevel frame; called in the initialization phase by the main function.
     */
    public void setFrame(JFrame frame) {
        Dbg.pr("setting frame...");
        this.frame = frame;
    }
    
    public JFrame getFrame() {
        return frame;
    }
    
    public void setFrameTitle(String title) {
        if (frame == null) return;
        String sep = " -- ";
        String oldtitle = getFrameTitle();
        int index = oldtitle.indexOf(sep);
        if (index > 0) {
            frame.setTitle(oldtitle.substring(0,index)+sep+title);
        } else {
            frame.setTitle(oldtitle+sep+title);
        }
    }
    
    public String getFrameTitle() {
        if (frame == null) return "";
        return frame.getTitle();
    }
    
    /** returns the file filter that is used in open/save operations.
     */
    protected FileFilter createFileFilter() {
        return new FileFilter() {
            public boolean accept(File f) {
                if (f.isDirectory()) return true;
                String fname = f.getName();
                return fname.endsWith(defaultFileSuffix);
            }
            public String getDescription() {
                return "Graph Model Files";
            }
        };
    }
    
    public void openAction(String filename) {
        if (!newAction()) return;
        if (filename == null) {
            JFileChooser chooser = new JFileChooser();
            FileFilter filter = createFileFilter();
            chooser.setFileFilter(filter);
            if (currentdir != null) {
                chooser.setCurrentDirectory(new File(currentdir));
            }
            int returnVal = chooser.showOpenDialog(this);
            if(returnVal == JFileChooser.APPROVE_OPTION) {
                File dir = chooser.getCurrentDirectory();
                //Dbg.pr("directory="+dir.toString());
                String fsep = System.getProperty("file.separator");
                filename = dir.toString() + fsep + chooser.getSelectedFile().getName();
                currentdir = dir.toString();
                //filename = manipulateFilenameForSave(filename);
            }
        }
        if (filename != null) {
            appl.setCurrentFilename(filename);
            try {
                ReadWriteOperation rwop = ReadWriteOperation.createFromFile(appl,filename);
                System.out.println("model data read from file \""+filename+"\"...");
                appl.loadFromReadWriteOperation(rwop);
            } catch (IOException ioe) {
                JOptionPane.showMessageDialog(this,ioe.getMessage(),"error",JOptionPane.ERROR_MESSAGE);
                appl.setCurrentFilename(null);
            }
        }
    }
    
    /** removes everything after confirmation; returns true, if the new action has been performed, false if not.
     */
    public boolean newAction() {
        if (!appl.isEmpty()) {
            String msg = "Do want to delete all elements and displays?";
            int answ = JOptionPane.showConfirmDialog(this,msg,"delete all?",JOptionPane.OK_CANCEL_OPTION);
            if (answ != JOptionPane.OK_OPTION) return false;
        }
        Dbg.pr("deleting everything...");
        appl.deleteAllAction();
        removeModelFrame();
        appl.setCurrentFilename(null);
        return true;
    }
    
    /** action taken when the user decides to exit the application; the canStopExiting flag is true, if the exit doesn't need
     * to be carried out; it is false, if this action is called while the main window is closing, so there is no chance of keeping
     * the application "alive".
     */
    public boolean exitAction(boolean canStopExiting) {
        if (!appl.isEmpty()) {
            String msg = "You are about to exit, save unsaved changes?";
            int option = JOptionPane.YES_NO_OPTION;
            int okoption = JOptionPane.YES_OPTION;
            if (canStopExiting) {
                msg = "Do you really want to exit, all unsaved changes will be lost, if you continue.";
                option = JOptionPane.OK_CANCEL_OPTION;
                okoption = JOptionPane.OK_OPTION;
            }
            int answ = JOptionPane.showConfirmDialog(this,msg,"exit",option);
            if (answ != okoption) return false;
            
            if (!canStopExiting) {
                saveAction();
            }
        }
        if (canStopExiting) {
            System.exit(0);
        }
        return true;
    }
    
    public void saveAction() {
        saveAsAction(appl.getCurrentFilename());
    }
    
    public void saveAsXmlAction(String filename) {
        appl.clearClipboard();
        if (filename == null) {
            JFileChooser chooser = new JFileChooser();
            FileFilter filter = createXmlFileFilter();
            chooser.setFileFilter(filter);
            if (currentdir != null) {
                chooser.setCurrentDirectory(new File(currentdir));
            }
            int returnVal = chooser.showSaveDialog(this);
            if(returnVal == JFileChooser.APPROVE_OPTION) {
                filename = chooser.getSelectedFile().getName();
            }
        }
        if (filename != null) {
            //appl.setCurrentFilename(filename);
            try {
                PrintStream ps = new PrintStream(new FileOutputStream(filename));
                ps.print(appl.allToXml());
                ps.close();
                System.out.println("model data written to file \""+filename+"\"...");
            } catch (IOException ioe) {
                JOptionPane.showMessageDialog(this,ioe.getMessage(),"error",JOptionPane.ERROR_MESSAGE);
            }
        }
    }
    
    /** performs manipulation on the filename that has been selected as target for a save operation;
     * this is here adding of a default suffix; subclasser can customize this
     */
    protected String manipulateFilenameForSave(String filename) {
        if (filename.endsWith(defaultFileSuffix)) return filename;
        int index = filename.indexOf('.');
        if (index<0) {
            return filename+defaultFileSuffix;
        }
        return filename;
    }
    
    public void saveAsAction(String filename) {
        appl.clearClipboard();
        if (filename == null) {
            JFileChooser chooser = new JFileChooser();
            FileFilter filter = createFileFilter();
            chooser.setFileFilter(filter);
            if (currentdir != null) {
                chooser.setCurrentDirectory(new File(currentdir));
            }
            int returnVal = chooser.showSaveDialog(this);
            if(returnVal == JFileChooser.APPROVE_OPTION) {
                File dir = chooser.getCurrentDirectory();
                //Dbg.pr("directory="+dir.toString());
                String fsep = System.getProperty("file.separator");
                filename = dir.toString() + fsep + chooser.getSelectedFile().getName();
                currentdir = dir.toString();
                filename = manipulateFilenameForSave(filename);
            }
        }
        if (filename != null) {
            appl.setCurrentFilename(filename);
            try {
                ReadWriteOperation rwop = appl.getToplevelReadWriteOperation();
                rwop.writeToFile(filename);
                System.out.println("model data written to file \""+filename+"\"...");
                saveAsXmlAction(filename+".xml");
            } catch (IOException ioe) {
                JOptionPane.showMessageDialog(this,ioe.getMessage(),"error",JOptionPane.ERROR_MESSAGE);
                appl.setCurrentFilename(null);
            }
        }
    }
    
    public void newGraphAction() {
        XGraphDisplay graph = appl.newGraphAction();
        XGraphDisplayInternalFrame f = new XGraphDisplayInternalFrame(graph);
        //f.setSize(300,300);
        newInternalFrame(f);
        //f.setVisible(true);
        //desktopPane.add(f);
        //desktopPane.moveToFront(f);
    }
    
    public void newInternalFrame(JInternalFrame f) {
        f.setVisible(true);
        desktopPane.add(f);
        desktopPane.moveToFront(f);
    }
    
    /** ensures that a window for graph is open, if not it opens a new one.
     */
    public void ensureDisplayGraphAction(XGraphDisplay graph) {
        if (displaysXGraphDisplay(graph)) return;
        XGraphDisplayInternalFrame f = new XGraphDisplayInternalFrame(graph);
        f.setVisible(true);
        desktopPane.add(f);
        desktopPane.moveToFront(f);
    }
    
    public void closeGraphAction(XGraphDisplay graph) {
        XGraphDisplayInternalFrame f = getXGraphDisplay(graph);
        if (f != null) {
            Dimension dim = f.getSize();
            Point p = f.getLocation();
            Rectangle bounds = new Rectangle(p.x,p.y,dim.width,dim.height);
            graph.closeAction(bounds);
            desktopPane.remove(f);
            desktopPane.repaint();
        }
    }
    
    /** calls close action on graph that are empty and that are not currently contained in an internal frame in the
     * desktop; exception: if they are iconified, they will be removed if empty.
     */
    public void closeGraphIfEmptyAction(XGraphDisplay graph) {
        XGraphDisplayInternalFrame f = getXGraphDisplay(graph);
        if (f != null)
            if (!f.isIcon())
                return;
        if (graph.isEmpty()) {
            //closeGraphAction(graph);
            appl.unregisterGraph(graph);
        }
    }
    
    public void showClipboardAction() {
        XGraphDisplayInternalFrame f = new XGraphDisplayInternalFrame(appl.getClipboard());
        //f.setSize(300,300);
        f.setVisible(true);
        desktopPane.add(f);
        desktopPane.moveToFront(f);
    }
    
    protected JInternalFrame modelFrame = null;
    protected XModelTree modelTree;
    
    
    /** returns the tree representing the toplevel tree model of the application. This tree model has 2 children:
     * the graph displays and the application model. It provides access to all data contained in the application.
     */
    public XModelTree getModelTree() {
        if (modelTree == null) {
            TreeModel tm = appl.getToplevelTreeModel();
            //TreeModel tm1 = appl.getModelNode();
            modelTree = new XModelTree(appl,tm);
            modelTree.setRootVisible(false);
            tm.addTreeModelListener(modelTree);
            //tm1.addTreeModelListener(modelTree);
            appl.initModelTree(modelTree);
        }
        return modelTree;
    }
    
    /** displays the model tree frame containing the application's graph displays and model nodes.
     */
    public void showModelTree(Rectangle bounds) {
        removeModelFrame();
        XModelTree modelTree = getModelTree();
        modelFrame = new JInternalFrame("Model",true,true,false,false);
        modelFrame.getContentPane().setLayout(new BorderLayout());
        modelFrame.getContentPane().add(new JScrollPane(modelTree));
        if (bounds == null) {
            modelFrame.setSize(200,300);
        } else {
            modelFrame.setLocation(bounds.x,bounds.y);
            modelFrame.setSize(bounds.width,bounds.height);
        }
        modelFrame.setVisible(true);
        desktopPane.add(modelFrame);
        desktopPane.moveToFront(modelFrame);
    }
    
    /** returns true, if the model tree window is currently displayed on the desktop.
     */
    public boolean displaysModelTree() {
        if (modelFrame == null) return false;
        JInternalFrame[] frames = desktopPane.getAllFrames();
        if (frames == null) return false;
        for(int i=0;i<frames.length;i++) {
            if (modelFrame.equals(frames[i]))
                return true;
        }
        return false;
    }
    
    /** returns true, if the model tree window is currently displayed on the desktop.
     */
    public Rectangle getModelTreeBounds() {
        if (!displaysModelTree()) return null;
        Point p = modelFrame.getLocation();
        Dimension dim = modelFrame.getSize();
        return new Rectangle(p.x,p.y,dim.width,dim.height);
    }
    
    /** removes the frame displaying the model of the application.
     */
    public void removeModelFrame() {
        if (modelFrame != null) {
            desktopPane.remove(modelFrame);
            desktopPane.repaint();
        }
    }
    
    /** returns true, if there is an internal frame displaying the given graph display.
     */
    public boolean displaysXGraphDisplay(XGraphDisplay graph) {
        return (getXGraphDisplay(graph) != null);
    }
    
    /** returns the internal frame displaying the given graph display.
     */
    public XGraphDisplayInternalFrame getXGraphDisplay(XGraphDisplay graph) {
        JInternalFrame[] allframes = desktopPane.getAllFrames();
        for(int i=0;i<allframes.length;i++) {
            if (allframes[i] instanceof XGraphDisplayInternalFrame) {
                XGraphDisplayInternalFrame f = (XGraphDisplayInternalFrame) allframes[i];
                if (f.displaysGraph(graph)) {
                    //Dbg.pr("found frame for graph "+graph);
                    return f;
                }
            }
        }
        return null;
    }
    
    /** removes the XGraphDisplayInternalFrame containing the given graph.
     */
    public void removeXGraphDisplay(XGraphDisplay graph) {
        XGraphDisplayInternalFrame f = getXGraphDisplay(graph);
        if (f != null) {
            try {
                f.setIcon(false);
            } catch (Exception e) {}
            desktopPane.remove(f);
            desktopPane.repaint();
        }
    }
    
    protected JToolBar createToolBar(int direction) {
        JToolBar tb = new JToolBar(direction);
        tb.setFloatable(false);
        ButtonGroup grp = new ButtonGroup();
        JButton btn;
        btn = new JButton(IconImageData.new24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("new model");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                newAction();
            }
        });
        tb.add(btn);
        btn = new JButton(IconImageData2.open24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("open");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                openAction(null);
            }
        });
        tb.add(btn);
        btn = new JButton(IconImageData.save24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("save");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                saveAction();
            }
        });
        tb.add(btn);
        tb.addSeparator();
        // new graph display button
        btn = new JButton(IconImageData.container24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("new graph display");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                newGraphAction();
            }
        });
        tb.add(btn);
        btn = new JButton(IconImageData.tree24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("show model");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showModelTree(null);
            }
        });
        tb.add(btn);
        tb.addSeparator();
        btn = new JButton(IconImageData.paste24Icon);
        btn.setMargin(new Insets(0,0,0,0));
        btn.setToolTipText("show clipboard");
        btn.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                showClipboardAction();
            }
        });
        if (Dbg.isDebug()) tb.add(btn);
        //grp.add(btn);
        return tb;
    }
    
    class ActionListenerForToolBar implements ActionListener {
        public ActionListenerForToolBar() {
        }
        public void actionPerformed(ActionEvent e) {
        }
    }
    
    protected JDesktopPane createDesktopPane() {
        JDesktopPane dt = new JDesktopPane();
        return dt;
    }
    
}
