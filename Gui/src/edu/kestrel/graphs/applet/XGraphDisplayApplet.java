/*
 * XGraphDisplayApplet.java
 *
 * Created on November 18, 2002, 1:21 PM
 */

package edu.kestrel.graphs.applet;

import edu.kestrel.graphs.*;
import javax.swing.*;
import java.awt.*;

/**
 *
 * @author  ma
 */
public class XGraphDisplayApplet extends JApplet {

    
    /** this method can be overwritten by sub-classers in order to create an instance of a sub-class
     * of <code>XGraphDisplay</code>
     */
    public XGraphDisplay createXGraphDisplay() {
        return new XGraphDisplay();
    }
    
    /** Initialization method that will be called after the applet is loaded
     *  into the browser.
     */
    public void init() {
        JPanel frame = new JPanel();
        frame.setLayout(new BorderLayout());
        Dbg.setDebugLevel(0);
        
        XGraphDisplay graph = createXGraphDisplay();
        frame.add(new JScrollPane(graph));
        frame.add(graph.createToolBar(JToolBar.HORIZONTAL),"North");
        setContentPane(frame);
    }
    
    
    
    /** Called by the browser or applet viewer to inform
     * this applet that it should start its execution. It is called after
     * the <code>init</code> method and each time the applet is revisited
     * in a Web page.
     * <p>
     * A subclass of <code>Applet</code> should override this method if
     * it has any operation that it wants to perform each time the Web
     * page containing it is visited. For example, an applet with
     * animation might want to use the <code>start</code> method to
     * resume animation, and the <code>stop</code> method to suspend the
     * animation.
     * <p>
     * The implementation of this method provided by the
     * <code>Applet</code> class does nothing.
     *
     * @see     java.applet.Applet#destroy()
     * @see     java.applet.Applet#init()
     * @see     java.applet.Applet#stop()
     *
     */
    public void start() {
        super.start();
    }
    
    /** Called by the browser or applet viewer to inform
     * this applet that it should stop its execution. It is called when
     * the Web page that contains this applet has been replaced by
     * another page, and also just before the applet is to be destroyed.
     * <p>
     * A subclass of <code>Applet</code> should override this method if
     * it has any operation that it wants to perform each time the Web
     * page containing it is no longer visible. For example, an applet
     * with animation might want to use the <code>start</code> method to
     * resume animation, and the <code>stop</code> method to suspend the
     * animation.
     * <p>
     * The implementation of this method provided by the
     * <code>Applet</code> class does nothing.
     *
     * @see     java.applet.Applet#destroy()
     * @see     java.applet.Applet#init()
     *
     */
    public void stop() {
        super.stop();
    }
    
    /** Called by the browser or applet viewer to inform
     * this applet that it is being reclaimed and that it should destroy
     * any resources that it has allocated. The <code>stop</code> method
     * will always be called before <code>destroy</code>.
     * <p>
     * A subclass of <code>Applet</code> should override this method if
     * it has any operation that it wants to perform before it is
     * destroyed. For example, an applet with threads would use the
     * <code>init</code> method to create the threads and the
     * <code>destroy</code> method to kill them.
     * <p>
     * The implementation of this method provided by the
     * <code>Applet</code> class does nothing.
     *
     * @see     java.applet.Applet#init()
     * @see     java.applet.Applet#start()
     * @see     java.applet.Applet#stop()
     *
     */
    public void destroy() {
        super.destroy();
    }
    
}
