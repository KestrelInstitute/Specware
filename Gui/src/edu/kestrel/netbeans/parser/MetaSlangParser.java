/*
 * MetaSlangParser.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:19  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.beans.PropertyChangeListener;
import java.io.Reader;
import java.io.InputStream;
import java.io.IOException;
import javax.swing.event.ChangeListener;

import org.openide.filesystems.FileObject;
import org.openide.nodes.Node;
import org.openide.src.SourceException;
import org.openide.util.Task;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.cookies.SourceCookie;

/**
 *
 */
public interface MetaSlangParser extends SourceCookie {
    /**
     * This priority level is recommended for background operations, that the user
     * does not need to wait for.
     */
    public static final int    PRIORITY_BACKGROUND = Thread.MIN_PRIORITY;
    /**
     * Normal priority is recommended for parse operations that needs to be completed soon,
     * but should not block the IDE. This priority is internally used in prepare() call.
     */
    public static final int    PRIORITY_NORMAL = Thread.MIN_PRIORITY + 1;
    /**
     * Recommended priority for carrying out blocking calls. This priority is used
     * by blocking calls on SourceElement.
     */
    public static final int    PRIORITY_DEMAND = Thread.MAX_PRIORITY - 1;
    /**
     * Recommended priority for hierarchy refresh operations. This priority is used
     * in MetaSlang module in refresh operation after the user stops editing for a period of
     * time.
     */
    public static final int    PRIORITY_REFRESH = PRIORITY_NORMAL;

    /**
     * Shallow parser request. 
     */
    public static final String SHALLOW_PARSER = "shallow"; // NOI18N
    /**
     * Deep parser request.
     */
    public static final String DEEP_PARSER = "deep"; // NOI18N
    /**
     * Adds a Listener on the parser.
     */
    public void addPropertyChangeListener(PropertyChangeListener l);
    
    /**
     * Removes the listener from the parser.
     */
    public void removePropertyChangeListener(PropertyChangeListener l);
    
    /**
     * Listens on parser state changes (more events than just PropertyChanges!)
     */
    public void addChangeListener(ChangeListener l);
    
    /**
     * Removes the change listener from the parser.
     */
    public void removeChangeListener(ChangeListener l);
    
    /**
     * Returns the Element representing the source.
     */
    public SourceElement    getSource();
    
    /**
     * Prepares the source hierarchy; after the task is finished, there are some
     * parsed data. If the model already exists, the task returned is already finished.
     * The returned task, after it completes, also guarantees that the model will not
     * be garbage collected.
     */
    public Task             prepare();
    
    /**
     * Schedules a parse task with various parameters.
     * @param force schedules a parse even if the underlying document contains no
     * uparsed changes. The method returns a task that you can wait for, or attach
     * TaskListeners to. See {@link #prepare} for more information.
     * @param acceptErrors force model update even if the parsed data indicate syntax
     * errors.
     * @param priority priority of the task.
     * @return task for synchronization purposes. The task is marked finished after the
     * model is created or refreshed.
     */
    public Task             parse(int priority, boolean force, boolean acceptErrors);

    /**
     * Schedules a parse task with various parameters.
     * @param force schedules a parse even if the underlying document contains no
     * uparsed changes. The method returns a task that you can wait for, or attach
     * TaskListeners to. See {@link #prepare} for more information.
     * @param acceptErrors force model update even if the parsed data indicate syntax
     * errors.
     * @param priority priority of the task.
     * @return task for synchronization purposes. The task is marked finished after the
     * model is created or refreshed.
     */
    public Task             parse(int priority, boolean force, boolean acceptErrors, ParsableObjectRequest request);
    
    /**
     * Returns current running parser task, if there is no task running returns FinishedTask
     * @return task for synchronization purposes.
     */
    public Task getCurrentTask();
    
    /**
     * Returns the overall current parser's status. The returned value is one of
     * the manifested constants SourceElement.STATUS_*.
     * @return status information
     */
    public int              getStatus();
    
    /**
     * Retrieves the exception that describes the last failure to parse the
     * input. This will be mostly SourceException.IO.
     */
    public SourceException  getErrorCause();
    
    /**
     * Returns the <B>real</B> implementation of the source provided by the data model.
     */
    public SourceElement.Impl   getSourceImpl();
    
    /**
     * Returns the model the parser operatges on.
     */
    public LangModel            getModel();

    /**
     * Interface that the support uses to talk to the outside world.
     */
    public interface Env {
        /** Retrieves the source text for parsing. Can throw IOException, if the
         * source cannot be retrieved.
         */
        public Reader   getSourceText() throws IOException;

        /** Retrieves the source file object for parsing. 
         */
        public FileObject   getSourceFile();

        /**
         * Environment can find precompiled classes to speed up name resoltion
         */
        //public InputStream  findCompiledClass(String classFQN);
        
        /**
         * Finds appropriate cookie for the element.
         */
        public Node.Cookie  findCookie(SourceElement el, Class cls);

        /**
         * Annotate the throwable with a localized message. The flag controls whether
         * the error is a user-level one, or it is an internal failure.
         */
        public void annotateThrowable(Throwable t, String locMessage, boolean user);
        
        /**
         * Annotates wrapping throwable with the nested one - whatever that means to the
         * environment.
         */
        public void annotateThrowable(Throwable wrapper, Throwable nested);
    }
}
