/*
 * DocumentBinding.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.codegen;

import java.util.Collection;

import org.openide.cookies.SourceCookie;

import org.openide.src.SourceException;

import org.openide.text.CloneableEditorSupport;
import org.openide.text.PositionBounds;
import org.openide.text.PositionRef;

import edu.kestrel.netbeans.model.Binding;
import edu.kestrel.netbeans.model.BindingFactory;

/**
 * Definition of code generation package. The package exports those functions of
 * the BindingFactory and several management functions.
 */
public interface DocumentBinding extends BindingFactory {
    /**
     * Finds and returns the CloneableEditorSupport. This method siply delegates
     * to the environment's findEditorSupport() method.
     * @return CloneableEditorSupport instance used for binding of the model.
     */
    public CloneableEditorSupport    getEditorSupport();
    
    /**
     * Causes the operation to run atomically on the document. The document
     * will be locked out for writing for the length of the operation.
     * @throw SourceException if the document cannot be loaded, locked or if some
     * of the Runnable's operation fails.
     */
    public void runAtomic(Runnable r) throws SourceException;
    
    /**
     * Causes the operation to run atomically on the document at the user-level. The document
     * will be locked out for writing for the length of the operation.
     * @throw SourceException if the document cannot be loaded, locked or if some
     * of the Runnable's operation fails.
     */
    public void enableAtomicAsUser(boolean enable);

    /**
     * Atomically updates bindings in the source, possibly inserting new ones. The 
     * hierarchy of Bindings is locked for the length of the operation. This will lock out
     * operations like get
     */
    public void updateBindings(Runnable r);
    
    /**
     * Enables or disables the code generator. If the calling code disables the generation,
     * it is <B>responsible</B> to reenable it again at the appropriate time. For example,
     * parsing updater should disable code generation before it starts to update the
     * source text model.
     */
    public void enableGenerator(boolean enableFlag);

    /**
     * Environment for the document generation package.
     */
    public static interface Env {
        /**
         * Finds CloneableEditorSupport for the code generator. The support is used
         * to load/access the document.
         */
        public CloneableEditorSupport findEditorSupport();

        /** Attempts to find "free" position in the source text, between (inclusive)
         * the given bounds. This is, actually, a test for a guarded block - it is
         * deferred to the user of the code generation suite.
         */
        public PositionRef  findFreePosition(PositionBounds bounds);
    }
}

