/*
 * StorableInitActions.java
 *
 * Created on December 7, 2002, 11:28 PM
 */

package edu.kestrel.graphs.io;

/**
 * This interface is used to inject customized actions before initialization of a storable element in the
 * process of object creation from an ElementProperties instance.
 * @author  ma
 */
public interface StorableInitActions {
    public void preinitAction(Storable obj);
}
