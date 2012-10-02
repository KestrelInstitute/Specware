/*
 * Derivable.java
 *
 * Created on January 30, 2003, 2:33 PM
 */

package edu.kestrel.especs.graphs;

/**
 * Interface for elements that are derived from other elements, which must implement interface DerivationSource
 * @author  ma
 */
public interface Derivable {
    
    public void addDerivedFrom(DerivationSource elem);

    public void removeDerivedFrom(DerivationSource elem);
    
    public boolean isDerived();
    
    public java.util.List getDerivedFrom();
    
}
