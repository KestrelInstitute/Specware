/*
 * DerivationSource.java
 *
 * Created on January 30, 2003, 2:30 PM
 */

package edu.kestrel.especs.graphs;

/**
 * interface for describing elements that may be used to derive other elements,
 * e.g. an EspecNode a is derived from an Espec b if b imports a
 * The derived element must implement interface Derivable
 * @author  ma
 */
public interface DerivationSource {
    
    public void addDerivedElement(Derivable elem);

    public void removeDerivedElement(Derivable elem);

    public boolean hasDerivedElements();
    
    public java.util.List getDerivedElements();
    
    public void decoupleDerivedElements();
    
}
