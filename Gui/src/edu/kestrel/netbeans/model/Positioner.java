/*
 * Positioner.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 *
 *
 */

package edu.kestrel.netbeans.model;

/**
 *
 */
public interface Positioner {
    public static final Element FIRST = new SpecElement();

    public Element[] findInsertPositions(Element container, Element[] els, Acceptor posAcceptor);
    
    public interface Acceptor {
        public boolean canInsertAfter(Element el);
    }
}

