/*
 * Positioner.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:02  gilham
 * Initial version.
 *
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

