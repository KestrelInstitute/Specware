/*
 * TextPositionMatch.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:28  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.parser;

import java.util.*;

import edu.kestrel.netbeans.model.*;
import edu.kestrel.netbeans.codegen.TextBinding;

/**
 *
 */
public class TextPositionMatch implements ElementMatch.Finder {
    public void findMatches(ElementMatch data) {
        int oldPos = 0;
        Element[] elements = data.getOldElements();
        
        for (; data.hasMoreElements(); ) {
            TextBinding found = null;
            BaseElementInfo info = data.nextElement();
            
            while (oldPos < elements.length) {
                TextBinding b;
                int beginPos, endPos;
                int relativePos;

                ElementImpl impl = (ElementImpl)elements[oldPos].getCookie(ElementImpl.class);
                b = (TextBinding)impl.getBinding();
                relativePos = info.comparePositionTo(b);
                if (relativePos == 0) {
                    found = b;
                    break;
                } else if (relativePos > 0) {
                    oldPos++;
                } else if (relativePos < 0) {
                    break;
                }
            }
            
            if (found != null) {
                data.matchElement(oldPos++);
            }
        }
    }
}
