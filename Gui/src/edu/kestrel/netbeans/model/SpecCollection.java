/*
 * SpecCollection.java
 *
 * $Id$
 *
 *
 *
 * $Log$
 * Revision 1.1  2003/01/30 02:02:04  gilham
 * Initial version.
 *
 *
 *
 */

package edu.kestrel.netbeans.model;

import edu.kestrel.netbeans.Util;

/**
 */
class SpecCollection extends PartialCollection { //implements Positioner.Acceptor {
    static final SpecElement[] EMPTY = new SpecElement[0];
    
    Positioner      positioner;
    
    public SpecCollection(ElementEvents events, ElementCreator creator, MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_SPECS);
        //positioner = DefaultLangModel.DEFAULT_POSITIONER;
	Util.log("SpecCollection after initialization this = "+this+" positions = "+getPositions());

    }
    
//     public void setPositioner(Positioner pos) {
//         this.positioner = pos;
//     }
    
  public SpecElement getSpec(String name) {
    SpecElement[] els = (SpecElement[])getElements();        
    for (int i = 0; i < els.length; i++) {
      if (els[i].getName().equals(name)) {
	return els[i];
      }
    }
    return null;
  }

  public ElementImpl createElement(Element parent) {
    SpecElementImpl cimpl = creator.createSpec((SourceElement)parent);
    return cimpl;
  }

    protected Object[] createEmpty() {
        return EMPTY;
    }
    
  public Element[] createEmpty(int size) {
    return new SpecElement[size];
  }

    
//   public Element[] findPositions(Element[] elements) {
//     return positioner.findInsertPositions((Element)events.getEventSource(), elements, this);
//   }
  
//   public boolean canInsertAfter(Element el) {
//     ElementImpl impl;
    
//     // special case -- element is just being created.
//     if (events.getElementImpl().isCreated())
//       return true;
    
//     if (el != null && el != Positioner.FIRST) {
//       impl =  (ElementImpl)el.getCookie(ElementImpl.class);
//       if (impl == null) {
// 	throw new IllegalArgumentException("Unsupported element implementation"); // NOI18N
//       }
//     } else
//       impl = null;
//     //return containerBinding.canInsertAfter(impl == null ? null : impl.getBinding());
//     return ((Binding.Container)(((ElementImpl)events).getBinding())).canInsertAfter(impl.getBinding());
//   }
  
  
  /** Returns the Class object for element impls contained within the collection.
   *
   */
  public Class getElementImplClass() {
    return SpecElementImpl.class;
  }
  
}
