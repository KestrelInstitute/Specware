package edu.kestrel.netbeans.model;

import edu.kestrel.netbeans.Util;

/**
 */
class ColimitCollection extends PartialCollection { //implements Positioner.Acceptor {
    static final ColimitElement[] EMPTY = new ColimitElement[0];
    
    Positioner      positioner;
    
    public ColimitCollection(ElementEvents events, ElementCreator creator, MemberCollection allMembers) {
        super(events, creator, allMembers, ElementProperties.PROP_COLIMITS);
        //positioner = DefaultLangModel.DEFAULT_POSITIONER;
	//Util.log("ColimitCollection after initialization this = "+this+" positions = "+getPositions());

    }
    
//     public void setPositioner(Positioner pos) {
//         this.positioner = pos;
//     }
    
  public ColimitElement getColimit(String name) {
    ColimitElement[] els = (ColimitElement[])getElements();        
    for (int i = 0; i < els.length; i++) {
      if (els[i].getName().equals(name)) {
	return els[i];
      }
    }
    return null;
  }

  public ElementImpl createElement(Element parent) {
    ColimitElementImpl cimpl = creator.createColimit((SourceElement)parent);
    return cimpl;
  }

    protected Object[] createEmpty() {
        return EMPTY;
    }
    
  public Element[] createEmpty(int size) {
    return new ColimitElement[size];
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
    return ColimitElementImpl.class;
  }
  
}
