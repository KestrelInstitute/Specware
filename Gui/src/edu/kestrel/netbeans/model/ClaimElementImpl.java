/*
 * ClaimElementImpl.java
 *
 * Created on February 7, 2003, 5:56 PM
 */

package edu.kestrel.netbeans.model;

import java.beans.*;

import org.openide.src.SourceException;

/**
 *
 * @author  weilyn
 */
public class ClaimElementImpl extends MemberElementImpl implements ClaimElement.Impl {
    private static final long serialVersionUID = 6799964214013985830L;
    
    /** Kind of the claim.
     */
    private String claimKind;

    /** Creates a new instance of ClaimElementImpl */
    public ClaimElementImpl(DefaultLangModel model) {
        super(model);
        claimKind = null;
    }
    
    /** Creates a suitable binding for the element. The binding is created with the
     * help of BindingFactory available from the element's model object; descendants
     * are required to route the request to the most appropriate factory's method.
     *
     */
    protected Binding createBinding(Element el) {
        return getModelImpl().getBindingFactory().bindClaim((ClaimElement)el);
    }
   
    protected void createFromModel(Element el) throws SourceException {
        super.createFromModel(el);
        ClaimElement element = (ClaimElement)el;
        setClaimKind(element.getClaimKind());
    }
    
    public Object readResolve() {
        return null;
    }    
    
    /** Get the value claimKind of the Claim.
     * @return the claimKind
     *
     */
    public String getClaimKind() {
        return this.claimKind;
    }
    
    /** Set the value claimKind of the Claim.
     * @param claimKind the claimKind
     * @throws SourceException if impossible
     *
     */
    public void setClaimKind(String claimKind) throws SourceException {
        Object token = takeLock();
        try {
            PropertyChangeEvent evt;
            if (!isCreated()) {
                if (claimKind == this.claimKind)
                    return;
                evt = new PropertyChangeEvent(getElement(), PROP_CLAIM_KIND, this.claimKind, claimKind);
                // no constraings on the Initializer... only check vetoable listeners.
                checkVetoablePropertyChange(evt);
                getClaimBinding().changeClaimKind(claimKind);
                addPropertyChange(evt);
            }
            this.claimKind = claimKind;
            commit();
        } finally {
            releaseLock(token);
        }        
    }

    // Utility methods.
    //////////////////////////////////////////////////////////////////////////////////
    
    protected Binding.Claim getClaimBinding() {
        return (Binding.Claim)getBinding();
    }
    
    protected Element createWrapperElement() {
        return null;
    }
    
    public String toString() {
        return "ClaimElementImpl[" + getName() + "]"; // NOI18N
    }
    
    protected Element cloneSelf() {
        return (Element)((ClaimElement)getElement()).clone();
    }    
}
