/*
 * ClaimElement.java
 *
 * Created on February 7, 2003, 5:48 PM
 */

package edu.kestrel.netbeans.model;

import edu.kestrel.netbeans.codegen.ElementPrinter;
import edu.kestrel.netbeans.codegen.ElementFormat;

import org.openide.util.NbBundle;

import org.openide.src.SourceException;
import org.openide.src.ElementPrinterInterruptException;

/**
 *
 * @author  weilyn
 */
public final class ClaimElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat CLAIM_FORMAT =
        
        new ElementFormat("{c} {n}"); // NOI18N
    
    /** Create a new Claim element represented in memory.
     */
    public ClaimElement() {
        this(new Memory(), null);
    }
    
    /** Create a new Claim element.
     * @param impl the pluggable implementation
     * @param parent parent of this Claim, or <code>null</code>
     */
    public ClaimElement(ClaimElement.Impl impl, SpecElement spec) {
        super(impl, spec);
    }    

    final ClaimElement.Impl getClaimImpl() {
        return (ClaimElement.Impl) impl;
    }

    /** Clone the Claim element.
    *   @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new ClaimElement (new Memory (this), null);
    }
    
    /** Get the value claimKind of the Claim.
     * @return the claimKind
     */
    public String getClaimKind() {
        return getClaimImpl().getClaimKind();
    }

    /** Set the value claimKind of the Claim.
     * @param claimKind the claimKind
     * @throws SourceException if impossible
     */
    public void setClaimKind(String claimKind) throws SourceException {
        // sanity check:
        if (claimKind == null) {
	    throwSourceException(NbBundle.getMessage(ClaimElement.class, "ERR_NullClaimKind"));
        }
        getClaimImpl().setClaimKind(claimKind);
    }
    
    /** Print this element (and all its subelements) into an element printer.
     * @param printer the element printer
     * @exception ElementPrinterInterruptException if the printer canceled the printing
     *
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markClaim(this, printer.ELEMENT_BEGIN);

        printer.markClaim(this, printer.HEADER_BEGIN);
        printer.print(CLAIM_FORMAT.format(this));
        printer.markClaim(this, printer.HEADER_END);

        printer.markClaim(this, printer.ELEMENT_END);
    }

    /** Implementation of a claim element.
     * @see ClaimElement
     */
    public interface Impl extends MemberElement.Impl {
        /** Get the value claimKind of the Claim.
         * @return the claimKind
         */
        public String getClaimKind();

        /** Set the value claimKind of the Claim.
         * @param claimKind the claimKind
         * @throws SourceException if impossible
         */
        public void setClaimKind(String claimKind) throws SourceException;

    }
 
    static class Memory extends MemberElement.Memory implements Impl {
        private String claimKind;

        Memory() {
            claimKind = null;
        }

        /** Copy constructor.
	 * @param claim the object to read values from
	 */
        Memory (ClaimElement claim) {
            super (claim);
            claimKind = claim.getClaimKind();
        }

        /** Get the value claimKind of the Claim.
         * @return the claimKind
         *
         */
        public String getClaimKind() {
            return claimKind;
        }
        
        /** Set the value claimKind of the Claim.
         * @param claimKind the claimKind
         * @throws SourceException if impossible
         *
         */
        public void setClaimKind(String claimKind) {
            String old = this.claimKind;
            this.claimKind = claimKind;
            firePropertyChange (PROP_CLAIM_KIND, old, claimKind);
        }
        
    }    
}
