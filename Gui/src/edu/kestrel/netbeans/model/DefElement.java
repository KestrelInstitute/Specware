/*
 * DefElement.java
 *
 * Created on February 15, 2003, 4:12 PM
 */

package edu.kestrel.netbeans.model;

import edu.kestrel.netbeans.codegen.ElementFormat;
import edu.kestrel.netbeans.codegen.ElementPrinter;

import java.beans.PropertyChangeEvent;

import org.openide.src.ElementPrinterInterruptException;
import org.openide.src.SourceException;
/**
 *
 * @author  weilyn
 */
public final class DefElement extends MemberElement {
    /** Format for the code generator */
    private static final ElementFormat DEF_FORMAT =
        new ElementFormat("def {n}{p,\"(\",\")\"} = {e}"); // NOI18N
   
    /** Create a new def element represented in memory.
     */
    public DefElement() {
        this(new Memory(), null);
    }
    
    /** Create a new def element.
     * @param impl the pluggable implementation
     * @param parent parent of this def, or <code>null</code>
     */
    public DefElement(DefElement.Impl impl, SpecElement spec) {
        super(impl, spec);
    }

    final DefElement.Impl getDefImpl() {
        return (DefElement.Impl) impl;
    }

    /** Clone the def element.
    * @return a new element that has the same values as the original
    *   but is represented in memory
    */
    public Object clone () {
        return new DefElement (new Memory (this), null);
    }

    /** Set the name of this member.
     * @param name the name
     * @throws SourceException if impossible
     */
    public final void setName(String name) throws SourceException {
        super.setName(name);
    }

    /** Get the value parameters of the Def.
     * @return the parameters
     */
    public String[] getParameters() {
        return getDefImpl().getParameters();
    }

    /** Set the value parameters of the Def.
     * @param parameters the parameters
     * @throws SourceException if impossible
     */
    public void setParameters(String[] parameters) throws SourceException {
        getDefImpl().setParameters(parameters);
    }

    /** Get the value expression of the Def.
     * @return the expression
     */
    public String getExpression() {
        return getDefImpl().getExpression();
    }

    /** Set the value expression of the Def.
     * @param expression the expression
     * @throws SourceException if impossible
     */
    public void setExpression(String expression) throws SourceException {
        getDefImpl().setExpression(expression);
    }
    
    /* Prints the element into the element printer.
     * @param printer The element printer where to print to
     * @exception ElementPrinterInterruptException if printer cancel the printing
     */
    public void print(ElementPrinter printer) throws ElementPrinterInterruptException {
        printer.markDef(this, printer.ELEMENT_BEGIN);

        printer.markDef(this, printer.HEADER_BEGIN);
        printer.print(DEF_FORMAT.format(this));
        printer.markDef(this, printer.HEADER_END);

        printer.markDef(this, printer.ELEMENT_END);
    }
    
    /** Implementation of a def element.
     * @see DefElement
     */
    public interface Impl extends MemberElement.Impl {
        /** Get the value parameters of the Def.
         * @return the parameters
         */
        public String[] getParameters();

        /** Set the value parameters of the Def.
         * @param parameters the parameters
         * @throws SourceException if impossible
         */
        public void setParameters(String[] parameters) throws SourceException;

        /** Get the value expression of the Def.
         * @return the expression
         */
        public String getExpression();

        /** Set the value expression of the Def.
         * @param expression the expression
         * @throws SourceException if impossible
         */
        public void setExpression(String expression) throws SourceException;
        
    }

    static class Memory extends MemberElement.Memory implements Impl {
        private String[] parameters;
        private String expression;

        Memory() {
            parameters = null;
            expression = null;
        }

        /** Copy constructor.
	 * @param def the object to read values from
	 */
        Memory (DefElement def) {
            super (def);
            parameters = def.getParameters();
            expression = def.getExpression();
        }

        /** Parameters of the variable.
	 * @return the parameters
	 */
        public String[] getParameters() {
            return parameters;
        }

        /** Setter for parameters of the variable.
	 * @param parameters the variable parameters
	 */
        public void setParameters(String[] parameters) {
            String[] old = this.parameters;
            this.parameters = parameters;
            firePropertyChange (PROP_PARAMETERS, old, parameters);
        }

        /** Expression of the variable.
	 * @return the expression
	 */
        public String getExpression() {
            return expression;
        }

        /** Setter for expression of the variable.
	 * @param expression the variable expression
	 */
        public void setExpression(String expression) {
            String old = this.expression;
            this.expression = expression;
            firePropertyChange (PROP_EXPRESSION, old, expression);
        }

    }
}
