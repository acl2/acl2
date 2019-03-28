/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 quoted constants.
 * These are translated terms of the form {@code (quote ...)}.
 */
public final class Acl2QuotedConstant extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * ACL2 value of the quoted constant.
     * This is never {@code null}.
     */
    private final Acl2Value value;

    /**
     * Constructs an ACL2 quoted constant from its value.
     */
    private Acl2QuotedConstant(Acl2Value value) {
        assert value != null;
        this.value = value;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Validates all the function calls in this quoted constants.
     * Since a quoted constant contains no function calls,
     * this method does nothing.
     */
    @Override
    void validateFunctionCalls() {
    }

    /**
     * Sets the indices of all the variables in this quoted constant.
     * Since a quoted constant contains no variables, this method does nothing.
     */
    @Override
    void setVariableIndices(Map<Acl2Symbol, Integer> indices) {
    }

    /**
     * Evaluates this ACL2 quoted constant to an ACL2 value,
     * with respect to the given binding of values to variable indices.
     * The result is the value of the quoted constant,
     * which is actually independent from the bindings.
     * This evaluation never fails.
     */
    @Override
    Acl2Value eval(Acl2Value[] binding) {
        assert binding != null;
        return this.value;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 quoted constant is equal to the argument object.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2QuotedConstant)) return false;
        Acl2QuotedConstant that = (Acl2QuotedConstant) o;
        return value.equals(that.value);
    }

    /**
     * Returns a hash code for this ACL2 quoted constant.
     */
    @Override
    public int hashCode() {
        return value.hashCode();
    }

    /**
     * Compares this ACL2 quoted constant with the argument ACL2 term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then quoted constants, ordered according to their underlying symbols;
     * finally applications, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @return a negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Term o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2Variable)
            // quoted constants are greater than variables:
            return 1;
        if (o instanceof Acl2QuotedConstant) {
            Acl2QuotedConstant that = (Acl2QuotedConstant) o;
            return this.value.compareTo(that.value);
        }
        // quoted constants are less than applications:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 quoted constant.
     */
    @Override
    public String toString() {
        return this.value.toString();
    }

    /**
     * Returns an ACL2 quoted quoted constant with the given ACL2 value.
     *
     * @throws IllegalArgumentException if value is null
     */
    public static Acl2QuotedConstant make(Acl2Value value) {
        if (value == null)
            throw new IllegalArgumentException("Null value.");
        else
            return new Acl2QuotedConstant(value);
    }
}
