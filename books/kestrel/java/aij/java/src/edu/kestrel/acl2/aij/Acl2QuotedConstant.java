/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 quoted constants, in translated form.
 * These are translated terms of the form {@code (quote ...)}.
 */
public final class Acl2QuotedConstant extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * Value of the quoted constant.
     * Invariant: not null.
     */
    private final Acl2Value value;

    /**
     * Constructs an quoted constant with the given value.
     *
     * @param value The value of the quoted constant.
     *              Invariant: not null.
     */
    private Acl2QuotedConstant(Acl2Value value) {
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
     * Sets the indices of all the variables in this quoted constant,
     * starting with the supplied map from variable symbols to indices.
     * Since a quoted constant contains no variables, this method does nothing.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @param indices Map from variable symbols to indices.
     *                Invariants:
     *                not null,
     *                no null keys,
     *                no null values,
     *                no negative values.
     */
    @Override
    void setVariableIndices(Map<Acl2Symbol, Integer> indices) {
    }

    /**
     * Evaluates this quoted constant to a value,
     * with respect to the given binding of variable indices to values.
     * The result is the value of the quoted constant,
     * which is actually independent from the bindings.
     * This evaluation never fails.
     *
     * @param binding The binding of variable indices to values.
     *                Invariants:
     *                not null,
     *                no null keys,
     *                no null values,
     *                no negative values.
     * @return The value that results from evaluation.
     */
    @Override
    Acl2Value eval(Acl2Value[] binding) {
        return this.value;
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this quoted constant with the argument object for equality.
     *
     * @param o The object to compare this quoted constant with.
     * @return {@code true} if the object is equal to this quoted constant,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2QuotedConstant)) return false;
        Acl2QuotedConstant that = (Acl2QuotedConstant) o;
        return value.equals(that.value);
    }

    /**
     * Returns a hash code for this quoted constant.
     *
     * @return The hash code for this quoted constant.
     */
    @Override
    public int hashCode() {
        return value.hashCode();
    }

    /**
     * Compares this quoted constant with the argument term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then quoted constants, ordered according to their underlying symbols;
     * finally function calls, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @param o The term to compare this quoted constant with.
     * @return A negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
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
        // quoted constants are less than function calls:
        return -1;
    }

    /**
     * Returns a printable representation of this quoted constant.
     *
     * @return A printable representation of this quoted constant.
     */
    @Override
    public String toString() {
        return this.value.toString();
    }

    /**
     * Returns a quoted quoted constant with the given value.
     *
     * @param value The value of the quoted constant.
     * @return The quoted constant.
     * @throws IllegalArgumentException If {@code value} is null.
     */
    public static Acl2QuotedConstant make(Acl2Value value) {
        if (value == null)
            throw new IllegalArgumentException("Null value.");
        else
            return new Acl2QuotedConstant(value);
    }

}
