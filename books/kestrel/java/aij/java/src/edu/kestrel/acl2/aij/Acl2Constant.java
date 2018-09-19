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
public final class Acl2Constant extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * ACL2 value of the constant.
     * This is never {@code null}.
     */
    private final Acl2Value value;

    /**
     * Constructs an ACL2 quoted constant from its value.
     */
    private Acl2Constant(Acl2Value value) {
        assert value != null;
        this.value = value;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Evaluates this ACL2 quoted constant to an ACL2 value,
     * with respect to the given binding of values to variable symbols.
     * The result is the value of the constant,
     * which is actually independent from the bindings.
     * This evaluation never fails.
     */
    @Override
    Acl2Value eval(Map<Acl2Symbol, Acl2Value> bindings) {
        assert bindings != null;
        return this.value;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 constant is equal to the argument object.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Constant)) return false;
        Acl2Constant that = (Acl2Constant) o;
        return value.equals(that.value);
    }

    /**
     * Returns a hash code for this ACL2 constant.
     */
    @Override
    public int hashCode() {
        return value.hashCode();
    }

    /**
     * Compares this ACL2 constant with the argument ACL2 term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then constants, ordered according to their underlying symbols;
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
            // constants are greater than variables:
            return 1;
        if (o instanceof Acl2Constant) {
            Acl2Constant that = (Acl2Constant) o;
            return this.value.compareTo(that.value);
        }
        // constants are less than applications:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 constant.
     * This is meant for printing;
     * it should be improved to return something non-confusing
     * when the constant includes "unusual" characters.
     */
    @Override
    public String toString() {
        return this.value.toString();
    }

    /**
     * Returns an ACL2 quoted constant with the given ACL2 value.
     *
     * @throws IllegalArgumentException if value is null
     */
    public static Acl2Constant make(Acl2Value value) {
        if (value == null)
            throw new IllegalArgumentException("Null value.");
        else
            return new Acl2Constant(value);
    }
}
