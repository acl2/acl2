/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 variables.
 * These are translated terms that are ACL2 symbols.
 */
public final class Acl2Variable extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * Symbol that the variable consists of.
     * This is never {@code null}.
     */
    private final Acl2Symbol name;

    /**
     * Constructs an ACL2 variable from
     * the ACL2 symbol that the variable consists of.
     */
    private Acl2Variable(Acl2Symbol name) {
        assert name != null;
        this.name = name;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Evaluates this ACL2 variable to an ACL2 value,
     * with respect to the given binding of values to variable symbols.
     * The result is the value bound to the symbol of the variable.
     *
     * @throws Acl2EvaluationException if bindings does not contain
     *                                 the symbol of this variable
     */
    @Override
    Acl2Value eval(Map<Acl2Symbol, Acl2Value> bindings)
            throws Acl2EvaluationException {
        assert bindings != null;
        Acl2Value result = bindings.get(this.name);
        if (result == null)
            throw new Acl2EvaluationException
                    ("Unbound variable: '" + this.name + "'.");
        else
            return result;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 variable is equal to the argument object.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Variable)) return false;
        Acl2Variable that = (Acl2Variable) o;
        return name.equals(that.name);
    }

    /**
     * Returns a hash code for this ACL2 variable.
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }

    /**
     * Compares this ACL2 variable with the argument ACL2 term for order.
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
        if (o instanceof Acl2Variable) {
            Acl2Variable that = (Acl2Variable) o;
            return this.name.compareTo(that.name);
        }
        // variables are less than quoted constants and applications:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 variable.
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns an ACL2 variable with the given ACL2 name.
     *
     * @throws IllegalArgumentException if name is null
     */
    public static Acl2Variable make(Acl2Symbol name) {
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        else
            return new Acl2Variable(name);
    }
}
