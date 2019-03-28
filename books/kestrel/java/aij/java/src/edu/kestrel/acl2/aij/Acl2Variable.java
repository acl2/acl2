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

    /**
     * Index of this variable.
     * This is set, once, to a non-negative integer
     * by {@link #setVariableIndices(Map)}.
     * The purpose of this index is just to optimize the evaluation of terms,
     * so that bindings of values to variables can be represented as
     * arrays instead of maps, for faster access:
     * see {@link Acl2Term#eval(Acl2Value[])}.
     */
    private int index = -1;

    //////////////////////////////////////// package-private members:

    /**
     * Validates all the function calls in this variable.
     * Since a variable contains no function calls, this method does nothing.
     */
    @Override
    void validateFunctionCalls() {
    }

    /**
     * Sets the index of this variable,
     * according to the supplied map from variable symbols to indices.
     *
     * @throws IllegalArgumentException if this variable
     *                                  is not a key of the map,
     *                                  or if the value associated with it
     *                                  is negative
     * @throws IllegalStateException    if this variable index is already set
     */
    @Override
    void setVariableIndices(Map<Acl2Symbol, Integer> indices) {
        if (this.index != -1)
            throw new IllegalStateException
                    ("Index of variable " + this.name
                            + " already set to " + this.index + ".");
        Integer index = indices.get(this.name);
        if (index == null)
            throw new IllegalArgumentException
                    ("Variable " + this.name + " has no associated index.");
        if (index < 0)
            throw new IllegalArgumentException
                    ("Negative index " + index
                            + "associated to variable " + this.name + ".");
        this.index = index;
    }

    /**
     * Evaluates this ACL2 variable to an ACL2 value,
     * with respect to the given binding of values to variable symbols.
     * The result is the value bound to the symbol of the variable.
     * Since variable indices are set
     * when a function definition is added to the environment
     * and terms are evaluated after that,
     * the conditions in the assertion below should hold.
     * This evaluation never fails.
     */
    @Override
    Acl2Value eval(Acl2Value[] binding) {
        assert binding != null &&
                this.index >= 0 &&
                this.index < binding.length;
        return binding[this.index];
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
