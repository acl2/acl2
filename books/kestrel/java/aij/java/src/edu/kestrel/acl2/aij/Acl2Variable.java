/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 variables.
 * These are translated terms that are symbols.
 */
public final class Acl2Variable extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * Name of the variable.
     * Invariant: not null.
     */
    private final Acl2Symbol name;

    /**
     * Constructs a variable with the given name.
     *
     * @param name The symbol of the variable.
     */
    private Acl2Variable(Acl2Symbol name) {
        this.name = name;
    }

    /**
     * Index of this variable.
     * This is set, once, to a non-negative integer
     * by {@link #setVariableIndices(Map)}.
     * The purpose of this index is just to optimize the evaluation of terms,
     * so that bindings of variables to values can be represented as
     * arrays instead of maps, for faster access:
     * see {@link Acl2Term#eval(Acl2Value[])}.
     * Since variables with the same name may have different indices
     * (when they occur in different terms),
     * instances of this class must not be interned based on their names.
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
     * @param indices Map from variable symbols to indices.
     *                Invariants:
     *                not null,
     *                no null keys,
     *                no null values,
     *                no negative values.
     * @throws IllegalArgumentException If this variable index is already set,
     *                                  or this variable is not
     *                                  a key of the map.
     */
    @Override
    void setVariableIndices(Map<Acl2Symbol, Integer> indices) {
        if (this.index != -1)
            throw new IllegalArgumentException
                    ("Index of variable " + this.name
                            + " already set to " + this.index + ".");
        Integer index = indices.get(this.name);
        if (index == null)
            throw new IllegalArgumentException
                    ("Variable " + this.name + " has no associated index.");
        this.index = index;
    }

    /**
     * Evaluates this variable to a value,
     * with respect to the given binding of variable indices to values.
     * The result is the value bound to the symbol of the variable.
     * This evaluation never fails.
     *
     * @param binding The binding of variable indices to values.
     *                Invariant: not null, no null elements.
     * @return The value that results from the evaluation.
     */
    @Override
    Acl2Value eval(Acl2Value[] binding) {
        return binding[this.index];
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this variable with the argument object for equality.
     *
     * @param o The object to compare this variable with.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Variable)) return false;
        Acl2Variable that = (Acl2Variable) o;
        return name.equals(that.name);
    }

    /**
     * Returns a hash code for this variable.
     *
     * @return The hash code for this variable.
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }

    /**
     * Compares this variable with the argument term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then quoted constants, ordered according to their underlying symbols;
     * finally function calls, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @param o The term to compare this variable with.
     * @return A negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Term o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2Variable) {
            Acl2Variable that = (Acl2Variable) o;
            return this.name.compareTo(that.name);
        }
        // variables are less than quoted constants and function calls:
        return -1;
    }

    /**
     * Returns a printable representation of this variable.
     *
     * @return A printable representation of this variable.
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns a variable with the given name.
     *
     * @param name The name of the variable.
     * @return The variable.
     * @throws IllegalArgumentException If {@code name} is null.
     */
    public static Acl2Variable make(Acl2Symbol name) {
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        else
            return new Acl2Variable(name);
    }

}
