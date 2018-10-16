/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 named functions in ACL2 terms.
 * These are just the symbols that name the functions.
 */
public final class Acl2NamedFunction extends Acl2Function {

    //////////////////////////////////////// private members:

    /**
     * Name of this function.
     * This is never {@code null}.
     */
    private final Acl2Symbol name;

    /**
     * Constructs an ACL2 named function from its name.
     */
    private Acl2NamedFunction(Acl2Symbol name) {
        assert name != null;
        this.name = name;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Applies this ACL2 named function to the given ACL2 values.
     * The function is called on the given values;
     * see {@link Acl2Environment#call(Acl2Symbol, Acl2Value[])}.
     *
     * @throws Acl2EvaluationException if the call to this function fails
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException {
        assert values != null;
        for (Acl2Value value : values) assert value != null;
        return Acl2Environment.call(this.name, values);
    }

    /**
     * Checks if this named function is the {@code if} ACL2 function.
     */
    @Override
    boolean isIf() {
        return name.equals(Acl2Symbol.IF);
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 named function is equal to the argument object.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2NamedFunction)) return false;
        Acl2NamedFunction that = (Acl2NamedFunction) o;
        return name.equals(that.name);
    }

    /**
     * Returns a hash code for this ACL2 named function.
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }

    /**
     * Compares this ACL2 named function with the argument ACL2 function
     * for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.).
     *
     * @return a negative integer, zero, or a positive integer as
     * this function is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Function o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2NamedFunction) {
            Acl2NamedFunction that = (Acl2NamedFunction) o;
            return this.name.compareTo(that.name);
        }
        // named functions are less than lambda expressions:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 named function.
     * This is meant for printing;
     * it should be improved to return something non-confusing
     * when the function name includes "unusual" characters.
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns an ACL2 named function with the given name.
     *
     * @throws IllegalArgumentException if name is null
     */
    public static Acl2NamedFunction make(Acl2Symbol name) {
        if (name == null)
            throw new IllegalArgumentException("Null name.");
        else
            return new Acl2NamedFunction(name);
    }
}
