/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 functions in ACL2 terms.
 * These are named functions (subclass {@link Acl2NamedFunction})
 * and lambda expressions (subclass {@link Acl2LambdaExpression}).
 */
public abstract class Acl2Function implements Comparable<Acl2Function> {

    //////////////////////////////////////// package-private members:

    /**
     * Applies this ACL2 function to the given ACL2 values.
     *
     * @throws Acl2EvaluationException if the application fails
     */
    abstract Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException;

    /**
     * Checks if this function is the {@code if} ACL2 function.
     *
     * @throws IllegalStateException if the "ACL2" package is not defined yet
     */
    abstract boolean isIf();

    //////////////////////////////////////// public members:

    /**
     * Compares this ACL2 function with the argument ACL2 function for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.
     *
     * @return a negative integer, zero, or a positive integer as
     * this function is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public abstract int compareTo(Acl2Function o);
}
