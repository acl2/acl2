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
     * Prevents the creation of subclasses outside this package.
     * Since this constructor is package-private,
     * it inhibits the generation of the default public constructor.
     */
    Acl2Function() {
    }

    /**
     * Validates all the function calls in this function.
     * See the overriding methods for details.
     *
     * @throws IllegalStateException if validation fails
     */
    abstract void validateFunctionCalls();

    /**
     * Returns the number of parameters of this function.
     *
     * @throws IllegalStateException if this is a defined function
     *                               without an actual definition yet
     */
    abstract int getArity();

    /**
     * Sets the indices of all the variables in this function.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @throws IllegalArgumentException if this function is malformed
     *                                  in a way that
     *                                  some valid index cannot be set
     * @throws IllegalStateException    if some index is already set
     */
    abstract void setVariableIndices();

    /**
     * Checks if this function is the {@code if} ACL2 primitive function.
     *
     * @throws IllegalStateException if the "ACL2" package is not defined yet
     */
    abstract boolean isIf();

    /**
     * Checks if this function is the {@code or} ACL2 "pseudo-function".
     * This is not an ACL2 notion; it is an AIJ notion.
     * See {@link Acl2FunctionApplication#eval(Acl2Value[])} for details.
     */
    abstract boolean isOr();

    /**
     * Applies this ACL2 function to the given ACL2 values.
     *
     * @throws Acl2EvaluationException if the application fails
     */
    abstract Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException;

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
