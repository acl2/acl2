/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 functions in terms.
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
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    abstract void validateFunctionCalls();

    /**
     * Returns the number of parameters of this function.
     *
     * @return The number of parameters of this function.
     * If the function is a defined one but it has no definition yet,
     * -1 is returned.
     */
    abstract int getArity();

    /**
     * Sets the indices of all the variables in this function.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @throws IllegalArgumentException If some index is already set,
     *                                  or this function contains some variable
     *                                  that is in the body
     *                                  of some lambda expression
     *                                  and that is not bound in the formals of
     *                                  its smallest enclosing
     *                                  lambda expression.
     */
    abstract void setVariableIndices();

    /**
     * Checks if this function is the {@code if} ACL2 primitive function.
     *
     * @return {@code true} if this function is {@code if},
     * otherwise {@code false}.
     */
    abstract boolean isIf();

    /**
     * Checks if this function is the {@code or} ACL2 "pseudo-function".
     * This is not an ACL2 notion; it is an AIJ notion.
     * See {@link Acl2FunctionCall#eval(Acl2Value[])} for details.
     *
     * @return {@code true} if this function is {@code or},
     * otherwise {@code false}.
     */
    abstract boolean isOr();

    /**
     * Applies this function to the given values.
     *
     * @param values The actual arguments to pass to the function.
     *               Invariants: not null, no null elements.
     * @return The result of the function on the given arguments.
     * @throws Acl2UndefinedPackageException If a call of {@code pkg-imports}
     *                                       or {@code pkg-witness} fails.
     */
    abstract Acl2Value apply(Acl2Value[] values) throws Acl2UndefinedPackageException;

    //////////////////////////////////////// public members:

    /**
     * Compares this function with the argument function for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.
     *
     * @return A negative integer, zero, or a positive integer as
     * this function is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public abstract int compareTo(Acl2Function o);

}
