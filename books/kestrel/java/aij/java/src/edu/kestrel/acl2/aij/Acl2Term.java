/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 terms, in translated form.
 * They consist of
 * quoted constants (subclass {@link Acl2QuotedConstant},
 * variables (subclass {@link Acl2Variable},
 * and function calls {@link Acl2FunctionCall}.
 * No other subclasses can be defined outside this package
 * because this class provides no public or protected constructors.
 */
public abstract class Acl2Term implements Comparable<Acl2Term> {

    //////////////////////////////////////// package-private members:

    /**
     * Prevents the creation of subclasses outside this package.
     * Since this constructor is package-private,
     * it inhibits the generation of the default public constructor.
     */
    Acl2Term() {
    }

    /**
     * Validates all the function calls in this term.
     * See the implementing methods for details.
     *
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    abstract void validateFunctionCalls();

    /**
     * Sets the indices of all the variables in this term,
     * starting with the supplied map from variable symbols to indices.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @param indices Map from variable symbols to indices.
     *                Invariants:
     *                not null,
     *                no null keys,
     *                no null values,
     *                no negative values.
     * @throws IllegalArgumentException If some index is already set,
     *                                  or this term contains some variable
     *                                  that is not in the body
     *                                  of any lambda expression
     *                                  and that is not a key of the map,
     *                                  or this term contains some variable
     *                                  that is in the body
     *                                  of some lambda expression
     *                                  and that is not bound in the formals of
     *                                  its smallest enclosing
     *                                  lambda expression.
     */
    abstract void setVariableIndices(Map<Acl2Symbol, Integer> indices);

    /**
     * Evaluates this term to a value,
     * with respect to the given binding of variable indices to values.
     * The binding is specified as an array of values:
     * the variable with index {@code i}
     * is bound to the value {@code bindings[i]}.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @param binding The binding of variable indices to values.
     *                Invariants: not null, not null elements.
     * @return The value that results from the evaluation.
     * @throws Acl2UndefinedPackageException If a call of {@code pkg-imports}
     *                                       or {@code pkg-witness} fails.
     */
    abstract Acl2Value eval(Acl2Value[] binding)
            throws Acl2UndefinedPackageException;

    //////////////////////////////////////// public members:

    /**
     * Compares this term with the argument term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then quoted constants, ordered according to their underlying symbols;
     * finally function calls, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @param o The term to compare this term with.
     * @return Aa negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public abstract int compareTo(Acl2Term o);

}
