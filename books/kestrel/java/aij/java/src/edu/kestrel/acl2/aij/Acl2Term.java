/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Representation of ACL2 terms, in translated form.
 * <p>
 * They consist of
 * quoted constants (subclass {@link Acl2QuotedConstant},
 * variables (subclass {@link Acl2Variable},
 * and function applications {@link Acl2FunctionApplication}.
 * No other subclasses can be defined outside this package
 * because this class provides no public or protected constructors.
 * <p>
 * Instances of this class are immutable.
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
     * Evaluates this ACL2 term to an ACL2 value,
     * with respect to the given binding of values to variable symbols.
     *
     * @throws Acl2EvaluationException if evaluation fails
     */
    abstract Acl2Value eval(Map<Acl2Symbol, Acl2Value> bindings)
            throws Acl2EvaluationException;

    //////////////////////////////////////// public members:

    /**
     * Compares this ACL2 term with the argument ACL2 term for order.
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
    public abstract int compareTo(Acl2Term o);
}
