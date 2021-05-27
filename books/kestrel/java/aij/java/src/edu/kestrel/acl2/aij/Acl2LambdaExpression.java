/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Representation of ACL2 lambda expressions in terms.
 * These are in translated form.
 */
public final class Acl2LambdaExpression extends Acl2Function {

    //////////////////////////////////////// private members:

    /**
     * Formal parameters of this lambda expression.
     * Invariant: not null.
     */
    private final Acl2Symbol[] parameters;

    /**
     * Body of this lambda expression.
     * Invariant: not null.
     */
    private final Acl2Term body;

    /**
     * Constructs a lambda expression with the given formal parameters and body.
     *
     * @param parameters The formal parameters of the lambda expression.
     *                   Invariant: not nulll.
     * @param body       The body of the lambda expression.
     *                   Invariant: not null.
     */
    private Acl2LambdaExpression(Acl2Symbol[] parameters, Acl2Term body) {
        this.parameters = parameters;
        this.body = body;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Returns the number of parameters of this lambda expression.
     *
     * @return The number of parameters of this lambda expression.
     */
    @Override
    int getArity() {
        return this.parameters.length;
    }

    /**
     * Validates all the function calls in this lambda expression.
     * We recursively validate the function calls in the body.
     *
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    @Override
    void validateFunctionCalls() {
        body.validateFunctionCalls();
    }

    /**
     * Sets the indices of all the variables in this lambda expression.
     * The index of each free variable in the body of this lambda expression
     * is set to the zero-based position of the variable symbol
     * in the formal parameters of this lambda expression.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @throws IllegalArgumentException If some index is already set,
     *                                  or this lambda expression
     *                                  contains some variable
     *                                  that is not bound in the formals of
     *                                  its smallest enclosing
     *                                  lambda expression.
     */
    @Override
    void setVariableIndices() {
        int len = parameters.length;
        Map<Acl2Symbol, Integer> indices = new HashMap<>(len);
        for (int i = 0; i < len; ++i)
            indices.put(parameters[i], i);
        body.setVariableIndices(indices);
    }

    /**
     * Applies this lambda expression to the given values.
     * Since lambda expressions in well-formed terms are closed,
     * the body of the lambda expression is evaluated
     * with respect to a binding of the given values
     * to the formal parameters of the lambda expression.
     *
     * @param values The actual arguments to pass to the function.
     *               Invariant: not null, no null elements.
     * @return The result of the lambda expression on the given arguments.
     * @throws Acl2UndefinedPackageException If a call of {@code pkg-imports}
     *                                       or {@code pkg-witness} fails.
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2UndefinedPackageException {
        return this.body.eval(values);
    }

    /**
     * Checks if this lambda expression is
     * the {@code if} ACL2 primitive function.
     * This is never the case, because {@code if} is represented as
     * an instance of {@link Acl2NamedFunction}.
     *
     * @return {@code false}.
     */
    @Override
    boolean isIf() {
        return false;
    }

    /**
     * Checks if this lambda expression is
     * the {@code or} ACL2 "pseudo-function".
     * This is never the case, because {@code or} is represented as
     * an instance of {@link Acl2NamedFunction}.
     */
    @Override
    boolean isOr() {
        return false;
    }

    /**
     * Returns the formal parameters of this lambda expression.
     *
     * @return The formal parameters of this lambda expression.
     */
    Acl2Symbol[] getParameters() {
        return this.parameters;
    }

    /**
     * Returns the body of this lambda expression.
     *
     * @return The body of this lambda expression.
     */
    Acl2Term getBody() {
        return this.body;
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this lambda expression with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this lambda expression with.
     * @return {@code true} if the object is equal to this lambda expression,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2LambdaExpression)) return false;
        Acl2LambdaExpression that = (Acl2LambdaExpression) o;
        if (!Arrays.equals(parameters, that.parameters)) return false;
        return body.equals(that.body);
    }

    /**
     * Returns a hash code for this lambda expression.
     *
     * @return The hash code for this lambda expression.
     */
    @Override
    public int hashCode() {
        int result = Arrays.hashCode(parameters);
        result = 31 * result + body.hashCode();
        return result;
    }

    /**
     * Compares this lambda expression with the argument function for order.
     * This order consists of:
     * first named functions, ordered according to their underlying symbols;
     * then lambda expressions, ordered lexicographically according to
     * their list of formal parameters followed by their body.
     *
     * @param o The function to compare this lambda expression with.
     * @return A negative integer, zero, or a positive integer as this
     * lambda expression is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Function o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2LambdaExpression) {
            Acl2LambdaExpression that = (Acl2LambdaExpression) o;
            int thisLen = this.parameters.length;
            int thatLen = that.parameters.length;
            int minLen = Integer.min(thisLen, thatLen);
            for (int i = 0; i < minLen; ++i) {
                int cmp = this.parameters[i].compareTo(that.parameters[i]);
                if (cmp != 0)
                    return cmp;
            }
            if (thisLen > minLen)
                return 1;
            else if (thatLen > minLen)
                return -1;
            else
                return this.body.compareTo(that.body);
        }
        // lambda expressions are greater than named functions:
        return 1;
    }

    /**
     * Returns a printable representation of this lambda expression.
     *
     * @return A printable representation of this lambda expression.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder("(LAMBDA (");
        int len = this.parameters.length;
        for (int i = 0; i < len - 1; ++i)
            result.append(this.parameters[i]).append(" ");
        if (len > 0)
            result.append(this.parameters[len - 1]);
        result.append(") ").append(this.body).append(")");
        return new String(result);
    }

    /**
     * Returns a lambda expression with the given formal parameters and body.
     *
     * @param parameters The formal parameters of the lambda expression.
     * @param body       The body of the lambda expression.
     * @return The lambda expression.
     * @throws IllegalArgumentException If {@code parameter} is null,
     *                                  or any of its elements is null,
     *                                  or {@code body} is null.
     */
    public static Acl2LambdaExpression make(Acl2Symbol[] parameters,
                                            Acl2Term body) {
        if (parameters == null)
            throw new IllegalArgumentException("Null parameters.");
        for (int i = 0; i < parameters.length; ++i)
            if (parameters[i] == null)
                throw new IllegalArgumentException
                        ("Null parameter at index " + i + ".");
        if (body == null)
            throw new IllegalArgumentException("Null body.");
        return new Acl2LambdaExpression(parameters, body);
    }

}
