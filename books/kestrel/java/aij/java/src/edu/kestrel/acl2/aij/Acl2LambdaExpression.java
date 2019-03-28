/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Representation of ACL2 lambda expressions in ACL2 terms.
 * These are in translated form.
 */
public final class Acl2LambdaExpression extends Acl2Function {

    //////////////////////////////////////// private members:

    /**
     * Formal parameter of this ACL2 lambda expression.
     * This is never {@code null}.
     */
    private final Acl2Symbol[] parameters;

    /**
     * Body of this ACL2 lambda expression.
     * This is never {@code null}.
     */
    private final Acl2Term body;

    /**
     * Constructs an ACL2 lambda expression from its formal parameters and body.
     */
    private Acl2LambdaExpression(Acl2Symbol[] parameters, Acl2Term body) {
        assert parameters != null && body != null;
        this.parameters = parameters;
        this.body = body;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Returns the number of parameters of this lambda expression.
     */
    @Override
    int getArity() {
        return this.parameters.length;
    }

    /**
     * Sets the indices of all the variables in this lambda expression.
     * The index of each free variable in the body of this lambda expression
     * is set to the zero-based position of the variable symbol
     * in the parameters of this lambda expression.
     *
     * @throws IllegalArgumentException if this function is malformed
     *                                  in a way that
     *                                  some valid index cannot be set
     * @throws IllegalStateException    if some index is already set
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
     * Applies this ACL2 lambda expression to the given ACL2 values.
     * Since lambda expressions in well-formed ACL2 terms are closed,
     * the body of the lambda expression is evaluated
     * with respect to a binding of the given values
     * to the formal parameters of the lambda expression.
     *
     * @throws Acl2EvaluationException if values.length differs from
     *                                 the arity of the lambda expression,
     *                                 or the evaluation of the body fails
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException {
        assert values != null;
        for (Acl2Value value : values) assert value != null;
        int len = values.length;
        if (this.parameters.length != len)
            throw new Acl2EvaluationException
                    ("Called "
                            + this.parameters.length
                            + "-ary lambda expression on "
                            + len
                            + (len == 1 ? " argument." : " arguments."));
        return this.body.eval(values);
    }

    /**
     * Checks if this lambda expression is
     * the {@code if} ACL2 primitive function.
     * This is never the case,
     * because {@code if} is represented as a {@link Acl2NamedFunction}.
     */
    @Override
    boolean isIf() {
        return false;
    }

    /**
     * Checks if this lambda expression is
     * the {@code or} ACL2 "pseudo-function".
     * This is never the case,
     * because {@code or} is represented as a {@link Acl2NamedFunction}.
     */
    @Override
    boolean isOr() {
        return false;
    }

    /**
     * Returns the parameters of this lambda expression.
     */
    Acl2Symbol[] getParameters() {
        return this.parameters;
    }

    /**
     * Returns the body of this lambda expression.
     */
    Acl2Term getBody() {
        return this.body;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 lambda expression is equal to the argument object.
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
     * Returns a hash code for this ACL2 lambda expression.
     */
    @Override
    public int hashCode() {
        int result = Arrays.hashCode(parameters);
        result = 31 * result + body.hashCode();
        return result;
    }

    /**
     * Compares this ACL2 lambda expression with the argument ACL2 function
     * for order.
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
     * Returns a printable representation of this ACL2 lambda expression.
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
     * Returns an ACL2 lambda expression
     * with the given ACL2 symbols as formal parameters
     * and the given ACL2 term as body.
     *
     * @throws IllegalArgumentException if parameters or body is null
     */
    public static Acl2LambdaExpression make(Acl2Symbol[] parameters,
                                            Acl2Term body) {
        if (parameters == null)
            throw new IllegalArgumentException("Null parameters.");
        if (body == null)
            throw new IllegalArgumentException("Null body.");
        return new Acl2LambdaExpression(parameters, body);
    }
}
