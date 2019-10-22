/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Arrays;
import java.util.Map;

/**
 * Representation of ACL2 function applications, in translated form.
 * These are translated terms of the form {@code (f arg1 ... argn)},
 * where {@code f} is a named function or lambda expression and {@code n >= 0}.
 */
public final class Acl2FunctionApplication extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * Function of this function application.
     * This is never {@code null}.
     */
    private final Acl2Function function;

    /**
     * Arguments of this function application.
     * This is never {@code null}.
     * It may be empty.
     */
    private final Acl2Term[] arguments;

    /**
     * Constructs a function application with the given function and arguments.
     *
     * @param function  The function of the function application.
     * @param arguments The arguments of the function application.
     */
    private Acl2FunctionApplication(Acl2Function function,
                                    Acl2Term[] arguments) {
        this.function = function;
        this.arguments = arguments;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Validates all the function calls in this function application.
     * We check that the number of arguments matches the arity;
     * this implicitly also checks that,
     * if the function is a defined function,
     * it has an actual definition.
     * We check not only this function application/call,
     * but also the function calls in the argument terms
     * and in the function itself (if the function is a lambda expression).
     *
     * @throws IllegalStateException If validation fails.
     */
    @Override
    void validateFunctionCalls() {
        function.validateFunctionCalls();
        for (int i = 0; i < arguments.length; ++i)
            arguments[i].validateFunctionCalls();
        int arity = function.getArity();
        if (arity != arguments.length)
            throw new IllegalStateException
                    ("The function " + function + ", which has arity " + arity
                            + ", is applied to " + arguments.length
                            + " arguments.");
    }

    /**
     * Sets the indices of all the variables in this function application,
     * starting with the supplied map from variable symbols to indices.
     * The supplied map is used for the argument terms.
     * The function is processed separately:
     * see {@link Acl2Function#setVariableIndices()}.
     * See {@link Acl2Variable} for more information about variable indices.
     *
     * @param indices Map from variable symbols to indices.
     * @throws IllegalArgumentException If the term or the map are malformed
     *                                  in a way that some index cannot be set.
     * @throws IllegalStateException    If some index is already set.
     */
    @Override
    void setVariableIndices(Map<Acl2Symbol, Integer> indices) {
        int len = arguments.length;
        for (int i = 0; i < len; ++i)
            arguments[i].setVariableIndices(indices);
        function.setVariableIndices();
    }

    /**
     * Evaluates this function application to a value,
     * with respect to the given binding of variable indices to values.
     * Unless the function is the function {@code if},
     * first the argument terms are evaluated,
     * and then the function is applied to them.
     * If instead the function is {@code if},
     * first the first argument is evaluated,
     * and then either the second or third one is evaluated,
     * based on the result of evaluating the first argument;
     * {@code if} is the only non-strict function in ACL2.
     * <p>
     * We handle calls to the ACL2 "pseudo-function" {@code or} specially.
     * In ACL2, {@code or} is a macro:
     * {@code (or a b)} expands to {@code (if a a b)},
     * which would cause {@code a} to be evaluated twice in a "naive" execution.
     * ACL2 relies on the underlying Common Lisp implementation
     * to optimize this situation and evaluate {@code a} just once.
     * In AIJ, {@code or} is treated like a non-strict primitive function,
     * which evaluates the first argument and returns its value
     * if it is not {@code nil},
     * and otherwise evaluates the second argument and returns its value.
     * This {@code or} pseudo-function can be viewed as
     * an optimized version of {@code if}
     * when test and "then" branch are the same.
     * Java code external to AIJ can use this {@code or} pseudo-function
     * to represent calls to the {@code or} macro,
     * or more in general calls of the form {@code (if a a b)}.
     * Note that the {@code acl2::or} symbol
     * can never appear in an ACL2 translated term,
     * because ACL2 prohibits the definition of functions
     * with names in the {@code "COMMON-LISP"} package;
     * thus, the use of this {@code or} pseudo-function in AIJ
     * can never interfere with other functions.
     *
     * @param binding The binding of variable indices to values.
     * @return The value that results from the evaluation.
     * @throws Acl2EvaluationException If a call of {@code pkg-imports}
     *                                 or {@code pkg-witness} fails.
     */
    @Override
    Acl2Value eval(Acl2Value[] binding) throws Acl2EvaluationException {
        if (function.isIf()) {
            Acl2Value test = arguments[0].eval(binding);
            if (test.equals(Acl2Symbol.NIL))
                return arguments[2].eval(binding);
            else
                return arguments[1].eval(binding);
        } else if (function.isOr()) {
            Acl2Value first = arguments[0].eval(binding);
            if (first.equals(Acl2Symbol.NIL))
                return arguments[1].eval(binding);
            else
                return first;
        } else {
            int len = arguments.length;
            Acl2Value[] argumentValues = new Acl2Value[len];
            for (int i = 0; i < len; ++i)
                argumentValues[i] = this.arguments[i].eval(binding);
            return this.function.apply(argumentValues);
        }
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this function application with the argument object for equality.
     *
     * @param o The object to compare this function application with.
     * @return {@code true} if the object is equal to this function application,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2FunctionApplication)) return false;
        Acl2FunctionApplication that = (Acl2FunctionApplication) o;
        if (!function.equals(that.function)) return false;
        return Arrays.equals(arguments, that.arguments);
    }

    /**
     * Returns a hash code for this function application.
     *
     * @return The hash code for this function application.
     */
    @Override
    public int hashCode() {
        int result = function.hashCode();
        result = 31 * result + Arrays.hashCode(arguments);
        return result;
    }

    /**
     * Compares this function application with the argument term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then quoted constants, ordered according to their underlying values;
     * finally applications, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @param o The term to compare this function application with.
     * @return A negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is {@code null}.
     */
    @Override
    public int compareTo(Acl2Term o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2FunctionApplication) {
            Acl2FunctionApplication that = (Acl2FunctionApplication) o;
            int funCmp = this.function.compareTo(that.function);
            if (funCmp != 0)
                return funCmp;
            int thisLen = this.arguments.length;
            int thatLen = that.arguments.length;
            int minLen = Integer.min(thisLen, thatLen);
            for (int i = 0; i < minLen; ++i) {
                int cmp = this.arguments[i].compareTo(that.arguments[i]);
                if (cmp != 0)
                    return cmp;
            }
            if (thisLen > minLen)
                return 1;
            else if (thatLen > minLen)
                return -1;
            else
                return 0;
        }
        // applications are greater than variables and quoted constants:
        return 1;
    }

    /**
     * Returns a printable representation of this function application.
     *
     * @return A printable representation of this function application.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder("(");
        result.append(this.function);
        int len = this.arguments.length;
        for (int i = 0; i < len; ++i)
            result.append(" ").append(this.arguments[i]);
        result.append(")");
        return new String(result);
    }

    /**
     * Returns a function application with the given function and arguments.
     *
     * @param function  The function of this function application.
     * @param arguments The arguments of this function application.
     * @return The function application.
     * @throws IllegalArgumentException If any arguments is {@code null}.
     */
    public static Acl2FunctionApplication make(Acl2Function function,
                                               Acl2Term[] arguments) {
        if (function == null)
            throw new IllegalArgumentException("Null function.");
        if (arguments == null)
            throw new IllegalArgumentException("Null arguments.");
        return new Acl2FunctionApplication(function, arguments);
    }

}
