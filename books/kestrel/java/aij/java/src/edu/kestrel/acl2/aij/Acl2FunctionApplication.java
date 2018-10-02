/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Arrays;
import java.util.Map;

/**
 * Representation of ACL2 function applications.
 * These are translated terms of the form {@code (f arg1 ... argn)},
 * where {@code f} is a named function or lambda expression and {@code n >= 0}.
 */
public final class Acl2FunctionApplication extends Acl2Term {

    //////////////////////////////////////// private members:

    /**
     * Function.
     * This is never {@code null}.
     */
    private final Acl2Function function;

    /**
     * Arguments.
     * This is never {@code null}.
     * But it may be empty.
     */
    private final Acl2Term[] arguments;

    /**
     * Constructs an application from its function and arguments.
     */
    private Acl2FunctionApplication(Acl2Function function,
                                    Acl2Term[] arguments) {
        assert function != null && arguments != null;
        this.function = function;
        this.arguments = arguments;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Evaluates this ACL2 function application to an ACL2 value,
     * with respect to the given binding of values to variable symbols.
     * Unless the function is the ACL2 function {@code if},
     * the argument terms are evaluated,
     * then the function is applied to them.
     * If instead the function is {@code if},
     * the first argument is evaluated first,
     * then either the second or third one,
     * based on the result of evaluating the first argument;
     * {@code if} is the only non-strict function in ACL2.
     *
     * @throws Acl2EvaluationException if the evaluation of an argument fails,
     *                                 or the application of
     *                                 the function or lambda expression fails
     */
    @Override
    Acl2Value eval(Map<Acl2Symbol, Acl2Value> bindings)
            throws Acl2EvaluationException {
        assert bindings != null;
        int len = arguments.length;
        if (function.isIf()) {
            if (len != 3) // this should never happen
                throw new Acl2EvaluationException
                        ("Called IF on " + len +
                                (len == 1 ? " argument." : " arguments."));
            Acl2Value test = arguments[0].eval(bindings);
            if (test.equals(Acl2Symbol.NIL))
                return arguments[2].eval(bindings);
            else
                return arguments[1].eval(bindings);
        } else {
            Acl2Value[] argumentValues = new Acl2Value[len];
            for (int i = 0; i < len; ++i)
                argumentValues[i] = this.arguments[i].eval(bindings);
            return this.function.apply(argumentValues);
        }
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 application is equal to the argument object.
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
     * Returns a hash code for this ACL2 application.
     */
    @Override
    public int hashCode() {
        int result = function.hashCode();
        result = 31 * result + Arrays.hashCode(arguments);
        return result;
    }

    /**
     * Compares this ACL2 application with the argument ACL2 term for order.
     * This is not the order on terms documented in the ACL2 manual.
     * Instead, this order consists of:
     * first variables, ordered according to their underlying symbols;
     * then constants, ordered according to their underlying values;
     * finally applications, ordered lexicographically according to
     * the function followed by the arguments.
     *
     * @return a negative integer, zero, or a positive integer as
     * this term is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
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
        // applications are greater than variables and constants:
        return 1;
    }

    /**
     * Returns a printable representation of this ACL2 application.
     * This is meant for printing;
     * it should be improved to return something non-confusing
     * when the function or arguments include "unusual" characters.
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
     * Returns an ACL2 application with the given function and arguments.
     *
     * @throws IllegalArgumentException if function or arguments is null
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
