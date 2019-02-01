/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 values.
 * <p>
 * They consist of
 * characters (subclass {@link Acl2Character}),
 * strings (subclass {@link Acl2String}),
 * symbols (subclass {@link Acl2Symbol}),
 * numbers (subclass {@link Acl2Number}),
 * and {@code cons} pairs (subclass {@link Acl2ConsPair}).
 * No other subclasses can be defined outside this package
 * because this class provides no public or protected constructors.
 * <p>
 * Instances of this class are immutable.
 * <p>
 * Unlike ACL2, which puts no firm limits on the size of values
 * (so long as there is memory available),
 * this Java representation has potentially lower limits:
 * <ul>
 * <li>
 * The length of ACL2 strings,
 * including the ones used for package and symbol names,
 * cannot exceed the maximum length of arrays
 * supported by the underlying Java implementation.
 * <li>
 * The magnitude of ACL2 integers,
 * including numerator and denominator of rational numbers
 * as well as real and imaginary part of complex numbers,
 * cannot exceed the maximum magnitude of big integers
 * (i.e. instances of {@link java.math.BigInteger})
 * supported by the underlying Java implementation.
 * </ul>
 * <p>
 * However, these limits are very large,
 * and the inability to create larger values
 * can be regarded as similar to running out of memory,
 * which may also happen in ACL2's underlying Lisp implementation.
 */
public abstract class Acl2Value implements Comparable<Acl2Value> {

    //////////////////////////////////////// package-private members:

    /**
     * Prevents the creation of subclasses outside this package.
     * Since this constructor is package-private,
     * it inhibits the generation of the default public constructor.
     */
    Acl2Value() {
    }

    /**
     * Supports the native implementation of
     * the {@code characterp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Character}.
     */
    Acl2Symbol characterp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code stringp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     */
    Acl2Symbol stringp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code symbolp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Symbol}.
     */
    Acl2Symbol symbolp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code integerp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Integer}.
     */
    Acl2Symbol integerp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code rationalp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Rational}.
     */
    Acl2Symbol rationalp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code complex-rationalp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ComplexRational}.
     */
    Acl2Symbol complexRationalp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code acl2-numberp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Number}.
     */
    Acl2Symbol acl2Numberp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code consp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     */
    Acl2Symbol consp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code char-code} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Character}.
     */
    Acl2Integer charCode() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code code-char} ACL2 function.
     * It returns the character with code 0 by default;
     * it is overridden in {@link Acl2Integer}.
     */
    Acl2Character codeChar() {
        return Acl2Character.CODE_0;
    }

    /**
     * Supports the native implementation of
     * the {@code coerce} ACL2 function,
     * when the second argument is {@code list}.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     */
    Acl2Value coerceToList() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code intern-in-package-of-symbol} ACL2 function,
     * where this ACL2 value is the first argument of that function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     */
    Acl2Symbol internInPackageOfSymbol(Acl2Value sym) {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code symbol-package-name} ACL2 function.
     * It returns the empty string by default;
     * it is overridden in {@link Acl2Symbol}.
     */
    Acl2String symbolPackageName() {
        return Acl2String.EMPTY;
    }

    /**
     * Supports the native implementation of
     * the {@code symbol-name} ACL2 function.
     * It returns the empty string by default;
     * it is overridden in {@link Acl2Symbol}.
     */
    Acl2String symbolName() {
        return Acl2String.EMPTY;
    }

    /**
     * Supports the native implementation of
     * the {@code pkg-imports} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     */
    Acl2Value pkgImports() throws Acl2EvaluationException {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code pkg-witness} ACL2 function.
     * Since this function treats an argument that is not an ACL2 string
     * as the ACL2 string "ACL2",
     * the default implementation of this method
     * invokes its overriding method on the ACL2 string "ACL2".
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     * @throws IllegalStateException   if the package witness is not set yet
     */
    Acl2Value pkgWitness() throws Acl2EvaluationException {
        return Acl2String.ACL2.pkgWitness();
    }

    /**
     * Supports the native implementation of
     * the {@code unary--} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational} and {@link Acl2ComplexRational}.
     */
    Acl2Number negate() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code unary-/} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational} and {@link Acl2ComplexRational}.
     */
    Acl2Number reciprocate() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code binary-+} ACL2 function.
     * It returns the result of coercing the argument to a number by default;
     * it is overridden in
     * {@link Acl2Integer}, {@link Acl2Ratio}, and {@link Acl2ComplexRational}.
     */
    Acl2Number add(Acl2Value other) {
        return other.fix();
    }

    /**
     * Supports the native implementation of
     * the {@code binary-*} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Integer}, {@link Acl2Ratio}, and {@link Acl2ComplexRational}.
     */
    Acl2Number multiply(Acl2Value other) {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code realpart} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     */
    Acl2Rational realpart() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code imagpart} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     */
    Acl2Rational imagpart() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code numerator} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     */
    Acl2Integer numerator() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code denominator} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     */
    Acl2Integer denominator() {
        return Acl2Integer.ZERO;
    }

    /**
     * Supports the native implementation of
     * the {@code car} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     */
    Acl2Value car() {
        return Acl2Symbol.NIL;
    }

    /**
     * Supports the native implementation of
     * the {@code cdr} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     */
    Acl2Value cdr() {
        return Acl2Symbol.NIL;
    }

    /**
     * Coerce this ACL2 value to an ACL2 number.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     * This is consistent with the {@code fix} ACL2 function.
     */
    Acl2Number fix() {
        return Acl2Integer.ZERO;
    }

    /**
     * Coerce this ACL2 value to an ACL2 rational.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     * This is consistent with the {@code rfix} ACL2 function.
     */
    Acl2Rational rfix() {
        return Acl2Integer.ZERO;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 value is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     * This method is abstract and overrides {@link Object#equals(Object)},
     * thus forcing the subclasses to provide an implementation.
     */
    @Override
    public abstract boolean equals(Object o);

    /**
     * Compares this ACL2 value with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public abstract int compareTo(Acl2Value o);
}
