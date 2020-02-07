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
 * The length of strings,
 * including the ones used for package and symbol names,
 * cannot exceed the maximum length of arrays
 * supported by the underlying Java implementation.
 * <li>
 * The magnitude of integers,
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
     * Checks if this value is a character,
     * consistently with the {@code characterp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Character}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol characterp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a string,
     * consistently with the {@code stringp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol stringp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a symbol,
     * consistently with the {@code symbolp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Symbol}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol symbolp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a integer,
     * consistently with the {@code integerp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Integer}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol integerp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a rational,
     * consistently with the {@code rationalp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Rational}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol rationalp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a complex rational,
     * consistently with the {@code complex-rationalp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ComplexRational}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol complexRationalp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a number,
     * consistently with the {@code acl2-numberp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Number}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol acl2Numberp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Checks if this value is a {@code cons} pair,
     * consistently with the {@code consp} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     *
     * @return The symbol (@code t} or {@code nil}.
     */
    Acl2Symbol consp() {
        return Acl2Symbol.NIL;
    }

    /**
     * Returns the integer code of this value,
     * consistently with the {@code char-code} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Character}.
     *
     * @return The integer code.
     */
    Acl2Integer charCode() {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the character of this value,
     * consistently with the {@code code-char} ACL2 function.
     * It returns the character with code 0 by default;
     * it is overridden in {@link Acl2Integer}.
     *
     * @return The character.
     */
    Acl2Character codeChar() {
        return Acl2Character.CODE_0;
    }

    /**
     * Coerces this value to a list,
     * consistently with the {@code coerce} ACL2 function
     * when the second argument is {@code list}.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     *
     * @return The list.
     */
    Acl2Value coerceToList() {
        return Acl2Symbol.NIL;
    }

    /**
     * Coerces this value to a string,
     * consistently with the {@code coerce} ACL2 function
     * when the second argument is not {@code list}.
     * It returns the empty string by default;
     * it is overwritten in {@link Acl2ConsPair}.
     *
     * @return The string.
     */
    Acl2String coerceToString() {
        return Acl2String.EMPTY;
    }

    /**
     * Interns this value in the package of the argument value,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this value is the first argument of that function
     * and the argument value is the second argument of that function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     *
     * @param sym A symbol of the package where to intern
     *            the symbol named by this value.
     * @return The interned symbol.
     */
    Acl2Symbol internThisInPackageOf(Acl2Value sym) {
        return Acl2Symbol.NIL;
    }

    /**
     * Interns the argument string in the package of this value,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this value is the second argument of that function
     * and the argument value is the first argument of that function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2Symbol}.
     *
     * @param str The name of the symbol to intern.
     * @return The interned symbol.
     */
    Acl2Symbol internInPackageOfThis(Acl2String str) {
        return Acl2Symbol.NIL;
    }

    /**
     * Returns the symbol package name of this value,
     * consistently with the {@code symbol-package-name} ACL2 function.
     * It returns the empty string by default;
     * it is overridden in {@link Acl2Symbol}.
     *
     * @return The symbol package name.
     */
    Acl2String symbolPackageName() {
        return Acl2String.EMPTY;
    }

    /**
     * Returns the symbol name of this value,
     * consistently with the {@code symbol-name} ACL2 function.
     * It returns the empty string by default;
     * it is overridden in {@link Acl2Symbol}.
     *
     * @return The symbol name.
     */
    Acl2String symbolName() {
        return Acl2String.EMPTY;
    }

    /**
     * Returns the list of symbols imported by the package named by this value,
     * consistently with the {@code pkg-imports} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2String}.
     *
     * @return The list of imported symbols.
     * @throws Acl2UndefinedPackageException If the package name is invalid
     *                                       or the package is not defined.
     */
    Acl2Value pkgImports() throws Acl2UndefinedPackageException {
        return Acl2Symbol.NIL;
    }

    /**
     * Returns the witness symbol of the package named by this value,
     * consistently with the {@code pkg-witness} ACL2 function.
     * Since this function treats an argument that is not an ACL2 string
     * as the ACL2 string "ACL2",
     * the default implementation of this method
     * invokes its overriding method on the ACL2 string "ACL2".
     *
     * @return The witness symbol.
     * @throws Acl2UndefinedPackageException If the package name is invalid
     *                                       or the package is not defined.
     * @throws IllegalStateException         If the package witness is not set yet.
     */
    Acl2Symbol pkgWitness() throws Acl2UndefinedPackageException {
        return Acl2String.ACL2.pkgWitness();
    }

    /**
     * Negates (arithmetically) this value,
     * consistently with the {@code unary--} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @return The negation of this value.
     */
    Acl2Number negate() {
        return Acl2Integer.ZERO;
    }

    /**
     * Reciprocates (arithmetically) this value,
     * consistently with the {@code unary-/} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @return The reciprocal of this value.
     */
    Acl2Number reciprocate() {
        return Acl2Integer.ZERO;
    }

    /**
     * Adds the argument value to this value,
     * consistently with the {@code binary-+} ACL2 function.
     * It returns the result of coercing the argument to a number by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The value to add to this value.
     *              Invariant: not null.
     * @return The sum of this value with the argument value.
     */
    Acl2Number addValue(Acl2Value other) {
        return other.fix();
    }

    /**
     * Adds the argument number to this value,
     * consistently with the {@code binary-+} ACL2 function.
     * It returns the argument by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The number to add to this value.
     *              Invariant: not null.
     * @return The sum of this value with the argument number.
     */
    Acl2Number addNumber(Acl2Number other) {
        return other;
    }

    /**
     * Adds the argument rational to this value,
     * consistently with the {@code binary-+} ACL2 function.
     * It returns the argument by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The rational to add to this value.
     *              Invariant: not null.
     * @return The sum of this value with the argument rational.
     */
    Acl2Number addRational(Acl2Rational other) {
        return other;
    }

    /**
     * Adds the argument integer to this value,
     * consistently with the {@code binary-+} ACL2 function.
     * It returns the argument by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The integer to add to this value.
     *              Invariant: not null.
     * @return The sum of this value with the argument integer.
     */
    Acl2Number addInteger(Acl2Integer other) {
        return other;
    }

    /**
     * Multiplies the argument value to this value,
     * consistently with the {@code binary-*} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The value by which to multiply this value.
     *              Invariant: not null.
     * @return The product of this value with the argument value.
     */
    Acl2Number multiplyValue(Acl2Value other) {
        return Acl2Integer.ZERO;
    }

    /**
     * Multiplies the argument number to this value,
     * consistently with the {@code binary-*} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The number by which to multiply this value.
     *              Invariant: not null.
     * @return The product of this value with the argument number.
     */
    Acl2Number multiplyNumber(Acl2Number other) {
        return Acl2Integer.ZERO;
    }

    /**
     * Multiplies the argument rational to this value,
     * consistently with the {@code binary-*} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The rational by which to multiply this value.
     *              Invariant: not null.
     * @return The product of this value with the argument rational.
     */
    Acl2Number multiplyRational(Acl2Rational other) {
        return Acl2Integer.ZERO;
    }

    /**
     * Multiplies the argument integer to this value,
     * consistently with the {@code binary-*} ACL2 function.
     * It returns 0 by default;
     * it is overridden in
     * {@link Acl2Number}, {@link Acl2Rational}, and {@link Acl2Integer}.
     *
     * @param other The integer by which to multiply this value.
     *              Invariant: not null.
     * @return The product of this value with the argument integer.
     */
    Acl2Number multiplyInteger(Acl2Integer other) {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the real part of this value,
     * consistently with the {@code realpart} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     *
     * @return The real part of this value.
     */
    Acl2Rational realpart() {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the imaginary part of this value,
     * consistently with the {@code imagpart} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     *
     * @return The imaginary part of this value.
     */
    Acl2Rational imagpart() {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the numerator of this value,
     * consistently with the {@code numerator} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     *
     * @return The numerator of this value.
     */
    Acl2Integer numerator() {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the denominator of this value,
     * consistently with the {@code denominator} ACL2 function.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     *
     * @return The denominator of this value.
     */
    Acl2Integer denominator() {
        return Acl2Integer.ZERO;
    }

    /**
     * Returns the first component of this value,
     * consistently with the {@code car} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     *
     * @return The {@code car} of this value.
     */
    Acl2Value car() {
        return Acl2Symbol.NIL;
    }

    /**
     * Returns the second component of this value,
     * consistently with the {@code cdr} ACL2 function.
     * It returns {@code nil} by default;
     * it is overridden in {@link Acl2ConsPair}.
     *
     * @return The {@code cdr} of this value.
     */
    Acl2Value cdr() {
        return Acl2Symbol.NIL;
    }

    /**
     * Coerces this value to a number.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Number}.
     * This is consistent with the {@code fix} ACL2 function.
     *
     * @return The number that this value is coerced to.
     */
    Acl2Number fix() {
        return Acl2Integer.ZERO;
    }

    /**
     * Coerces this value to an rational.
     * It returns 0 by default;
     * it is overridden in {@link Acl2Rational}.
     * This is consistent with the {@code rfix} ACL2 function.
     *
     * @return The rational that this value is coerced to.
     */
    Acl2Rational rfix() {
        return Acl2Integer.ZERO;
    }

    /**
     * Coerces this value to a character.
     * It returns the character with code 0 by default;
     * it is overridden in {@link Acl2Character}.
     * This is consistent with
     * the {@code char-fix} ACL2 (non-built-in) function.
     *
     * @return The character that this value is coerced to.
     */
    Acl2Character charFix() {
        return Acl2Character.CODE_0;
    }

    /**
     * Coerces this value to a string.
     * It returns the empty string by default;
     * it is overridden in {@link Acl2String}.
     * This is consistent with
     * the {@code str-fix} ACL2 (non-built-in) function.
     *
     * @return The string that this value is coerced to.
     */
    Acl2String stringFix() {
        return Acl2String.EMPTY;
    }

    /**
     * String-appends the argument value to the right of this value,
     * consistently with the {@code string-append} ACL2 function.
     * It returns the result of coercing the argument to a string by default;
     * it is overridden in {@link Acl2String}.
     *
     * @param other The value to string-append to the right of this value.
     *              Invariant: not null.
     * @return The resulting of string-appending
     * the argument value to the right of this value.
     */
    Acl2String stringAppendValueRight(Acl2Value other) {
        return other.stringFix();
    }

    /**
     * String-appends the argument string to the left of this value,
     * consistently with the {@code string-append} ACL2 function.
     * It returns the argument by default;
     * it is overridden in {@link Acl2String}.
     *
     * @param other The string to string-append to the left of this value.
     *              Invariant: not null.
     * @return The result of string-appending
     * the argument string to the left of this value.
     */
    Acl2String stringAppendStringLeft(Acl2String other) {
        return other;
    }

    /**
     * Compares this value with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToCharacter(Acl2Character o);

    /**
     * Compares this value with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToString(Acl2String o);

    /**
     * Compares this value with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToSymbol(Acl2Symbol o);

    /**
     * Compares this value with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToNumber(Acl2Number o);

    /**
     * Compares this value with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToRational(Acl2Rational o);

    /**
     * Compares this value with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToInteger(Acl2Integer o);

    /**
     * Compares this value with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this value with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    abstract int compareToConsPair(Acl2ConsPair o);

    //////////////////////////////////////// public members:

    /**
     * Compares this value with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     * This method is abstract and overrides {@link Object#equals(Object)},
     * thus forcing the subclasses to provide an implementation.
     *
     * @param o The object to compare this value with.
     * @return {@code true} if the object is equal to this value,
     * otherwise {@code false}.
     */
    @Override
    public abstract boolean equals(Object o);

    /**
     * Compares this value with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this value with.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public abstract int compareTo(Acl2Value o);

    /**
     * Returns a true list consisting of the elements passed as arguments,
     * in the same order.
     * This is somewhat analogous to the ACL2 macro {@code list}.
     * This is a variable arity method.
     *
     * @param elements The list elements.
     * @return The list.
     * @throws IllegalArgumentException If any of the {@code elements} arguments
     *                                  is {@code null}.
     */
    public static Acl2Value makeList(Acl2Value... elements) {
        Acl2Value list = Acl2Symbol.NIL;
        for (int i = elements.length - 1; i >= 0; --i) {
            list = Acl2ConsPair.make(elements[i], list);
        }
        return list;
    }

    /**
     * Returns a dotted list consisting of the elements passed as arguments,
     * in the same order, with the last element as the final {@code cdr}.
     * This is somewhat analogous to the ACL2 macro {@code list*}.
     * This is a variable arity method.
     *
     * @param elements The list elements.
     * @return The list.
     * @throws IllegalArgumentException If any of the {@code elements} arguments
     *                                  is {@code null}.
     */
    public static Acl2Value makeListStar(Acl2Value... elements) {
        if (elements.length == 0)
            throw new IllegalArgumentException("No list elements.");
        Acl2Value finalCdr = elements[elements.length - 1];
        if (finalCdr == null)
            throw new IllegalArgumentException
                    ("Null final element of dotted list.");
        Acl2Value list = finalCdr;
        for (int i = elements.length - 2; i >= 0; --i) {
            list = Acl2ConsPair.make(elements[i], list);
        }
        return list;
    }

}
