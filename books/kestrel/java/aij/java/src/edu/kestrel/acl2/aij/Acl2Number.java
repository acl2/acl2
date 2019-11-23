/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.math.BigInteger;

/**
 * Representation of ACL2 numbers.
 * These are the values that satisfy {@code acl2-numberp}.
 * <p>
 * They consist of
 * rationals (subclass {@link Acl2Rational}) and
 * complex rationals (subclass {@link Acl2ComplexRational}.
 * No other subclasses can be defined outside this package
 * because this class provides no public or protected constructors.
 */
public abstract class Acl2Number extends Acl2Value {

    //////////////////////////////////////// package-private members:

    /**
     * Prevents the creation of subclasses outside this package.
     * Since this constructor is package-private,
     * it inhibits the generation of the default public constructor.
     */
    Acl2Number() {
    }

    /**
     * Checks if this number is a number, which is always true.
     * This is consistent with the {@code acl2-numberp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol acl2Numberp() {
        return Acl2Symbol.T;
    }

    /**
     * Negates (arithmetically) this number,
     * consistently with the {@code unary--} ACL2 function.
     *
     * @return The negation of this number.
     */
    @Override
    Acl2Number negate() {
        // -(a+bi) is (-a)+(-b)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.imake(a.negate(), b.negate());
    }

    /**
     * Reciprocates (arithmetically) this number,
     * assuming it is not 0,
     * consistently with the {@code unary-/} ACL2 function.
     * Invariant: this number is not 0.
     *
     * @return The reciprocal of this number.
     */
    Acl2Number reciprocateNonZero() {
        // 1/(a+bi) is (a/(aa+bb))-(b/(aa+bb))i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational aa = a.multiplyRational(a);
        Acl2Rational bb = b.multiplyRational(b);
        Acl2Rational aabb = aa.addRational(bb);
        Acl2Rational aabbInv = aabb.reciprocateNonZero(); // see note below
        Acl2Rational resultReal = a.multiplyRational(aabbInv);
        Acl2Rational resultImag = b.negate().multiplyRational(aabbInv);
        return Acl2Number.imake(resultReal, resultImag);
        // Note: the code just above is executed
        // only if this number is a complex rational
        // (otherwise the code of an overriding method would be executed),
        // so aabb is never zero because b is never 0.
    }

    /**
     * Reciprocates (arithmetically) this number,
     * consistently with the {@code unary-/} ACL2 function.
     * If this number is 0, the result is 0.
     *
     * @return The reciprocal of this number.
     */
    @Override
    Acl2Number reciprocate() {
        // This code is executed
        // only if this number is a complex rational
        // (otherwise the code of an overriding method would be executed),
        // so this number is never 0 because its imaginary part is never 0.
        return reciprocateNonZero();
    }

    /**
     * Adds the argument value to this number,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The value to add to this number.
     *              Invariant: not null.
     * @return The sum of this number with the argument value.
     */
    @Override
    Acl2Number addValue(Acl2Value other) {
        return other.addNumber(this);
    }

    /**
     * Adds the argument number to this number,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The number to add to this number.
     *              Invariant: not null.
     * @return The sum of this number with the argument number.
     */
    @Override
    Acl2Number addNumber(Acl2Number other) {
        // (a+bi)+(c+di) is (a+c)+(b+d)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational c = other.realpart();
        Acl2Rational d = other.imagpart();
        return Acl2Number.imake(a.addRational(c), b.addRational(d));
    }

    /**
     * Adds the argument rational to this number,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The rational to add to this number.
     *              Invariant: not null.
     * @return The sum of this number with the argument rational.
     */
    @Override
    Acl2Number addRational(Acl2Rational other) {
        // (a+bi)+c is (a+c)+bi:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.imake(a.addRational(other), b);
    }

    /**
     * Adds the argument integer to this number,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The integer to add to this number.
     *              Invariant: not null.
     * @return The sum of this number with the argument integer.
     */
    @Override
    Acl2Number addInteger(Acl2Integer other) {
        // (a+bi)+c is (a+c)+bi:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.imake(a.addRational(other), b);
    }

    /**
     * Multiplies the argument value to this number,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The value by which to multiply this number.
     *              Invariant: not null.
     * @return The product of this number with the argument value.
     */
    @Override
    Acl2Number multiplyValue(Acl2Value other) {
        return other.multiplyNumber(this);
    }

    /**
     * Multiplies the argument number to this number,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The number by which to multiply this number.
     *              Invariant: not null.
     * @return The product of this number with the argument number.
     */
    @Override
    Acl2Number multiplyNumber(Acl2Number other) {
        // (a+bi)*(c+di) is (ac-bd)+(bc+ad)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational c = other.realpart();
        Acl2Rational d = other.imagpart();
        Acl2Rational ac = a.multiplyRational(c);
        Acl2Rational bd = b.multiplyRational(d);
        Acl2Rational bc = b.multiplyRational(c);
        Acl2Rational ad = a.multiplyRational(d);
        return Acl2Number.imake(ac.addRational(bd.negate()),
                bc.addRational(ad));
    }

    /**
     * Multiplies the argument rational to this number,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The rational by which to multiply this number.
     *              Invariant: not null.
     * @return The product of this number with the argument rational.
     */
    @Override
    Acl2Number multiplyRational(Acl2Rational other) {
        // (a+bi)*c is (ac)+(bc)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.imake(a.multiplyRational(other),
                b.multiplyRational(other));
    }

    /**
     * Multiplies the argument integer to this number,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The integer by which to multiply this number.
     *              Invariant: not null.
     * @return The product of this number with the argument integer.
     */
    @Override
    Acl2Number multiplyInteger(Acl2Integer other) {
        // (a+bi)*c is (ac)+(bc)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.imake(a.multiplyRational(other),
                b.multiplyRational(other));
    }

    /**
     * Returns the real part of this number,
     * consistently with the {@code realpart} ACL2 function.
     *
     * @return The real part of this number.
     */
    @Override
    Acl2Rational realpart() {
        return this.getRealPart();
    }

    /**
     * Returns the imaginary part of this number,
     * consistently with the {@code imagpart} ACL2 function.
     *
     * @return The imaginary part of this number.
     */
    @Override
    Acl2Rational imagpart() {
        return this.getImaginaryPart();
    }

    /**
     * Coerce this number to a number, which is a no-op.
     * This is consistent with the {@code fix} ACL2 function.
     *
     * @return This number, unchanged.
     */
    @Override
    Acl2Number fix() {
        return this;
    }

    /**
     * Compares this number with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // numbers are less than characters:
        return -1;
    }

    /**
     * Compares this number with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // numbers are less than strings:
        return -1;
    }

    /**
     * Compares this number with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // numbers are less than symbols:
        return -1;
    }

    /**
     * Compares this number with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // compare real and imaginary parts lexicographically:
        int realCmp = this.realpart().compareToRational(o.realpart());
        if (realCmp != 0)
            return realCmp;
        else
            return this.imagpart().compareToRational(o.imagpart());
    }

    /**
     * Compares this number with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // compare real and imaginary parts lexicographically:
        int realCmp = this.realpart().compareToRational(o.realpart());
        if (realCmp != 0)
            return realCmp;
        else
            // the imaginary part is always 0 for the rational:
            return this.imagpart().compareToInteger(Acl2Integer.ZERO);
    }

    /**
     * Compares this number with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // compare real and imaginary parts lexicographically:
        int realCmp = this.realpart().compareToRational(o.realpart());
        if (realCmp != 0)
            return realCmp;
        else
            // the imaginary part is always 0 for the integer:
            return this.imagpart().compareToInteger(Acl2Integer.ZERO);
    }

    /**
     * Compares this number with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this number with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // numbers are less than cons pairs:
        return -1;
    }

    /**
     * Returns a number with the given real and imaginary parts.
     * This is for AIJ's internal use, as conveyed by the {@code i} in the name.
     * If the imaginary part is 0, the result is a rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @param realPart      The real part of the number.
     *                      Invariant: not null.
     * @param imaginaryPart The imaginary part of the number.
     *                      Invariant: not null.
     * @return The number.
     */
    static Acl2Number imake(Acl2Rational realPart,
                            Acl2Rational imaginaryPart) {
        if (imaginaryPart.equals(Acl2Integer.ZERO))
            return realPart;
        else
            return Acl2ComplexRational.makeInternal(realPart, imaginaryPart);
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this number with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this number with.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return -o.compareToNumber(this);
    }

    /**
     * Returns a number with the given real and imaginary parts.
     * If the imaginary part is 0, the result is a rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @param realPart      The real part of the number.
     * @param imaginaryPart The imaginary part of the number.
     * @return The number.
     * @throws IllegalArgumentException If {@code realpart} is null
     *                                  or {@code imaginaryPart} is null.
     */
    public static Acl2Number make(Acl2Rational realPart,
                                  Acl2Rational imaginaryPart) {
        if (realPart == null)
            throw new IllegalArgumentException("Null real part.");
        if (imaginaryPart == null)
            throw new IllegalArgumentException("Null imaginary part.");
        return imake(realPart, imaginaryPart);
    }

    /**
     * Returns a number with the given real and imaginary parts.
     * If the imaginary part is 0, the result is a rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @param realPart      The real part of the number.
     * @param imaginaryPart The imaginary part of the number.
     * @return The number.
     */
    public static Acl2Number make(int realPart, int imaginaryPart) {
        return imake(Acl2Integer.make(realPart),
                Acl2Integer.make(imaginaryPart));
    }

    /**
     * Returns a number with the given real and imaginary parts.
     * If the imaginary part is 0, the result is a rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @param realPart      The real part of the number.
     * @param imaginaryPart The imaginary part of the number.
     * @return The number.
     */
    public static Acl2Number make(long realPart, long imaginaryPart) {
        return imake(Acl2Integer.make(realPart),
                Acl2Integer.make(imaginaryPart));
    }

    /**
     * Returns a number with the given real and imaginary parts.
     * If the imaginary part is 0, the result is a rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @param realPart      The real part of the number.
     * @param imaginaryPart The imaginary part of the number.
     * @return The number.
     * @throws IllegalArgumentException If {@code realpart} is null
     *                                  or {@code imaginaryPart} is null.
     */
    public static Acl2Number make(BigInteger realPart,
                                  BigInteger imaginaryPart) {
        if (realPart == null)
            throw new IllegalArgumentException("Null real part.");
        if (imaginaryPart == null)
            throw new IllegalArgumentException("Null imaginary part.");
        return imake(Acl2Integer.imake(realPart),
                Acl2Integer.imake(imaginaryPart));
    }

    /**
     * Returns the real part of this number.
     * This is consistent with the {@code realpart} ACL2 function.
     *
     * @return The real part of this number.
     */
    public abstract Acl2Rational getRealPart();

    /**
     * Returns the imaginary part of this number.
     * This is consistent with the {@code imaggpart} ACL2 function.
     *
     * @return The imaginary part of this number.
     */
    public abstract Acl2Rational getImaginaryPart();

}
