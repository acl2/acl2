/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.math.BigInteger;

/**
 * Representation of ACL2 integers.
 * These are the values that satisfy {@code integerp}.
 */
public final class Acl2Integer extends Acl2Rational {

    //////////////////////////////////////// private members:

    /**
     * Numeric value of this integer.
     * Invariant: not null.
     */
    private final BigInteger numericValue;

    /**
     * Constructs an integer with the given numeric value.
     *
     * @param numericValue The numeric value of the integer.
     *                     Invariant: not null.
     */
    private Acl2Integer(BigInteger numericValue) {
        this.numericValue = numericValue;
    }

    /**
     * The {@link BigInteger} 256.
     * This is used to speed up {@link #codeChar()}.
     */
    private static final BigInteger BIG_INTEGER_256 = BigInteger.valueOf(256);

    //////////////////////////////////////// package-private members:

    /**
     * Returns the greatest common divisor of the absolute values of
     * this integer and the argument integer.
     * The result is 0 if both integers are 0.
     *
     * @param other The integer for which to take the greatest common divisor
     *              with this integer.
     *              Invariant: not null.
     * @return The greatest common divisor.
     */
    Acl2Integer gcd(Acl2Integer other) {
        return imake(this.numericValue.gcd(other.numericValue));
    }

    /**
     * Returns the least common multiple of the absolute values of
     * this integer and the argument integer.
     * The result is 0 if any integer is 0.
     *
     * @param other The integer for which to take the least common multiple
     *              with this integer.
     *              Invariant: not null.
     * @return The least common multiple.
     */
    Acl2Integer lcm(Acl2Integer other) {
        // lcm is (|a|*|b|)/gcd, where gcd is the greatest common divisor:
        BigInteger thisBigInt = this.numericValue;
        BigInteger otherBigInt = other.numericValue;
        BigInteger gcd = thisBigInt.gcd(otherBigInt);
        BigInteger mayBeNegative = // (a*b)/gcd
                thisBigInt.divide(gcd).multiply(otherBigInt);
        if (mayBeNegative.signum() == -1)
            return imake(mayBeNegative.negate());
        else
            return imake(mayBeNegative);
    }

    /**
     * Divides this integer by the argument integer.
     *
     * @param other The divisor by which this integer is divided.
     *              Invariant: not null, not 0.
     * @return The quotient.
     */
    Acl2Integer divide(Acl2Integer other) {
        return imake(this.numericValue.divide(other.numericValue));
    }

    /**
     * Negates (arithmetically) this integer,
     * consistently with the {@code unary--} ACL2 function.
     *
     * @return The negation of this integer.
     */
    @Override
    Acl2Integer negate() {
        return imake(this.numericValue.negate());
    }

    /**
     * Reciprocates (arithmetically) this integer,
     * assuming it is not 0,
     * consistently with the {@code unary-/} ACL2 function.
     * Invariant: this integer is not 0.
     *
     * @return The reciprocal of this integer.
     */
    Acl2Rational reciprocateNonZero() {
        // 1/a:
        return Acl2Rational.imake(Acl2Integer.ONE, this);
    }

    /**
     * Reciprocates (arithmetically) this integer,
     * consistently with the {@code unary-/} ACL2 function.
     * If this integer is 0, the result is 0.
     *
     * @return The reciprocal of this integer.
     */
    @Override
    Acl2Rational reciprocate() {
        if (this.equals(Acl2Integer.ZERO))
            return Acl2Integer.ZERO;
        else
            return reciprocateNonZero();
    }

    /**
     * Adds the argument value to this integer,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The value to add to this integer.
     *              Invariant: not null.
     * @return The sum of this integer with the argument value.
     */
    @Override
    Acl2Number addValue(Acl2Value other) {
        return other.addInteger(this);
    }

    /**
     * Adds the argument number to this integer,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The number to add to this integer.
     *              Invariant: not null.
     * @return The sum of this integer with the argument number.
     */
    @Override
    Acl2Number addNumber(Acl2Number other) {
        return other.addInteger(this);
    }

    /**
     * Adds the argument rational to this integer,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The rational to add to this integer.
     *              Invariant: not null.
     * @return The sum of this integer with the argument rational.
     */
    @Override
    Acl2Rational addRational(Acl2Rational other) {
        return other.addInteger(this);
    }

    /**
     * Adds the argument integer to this integer,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The integer to add to this integer.
     *              Invariant: not null.
     * @return The sum of this integer with the argument integer.
     */
    Acl2Integer addInteger(Acl2Integer other) {
        return imake(this.numericValue.add(other.numericValue));
    }

    /**
     * Multiplies the argument value to this integer,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The value by which to multiply this integer.
     *              Invariant: not null.
     * @return The product of this integer with the argument value.
     */
    @Override
    Acl2Number multiplyValue(Acl2Value other) {
        return other.multiplyInteger(this);
    }

    /**
     * Multiplies the argument number to this integer,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The number by which to multiply this integer.
     *              Invariant: not null.
     * @return The product of this integer with the argument number.
     */
    @Override
    Acl2Number multiplyNumber(Acl2Number other) {
        return other.multiplyInteger(this);
    }

    /**
     * Multiplies the argument rational to this integer,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The rational by which to multiply this integer.
     *              Invariant: not null.
     * @return The product of this integer with the argument rational.
     */
    @Override
    Acl2Rational multiplyRational(Acl2Rational other) {
        return other.multiplyInteger(this);
    }

    /**
     * Multiplies the argument integer to this integer,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The integer by which to multiply this integer.
     *              Invariant: not null.
     * @return The product of this integer with the argument integer.
     */
    Acl2Integer multiplyInteger(Acl2Integer other) {
        return imake(this.numericValue.multiply(other.numericValue));
    }

    /**
     * Checks if this integer is an integer, which is always true.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol integerp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the character with this integer code,
     * consistently with the {@code code-char} ACL2 function.
     * If this integer is below 0 or above 255, it is treated as 0.
     *
     * @return The character with this integer as code.
     */
    @Override
    Acl2Character codeChar() {
        if (numericValue.compareTo(BigInteger.ZERO) >= 0 &&
                numericValue.compareTo(BIG_INTEGER_256) < 0)
            return Acl2Character.imake((char) numericValue.intValue());
        else
            return Acl2Character.CODE_0;
    }

    /**
     * Compares this integer with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this integer with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this integer is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // swap comparison and flip result:
        return -o.compareToInteger(this);
    }

    /**
     * Compares this integer with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this integer with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this integer is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // swap comparison and flip result:
        return -o.compareToInteger(this);
    }

    /**
     * Compares this integer with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this integer with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this integer is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // compare numeric values:
        return this.numericValue.compareTo(o.numericValue);
    }

    /**
     * Returns an integer with the numeric value of the given Java big integer.
     * This is for AIJ's internal use, as conveyed by the {@code i} in the name.
     *
     * @param numericValue The numeric value of the integer.
     *                     Invariant: not null.
     * @return The integer.
     */
    static Acl2Integer imake(BigInteger numericValue) {
        return new Acl2Integer(numericValue);
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this integer with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this integer with.
     * @return {@code true} if the object is equal to this integer,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Integer)) return false;
        Acl2Integer that = (Acl2Integer) o;
        return numericValue.equals(that.numericValue);
    }

    /**
     * Returns a hash code for this integer.
     *
     * @return The hash code for this integer.
     */
    @Override
    public int hashCode() {
        return numericValue.hashCode();
    }

    /**
     * Compares this integer with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this integer with.
     * @return A negative integer, zero, or a positive integer as
     * this integer is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        // swap comparison and flip result:
        return -o.compareToInteger(this);
    }

    /**
     * Returns a printable representation of this integer.
     *
     * @return A printable representation of this character.
     */
    @Override
    public String toString() {
        return this.numericValue.toString();
    }

    /**
     * Returns an integer with the numeric value of the given Java integer.
     *
     * @param numericValue The numeric value of the integer.
     * @return The integer.
     */
    public static Acl2Integer make(int numericValue) {
        if (numericValue == 0) return ZERO;
        if (numericValue == 1) return ONE;
        return imake(BigInteger.valueOf(numericValue));
    }

    /**
     * Returns an integer with the numeric value of the given Java long integer.
     *
     * @param numericValue The numeric value of the integer.
     * @return The integer.
     */
    public static Acl2Integer make(long numericValue) {
        return imake(BigInteger.valueOf(numericValue));
    }

    /**
     * Returns an integer with the numeric value of the given Java big integer.
     *
     * @param numericValue The numeric value of the integer.
     * @return The integer.
     * @throws IllegalArgumentException If {@code numericValue} is null.
     */
    public static Acl2Integer make(BigInteger numericValue) {
        if (numericValue == null)
            throw new IllegalArgumentException("Null numeric value.");
        else
            return imake(numericValue);
    }

    /**
     * The integer 0.
     */
    public static final Acl2Integer ZERO =
            new Acl2Integer(BigInteger.valueOf(0));

    /**
     * The integer 1.
     */
    public static final Acl2Integer ONE =
            new Acl2Integer(BigInteger.valueOf(1));

    /**
     * Returns the numeric value of this integer as a Java integer,
     * if it fits the Java {@code int} type.
     *
     * @return The numeric value of this integer.
     * @throws ArithmeticException If the numeric value
     *                             does not fit {@code int}.
     */
    public int getJavaInt() {
        return this.numericValue.intValueExact();
    }

    /**
     * Returns the numeric value of this integer as a Java long integer,
     * if it fits the Java {@code long} type.
     *
     * @return The numeric value of this integer.
     * @throws ArithmeticException If the numeric value
     *                             does not fit {@code long}.
     */
    public long getJavaLong() {
        return this.numericValue.longValueExact();
    }

    /**
     * Returns the numeric value of this integer as a Java big integer.
     *
     * @return The numeric value of this integer.
     */
    public BigInteger getJavaBigInteger() {
        return this.numericValue;
    }

    /**
     * Returns the numerator of this integer, which is the integer itself.
     *
     * @return This integer.
     */
    @Override
    public Acl2Integer getNumerator() {
        return this;
    }

    /**
     * Returns the denominator of this integer, which is 1.
     *
     * @return The integer 1.
     */
    @Override
    public Acl2Integer getDenominator() {
        return ONE;
    }

}
