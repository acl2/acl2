/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.math.BigInteger;

/**
 * Representation of ACL2 integers.
 * These are the ACL2 values that satisfy {@code integerp}.
 */
public final class Acl2Integer extends Acl2Rational {

    //////////////////////////////////////// private members:

    /**
     * Numeric value of the ACL2 integer.
     * This is never {@code null}.
     */
    private final BigInteger numericValue;

    /**
     * Constructs an ACL2 integer from its numeric value.
     */
    private Acl2Integer(BigInteger numericValue) {
        assert numericValue != null;
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
     * this ACL2 integer and the argument ACL2 integer.
     * The result is 0 if both integers are 0.
     */
    Acl2Integer gcd(Acl2Integer other) {
        assert other != null;
        return Acl2Integer.make(this.numericValue.gcd(other.numericValue));
    }

    /**
     * Returns the least common multiple of the absolute values of
     * this ACL2 integer and the argument ACL2 integer.
     * The result is 0 if any integer is 0.
     */
    Acl2Integer lcm(Acl2Integer other) {
        assert other != null;
        // lcm is (|a|*|b|)/gcd, where gcd is the greatest common divisor:
        BigInteger thisBigInt = this.numericValue;
        BigInteger otherBigInt = other.numericValue;
        BigInteger gcd = thisBigInt.gcd(otherBigInt);
        BigInteger mayBeNegative = // (a*b)/gcd
                thisBigInt.divide(gcd).multiply(otherBigInt);
        if (mayBeNegative.signum() == -1)
            return Acl2Integer.make(mayBeNegative.negate());
        else
            return Acl2Integer.make(mayBeNegative);
    }

    /**
     * Divides this ACL2 integer by the argument ACL2 integer.
     * The argument must not be 0.
     */
    Acl2Integer divide(Acl2Integer other) {
        assert other != null && !other.equals(ZERO);
        return Acl2Integer.make(this.numericValue.divide(other.numericValue));
    }

    /**
     * Supports the native implementation of
     * the {@code unary--} ACL2 function.
     * This method refines the return type of {@link Acl2Rational#negate()}.
     */
    @Override
    Acl2Integer negate() {
        return Acl2Integer.make(this.numericValue.negate());
    }

    /**
     * Supports the native implementation of
     * the {@code unary-/} ACL2 function.
     */
    @Override
    Acl2Rational reciprocate() {
        if (this.equals(Acl2Integer.ZERO))
            return Acl2Integer.ZERO;
        return Acl2Rational.make(Acl2Integer.ONE, this);
    }

    /**
     * Supports the native implementation of
     * the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number add(Acl2Value other) {
        assert other != null;
        if (other instanceof Acl2Integer) {
            Acl2Integer otherInteger = (Acl2Integer) other;
            return Acl2Integer.make
                    (this.numericValue.add(otherInteger.numericValue));
        } else {
            // use Acl2Ratio.add() or Acl2ComplexNumber.add() or Acl2Value.add()
            // and return the result because addition is commutative:
            return other.add(this);
        }
    }

    /**
     * Supports the native implementation of
     * the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiply(Acl2Value other) {
        assert other != null;
        if (other instanceof Acl2Integer) {
            Acl2Integer otherInteger = (Acl2Integer) other;
            return Acl2Integer.make
                    (this.numericValue.multiply(otherInteger.numericValue));
        } else {
            // use Acl2Ratio.multiply()
            // or Acl2ComplexNumber.multiply()
            // or Acl2Value.multiply()
            // and return the result because multiplication is commutative:
            return other.multiply(this);
        }
    }

    /**
     * Supports the native implementation of
     * the {@code integerp} ACL2 function.
     */
    @Override
    Acl2Symbol integerp() {
        return Acl2Symbol.T;
    }

    /**
     * Supports the native implementation of
     * the {@code code-char} ACL2 function.
     * If this integer is negative or above 255, it is treated as 0.
     */
    @Override
    Acl2Character codeChar() {
        if (numericValue.compareTo(BigInteger.ZERO) >= 0 &&
                numericValue.compareTo(BIG_INTEGER_256) < 0)
            return Acl2Character.make((char) numericValue.intValue());
        else
            return Acl2Character.CODE_0;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 integer is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Integer)) return false;
        Acl2Integer that = (Acl2Integer) o;
        return numericValue.equals(that.numericValue);
    }

    /**
     * Returns a hash code for this ACL2 integer.
     */
    @Override
    public int hashCode() {
        return numericValue.hashCode();
    }

    /**
     * Compares this ACL2 integer with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this integer is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2Integer)
            return this.numericValue.compareTo
                    (((Acl2Integer) o).numericValue);
        if (o instanceof Acl2Ratio) {
            // use Acl2Ratio.compareTo() and flip result:
            int cmp = o.compareTo(this);
            if (cmp < 0)
                return 1; // in case cmp is Integer.MIN_VALUE
            else if (cmp > 0)
                return -1;
            else
                return 0;
        }
        // integers are less than
        // complex rationals, characters, strings, symbols, and cons pairs:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 integer.
     */
    @Override
    public String toString() {
        return this.numericValue.toString();
    }

    /**
     * Returns an ACL2 integer
     * with the numeric value of the given Java integer.
     */
    public static Acl2Integer make(int numericValue) {
        return new Acl2Integer(BigInteger.valueOf(numericValue));
    }

    /**
     * Returns an ACL2 integer
     * with the numeric value of the given Java long integer.
     */
    public static Acl2Integer make(long numericValue) {
        return new Acl2Integer(BigInteger.valueOf(numericValue));
    }

    /**
     * Returns an ACL2 integer
     * with the numeric value of the given Java big integer.
     *
     * @throws IllegalArgumentException if numericValue is null
     */
    public static Acl2Integer make(BigInteger numericValue) {
        if (numericValue == null)
            throw new IllegalArgumentException("Null numeric value.");
        else
            return new Acl2Integer(numericValue);
    }

    /**
     * The ACL2 integer 0.
     */
    public static final Acl2Integer ZERO = Acl2Integer.make(0);

    /**
     * The ACL2 integer 1.
     */
    public static final Acl2Integer ONE = Acl2Integer.make(1);

    /**
     * Returns the numeric value of this ACL2 integer as a Java integer,
     * if it fits the Java {@code int} type.
     *
     * @throws ArithmeticException if the numeric value does not fit int
     */
    public int getJavaInt() {
        return this.numericValue.intValueExact();
    }

    /**
     * Returns the numeric value of this ACL2 integer as a Java long integer,
     * if it fits the Java {@code long} type.
     *
     * @throws ArithmeticException if the numeric value does not fit long
     */
    public long getJavaLong() {
        return this.numericValue.longValueExact();
    }

    /**
     * Returns the numeric value of this ACL2 integer as a Java big integer.
     */
    public BigInteger getJavaBigInteger() {
        return this.numericValue;
    }

    /**
     * Returns the numerator of this ACL2 integer.
     * The result is the integer itself.
     */
    @Override
    public Acl2Integer getNumerator() {
        return this;
    }

    /**
     * Returns the denominator of this ACL2 integer.
     * The result is 1.
     */
    @Override
    public Acl2Integer getDenominator() {
        return ONE;
    }
}
