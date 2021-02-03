/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.math.BigInteger;

/**
 * Representation of ACL2 rationals.
 * These are the values that satisfy {@code rationalp}.
 * <p>
 * They consist of
 * integers (subclass {@link Acl2Integer} and
 * ratios (subclass {@link Acl2Ratio}.
 * No other subclasses can be defined outside this package
 * because this class provides no public or protected constructors.
 */
public abstract class Acl2Rational extends Acl2Number {

    //////////////////////////////////////// package-private members:

    /**
     * Prevents the creation of subclasses outside this package.
     * Since this constructor is package-private,
     * it inhibits the generation of the default public constructor.
     */
    Acl2Rational() {
    }

    /**
     * Checks if this rational is a rational, which is always true.
     * This is consistent with the {@code rationalp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol rationalp() {
        return Acl2Symbol.T;
    }

    /**
     * Checks if this rational is a rational, which is always true,
     * returning a Java boolean instead of an ACL2 symbol.
     * This is consistent with the {@code rationalp} ACL2 function.
     *
     * @return {@code true}.
     */
    @Override
    boolean rationalpBoolean() {
        return true;
    }

    /**
     * Negates (arithmetically) this rational,
     * consistently with the {@code unary--} ACL2 function.
     *
     * @return The negation of this rational.
     */
    @Override
    Acl2Rational negate() {
        // -(a/b) is (-a)/b:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return imake(a.negate(), b);
    }

    /**
     * Reciprocates (arithmetically) this rational,
     * assuming it is not 0,
     * consistently with the {@code unary-/} ACL2 function.
     * Invariant: this rational is not 0.
     *
     * @return The reciprocal of this rational.
     */
    @Override
    Acl2Rational reciprocateNonZero() {
        // 1/(a/b) is b/a:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return imake(b, a); // see note below
        // Note: the code just above is executed
        // only if this rational is a ratio
        // (otherwise the overriding method in Acl2Integer would be executed),
        // so this rational is never 0, because ratios are never 0.
    }

    /**
     * Reciprocates (arithmetically) this rational,
     * consistently with the {@code unary-/} ACL2 function.
     * If this rational is 0, the result is 0.
     *
     * @return The reciprocal of this rational.
     */
    @Override
    Acl2Rational reciprocate() {
        // This code is executed
        // only if this rational is a ratio
        // (otherwise the overriding method in Acl2Integer would be executed),
        // so this rational is never 0, because ratios are never 0.
        return reciprocateNonZero();
    }

    /**
     * Adds the argument value to this rational,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The value to add to this rational.
     *              Invariant: not null.
     * @return The sum of this rational with the argument value.
     */
    @Override
    Acl2Number addValue(Acl2Value other) {
        return other.addRational(this);
    }

    /**
     * Adds the argument number to this rational,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The number to add to this rational.
     *              Invariant: not null.
     * @return The sum of this rational with the argument number.
     */
    @Override
    Acl2Number addNumber(Acl2Number other) {
        return other.addRational(this);
    }

    /**
     * Adds the argument rational to this rational,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The rational to add to this raational.
     *              Invariant: not null.
     * @return The sum of this rational with the argument rational.
     */
    Acl2Rational addRational(Acl2Rational other) {
        // a/b+c/d is (a*(lcm/b)+c*(lcm/d))/lcm,
        // where lcm is the least common multiple of b and d:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        Acl2Integer c = other.numerator();
        Acl2Integer d = other.denominator();
        Acl2Integer lcm = b.lcm(d);
        Acl2Integer aMultiplied = // a*(lcm/b)
                (Acl2Integer) a.multiplyRational(imake(lcm, b));
        Acl2Integer bMultiplied = // c*(lcm/d)
                (Acl2Integer) c.multiplyRational(imake(lcm, d));
        return imake(aMultiplied.addInteger(bMultiplied), lcm);
    }

    /**
     * Adds the argument integer to this rational,
     * consistently with the {@code binary-+} ACL2 function.
     *
     * @param other The integer to add to this rational.
     *              Invariant: not null.
     * @return The sum of this rational with the argument integer.
     */
    @Override
    Acl2Rational addInteger(Acl2Integer other) {
        // a/b+c is (a+b*c)/b:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        Acl2Integer c = other;
        return imake(a.addInteger(b.multiplyInteger(c)), b);
    }

    /**
     * Multiplies the argument value to this rational,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The value by which to multiply this rational.
     *              Invariant: not null.
     * @return The product of this rational with the argument value.
     */
    @Override
    Acl2Number multiplyValue(Acl2Value other) {
        return other.multiplyRational(this);
    }

    /**
     * Multiplies the argument number to this rational,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The number by which to multiply this rational.
     *              Invariant: not null.
     * @return The product of this rational with the argument number.
     */
    @Override
    Acl2Number multiplyNumber(Acl2Number other) {
        return other.multiplyRational(this);
    }

    /**
     * Multiplies the argument rational to this rational,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The rational by which to multiply this rational.
     *              Invariant: not null.
     * @return The product of this rational with the argument rational.
     */
    @Override
    Acl2Rational multiplyRational(Acl2Rational other) {
        // (a/b)*(c/d) is (a*c)/(b*d):
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        Acl2Integer c = other.numerator();
        Acl2Integer d = other.denominator();
        return imake(a.multiplyInteger(c), b.multiplyInteger(d));
    }

    /**
     * Multiplies the argument integer to this rational,
     * consistently with the {@code binary-*} ACL2 function.
     *
     * @param other The integer by which to multiply this rational.
     *              Invariant: not null.
     * @return The product of this rational with the argument integer.
     */
    @Override
    Acl2Rational multiplyInteger(Acl2Integer other) {
        // (a/b)*c is (a*c)/b:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return imake(a.multiplyInteger(other), b);
    }

    /**
     * Returns the numerator of this rational,
     * consistently with the {@code numerator} ACL2 function.
     *
     * @return The numerator of this rational.
     */
    Acl2Integer numerator() {
        return this.getNumerator();
    }

    /**
     * Returns the denominator of this rational,
     * consistently with the {@code denominator} ACL2 function.
     *
     * @return The denominator of this rational.
     */
    Acl2Integer denominator() {
        return this.getDenominator();
    }

    /**
     * Coerce this rational to a rational, which is a no-op.
     * This is consistent with the {@code rfix} ACL2 function.
     *
     * @return This rational, unchanged.
     */
    @Override
    Acl2Rational rfix() {
        return this;
    }

    /**
     * Compares this rational with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this rational with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this rational is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        return -o.compareToRational(this);
    }

    /**
     * Compares this rational with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this rational with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this rational is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // a/b is less than or equal to or greater than c/d iff
        // a*d is less than or equal to or greater than c*b,
        // since b and d are always positive:
        Acl2Integer thisMultiplied =
                this.numerator().multiplyInteger(o.denominator());
        Acl2Integer oMultiplied =
                o.numerator().multiplyInteger(this.denominator());
        return thisMultiplied.compareToInteger(oMultiplied);
    }

    /**
     * Compares this rational with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this rational with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this number is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // a/b is less than or equal to or greater than c iff
        // a is less than or equal to or greater than c*b,
        // since b is always positive:
        Acl2Integer cb = o.multiplyInteger(this.denominator());
        Acl2Integer a = this.numerator();
        return a.compareToInteger(cb);
    }

    /**
     * Returns a rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @param numerator   The numerator of the rational.
     *                    Invariant: not null.
     * @param denominator The denominator of the rational.
     *                    Invariant: not null, not 0.
     * @return The rational.
     */
    static Acl2Rational imake(Acl2Integer numerator, Acl2Integer denominator) {
        /* The numerator and denominator of the fraction are reduced,
           and the denominator is made positive.
           If the resulting denominator is 1, an ACL2 integer is returned;
           otherwise, an ACL2 ratio is returned. */
        Acl2Integer gcd = numerator.gcd(denominator);
        numerator = numerator.divide(gcd);
        denominator = denominator.divide(gcd);
        if (denominator.compareTo(Acl2Integer.ZERO) < 0) {
            numerator = numerator.negate();
            denominator = denominator.negate();
        }
        if (denominator.equals(Acl2Integer.ONE))
            return numerator;
        else
            return Acl2Ratio.makeInternal(numerator, denominator);
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this rational with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The object to compare this rational with.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return -o.compareToRational(this);
    }

    /**
     * Returns a rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @param numerator   The numerator of the rational.
     * @param denominator The denominator of the rational.
     * @return The rational.
     * @throws IllegalArgumentException If {@code numerator} or
     *                                  {@code denominator} is null,
     *                                  or {@code denominator} is 0.
     */
    public static Acl2Rational make(Acl2Integer numerator,
                                    Acl2Integer denominator) {
        if (numerator == null)
            throw new IllegalArgumentException("Null numerator.");
        if (denominator == null)
            throw new IllegalArgumentException("Null denominator.");
        if (denominator.equals(Acl2Integer.ZERO))
            throw new IllegalArgumentException("Zero denominator.");
        return imake(numerator, denominator);
    }

    /**
     * Returns a rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @param numerator   The numerator of the rational.
     * @param denominator The denominator of the rational.
     * @return The rational.
     * @throws IllegalArgumentException If {@code denominator} is 0.
     */
    public static Acl2Rational make(int numerator, int denominator) {
        if (denominator == 0)
            throw new IllegalArgumentException("Zero denominator.");
        return imake(Acl2Integer.make(numerator),
                Acl2Integer.make(denominator));
    }

    /**
     * Returns a rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @param numerator   The numerator of the rational.
     * @param denominator The denominator of the rational.
     * @return The rational.
     * @throws IllegalArgumentException If {@code denominator} is 0.
     */
    public static Acl2Rational make(long numerator, long denominator) {
        if (denominator == 0)
            throw new IllegalArgumentException("Zero denominator.");
        return imake(Acl2Integer.make(numerator),
                Acl2Integer.make(denominator));
    }

    /**
     * Returns a rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @param numerator   The numerator of the rational.
     * @param denominator The denominator of the rational.
     * @return The rational.
     * @throws IllegalArgumentException If {@code numerator} or
     *                                  {@code denominator} is null,
     *                                  or {@code denominator} is 0.
     */
    public static Acl2Rational make(BigInteger numerator,
                                    BigInteger denominator) {
        if (numerator == null)
            throw new IllegalArgumentException("Null numerator.");
        if (denominator == null)
            throw new IllegalArgumentException("Null denominator.");
        if (denominator.equals(BigInteger.ZERO))
            throw new IllegalArgumentException("Zero denominator.");
        return imake(Acl2Integer.imake(numerator),
                Acl2Integer.imake(denominator));
    }

    /**
     * Returns the numerator of this rational.
     * The numerator is in reduced form,
     * i.e. it is coprime with the denominator,
     * and its sign is consistent with a positive denominator.
     *
     * @return The numerator of this rational.
     */
    public abstract Acl2Integer getNumerator();

    /**
     * Returns the denominator of this rational.
     * The denominator is in reduced form,
     * i.e. it is positive and coprime with the numerator.
     * If this rational is an integer, the result is 1.
     *
     * @return The denominator of this rational.
     */
    public abstract Acl2Integer getDenominator();

    /**
     * Returns the real part of this rational, which is the rational itself.
     *
     * @return This rational.
     */
    @Override
    public Acl2Rational getRealPart() {
        return this;
    }

    /**
     * Returns the imaginary part of this rational, which is always 0.
     *
     * @return The integer 0.
     */
    @Override
    public Acl2Rational getImaginaryPart() {
        return Acl2Integer.ZERO;
    }

}
