/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 rationals.
 * These are the ACL2 values that satisfy {@code rationalp}.
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
     * Supports the native implementation of
     * the {@code rationalp} ACL2 function.
     */
    @Override
    Acl2Symbol rationalp() {
        return Acl2Symbol.T;
    }

    /**
     * Supports the native implementation of
     * the {@code unary--} ACL2 function.
     * This method refines the return type of {@link Acl2Value#negate()}.
     * This method is implemented by
     * {@link Acl2Ratio#negate()} and {@link Acl2Integer#negate()}.
     */
    @Override
    abstract Acl2Rational negate();

    /**
     * Supports the native implementation of
     * the {@code unary-/} ACL2 function.
     * This method refines the return type of {@link Acl2Value#reciprocate()}.
     * This method is implemented by
     * {@link Acl2Ratio#reciprocate()} and {@link Acl2Integer#reciprocate()}.
     */
    @Override
    abstract Acl2Rational reciprocate();

    /**
     * Supports the native implementation of
     * the {@code numerator} ACL2 function.
     */
    Acl2Integer numerator() {
        return this.getNumerator();
    }

    /**
     * Supports the native implementation of
     * the {@code denominator} ACL2 function.
     */
    Acl2Integer denominator() {
        return this.getDenominator();
    }

    /**
     * Coerce this ACL2 rational to an ACL2 rational,
     * i.e. just return this ACL2 rational.
     * This is consistent with the {@code rfix} ACL2 function.
     */
    @Override
    Acl2Rational rfix() {
        return this;
    }

    //////////////////////////////////////// public members:

    /**
     * Returns an ACL2 rational whose numeric value is
     * the fraction of the given numerator and denominator.
     * If the fraction is actually an integer, the result is an ACL2 integer,
     * according to the rule of rational canonicalization in Common Lisp.
     *
     * @throws IllegalArgumentException if numerator or denominator is null,
     *                                  or denominator is 0
     */
    public static Acl2Rational make(Acl2Integer numerator,
                                    Acl2Integer denominator) {
        if (numerator == null)
            throw new IllegalArgumentException("Null numerator.");
        if (denominator == null)
            throw new IllegalArgumentException("Null denominator.");
        if (denominator.equals(Acl2Integer.ZERO))
            throw new IllegalArgumentException("Zero denominator.");
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
            return Acl2Ratio.make(numerator, denominator);
    }

    /**
     * Returns the numerator of this ACL2 rational.
     * The numerator is in reduced form,
     * i.e. it is coprime with the denominator,
     * and its sign is consistent with a positive denominator.
     */
    public abstract Acl2Integer getNumerator();

    /**
     * Returns the denominator of this ACL2 rational.
     * The denominator is in reduced form,
     * i.e. it is positive and coprime with the numerator.
     * If this rational is an integer, the result is 1.
     */
    public abstract Acl2Integer getDenominator();

    /**
     * Returns the real part of this ACL2 rational.
     * The result is the rational itself.
     */
    @Override
    public Acl2Rational getRealPart() {
        return this;
    }

    /**
     * Returns the imaginary part of this ACL2 rational.
     * The result is 0.
     */
    @Override
    public Acl2Rational getImaginaryPart() {
        return Acl2Integer.ZERO;
    }
}
