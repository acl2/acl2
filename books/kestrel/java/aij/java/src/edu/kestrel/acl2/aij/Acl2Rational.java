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
     * Returns {@code true},
     * consistently with the {@code rationalp} ACL2 function.
     */
    @Override
    Acl2Symbol rationalp() {
        return Acl2Symbol.T;
    }

    /**
     * Negates (arithmetically) this ACL2 rational,
     * consistently with the {@code unary--} ACL2 function.
     */
    @Override
    Acl2Rational negate() {
        // -(a/b) is (-a)/b:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return Acl2Rational.make(a.negate(), b);
    }

    /**
     * Reciprocates (arithmetically) this ACL2 rational,
     * consistently with the {@code unary-/} ACL2 function.
     */
    @Override
    Acl2Rational reciprocate() {
        // 1/(a/b) is b/a:
        Acl2Integer a = this.numerator();
        if (a.equals(Acl2Integer.ZERO))
            return Acl2Integer.ZERO;
        Acl2Integer b = this.denominator();
        return Acl2Rational.make(b, a);
    }

    /**
     * Adds the argument ACL2 value to this ACL2 rational,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addValue(Acl2Value other) {
        return other.addRational(this);
    }

    /**
     * Adds the argument ACL2 number to this ACL2 rational,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addNumber(Acl2Number other) {
        return other.addRational(this);
    }

    /**
     * Adds the argument ACL2 rational to this ACL2 rational,
     * consistently with the {@code binary-+} ACL2 function.
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
                (Acl2Integer) a.multiplyRational(Acl2Rational.make(lcm, b));
        Acl2Integer bMultiplied = // c*(lcm/d)
                (Acl2Integer) c.multiplyRational(Acl2Rational.make(lcm, d));
        return Acl2Rational.make(aMultiplied.addInteger(bMultiplied), lcm);
    }

    /**
     * Adds the argument ACL2 integer to this ACL2 rational,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Rational addInteger(Acl2Integer other) {
        // a/b+c is (a*c)/d:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return Acl2Rational.make(a.multiplyInteger(other), b);
    }

    /**
     * Multiplies the argument ACL2 value to this ACL2 rational,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyValue(Acl2Value other) {
        return other.addRational(this);
    }

    /**
     * Multiplies the argument ACL2 number to this ACL2 rational,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyNumber(Acl2Number other) {
        return other.multiplyRational(this);
    }

    /**
     * Multiplies the argument ACL2 rational to this ACL2 rational,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Rational multiplyRational(Acl2Rational other) {
        // (a/b)*(c/d) is (a*c)/(b*d):
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        Acl2Integer c = other.numerator();
        Acl2Integer d = other.denominator();
        return Acl2Rational.make(a.multiplyInteger(c), b.multiplyInteger(d));
    }

    /**
     * Multiplies the argument ACL2 integer to this ACL2 rational,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Rational multiplyInteger(Acl2Integer other) {
        // (a/b)*c is (a*c)/b:
        Acl2Integer a = this.numerator();
        Acl2Integer b = this.denominator();
        return Acl2Rational.make(a.multiplyInteger(other), b);
    }

    /**
     * Returns the numerator of this ACL2 rational,
     * consistently with the {@code numerator} ACL2 function.
     */
    Acl2Integer numerator() {
        return this.getNumerator();
    }

    /**
     * Returns the denominator of this ACL2 rational,
     * consistently with the {@code denominator} ACL2 function.
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
