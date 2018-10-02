/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 ratios.
 * These are the ACL2 values that satisfy
 * {@code rationalp} but not {@code integerp},
 * i.e. ratios in Common Lisp.
 * <p>
 * This class is not public because code outside this package
 * must use the public methods in the {@link Acl2Rational} class
 * to create rational numbers (which may be integers or ratios).
 */
final class Acl2Ratio extends Acl2Rational {

    //////////////////////////////////////// private members:

    /**
     * Numerator of the ACL2 ratio.
     * This is never {@code null} and always coprime with the denominator.
     */
    private final Acl2Integer numerator;

    /**
     * Denominator of the ACL2 ratio.
     * This is never {@code null} and always greater than 1.
     */
    private final Acl2Integer denominator;

    /**
     * Constructs an ACL2 ratio from its numerator and denominator.
     */
    private Acl2Ratio(Acl2Integer numerator, Acl2Integer denominator) {
        assert numerator != null && denominator != null &&
                denominator.compareTo(Acl2Integer.ONE) > 0 &&
                numerator.gcd(denominator).equals(Acl2Integer.ONE);
        this.numerator = numerator;
        this.denominator = denominator;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Supports the native implementation of
     * the {@code unary--} ACL2 function.
     */
    @Override
    Acl2Rational negate() {
        // -(a/b) is (-a)/b:
        Acl2Integer a = this.numerator;
        Acl2Integer b = this.denominator;
        return Acl2Rational.make(a.negate(), b);
    }

    /**
     * Supports the native implementation of
     * the {@code unary-/} ACL2 function.
     */
    @Override
    Acl2Rational reciprocate() {
        // 1/(a/b) is b/a:
        Acl2Integer a = this.numerator;
        if (a.equals(Acl2Integer.ZERO))
            return Acl2Integer.ZERO;
        Acl2Integer b = this.denominator;
        return Acl2Rational.make(b, a);
    }

    /**
     * Supports the native implementation of
     * the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number add(Acl2Value other) {
        assert other != null;
        if (other instanceof Acl2Rational) {
            // a/b + c/d is (a*(lcm/b)+c*(lcm/d))/lcm,
            // where lcm is the least common multiple of b and d:
            Acl2Integer thisNumerator = this.numerator;
            Acl2Integer thisDenominator = this.denominator;
            Acl2Integer otherNumerator = other.numerator();
            Acl2Integer otherDenominator = other.denominator();
            Acl2Integer lcm = thisDenominator.lcm(otherDenominator);
            Acl2Integer thisMultiplied = // a*(lcm/b)
                    (Acl2Integer)
                            thisNumerator.multiply
                                    (Acl2Rational.make(lcm, thisDenominator));
            Acl2Integer otherMultiplied = // c*(lcm/d)
                    (Acl2Integer)
                            otherNumerator.multiply
                                    (Acl2Rational.make(lcm, otherDenominator));
            return Acl2Rational.make
                    ((Acl2Integer) thisMultiplied.add(otherMultiplied),
                            lcm);
        } else {
            // use Acl2ComplexRational.add() or Acl2Value.add()
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
        if (other instanceof Acl2Rational) {
            // (a/b)*(c/d) is (a*c)/(b*d):
            Acl2Integer resultNumerator =
                    (Acl2Integer) this.numerator.multiply(other.numerator());
            Acl2Integer resultDenominator =
                    (Acl2Integer) this.denominator.multiply(other.numerator());
            return Acl2Rational.make(resultNumerator, resultDenominator);
        } else {
            // use Acl2ComplexRational.multiply() or Acl2Value.multiply()
            // and return the result because multiplication is commutative:
            return other.multiply(this);
        }
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 integer is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since ratios are disjoint from integers and complex rationals,
           only a ratio can be equal to another ratio.
           Since the denominator is positive and coprime with the numerator,
           two ratio are equal iff their numerator and denominator are. */
        if (this == o) return true;
        if (!(o instanceof Acl2Ratio)) return false;
        Acl2Ratio that = (Acl2Ratio) o;
        if (!numerator.equals(that.numerator)) return false;
        return denominator.equals(that.denominator);
    }

    /**
     * Returns a hash code for this ACL2 ratio.
     */
    @Override
    public int hashCode() {
        int result = numerator.hashCode();
        result = 31 * result + denominator.hashCode();
        return result;
    }

    /**
     * Compares this ACL2 ratio with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this ratio is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2Rational) {
            // a/b is less than or equal to or greater than c/d iff
            // a*d is less than or equal to or greater than c*b,
            // since b and d are always positive:
            Acl2Integer thisMultiplied =
                    (Acl2Integer) this.numerator.multiply(o.numerator());
            Acl2Integer thatMultiplied =
                    (Acl2Integer) o.numerator().multiply(this.denominator);
            return thisMultiplied.compareTo(thatMultiplied);
        }
        // ratios are less than
        // complex rationals, characters, strings, symbols, and pairs:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 rational.
     */
    @Override
    public String toString() {
        return this.numerator + "/" + this.denominator;
    }

    /**
     * Returns an ACL2 ratio with the given numerator and denominator.
     * This method must be public because
     * the corresponding method in {@link Acl2Rational} is public,
     * but it cannot be called form outside the package
     * because the {@link Acl2Ratio} class is not public.
     */
    public static Acl2Ratio make(Acl2Integer numerator,
                                 Acl2Integer denominator) {
        assert numerator != null && denominator != null &&
                denominator.compareTo(Acl2Integer.ONE) > 0 &&
                numerator.gcd(denominator).equals(Acl2Integer.ONE);
        return new Acl2Ratio(numerator, denominator);
    }

    /**
     * Returns the numerator of this ACL2 ratio.
     * The numerator is in reduced form,
     * i.e. it is coprime with the denominator,
     * and its sign is consistent with a positive denominator.
     */
    @Override
    public Acl2Integer getNumerator() {
        return numerator;
    }

    /**
     * Returns the denominator of this ACL2 ratio.
     * The numerator is in reduced form,
     * i.e. it is positive and coprime with the numerator.
     */
    @Override
    public Acl2Integer getDenominator() {
        return denominator;
    }
}
