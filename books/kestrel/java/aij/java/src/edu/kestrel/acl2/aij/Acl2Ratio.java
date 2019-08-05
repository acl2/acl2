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
        this.numerator = numerator;
        this.denominator = denominator;
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
                    (Acl2Integer) this.numerator.multiplyValue(o.numerator());
            Acl2Integer thatMultiplied =
                    (Acl2Integer) o.numerator().multiplyValue(this.denominator);
            return thisMultiplied.compareTo(thatMultiplied);
        }
        // ratios are less than
        // complex rationals, characters, strings, symbols, and cons pairs:
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
