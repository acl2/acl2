/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 ratios.
 * These are the values that satisfy {@code rationalp} but not {@code integerp},
 * i.e. ratios in Common Lisp.
 * <p>
 * This class is not public because code outside this package
 * must use the public methods in the {@link Acl2Rational} class
 * to create rational numbers (which may be integers or ratios).
 */
final class Acl2Ratio extends Acl2Rational {

    //////////////////////////////////////// private members:

    /**
     * Numerator of the ratio.
     * This is never {@code null} and always coprime with the denominator.
     */
    private final Acl2Integer numerator;

    /**
     * Denominator of the ratio.
     * This is never {@code null} and always greater than 1.
     */
    private final Acl2Integer denominator;

    /**
     * Constructs a ratio with the given numerator and denominator.
     *
     * @param numerator   The numerator of the ratio.
     *                    It is never {@code null}
     *                    and always coprime with {@code denominator}.
     * @param denominator The denominator of the ratio.
     *                    It is never {@code null},
     *                    always greater than 1,
     *                    and always coprime with {@code numerator}.
     */
    private Acl2Ratio(Acl2Integer numerator, Acl2Integer denominator) {
        this.numerator = numerator;
        this.denominator = denominator;
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this ratio with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this ratio with.
     * @return {@code true} if the object is equal to this ratio,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since the denominator is positive and coprime with the numerator,
           two ratios are equal iff their numerator and denominator are. */
        if (this == o) return true;
        if (!(o instanceof Acl2Ratio)) return false;
        Acl2Ratio that = (Acl2Ratio) o;
        if (!numerator.equals(that.numerator)) return false;
        return denominator.equals(that.denominator);
    }

    /**
     * Returns a hash code for this ratio.
     *
     * @return A hash code for this ratio.
     */
    @Override
    public int hashCode() {
        int result = numerator.hashCode();
        result = 31 * result + denominator.hashCode();
        return result;
    }

    /**
     * Returns a printable representation of this ratio.
     * We return a Java string that
     * conforms to ACL2's notation for ratios.
     *
     * @return A printable representation of this ratio.
     */
    @Override
    public String toString() {
        return this.numerator + "/" + this.denominator;
    }

    /**
     * Returns a ratio with the given numerator and denominator.
     * This method must be public because
     * the corresponding method in {@link Acl2Rational} is public,
     * but it cannot be called form outside the package
     * because the {@link Acl2Ratio} class is not public.
     *
     * @param numerator   The numerator of the ratio.
     *                    It is never {@code null}
     *                    and always coprime with {@code denominator}.
     * @param denominator The denominator of the ratio.
     *                    It is never {@code null},
     *                    always greater than 1,
     *                    and always coprime with {@code numerator}.
     * @return The ratio.
     */
    public static Acl2Ratio make(Acl2Integer numerator,
                                 Acl2Integer denominator) {
        return new Acl2Ratio(numerator, denominator);
    }

    /**
     * Returns the numerator of this ratio.
     * The numerator is in reduced form,
     * i.e. it is coprime with the denominator,
     * and its sign is consistent with a positive denominator.
     *
     * @return The numerator of this ratio.
     */
    @Override
    public Acl2Integer getNumerator() {
        return numerator;
    }

    /**
     * Returns the denominator of this ACL2 ratio.
     * The numerator is in reduced form,
     * i.e. it is positive and coprime with the numerator.
     *
     * @return The denominator of this ratio.
     */
    @Override
    public Acl2Integer getDenominator() {
        return denominator;
    }

}
