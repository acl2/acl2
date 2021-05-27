/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 complex rationals.
 * These are the values that satisfy {@code complex-rationalp}.
 * Note that these values do not satisfy {@code rationalp}.
 * <p>
 * This class is not public because code outside this package
 * must use the public methods in the {@link Acl2Number} class
 * to create numbers (which may be rationals or complex rationals).
 */
final class Acl2ComplexRational extends Acl2Number {

    //////////////////////////////////////// private members:

    /**
     * Real part of this complex rational.
     * Invariant: not null.
     */
    private final Acl2Rational realPart;

    /**
     * Imaginary part of this complex rational.
     * Invariant: not null, not 0.
     */
    private final Acl2Rational imaginaryPart;

    /**
     * Constructs a complex rational
     * with the given real and imaginary parts.
     *
     * @param realPart      The real part of the complex rational.
     *                      Invariant: not null.
     * @param imaginaryPart The imaginary part of the complex rational.
     *                      Invariants: not null, not 0.
     */
    private Acl2ComplexRational(Acl2Rational realPart,
                                Acl2Rational imaginaryPart) {
        this.realPart = realPart;
        this.imaginaryPart = imaginaryPart;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this complex rational is a complex rational,
     * which is always true.
     * This is consistent with the {@code complex-rationalp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol complexRationalp() {
        return Acl2Symbol.T;
    }

    /**
     * Checks if this complex rational is a complex rational,
     * which is always true,
     * returning a Java boolean instead of an ACL2 symbol.
     * This is consistent with the {@code complex-rationalp} ACL2 function.
     *
     * @return {@code true}.
     */
    @Override
    boolean complexRationalpBoolean() {
        return true;
    }

    /**
     * Returns a complex rational with the given real and imaginary parts.
     *
     * @param realPart      The real part of the complex rational.
     *                      Invariant: not null.
     * @param imaginaryPart The imaginary part of the complex rational.
     *                      Invariants: not null, not 0.
     * @return The complex rational.
     */
    public static Acl2ComplexRational makeInternal(Acl2Rational realPart,
                                                   Acl2Rational imaginaryPart) {
        return new Acl2ComplexRational(realPart, imaginaryPart);
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this complex rational with the argument object
     * for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this complex rational with.
     * @return {@code true} if the object is equal to this complex rational,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Two complex rationals are equal iff
           their real and imaginary parts are. */
        if (this == o) return true;
        if (!(o instanceof Acl2ComplexRational)) return false;
        Acl2ComplexRational that = (Acl2ComplexRational) o;
        if (!realPart.equals(that.realPart)) return false;
        return imaginaryPart.equals(that.imaginaryPart);
    }

    /**
     * Returns a hash code for this complex rational.
     *
     * @return The hash code for this complex rational.
     */
    @Override
    public int hashCode() {
        int result = realPart.hashCode();
        result = 31 * result + imaginaryPart.hashCode();
        return result;
    }

    /**
     * Returns a printable representation of this complex rational.
     * We return a Java string that
     * conforms to ACL2's notation for complex rationals.
     *
     * @return A printable representation of this complex rational.
     */
    @Override
    public String toString() {
        return "#\\c(" + this.realPart + " " + this.imaginaryPart + ")";
    }

    /**
     * Returns the real part of this complex rational.
     * This is consistent with the {@code realpart} ACL2 function.
     *
     * @return The real part of this complex rational.
     */
    @Override
    public Acl2Rational getRealPart() {
        return this.realPart;
    }

    /**
     * Returns the imaginary part of this complex rational.
     * This is consistent with the {@code imagpart} ACL2 function.
     *
     * @return The imaginary part of this complex rational.
     */
    @Override
    public Acl2Rational getImaginaryPart() {
        return this.imaginaryPart;
    }

}
