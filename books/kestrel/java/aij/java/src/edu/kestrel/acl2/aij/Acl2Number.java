/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 numbers.
 * These are the ACL2 values that satisfy {@code acl2-numberp}.
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
     * Supports the native implementation of
     * the {@code acl2-numberp} ACL2 function.
     */
    @Override
    Acl2Symbol acl2Numberp() {
        return Acl2Symbol.T;
    }

    /**
     * Supports the native implementation of
     * the {@code realpart} ACL2 function.
     */
    @Override
    Acl2Rational realpart() {
        return this.getRealPart();
    }

    /**
     * Supports the native implementation of
     * the {@code imagpart} ACL2 function.
     */
    @Override
    Acl2Rational imagpart() {
        return this.getImaginaryPart();
    }

    /**
     * Coerce this ACL2 number to an ACL2 number,
     * i.e. just return this ACL2 number.
     * This is consistent with the {@code fix} ACL2 function.
     */
    @Override
    Acl2Number fix() {
        return this;
    }

    //////////////////////////////////////// public members:

    /**
     * Returns an ACL2 number with the given real and imaginary parts.
     * If the imaginary part is 0, the result is an ACL2 rational,
     * according to the rule of complex canonicalization in Common Lisp.
     *
     * @throws IllegalArgumentException if realpart or imaginaryPart is null
     */
    public static Acl2Number make(Acl2Rational realPart,
                                  Acl2Rational imaginaryPart) {
        if (realPart == null)
            throw new IllegalArgumentException("Null real part.");
        if (imaginaryPart == null)
            throw new IllegalArgumentException("Null imaginary part.");
        if (imaginaryPart.equals(Acl2Integer.ZERO))
            return realPart;
        else
            return Acl2ComplexRational.make(realPart, imaginaryPart);
    }

    /**
     * Returns the real part of this ACL2 number.
     */
    public abstract Acl2Rational getRealPart();

    /**
     * Returns the imaginary part of this ACL2 number.
     */
    public abstract Acl2Rational getImaginaryPart();
}
