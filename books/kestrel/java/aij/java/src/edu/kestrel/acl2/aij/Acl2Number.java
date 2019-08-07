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
     * Returns {@code true},
     * consistently with the {@code acl2-numberp} ACL2 function.
     */
    @Override
    Acl2Symbol acl2Numberp() {
        return Acl2Symbol.T;
    }

    /**
     * Negates (arithmetically) this ACL2 number,
     * consistently with the {@code unary--} ACL2 function.
     */
    @Override
    Acl2Number negate() {
        // -(a+bi) is (-a)+(-b)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.make(a.negate(), b.negate());
    }

    /**
     * Reciprocates (arithmetically) this ACL2 number,
     * consistently with the {@code unary-/} ACL2 function.
     */
    @Override
    Acl2Number reciprocate() {
        // 1/(a+bi) is (a/(aa+bb))-(b/(aa+bb))i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational aa = a.multiplyRational(a);
        Acl2Rational bb = b.multiplyRational(b);
        Acl2Rational aabb = aa.addRational(bb);
        Acl2Rational aabbInv = aabb.reciprocate();
        Acl2Rational resultReal = a.multiplyRational(aabbInv);
        Acl2Rational resultImag = b.negate().multiplyRational(aabbInv);
        return Acl2Number.make(resultReal, resultImag);
    }

    /**
     * Adds the argument ACL2 value to this ACL2 number,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addValue(Acl2Value other) {
        return other.addNumber(this);
    }

    /**
     * Adds the argument ACL2 number to this ACL2 number,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addNumber(Acl2Number other) {
        // (a+bi)+(c+di) is (a+c)+(b+d)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational c = other.realpart();
        Acl2Rational d = other.imagpart();
        return Acl2Number.make(a.addRational(c), b.addRational(d));
    }

    /**
     * Adds the argument ACL2 rational to this ACL2 number,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addRational(Acl2Rational other) {
        // (a+bi)+c is (a+c)+bi:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.make(a.addRational(other), b);
    }

    /**
     * Adds the argument ACL2 integer to this ACL2 number,
     * consistently with the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number addInteger(Acl2Integer other) {
        // (a+bi)+c is (a+c)+bi:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.make(a.addRational(other), b);
    }

    /**
     * Multiplies the argument ACL2 value to this ACL2 number,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyValue(Acl2Value other) {
        return other.multiplyNumber(this);
    }

    /**
     * Multiplies the argument ACL2 number to this ACL2 number,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyNumber(Acl2Number other) {
        // (a+bi)*(c+di) is (ac-bd)+(bc+ad)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        Acl2Rational c = other.realpart();
        Acl2Rational d = other.imagpart();
        Acl2Rational ac = a.multiplyRational(c);
        Acl2Rational bd = b.multiplyRational(d);
        Acl2Rational bc = b.multiplyRational(c);
        Acl2Rational ad = a.multiplyRational(d);
        return Acl2Number.make(ac.addRational(bd.negate()), bc.addRational(ad));
    }

    /**
     * Multiplies the argument ACL2 rational to this ACL2 number,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyRational(Acl2Rational other) {
        // (a+bi)*c is (ac)+(bc)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.make
                (a.multiplyRational(other), b.multiplyRational(other));
    }

    /**
     * Multiplies the argument ACL2 integer to this ACL2 number,
     * consistently with the {@code binary-*} ACL2 function.
     */
    @Override
    Acl2Number multiplyInteger(Acl2Integer other) {
        // (a+bi)*c is (ac)+(bc)i:
        Acl2Rational a = this.realpart();
        Acl2Rational b = this.imagpart();
        return Acl2Number.make
                (a.multiplyRational(other), b.multiplyRational(other));
    }

    /**
     * Returns the real part of this ACL2 number,
     * consistently with the {@code realpart} ACL2 function.
     */
    @Override
    Acl2Rational realpart() {
        return this.getRealPart();
    }

    /**
     * Returns the imaginary part of this ACL2 number,
     * consistently with the {@code imagpart} ACL2 function.
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
