/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
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
     * Real part of the ACL2 complex rational.
     * This is never {@code null}.
     */
    private final Acl2Rational realPart;

    /**
     * Imaginary part of the ACL2 complex rational.
     * This is never {@code null} and never 0.
     */
    private final Acl2Rational imaginaryPart;

    /**
     * Constructs an ACL2 complex rational from its real and imaginary parts.
     */
    private Acl2ComplexRational(Acl2Rational realPart,
                                Acl2Rational imaginaryPart) {
        assert realPart != null && imaginaryPart != null &&
                !imaginaryPart.equals(Acl2Integer.ZERO);
        this.realPart = realPart;
        this.imaginaryPart = imaginaryPart;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Supports the native implementation of
     * the {@code unary--} ACL2 function.
     */
    @Override
    Acl2Number negate() {
        // -(a+bi) is (-a)+(-b)i:
        Acl2Rational a = this.realPart;
        Acl2Rational b = this.imaginaryPart;
        return Acl2Number.make(a.negate(), b.negate());
    }

    /**
     * Supports the native implementation of
     * the {@code unary-/} ACL2 function.
     */
    Acl2Number reciprocate() {
        // 1/(a+bi) is (a/(aa+bb))-(b/(aa+bb))i:
        Acl2Rational a = this.realPart;
        Acl2Rational b = this.imaginaryPart;
        Acl2Rational aa = (Acl2Rational) a.multiply(a);
        Acl2Rational bb = (Acl2Rational) b.multiply(b);
        Acl2Rational aabb = (Acl2Rational) aa.add(bb);
        Acl2Rational aabbInv = aabb.reciprocate();
        Acl2Rational resultReal = (Acl2Rational) a.multiply(aabbInv);
        Acl2Rational resultImag = (Acl2Rational) b.negate().multiply(aabbInv);
        return Acl2Number.make(resultReal, resultImag);
    }

    /**
     * Supports the native implementation of
     * the {@code binary-+} ACL2 function.
     */
    @Override
    Acl2Number add(Acl2Value other) {
        assert other != null;
        if (other instanceof Acl2Number) {
            // (a+bi)+(c+di) is (a+c)+(b+d)i:
            Acl2Rational a = this.realPart;
            Acl2Rational b = this.imaginaryPart;
            Acl2Rational c = other.realpart();
            Acl2Rational d = other.imagpart();
            Acl2Rational resultReal = (Acl2Rational) a.add(c);
            Acl2Rational resultImag = (Acl2Rational) b.add(d);
            return Acl2Number.make(resultReal, resultImag);
        } else {
            // use Acl2Value.add()
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
        if (other instanceof Acl2Number) {
            // (a+bi)*(c+di) is (ac-bd)+(bc+ad)i:
            Acl2Rational a = this.realPart;
            Acl2Rational b = this.imaginaryPart;
            Acl2Rational c = other.realpart();
            Acl2Rational d = other.imagpart();
            Acl2Rational ac = (Acl2Rational) a.multiply(c);
            Acl2Rational bd = (Acl2Rational) b.multiply(d);
            Acl2Rational bc = (Acl2Rational) b.multiply(c);
            Acl2Rational ad = (Acl2Rational) a.multiply(d);
            Acl2Rational resultReal = (Acl2Rational) ac.add(bd.negate());
            Acl2Rational resultImag = (Acl2Rational) bc.add(ad);
            return Acl2Number.make(resultReal, resultImag);
        } else {
            // use Acl2Value.multiply()
            // and return the result because multiplication is commutative:
            return other.multiply(this);
        }
    }

    /**
     * Supports the native implementation of
     * the {@code complex-rationalp} ACL2 function.
     */
    @Override
    Acl2Symbol complexRationalp() {
        return Acl2Symbol.T;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 complex rational is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since complex rationals are disjoint from integers and rationals,
           only a complex rational can be equal to another complex rational.
           Two complex rationals are equal iff
           their real and imaginary parts are. */
        if (this == o) return true;
        if (!(o instanceof Acl2ComplexRational)) return false;
        Acl2ComplexRational that = (Acl2ComplexRational) o;
        if (!realPart.equals(that.realPart)) return false;
        return imaginaryPart.equals(that.imaginaryPart);
    }

    /**
     * Returns a hash code for this ACL2 complex rational.
     */
    @Override
    public int hashCode() {
        int result = realPart.hashCode();
        result = 31 * result + imaginaryPart.hashCode();
        return result;
    }

    /**
     * Compares this ACL2 complex rational
     * with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this complex rational is
     * less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        if (o instanceof Acl2Rational)
            // complex rationals are greater than rationals:
            return 1;
        if (o instanceof Acl2ComplexRational) {
            // compare real and imaginary parts lexicographically:
            Acl2ComplexRational that = (Acl2ComplexRational) o;
            int realCmp = this.realPart.compareTo(that.realPart);
            if (realCmp != 0)
                return realCmp;
            else
                return this.imaginaryPart.compareTo(that.imaginaryPart);
        }
        // complex rationals are less than
        // characters, strings, symbols, and pairs:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 complex rational.
     */
    @Override
    public String toString() {
        return this.realPart + "+" + this.imaginaryPart + "i";
    }

    /**
     * Returns an ACL2 complex rational with the given real and imaginary parts.
     * This method must be public because
     * the corresponding method in {@link Acl2Number} is public.
     * However, this method cannot be called from outside this package
     * because the {@link Acl2ComplexRational} class is not public.
     */
    public static Acl2ComplexRational make(Acl2Rational realPart,
                                           Acl2Rational imaginaryPart) {
        assert realPart != null && imaginaryPart != null &&
                !imaginaryPart.equals(Acl2Integer.ZERO);
        return new Acl2ComplexRational(realPart, imaginaryPart);
    }

    /**
     * Returns the real part of this ACL2 complex rational.
     */
    @Override
    public Acl2Rational getRealPart() {
        return this.realPart;
    }

    /**
     * Returns the imaginary part of this ACL2 complex rational.
     */
    @Override
    public Acl2Rational getImaginaryPart() {
        return this.imaginaryPart;
    }
}
