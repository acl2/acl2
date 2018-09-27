/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 pairs.
 * These are the ACL2 values that satisfy {@code consp}.
 */
public final class Acl2Cons extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * First (i.e. {@code car}) component of the ACL2 pair.
     * This is never {@code null}.
     */
    private final Acl2Value car;

    /**
     * Second (i.e. {@code cdr}) component of the ACL2 pair.
     * This is never {@code null}.
     */
    private final Acl2Value cdr;

    /**
     * Constructs an ACL2 pair from its components.
     */
    private Acl2Cons(Acl2Value car, Acl2Value cdr) {
        assert car != null && cdr != null;
        this.car = car;
        this.cdr = cdr;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Supports the native implementation of
     * the {@code consp} ACL2 function.
     */
    @Override
    Acl2Symbol consp() {
        return Acl2Symbol.T;
    }

    /**
     * Supports the native implementation of
     * the {@code car} ACL2 function.
     */
    Acl2Value car() {
        return this.car;
    }

    /**
     * Supports the native implementation of
     * the {@code cdr} ACL2 function.
     */
    Acl2Value cdr() {
        return this.cdr;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 pair is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2Cons)) return false;
        Acl2Cons that = (Acl2Cons) o;
        if (!car.equals(that.car)) return false;
        return cdr.equals(that.cdr);
    }

    /**
     * Returns a hash code for this ACL2 pair.
     */
    @Override
    public int hashCode() {
        int result = car.hashCode();
        result = 31 * result + cdr.hashCode();
        return result;
    }

    /**
     * Compares this ACL2 pair with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this pair is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o instanceof Acl2Cons) {
            // the two components are compared lexicographically:
            Acl2Cons that = (Acl2Cons) o;
            int carCmp = this.car.compareTo(that.car);
            if (carCmp != 0)
                return carCmp;
            return this.cdr.compareTo(that.cdr);
        }
        // pairs are greater than atoms:
        return 1;
    }

    /**
     * Returns a printable representation of this ACL2 pair.
     * This is meant for printing;
     * it should be improved to return something non-confusing
     * when the components of the pair (or their sub-components)
     * contain "unusual" characters.
     */
    @Override
    public String toString() {
        return "(" + this.car + " . " + this.cdr + ")";
    }

    /**
     * Returns an ACL2 pair with the given components.
     *
     * @throws IllegalArgumentException if car or cdr is null
     */
    public static Acl2Cons make(Acl2Value car, Acl2Value cdr) {
        if (car == null)
            throw new IllegalArgumentException("Null CAR component.");
        if (cdr == null)
            throw new IllegalArgumentException("Null CDR component.");
        return new Acl2Cons(car, cdr);
    }

    /**
     * Returns the first component of this ACL2 pair.
     */
    public Acl2Value getCar() {
        return this.car;
    }

    /**
     * Returns the second component of this ACL2 pair.
     */
    public Acl2Value getCdr() {
        return this.cdr;
    }
}
