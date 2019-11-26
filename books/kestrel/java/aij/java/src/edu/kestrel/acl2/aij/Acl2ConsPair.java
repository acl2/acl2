/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.LinkedList;
import java.util.List;

/**
 * Representation of ACL2 {@code cons} pairs.
 * These are the values that satisfy {@code consp}.
 */
public final class Acl2ConsPair extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * First (i.e. {@code car}) component of this {@code cons} pair.
     * Invariant: not null.
     */
    private final Acl2Value car;

    /**
     * Second (i.e. {@code cdr}) component of this {@code cons} pair.
     * Invariant: not null.
     */
    private final Acl2Value cdr;

    /**
     * Constructs a {@code cons} pair with the given components.
     *
     * @param car The first component of the {@code cons} pair.
     *            Invariant: not null.
     * @param cdr The second component of the {@code cons} pair.
     *            Invariant: not null.
     */
    private Acl2ConsPair(Acl2Value car, Acl2Value cdr) {
        this.car = car;
        this.cdr = cdr;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this {@code cons} pair is an {@code cons} pair.
     * This is consistent with the {@code consp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol consp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the first component of this {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this {@code cons} pair.
     */
    @Override
    Acl2Value car() {
        return this.car;
    }

    /**
     * Returns the first component of this {@code cons} pair.
     * This is consistent with the {@code cdr} ACL2 function.
     *
     * @return The second component of this {@code cons} pair.
     */
    @Override
    Acl2Value cdr() {
        return this.cdr;
    }

    /**
     * Coerces this {@code cons} pair to a string.
     * This is consistent with the {@code coerce} ACL2 function
     * when the second argument is not {@code list}.
     */
    @Override
    Acl2String coerceToString() {
        StringBuilder chars = new StringBuilder();
        Acl2Value list = this;
        do {
            Acl2ConsPair nonemptyList = (Acl2ConsPair) list;
            chars.append(nonemptyList.car.charFix().getJavaChar());
            list = nonemptyList.cdr;
        } while (list instanceof Acl2ConsPair);
        return Acl2String.imake(new String(chars));
    }

    /**
     * Compares this {@code cons} pair with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // cons pairs are greater than characters:
        return 1;
    }

    /**
     * Compares this {@code cons} pair with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // cons pairs are greater than strings:
        return 1;
    }

    /**
     * Compares this {@code cons} pair with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // cons pairs are greater than symbols:
        return 1;
    }

    /**
     * Compares this {@code cons} pair with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // cons pairs are greater than numbers:
        return 1;
    }

    /**
     * Compares this {@code cons} pair with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // cons pairs are greater than rationals:
        return 1;
    }

    /**
     * Compares this {@code cons} pair with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // cons pairs are greater than integers:
        return 1;
    }

    /**
     * Compares this {@code cons} pair
     * with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this {@code cons} pair with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // the two components are compared lexicographically:
        int carCmp = this.car.compareTo(o.car);
        if (carCmp != 0)
            return carCmp;
        return this.cdr.compareTo(o.cdr);
    }

    /**
     * Returns a {@code cons} pair with the given components.
     * This is for AIJ's internal use, as conveyed by the {@code i} in the name.
     *
     * @param car The first component of the {@code cons} pair.
     *            Invariant: not null.
     * @param cdr The second component of the {@code cons} pair.
     *            Invariant: not null.
     * @return The {@code cons} pair.
     */
    static Acl2ConsPair imake(Acl2Value car, Acl2Value cdr) {
        return new Acl2ConsPair(car, cdr);
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this {@code cons} pair is equal to the argument object.
     * This is consistent with the {@code equal} function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     *
     * @param o The object to compare this {@code cons} pair with.
     * @return {@code true} if the object is equal to this {@code cons} pair,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Acl2ConsPair)) return false;
        Acl2ConsPair that = (Acl2ConsPair) o;
        if (!car.equals(that.car)) return false;
        return cdr.equals(that.cdr);
    }

    /**
     * Returns a hash code for this {@code cons} pair.
     *
     * @return The hash code for this {@code cons} pair.
     */
    @Override
    public int hashCode() {
        int result = car.hashCode();
        result = 31 * result + cdr.hashCode();
        return result;
    }

    /**
     * Compares this {@code cons} pair with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        // compare the argument with this and flip the result:
        return -o.compareToConsPair(this);
    }

    /**
     * Returns a printable representation of this {@code cons} pair.
     * We use the same dotted pair notation as ACL2.
     * The {@code car} and the {@code cdr}
     * are recursively turned into string representations.
     * Overall, this method
     * and the {@code toString} methods of the other value classes
     * should ensure that {@code cons} pairs are always printed clearly.
     *
     * @return The printable representation of this {@code cons} pair.
     */
    @Override
    public String toString() {
        return "(" + this.car + " . " + this.cdr + ")";
    }

    /**
     * Returns a {@code cons} pair with the given components.
     *
     * @param car The first component of the {@code cons} pair.
     * @param cdr The second component of the {@code cons} pair.
     * @return The {@code cons} pair.
     * @throws IllegalArgumentException If {@code car} or {@code cdr} is null.
     */
    public static Acl2ConsPair make(Acl2Value car, Acl2Value cdr) {
        if (car == null)
            throw new IllegalArgumentException("Null CAR component.");
        if (cdr == null)
            throw new IllegalArgumentException("Null CDR component.");
        return imake(car, cdr);
    }

    /**
     * Returns the first component of this {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this {@code cons} pair.
     */
    public Acl2Value getCar() {
        return this.car;
    }

    /**
     * Returns the second component of this {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this {@code cons} pair.
     */
    public Acl2Value getCdr() {
        return this.cdr;
    }

}
