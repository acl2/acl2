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
 * These are the ACL2 values that satisfy {@code consp}.
 */
public final class Acl2ConsPair extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * First (i.e. {@code car}) component of this ACL2 {@code cons} pair.
     * This is never {@code null}.
     */
    private final Acl2Value car;

    /**
     * Second (i.e. {@code cdr}) component of this ACL2 {@code cons} pair.
     * This is never {@code null}.
     */
    private final Acl2Value cdr;

    /**
     * Constructs an ACL2 {@code cons} pair with the given components.
     *
     * @param car The first component of the {@code cons} pair.
     * @param cdr The second component of the {@code cons} pair.
     */
    private Acl2ConsPair(Acl2Value car, Acl2Value cdr) {
        this.car = car;
        this.cdr = cdr;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this ACL2 {@code cons} pair is an ACL2 {@code cons} pair.
     * This is consistent with the {@code consp} ACL2 function.
     *
     * @return The ACL2 symbol {@code t}.
     */
    @Override
    Acl2Symbol consp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the first component of this ACL2 {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this ACL2 {@code cons} pair.
     */
    @Override
    Acl2Value car() {
        return this.car;
    }

    /**
     * Returns the first component of this ACL2 {@code cons} pair.
     * This is consistent with the {@code cdr} ACL2 function.
     *
     * @return The second component of this ACL2 {@code cons} pair.
     */
    @Override
    Acl2Value cdr() {
        return this.cdr;
    }

    /**
     * Coerces this ACL2 {@code cons} pair to an ACL2 string.
     * This is consistent with the {@code coerce} ACL2 function
     * when the second argument is not {@code list}.
     */
    @Override
    Acl2String coerceToString() {
        List<Acl2Character> charList = new LinkedList<>();
        for (Acl2Value list = this;
             list instanceof Acl2ConsPair;
             list = ((Acl2ConsPair) list).cdr) {
            charList.add(((Acl2ConsPair) list).car.charFix());
        }
        int size = charList.size();
        char[] charArray = new char[size];
        for (int i = 0; i < size; ++i)
            charArray[i] = charList.get(i).getJavaChar();
        return Acl2String.make(new String(charArray));
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 character to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // cons pairs are greater than characters:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 string to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // cons pairs are greater than strings:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 symbol to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // cons pairs are greater than symbols:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 number to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // cons pairs are greater than numbers:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 rational to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // cons pairs are greater than rationals:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 integer to compare this ACL2 {@code cons} pair with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // cons pairs are greater than integers:
        return 1;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o ACL2 {@code cons} pair to compare
     *          this ACL2 {@code cons} pair with.
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

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 {@code cons} pair is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * If the argument is not a {@link Acl2Value}, the result is {@code false}.
     *
     * @param o The ACL2 object to compare this ACL2 {@code cons} pair with.
     * @return {@code true} if the ACL2 object is equal to
     * this ACL2 {@code cons} pair, otherwise {@code false}.
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
     * Returns a hash code for this ACL2 {@code cons} pair.
     *
     * @return The hash code for this ACL2 {@code cons} pair.
     */
    @Override
    public int hashCode() {
        int result = car.hashCode();
        result = 31 * result + cdr.hashCode();
        return result;
    }

    /**
     * Compares this ACL2 {@code cons} pair
     * with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The ACL2 value to compare this ACL2 character with.
     * @return A negative integer, zero, or a positive integer as this
     * {@code cons} pair is less than, equal to, or greater than the argument.
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        // compare the argument with this and flip the result:
        return -o.compareToConsPair(this);
    }

    /**
     * Returns a printable representation of this ACL2 {@code cons} pair.
     * We use the same dotted pair notation as ACL2.
     * The {@code car} and the {@code cdr}
     * are recursively turned into string representations.
     * Overall, this method
     * and the {@code toString} methods of the other value classes
     * should ensure that {@code cons} pairs are always printed clearly.
     *
     * @return The printable representation of this ACL2 {@code cons} pair.
     */
    @Override
    public String toString() {
        return "(" + this.car + " . " + this.cdr + ")";
    }

    /**
     * Returns an ACL2 {@code cons} pair with the given components.
     *
     * @param car The first component of the ACL2 {@code cons} pair.
     * @param cdr The second component of the ACL2 {@code cons} pair.
     * @return The ACL2 {@code cons} pair.
     * @throws IllegalArgumentException if car or cdr is null
     */
    public static Acl2ConsPair make(Acl2Value car, Acl2Value cdr) {
        if (car == null)
            throw new IllegalArgumentException("Null CAR component.");
        if (cdr == null)
            throw new IllegalArgumentException("Null CDR component.");
        return new Acl2ConsPair(car, cdr);
    }

    /**
     * Returns the first component of this ACL2 {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this ACL2 {@code cons} pair.
     */
    public Acl2Value getCar() {
        return this.car;
    }

    /**
     * Returns the second component of this ACL2 {@code cons} pair.
     * This is consistent with the {@code car} ACL2 function.
     *
     * @return The first component of this ACL2 {@code cons} pair.
     */
    public Acl2Value getCdr() {
        return this.cdr;
    }

}
