/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 characters.
 * These are the values that satisfy {@code characterp}.
 */
public final class Acl2Character extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Code of this character.
     * Invariant: below 256.
     */
    private final char jchar;

    /**
     * Constructs a character with the given code.
     *
     * @param jchar The code of the character.
     *              Invariant: below 256.
     */
    private Acl2Character(char jchar) {
        this.jchar = jchar;
    }

    /**
     * All the characters.
     * These are created in advance by the static initializer,
     * and reused by the {@link #make(char)} method.
     * In other words, all the characters are (exhaustively) interned.
     * Invariant: not null.
     */
    private static final Acl2Character[] characters = new Acl2Character[256];

    /**
     * All the character codes.
     * These are created in advance by the static initializer,
     * and returned by the {@link #charCode()} method,
     * which therefore executes quickly,
     * avoiding the creation of a new integer.
     * Invariant: not null.
     */
    private static final Acl2Integer[] codes = new Acl2Integer[256];

    static {
        for (int code = 0; code < 256; ++code) {
            characters[code] = new Acl2Character((char) code);
            codes[code] = Acl2Integer.make(code);
        }
    }

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this character is a character, which is always true.
     * This is consistent with the {@code characterp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol characterp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the integer code of this character.
     * This is consistent with the {@code char-code} ACL2 function.
     *
     * @return The code of this character.
     */
    @Override
    Acl2Integer charCode() {
        return codes[jchar];
    }

    /**
     * Coerces this character to a character, which is a no-op.
     * This is consistent with
     * the {@code char-fix} ACL2 (non-built-in) function.
     *
     * @return This character, unchanged.
     */
    @Override
    Acl2Character charFix() {
        return this;
    }

    /**
     * Compares this character with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // compare character codes:
        return Integer.compare(this.jchar, o.jchar);
    }

    /**
     * Compares this character with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // characters are less than strings:
        return -1;
    }

    /**
     * Compares this character with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // characters are less than symbols:
        return -1;
    }

    /**
     * Compares this character with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // characters are greater than numbers:
        return 1;
    }

    /**
     * Compares this character with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // characters are greater than rationals:
        return 1;
    }

    /**
     * Compares this character with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // characters are greater than integers:
        return 1;
    }

    /**
     * Compares this character with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this character with.
     *          Invariant: not null.
     * @return A negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // characters are less than cons pairs:
        return -1;
    }

    /**
     * Returns the character with the given code.
     * This is for AIJ's internal use, as conveyed by the {@code i} in the name.
     *
     * @param jchar The code of the character, as a Java character.
     *              Invariant: below 256.
     * @return The character.
     */
    static Acl2Character imake(char jchar) {
        return characters[jchar];
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this character with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this character with.
     * @return {@code true} if the object is equal to this character,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since characters are interned,
           a character is equal to an object iff
           they are the same object. */
        return this == o;
    }

    /**
     * Compares this character with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this character with.
     * @return A negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is null.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return -o.compareToCharacter(this);
    }

    /**
     * Returns a printable representation of this character.
     * If the character is visible
     * (i.e. its code is between 33 and 126 inclusive),
     * it is returned as is, preceded by {@code #\} as in ACL2.
     * If the character is among the six with a special notation in ACL2
     * ({@code #\Space} etc.), it is returned in that special notation.
     * Otherwise, we return its hexadecimal code,
     * always as two digits, with lowercase letters,
     * preceded by {@code #\}.
     * This scheme should ensure that characters are always printed clearly.
     *
     * @return A printable representation of this character.
     */
    @Override
    public String toString() {
        if (33 <= this.jchar && this.jchar <= 126)
            return "#\\" + this.jchar;
        switch (this.jchar) {
            case 9:
                return "#\\Tab";
            case 10:
                return "#\\Newline";
            case 12:
                return "#\\Page";
            case 13:
                return "#\\Return";
            case 32:
                return "#\\Space";
            case 127:
                return "#\\Rubout";
            default:
                return "#\\"
                        + Integer.toHexString(this.jchar / 16)
                        + Integer.toHexString(this.jchar % 16);
        }
    }

    /**
     * Returns the character with the given code.
     *
     * @param jchar The code of the character, as a Java character.
     * @return The character.
     * @throws IllegalArgumentException If {@code jchar} exceeds 255.
     */
    public static Acl2Character make(char jchar) {
        if (jchar < 256)
            return imake(jchar);
        else
            throw new IllegalArgumentException
                    ("Invalid character: '" + jchar + "'.");
    }

    /**
     * The character with code 0.
     */
    public static final Acl2Character CODE_0 = characters[0];

    /**
     * Returns the code of this character.
     *
     * @return The code of this character, as a Java character.
     * Invariant: below 256.
     */
    public char getJavaChar() {
        return this.jchar;
    }

}
