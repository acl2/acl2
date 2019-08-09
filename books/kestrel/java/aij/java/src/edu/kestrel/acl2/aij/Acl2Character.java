/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 characters.
 * These are the ACL2 values that satisfy {@code characterp}.
 */
public final class Acl2Character extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Code of the ACL2 character.
     * This is always below 256.
     */
    private final char jchar;

    /**
     * Constructs an ACL2 character with the given Java character as code.
     */
    private Acl2Character(char jchar) {
        this.jchar = jchar;
    }

    /**
     * All the ACL2 characters.
     * These are created in advance by the static initializer,
     * and reused by the {@link #make(char)} method.
     * In other words, all the ACL2 characters are (exhaustively) interned.
     * This field is never {@code null}.
     */
    private static final Acl2Character[] characters = new Acl2Character[256];

    static {
        for (int code = 0; code < 256; ++code)
            characters[code] = new Acl2Character((char) code);
    }

    //////////////////////////////////////// package-private members:

    /**
     * Returns {@code true},
     * consistently with the {@code characterp} ACL2 function.
     */
    @Override
    Acl2Symbol characterp() {
        return Acl2Symbol.T;
    }

    /**
     * Returns the ACL2 integer code of this ACL2 character,
     * consistently with the {@code char-code} ACL2 function.
     */
    @Override
    Acl2Integer charCode() {
        return Acl2Integer.make(jchar);
    }

    /**
     * Compares this ACL2 character with the argument ACL2 character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // compare character codes:
        return Integer.compare(this.jchar, o.jchar);
    }

    /**
     * Compares this ACL2 character with the argument ACL2 string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument
     */
    @Override
    int compareToString(Acl2String o) {
        // characters are less than strings:
        return -1;
    }

    /**
     * Compares this ACL2 character with the argument ACL2 symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // characters are less than symbols:
        return -1;
    }

    /**
     * Compares this ACL2 character with the argument ACL2 number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // characters are greater than numbers:
        return 1;
    }

    /**
     * Compares this ACL2 character with the argument ACL2 rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // characters are greater than rationals:
        return 1;
    }

    /**
     * Compares this ACL2 character with the argument ACL2 integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // characters are greater than integers:
        return 1;
    }

    /**
     * Compares this ACL2 character with
     * the argument ACL2 {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this value is less than, equal to, or greater than the argument
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // characters are less than cons pairs:
        return -1;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 character is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * Since the ACL2 characters are interned,
     * they are equal iff they are the same object.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this ACL2 character with the argument object for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this character is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return - o.compareToCharacter(this);
    }

    /**
     * Returns a printable representation of this ACL2 character.
     * If the character is visible
     * (i.e. its code is between 33 and 126 inclusive),
     * it is returned as is, preceded by {@code #\} as in ACL2.
     * If the character is among the six with a special notation in ACL2
     * ({@code #\Space} etc.), it is returned in that special notation.
     * Otherwise, we return its hexadecimal code,
     * always as two digits, with lowercase letters,
     * preceded by {@code #\}.
     * This scheme should ensure that
     * ACL2 characters are always printed clearly.
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
     * Returns the ACL2 character with the given Java character as code,
     * which must be below 256.
     *
     * @throws IllegalArgumentException if jchar exceeds 255
     */
    public static Acl2Character make(char jchar) {
        if (jchar < 256)
            return characters[jchar];
        else
            throw new IllegalArgumentException
                    ("Invalid character: '" + jchar + "'.");
    }

    /**
     * The ACL2 character with jchar 0.
     */
    public static final Acl2Character CODE_0 = characters[0];

    /**
     * Returns the code of this ACL2 character as a Java character,
     * always below 256.
     */
    public char getJavaChar() {
        return this.jchar;
    }

}
