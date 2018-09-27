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
        assert jchar < 256;
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
     * Supports the native implementation of
     * the {@code characterp} ACL2 function.
     */
    @Override
    Acl2Symbol characterp() {
        return Acl2Symbol.T;
    }

    /**
     * Supports the native implementation of
     * the {@code char-code} ACL2 function.
     */
    @Override
    Acl2Integer charCode() {
        return Acl2Integer.make(jchar);
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
        if (o instanceof Acl2Number)
            // characters are greater than numbers:
            return 1;
        if (o instanceof Acl2Character) {
            int thisCode = this.jchar;
            int thatCode = ((Acl2Character) o).jchar;
            return Integer.compare(thisCode, thatCode);
        }
        // characters are less than strings, symbols, and pairs:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 character.
     * This should be improved to return something non-confusing
     * when the character is "unusual".
     */
    @Override
    public String toString() {
        return "#\\" + this.jchar;
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
                    ("Invalid character jchar: '" + jchar + "'.");
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
