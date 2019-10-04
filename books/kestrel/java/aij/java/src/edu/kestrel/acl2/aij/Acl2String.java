/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Representation of ACL2 strings.
 * These are the values that satisfy {@code stringp}.
 */
public final class Acl2String extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Checks if the argument Java string
     * is a valid representation of an ACL2 string.
     * This is the case when every Java character of the string
     * is below 256, i.e. it is a valid representation of an ACL2 character.
     *
     * @param jstring The Java string to check for validity.
     * @return {@code true} if the string is valid, otherwise {@code false}.
     */
    private static boolean isValidString(String jstring) {
        int len = jstring.length();
        for (int i = 0; i < len; ++i)
            if (jstring.charAt(i) > 255)
                return false;
        return true;
    }

    /**
     * Representation of this string as a Java string.
     * This is never {@code null} and
     * it always satisfies {@link #isValidString(String)}.
     */
    private final String jstring;

    /**
     * Constructs a string with the given representation as a Java string.
     *
     * @param jstring The representation as a Java string.
     */
    private Acl2String(String jstring) {
        this.jstring = jstring;
    }

    /**
     * All the strings created so far.
     * These are stored as values of a map that has Java strings as keys:
     * each key-value pair is such that
     * the key is the {@link #jstring} field of the value.
     * The values of the map are reused by the {@link #make(String)} method.
     * In other words, all the strings are interned.
     * This field is never {@code null},
     * its keys are never {@code null},
     * and its valules are never {@code null}.
     */
    private static final Map<String, Acl2String> strings = new HashMap<>();

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this string is a string, which is always true.
     * This is consistent with the {@code stringp} ACL2 function.
     *
     * @return The symbol {@code t}.
     */
    @Override
    Acl2Symbol stringp() {
        return Acl2Symbol.T;
    }

    /**
     * Coerces this string to a list,
     * consistently with the {@code coerce} ACL2 function
     * when the second argument is {@code list}.
     *
     * @return The list of characters corresponding to this string.
     */
    @Override
    Acl2Value coerceToList() {
        Acl2Value list = Acl2Symbol.NIL;
        for (int i = this.jstring.length() - 1; i >= 0; --i) {
            Acl2Character character =
                    Acl2Character.make(this.jstring.charAt(i));
            list = Acl2ConsPair.make(character, list);
        }
        return list;
    }

    /**
     * Interns this string into the package of the argument value,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this string is the first argument of that function
     * and the argument value is the second argument of that function.
     *
     * @param sym The value whose package this string is interned into.
     * @return The symbol obtained by interning this string
     * into the package of the argument value.
     */
    @Override
    Acl2Symbol internThisInPackageOf(Acl2Value sym) {
        return sym.internInPackageOfThis(this);
    }

    /**
     * Returns the list of symbols imported by
     * the package named by this string,
     * consistently with the {@code pkg-imports} ACL2 function.
     * An exception is thrown if this string does not name a known package
     * (this includes the case in which the string is not a valid package name).
     * This is in accordance with the ACL2 manual page for {@code pkg-imports},
     * which says that evaluation fails in this case.
     *
     * @return The list of imported symbols.
     * @throws Acl2EvaluationException If the package name is invalid
     *                                 or the package is not defined.
     */
    @Override
    Acl2Value pkgImports() throws Acl2EvaluationException {
        String str = this.jstring;
        Acl2PackageName packageName;
        try {
            packageName = Acl2PackageName.make(str);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        Acl2Package packag = Acl2Package.getDefined(packageName);
        if (packag == null)
            throw new Acl2EvaluationException
                    ("Undefined package: \"" + packageName + "\".");
        List<Acl2Symbol> imports = packag.getImports();
        int len = imports.size();
        Acl2Value result = Acl2Symbol.NIL;
        for (int i = len - 1; i >= 0; --i)
            result = Acl2ConsPair.make(imports.get(i), result);
        return result;
    }

    /**
     * Returns the witness of the package named by this string,
     * consistently with the {@code pkg-witness} ACL2 function.
     *
     * @return The witness.
     * @throws Acl2EvaluationException If the package name is invalid
     *                                 or the package is not defined.
     * @throws IllegalStateException   If the package witness is not set yet.
     */
    @Override
    Acl2Symbol pkgWitness() throws Acl2EvaluationException {
        String str = this.jstring;
        Acl2PackageName packageName;
        try {
            packageName = Acl2PackageName.make(str);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        String witnessName = Acl2Package.getWitnessName();
        if (witnessName == null)
            throw new IllegalStateException("Witness not defined yet.");
        Acl2Symbol result;
        try {
            result = Acl2Symbol.make(packageName, witnessName);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        return result;
    }

    /**
     * Compares this string with the argument character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The character to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // strings are greater than characters:
        return 1;
    }

    /**
     * Compares this string with the argument string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The string to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToString(Acl2String o) {
        // compare underlying Java strings:
        return this.jstring.compareTo(o.jstring);
    }

    /**
     * Compares this string with the argument symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The symbol to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // strings are less than symbols:
        return -1;
    }

    /**
     * Compares this string with the argument number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The number to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // strings are greater than numbers:
        return 1;
    }

    /**
     * Compares this string with the argument rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The rational to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // strings are greater than rationals:
        return 1;
    }

    /**
     * Compares this string with the argument integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The integer to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // strings are greater than integers:
        return 1;
    }

    /**
     * Compares this string with the argument {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The {@code cons} pair to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // strings are less than cons pairs:
        return -1;
    }

    //////////////////////////////////////// public members:

    /**
     * Compares this string with the argument object for equality.
     * This is consistent with the {@code equal} ACL2 function.
     *
     * @param o The object to compare this string with.
     * @return {@code true} if the object is equal to this string,
     * otherwise {@code false}.
     */
    @Override
    public boolean equals(Object o) {
        /* Since strings are interned,
           a string is equal to an object iff
           they are the same object. */
        return this == o;
    }

    /**
     * Compares this string with the argument value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @param o The value to compare this string with.
     * @return A negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument.
     * @throws NullPointerException If the argument is {@code null}.
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return -o.compareToString(this);
    }

    /**
     * Returns a printable representation of this string.
     * The returned Java string is preceded and followed by double quotes.
     * Each character is kept as is if it is visible
     * (i.e. its code is between 33 and 126 inclusive)
     * and is not a backslash;
     * if it is a backslash, it is preceded by another backslash;
     * otherwise, it is turned into its hexadecimal code,
     * always as two digits, with lowercase letters,
     * preceded by backslash.
     * This scheme should ensure that strings are always printed clearly.
     *
     * @return A printable representation of this string.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append('"');
        for (int i = 0; i < this.jstring.length(); ++i) {
            char jchar = this.jstring.charAt(i);
            if (33 <= jchar && jchar <= 126 && jchar != '\\') {
                result.append(jchar);
            } else if (jchar == '\\') {
                result.append("\\\\");
            } else {
                result.append("\\")
                        .append(Integer.toHexString(jchar / 16))
                        .append(Integer.toHexString(jchar % 16));
            }
        }
        result.append('"');
        return new String(result);
    }

    /**
     * Returns a string consisting
     * with the given representation as a Java string.
     *
     * @param jstring The representation as a Java string.
     * @return The string.
     * @throws IllegalArgumentException If {@code jstring} is {@code null} or
     *                                  any of its characters exceeds 255.
     */
    public static Acl2String make(String jstring) {
        Acl2String string = strings.get(jstring);
        if (string != null)
            return string;
        if (jstring == null)
            throw new IllegalArgumentException("Null string.");
        if (!isValidString(jstring))
            throw new IllegalArgumentException
                    ("Invalid ACL2 string: \"" + jstring + "\".");
        string = new Acl2String(jstring);
        strings.put(jstring, string);
        return string;
    }

    /**
     * The empty string.
     */
    public static final Acl2String EMPTY = make("");

    /**
     * The string "ACL2".
     */
    public static final Acl2String ACL2 = make("ACL2");

    /**
     * Returns the representation of this string as a Java string.
     *
     * @return The representation of this string.
     */
    public String getJavaString() {
        return this.jstring;
    }

}
