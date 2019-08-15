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
 * These are the ACL2 values that satisfy {@code stringp}.
 */
public final class Acl2String extends Acl2Value {

    //////////////////////////////////////// private members:

    /**
     * Checks if the argument Java string
     * is a valid representation of an ACL2 string.
     * This is the case when every Java character of the string
     * is below 256, i.e. it is a valid representation of an ACL2 character.
     */
    private static boolean isValidString(String jstring) {
        int len = jstring.length();
        for (int i = 0; i < len; ++i)
            if (jstring.charAt(i) > 255)
                return false;
        return true;
    }

    /**
     * Java string that represents the ACL2 string.
     * This is never {@code null} and
     * it always satisfies {@link #isValidString(String)}.
     */
    private final String jstring;

    /**
     * Constructs an ACL2 string from its Java string representation.
     */
    private Acl2String(String jstring) {
        this.jstring = jstring;
    }

    /**
     * All the ACL2 strings created so far.
     * These are stored as values of a map that has Java strings as keys:
     * each key-value pair is such that
     * the key is the {@link #jstring} field of the value.
     * The values of the map are reused by the {@link #make(String)} method.
     * In other words, all the ACL2 strings are interned.
     * This field is never {@code null}.
     */
    private static final Map<String, Acl2String> strings = new HashMap<>();

    //////////////////////////////////////// package-private members:

    /**
     * Returns {@code true},
     * consistently with the {@code stringp} ACL2 function.
     */
    @Override
    Acl2Symbol stringp() {
        return Acl2Symbol.T;
    }

    /**
     * Coerces this ACL2 string to a list,
     * consistently with the {@code coerce} ACL2 function
     * when the second argument is {@code list}.
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
     * Interns this ACL2 value in the package of the argument ACL2 value,
     * consistently with the {@code intern-in-package-of-symbol} ACL2 function,
     * where this ACL2 value is the first argument of that function
     * and the argument ACL2 value is the second argument of that function.
     */
    @Override
    Acl2Symbol internThisInPackageOf(Acl2Value sym) {
        return sym.internInPackageOfThis(this);
    }

    /**
     * Returns the ACL2 list of symbols imported by
     * the package named by this ACL2 string,
     * consistently with the {@code pkg-imports} ACL2 function.
     * An exception is thrown if this string does not name a known package
     * (this includes the case in which the string is not a valid package name).
     * This is in accordance with the ACL2 manual page for {@code pkg-imports},
     * which says that evaluation fails in this case.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
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
     * Returns the ACL2 string that is the name of
     * the witness of the package named by this ACL2 string,
     * consistently with the {@code pkg-witness} ACL2 function.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     * @throws IllegalStateException   if the package witness is not set yet
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
     * Compares this ACL2 string with the argument ACL2 character for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToCharacter(Acl2Character o) {
        // strings are greater than characters:
        return 1;
    }

    /**
     * Compares this ACL2 string with the argument ACL2 string for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToString(Acl2String o) {
        // compare underlying Java strings:
        return this.jstring.compareTo(o.jstring);
    }

    /**
     * Compares this ACL2 string with the argument ACL2 symbol for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToSymbol(Acl2Symbol o) {
        // strings are less than symbols:
        return -1;
    }

    /**
     * Compares this ACL2 string with the argument ACL2 number for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToNumber(Acl2Number o) {
        // strings are greater than numbers:
        return 1;
    }

    /**
     * Compares this ACL2 string with the argument ACL2 rational for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToRational(Acl2Rational o) {
        // strings are greater than rationals:
        return 1;
    }

    /**
     * Compares this ACL2 string with the argument ACL2 integer for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToInteger(Acl2Integer o) {
        // strings are greater than integers:
        return 1;
    }

    /**
     * Compares this ACL2 string with
     * the argument ACL2 {@code cons} pair for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     */
    @Override
    int compareToConsPair(Acl2ConsPair o) {
        // strings are less than cons pairs:
        return -1;
    }

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 string is equal to the argument object.
     * This is consistent with the {@code equal} ACL2 function.
     * Since the ACL2 strings are interned,
     * they are equal iff they are the same object.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this ACL2 string with the argument ACL2 value for order.
     * This is consistent with the {@code lexorder} ACL2 function.
     *
     * @return a negative integer, zero, or a positive integer as
     * this string is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2Value o) {
        if (o == null)
            throw new NullPointerException();
        return - o.compareToString(this);
    }

    /**
     * Returns a printable representation of this ACL2 string.
     * The returned Java string is preceded and followed by double quotes.
     * Each character is kept as is if it is visible
     * (i.e. its code is between 33 and 126 inclusive)
     * and is not a backslash;
     * if it is a backslash, it is preceded by another backslash;
     * otherwise, it is turned into its hexadecimal code,
     * always as two digits, with lowercase letters,
     * preceded by backslash.
     * This scheme should ensure that ACL2 strings are always printed clearly.
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
     * Returns an ACL2 string represented by the given Java string.
     *
     * @throws IllegalArgumentException if jstring is null or
     *                                  any of its characters exceeds 255
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
     * The empty ACL2 string.
     */
    public static final Acl2String EMPTY = make("");

    /**
     * The ACL2 string "ACL2".
     */
    public static final Acl2String ACL2 = make("ACL2");

    /**
     * Returns the Java string representation of this ACL2 string.
     */
    public String getJavaString() {
        return this.jstring;
    }

}
