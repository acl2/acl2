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
        assert jstring != null;
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
        assert jstring != null && isValidString(jstring);
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
     * Supports the native implementation of
     * the {@code stringp} ACL2 function.
     */
    @Override
    Acl2Symbol stringp() {
        return Acl2Symbol.T;
    }

    /**
     * Coerce an ACL2 list of ACL2 characters to an ACL2 string.
     * If the ACL2 argument value is an atom that is not {@code nil},
     * it is treated as {@code nil}, i.e. the empty list.
     * If any element of the list is not an ACL2 character,
     * it is treated as the ACL2 character with code 0.
     * This is consistent with the {@code coerce} ACL2 function,
     * when its second argument is not {@code list}.
     *
     * @throws IllegalArgumentException if list is null or
     *                                  longer than the maximum Java integer
     */
    static Acl2String coerceFromList(Acl2Value list) {
        if (list == null)
            throw new IllegalArgumentException("Null character list.");
        int len = 0;
        for (;
             list instanceof Acl2ConsPair;
             list = ((Acl2ConsPair) list).getCdr()) {
            if (len == Integer.MAX_VALUE)
                throw new IllegalArgumentException("Character list too long.");
            else
                ++len;
        }
        char[] jcharacters = new char[len];
        for (int i = 0; i < len; ++i) {
            Acl2ConsPair pair = (Acl2ConsPair) list;
            Acl2Value element = pair.getCar();
            if (element instanceof Acl2Character)
                jcharacters[i] = ((Acl2Character) element).getJavaChar();
            else
                jcharacters[i] = 0;
            list = pair.getCdr();
        }
        return make(new String(jcharacters));
    }

    /**
     * Supports the native implementation of
     * the {@code coerce} ACL2 function,
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
     * Supports the native implementation of
     * the {@code intern-in-package-of-symbol} ACL2 function,
     * where this ACL2 value is the first argument of that function.
     */
    @Override
    Acl2Symbol internInPackageOfSymbol(Acl2Value sym) {
        if (sym instanceof Acl2Symbol) {
            Acl2PackageName packageName = ((Acl2Symbol) sym).getPackageName();
            return Acl2Symbol.make(packageName, this);
        } else {
            return Acl2Symbol.NIL;
        }
    }

    /**
     * Supports the native implementation of
     * the {@code pkg-imports} ACL2 function.
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
        String str = this.getJavaString();
        Acl2PackageName packageName = null;
        try {
            Acl2PackageName.make(str);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        if (Acl2Environment.hasPackage(packageName)) {
            List<Acl2Symbol> imported =
                    Acl2Environment.getImportedList(packageName);
            int len = imported.size();
            Acl2Value result = Acl2Symbol.NIL;
            for (int i = len - 1; i >= 0; --i)
                result = Acl2ConsPair.make(imported.get(i), result);
            return result;
        } else {
            throw new Acl2EvaluationException
                    ("Undefined package: \"" + packageName + "\".");
        }
    }

    /**
     * Supports the native implementation of
     * the {@code pkg-witness} ACL2 function.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     * @throws IllegalStateException   if the package witness is not set yet
     */
    @Override
    Acl2Value pkgWitness() throws Acl2EvaluationException {
        String str = this.jstring;
        Acl2PackageName packageName;
        try {
            packageName = Acl2PackageName.make(str);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        String witnessName = Acl2Environment.getPackageWitnessName();
        Acl2Symbol result;
        try {
            result = Acl2Symbol.make(packageName, witnessName);
        } catch (IllegalArgumentException e) {
            throw new Acl2EvaluationException(null, e);
        }
        return result;
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
        if (o instanceof Acl2Number || o instanceof Acl2Character)
            // strings are greater than numbers and characters:
            return 1;
        if (o instanceof Acl2String) {
            Acl2String that = (Acl2String) o;
            return this.jstring.compareTo(that.jstring);
        }
        // strings are less than symbols and cons pairs:
        return -1;
    }

    /**
     * Returns a printable representation of this ACL2 string.
     * This should be improved to return something non-confusing
     * when the string includes "unusual" characters.
     */
    @Override
    public String toString() {
        return this.jstring;
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
