/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.Map;

/**
 * Representation of ACL2 package names.
 * Instances of this class are immutable.
 */
public final class Acl2PackageName implements Comparable<Acl2PackageName> {

    //////////////////////////////////////// private members:

    /**
     * Checks if the argument Java character is valid for an ACL2 package name.
     * A valid package name character is standard
     * (i.e. it satisfies the {@code standard-char-p} ACL2 function)
     * and is not lowercase.
     * The standard characters have the code 10 (i.e. {@code #\Newline})
     * and the codes from 32 to 126.
     * The lowercase characters have the codes from 97 to 122.
     */
    private static boolean isValidChar(char chr) {
        return chr == 10 ||
                (32 <= chr && chr < 97) ||
                (122 < chr && chr <= 126);
    }

    /**
     * Checks if the argument Java string is a valid ACL2 package name.
     * A valid package name is not empty
     * and contains only characters that are valid for a package name.
     */
    private static boolean isValidString(String str) {
        if (str.equals(""))
            return false;
        int len = str.length();
        for (int i = 0; i < len; ++i)
            if (!isValidChar(str.charAt(i)))
                return false;
        return true;
    }

    /**
     * Java string representation of the ACL2 package name.
     * Note that Java strings are a superset of the valid ACL2 package names.
     * This is never {@code null} and
     * it always satisfies {@link #isValidString(String)}.
     */
    private final String name;

    /**
     * Constructs a package name from its Java string representation.
     */
    private Acl2PackageName(String name) {
        this.name = name;
    }

    /**
     * All the ACL2 package names created so far.
     * These are stored as values of a map that has Java strings as keys:
     * each key-value pair is such that
     * the key is the {@link #name} field of the value.
     * The values of the map are reused  by the {@link #make(String)} method.
     * In other words, all the package names are interned.
     * This field is never {@code null}.
     */
    private static final Map<String, Acl2PackageName> packageNames =
            new HashMap<>();

    //////////////////////////////////////// public members:

    /**
     * Checks if this ACL2 package name is equal to the argument object.
     * Since the package names are interned,
     * they are equal iff they are the same object.
     */
    @Override
    public boolean equals(Object o) {
        return this == o;
    }

    /**
     * Compares this ACL2 package name to the argument ACL2 package name
     * for order.
     * This amounts to comparing the underlying Java strings.
     *
     * @return a negative integer, zero, or a positive integer as
     * this package name is less than, equal to, or greater than the argument
     * @throws NullPointerException if the argument is null
     */
    @Override
    public int compareTo(Acl2PackageName o) {
        return this.name.compareTo(o.name);
    }

    /**
     * Returns a printable representation of this ACL2 package name.
     * The result is just the Java string consisting of the package name itself
     * if every character in the package name is a letter, digit, or a dash,
     * and the first character is not a digit.
     * otherwise, this Java string is preceded and followed by a vertical bar,
     * and any backslash or vertical bar in the package name
     * is preceded by backslash.
     * This scheme should ensure that
     * ACL2 package names are always printed clearly.
     * The conditions here under which
     * the package name is surrounded by vertical bars
     * are more stringent than in ACL2;
     * future versions of this method may relax those conditions
     * and match ACL2's conditions more closely.
     * This scheme should ensure that ACL2 package names
     * are always printed clearly.
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        boolean noBars = true;
        for (int i = 0; i < this.name.length(); ++i) {
            char jchar = this.name.charAt(i);
            noBars = noBars &&
                    (('A' <= jchar && jchar <= 'Z') ||
                            ('0' <= jchar && jchar <= '9' && i != 0) ||
                            (jchar == '-'));
            if (jchar == '|')
                result.append("\\|");
            else if (jchar == '\\')
                result.append("\\\\");
            else
                result.append(jchar);
        }
        if (!noBars) {
            result.insert(0, '|');
            result.append('|');
        }
        return new String(result);
    }

    /**
     * Returns the ACL2 package name represented by the given Java string.
     *
     * @throws IllegalArgumentException if name is null or
     *                                  not valid for ACL2 package names
     */
    public static Acl2PackageName make(String name) {
        Acl2PackageName packageName = packageNames.get(name);
        if (packageName != null)
            return packageName;
        if (name == null)
            throw new IllegalArgumentException("Null package name.");
        if (!isValidString(name))
            throw new IllegalArgumentException
                    ("Invalid package name: \"" + name + "\".");
        packageName = new Acl2PackageName(name);
        packageNames.put(name, packageName);
        return packageName;
    }

    /**
     * Name of the {@code "KEYWORD"} built-in package.
     */
    public static final Acl2PackageName KEYWORD = make("KEYWORD");

    /**
     * Name of the {@code "COMMON-LISP"} built-in package.
     */
    public static final Acl2PackageName LISP = make("COMMON-LISP");

    /**
     * Name of the {@code "ACL2"} built-in package.
     */
    public static final Acl2PackageName ACL2 = make("ACL2");

    /**
     * Name of the {@code "ACL2-OUTPUT-CHANNEL"} built-in package.
     */
    public static final Acl2PackageName ACL2_OUTPUT =
            make("ACL2-OUTPUT-CHANNEL");

    /**
     * Name of the {@code "ACL2-INPUT-CHANNEL"} built-in package.
     */
    public static final Acl2PackageName ACL2_INPUT = make("ACL2-INPUT-CHANNEL");

    /**
     * Name of the {@code "ACL2-PC"} built-in package.
     */
    public static final Acl2PackageName ACL2_PC = make("ACL2-PC");

    /**
     * Name of the {@code "ACL2-USER"} built-in package.
     */
    public static final Acl2PackageName ACL2_USER = make("ACL2-USER");

    /**
     * Returns the Java string that represents this ACL2 package name.
     */
    public String getJavaString() {
        return this.name;
    }
}
