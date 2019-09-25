/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Representation of ACL2 packages.
 * Instances of this class are immutable.
 */
public final class Acl2Package {

    //////////////////////////////////////// private members:

    /**
     * Name of this package.
     * This is never {@code null}.
     */
    private final Acl2PackageName name;

    /**
     * Import list of this package.
     * This is never {@code null}.
     */
    private final List<Acl2Symbol> imports;

    /**
     * Constructs a package with the given name and import list.
     *
     * @param name    The name of the package.
     * @param imports The import list of the package.
     */
    private Acl2Package(Acl2PackageName name, List<Acl2Symbol> imports) {
        this.name = name;
        this.imports = imports;
    }

    /**
     * All the packages defined so far.
     * These are stored as values of a map that has package names as keys:
     * each key-value pair is such that
     * the key is the {@link #name} field of the value.
     * The values of the map are reused
     * by the {@link #define(Acl2PackageName, List)} method.
     * In other words, all the packages are interned.
     * This field is never {@code null},
     * its keys are never {@code null},
     * and its values are never {@code null}.
     */
    private static final Map<Acl2PackageName, Acl2Package> packages =
            new HashMap<>();

    /**
     * Content of the {@code *pkg-witness-name*} ACL2 constant.
     * This constant describes
     * the exact semantics of the ACL2 function {@code pkg-witness}.
     * The value of this constant is an ACL2 string,
     * but we use the corresponding Java string here.
     */
    private static String witnessName;

    //////////////////////////////////////// package-private members:

    /**
     * Returns a Java list of the imported symbols of this package.
     * The returned list is created anew, so it can be freely modified.
     *
     * @return A Java list of the imported symbols of this package.
     */
    List<Acl2Symbol> getImports() {
        List<Acl2Symbol> result = new ArrayList<>(imports.size());
        result.addAll(imports);
        return result;
    }

    /**
     * Returns the package with the given name, if any.
     * If no package with the given name is defined, {@code null} is returned.
     *
     * @param name The name of the package
     * @return The package with the given name,
     * or {@code null} if there is no package with the given name.
     */
    static Acl2Package getDefined(Acl2PackageName name) {
        return packages.get(name);
    }

    /**
     * Returns the content of the {@code *pkg-witness-name*} ACL2 constant.
     *
     * @return The content of {@code *pkg-witness-name*}, as a Java string.
     */
    static String getWitnessName() {
        return witnessName;
    }

    //////////////////////////////////////// public members:

    /**
     * Defines a package with the given name and import list.
     * The imported symbols must have all different names.
     * This method makes an internal copy of the argument list,
     * which can be thus freely modified after this method returns.
     *
     * @param name    The name of the package.
     * @param imports The import list of the package.
     * @return The package.
     * @throws IllegalArgumentException If {@code name} or {@code imports}
     *                                  is {@code null},
     *                                  or two imported symbols
     *                                  have the same name.
     * @throws IllegalStateException    If a package with the given name
     *                                  is already defined.
     */
    public static Acl2Package define(Acl2PackageName name,
                                     List<Acl2Symbol> imports) {
        if (name == null)
            throw new IllegalArgumentException("Null package name.");
        if (imports == null)
            throw new IllegalArgumentException("Null import list.");
        if (packages.containsKey(name))
            throw new IllegalStateException
                    ("Package already defined: \"" + name + "\".");
        List<Acl2Symbol> importsCopy = new ArrayList<>(imports.size());
        for (Acl2Symbol symbol : imports) {
            if (importsCopy.contains(symbol))
                throw new IllegalArgumentException
                        ("Symbol with name "
                                + symbol.getName()
                                + " already imported by package "
                                + name + ".");
            importsCopy.add(symbol);
        }
        Acl2Package newPackage = new Acl2Package(name, importsCopy);
        packages.put(name, newPackage);
        Acl2Symbol.addPackageImports(name, importsCopy);
        return newPackage;
    }

    /**
     * Sets the content of the {@code *pkg-witness-name*} ACL2 constant.
     *
     * @param content The content to set {@code *pkg-witness-name*},
     *                as a Java string.
     * @throws IllegalArgumentException If {@code content} is {@code null}.
     * @throws IllegalStateException    If the content is already set.
     */
    public static void setWitnessName(String content) {
        if (content == null)
            throw new IllegalArgumentException("Null witness.");
        if (witnessName == null)
            witnessName = content;
        else
            throw new IllegalStateException
                    ("Witness already defined: \""
                            + witnessName
                            + "\".");
    }

}
