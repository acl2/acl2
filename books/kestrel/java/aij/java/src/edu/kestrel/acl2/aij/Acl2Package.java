/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
     * Invariant: not null.
     */
    private final Acl2PackageName name;

    /**
     * Import list of this package.
     * Invariant: not null.
     */
    private final List<Acl2Symbol> imports;

    /**
     * Constructs a package with the given name and import list.
     *
     * @param name    The name of the package.
     *                Invariant: not null.
     * @param imports The import list of the package.
     *                Invariant: not null.
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
     * Invariant: not null, no null keys, no null values.
     */
    private static final Map<Acl2PackageName, Acl2Package> packages =
            new HashMap<>();

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
     * @param name The name of the package.
     *             Invariant: not null.
     * @return The package with the given name,
     * or {@code null} if there is no package with the given name.
     */
    static Acl2Package getDefined(Acl2PackageName name) {
        return packages.get(name);
    }

    /**
     * Content of the {@code *pkg-witness-name*} ACL2 constant.
     * This constant describes
     * the exact semantics of the ACL2 function {@code pkg-witness}.
     * The value of this constant is an ACL2 string,
     * but we use the corresponding Java string here.
     */
    static final String WITNESS_NAME = "ACL2-PKG-WITNESS";

    //////////////////////////////////////// public members:

    /**
     * Defines a package with the given name and import list.
     * The imported symbols must have all different names.
     * This method makes an internal copy of the argument list,
     * which can be thus freely modified after this method returns.
     * <p>
     * The "KEYWORD" package must have an empty import list;
     * the "COMMON-LISP" package must have an empty import list;
     * the "ACL2" package must have an import list that only includes
     * symbols in the "COMMON-LISP" package.
     * We check these conditions because these three packages
     * are the first three to be defined (in that order),
     * but {@link Acl2Symbol} includes some symbols created
     * at class initialization time, i.e. before any package is defined;
     * thus, the additional checks here prevent
     * the import lists of "KEYWORD" and "COMMON-LISP"
     * from including any pre-created symbols
     * and the import list of "ACL2"
     * from including symbols not in the "COMMON-LISP" package.
     * We also check that these three packages are the first ones to be defined,
     * in that order.
     * After these three packages have been defined,
     * there is no issue with the pre-created symbols.
     *
     * @param name    The name of the package.
     * @param imports The import list of the package.
     * @return The package.
     * @throws IllegalArgumentException If {@code name} or {@code imports}
     *                                  is null,
     *                                  or if any element of {@code imports}
     *                                  is null
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
        // checks for the first three packages to define:
        int numberOfDefinedPackagesSoFar = packages.size();
        if (numberOfDefinedPackagesSoFar == 0) {
            if (name != Acl2PackageName.KEYWORD)
                throw new IllegalStateException
                        ("The " + Acl2PackageName.KEYWORD +
                                " package must be defined first, " +
                                "not the " + name + " package.");
            if (imports.size() != 0)
                throw new IllegalArgumentException
                        ("The " + Acl2PackageName.KEYWORD +
                                " package must import no symbols.");
        } else if (numberOfDefinedPackagesSoFar == 1) {
            if (name != Acl2PackageName.LISP)
                throw new IllegalStateException
                        ("The " + Acl2PackageName.LISP +
                                " package must be defined second, " +
                                "not the " + name + " package.");
            if (imports.size() != 0)
                throw new IllegalArgumentException
                        ("The " + Acl2PackageName.LISP +
                                " package must import no symbols.");
        } else if (numberOfDefinedPackagesSoFar == 2) {
            if (name != Acl2PackageName.ACL2)
                throw new IllegalStateException
                        ("The " + Acl2PackageName.ACL2 +
                                " package must be defined third, " +
                                "not the " + name + " package.");
            for (Acl2Symbol symbol : imports)
                if (symbol.getPackageName() != Acl2PackageName.LISP)
                    throw new IllegalArgumentException
                            ("The " + Acl2PackageName.ACL2 +
                                    " package must import only symbols " +
                                    " in the " + Acl2PackageName.LISP +
                                    " package.");
        }
        // define the package, unless already defined:
        if (packages.containsKey(name))
            throw new IllegalStateException
                    ("Package already defined: \"" + name + "\".");
        List<Acl2Symbol> importsCopy = new ArrayList<>(imports.size());
        for (Acl2Symbol symbol : imports) {
            if (symbol == null)
                throw new IllegalArgumentException("Null import symbol.");
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

}
