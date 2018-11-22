/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.Map;

/**
 * Native Java implementations of the ACL2 primitive functions.
 * <p>
 * The ACL2 primitive functions are the ones
 * listed in the {@code primitive} topic of the ACL2 manual.
 * These functions do not have an {@code unnormalized-body} property,
 * and thus they are not part of
 * the defined functions in {@link Acl2Environment}.
 * <p>
 * The primitive ACL2 functions are implemented here
 * as Java methods that operate on ACL2 values
 * in the same way as the corresponding ACL2 functions.
 * These methods operate on all ACL2 values, regardless of guards:
 * in other words, they run as if guard checking were off.
 * <p>
 * All the ACL2 primitive functions are implemented here, except for {@code if}.
 * The ACL2 function {@code if} is non-strict:
 * thus, it is handled specially by the term evaluator,
 * see {@link Acl2FunctionApplication#eval(Map)}.
 */
class Acl2Primitive {

    //////////////////////////////////////// private members:

    /**
     * Native implementation of the {@code characterp} ACL2 function.
     */
    private static Acl2Symbol execCharacterp(Acl2Value x) {
        assert x != null;
        return x.characterp();
    }

    /**
     * Native implementation of the {@code stringp} ACL2 function.
     */
    private static Acl2Symbol execStringp(Acl2Value x) {
        assert x != null;
        return x.stringp();
    }

    /**
     * Native implementation of the {@code symbolp} ACL2 function.
     */
    private static Acl2Symbol execSymbolp(Acl2Value x) {
        assert x != null;
        return x.symbolp();
    }

    /**
     * Native implementation of the {@code integerp} ACL2 function.
     */
    private static Acl2Symbol execIntegerp(Acl2Value x) {
        assert x != null;
        return x.integerp();
    }

    /**
     * Native implementation of the {@code rationalp} ACL2 function.
     */
    private static Acl2Symbol execRationalp(Acl2Value x) {
        assert x != null;
        return x.rationalp();
    }

    /**
     * Native implementation of the {@code complex-rationalp} ACL2 function.
     */
    private static Acl2Symbol execComplexRationalp(Acl2Value x) {
        assert x != null;
        return x.complexRationalp();
    }

    /**
     * Native implementation of the {@code acl2-numberp} ACL2 function.
     */
    private static Acl2Symbol execAcl2Numberp(Acl2Value x) {
        assert x != null;
        return x.acl2Numberp();
    }

    /**
     * Native implementation of the {@code consp} ACL2 function.
     */
    private static Acl2Symbol execConsp(Acl2Value x) {
        assert x != null;
        return x.consp();
    }

    /**
     * Native implementation of the {@code char-code} ACL2 function.
     */
    private static Acl2Integer execCharCode(Acl2Value x) {
        assert x != null;
        return x.charCode();
    }

    /**
     * Native implementation of the {@code code-char} ACL2 function.
     */
    private static Acl2Character execCodeChar(Acl2Value x) {
        assert x != null;
        return x.codeChar();
    }

    /**
     * Native implementation of the {@code coerce} ACL2 function.
     */
    private static Acl2Value execCoerce(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        if (y.equals(Acl2Symbol.LIST))
            return x.coerceToList();
        else
            return Acl2String.coerceFromList(x);
    }

    /**
     * Native implementation of the {@code intern-in-package-of-symbol}
     * ACL2 function.
     *
     * @throws Acl2EvaluationException if the package named by the string
     *                                 is invalid or not defined
     */
    private
    static Acl2Symbol execInternInPackageOfSymbol(Acl2Value str, Acl2Value sym)
            throws Acl2EvaluationException {
        assert str != null && sym != null;
        return str.internInPackageOfSymbol(sym);
    }

    /**
     * Native implementation of the {@code symbol-package-name} ACL2 function.
     */
    private static Acl2String execSymbolPackageName(Acl2Value x) {
        assert x != null;
        return x.symbolPackageName();
    }

    /**
     * Native implementation of the {@code symbol-name} ACL2 function.
     */
    private static Acl2String execSymbolName(Acl2Value x) {
        assert x != null;
        return x.symbolName();
    }

    /**
     * Native implementation of the {@code pkg-imports} ACL2 function.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     */
    private static Acl2Value execPkgImports(Acl2Value pkg)
            throws Acl2EvaluationException {
        assert pkg != null;
        return pkg.pkgImports();
    }

    /**
     * Native implementation of the {@code pkg-witness} ACL2 function.
     * An exception is thrown if the string does not name a known package
     * (this includes the case in which the string is not a valid package name).
     * This is in accordance with the ACL2 manual page for {@code pkg-witness},
     * which says that evaluation fails in this case.
     *
     * @throws Acl2EvaluationException if the package name is invalid
     *                                 or the package is not defined
     * @throws IllegalStateException   if the package witness is not set yet
     */
    private static Acl2Value execPkgWitness(Acl2Value pkg)
            throws Acl2EvaluationException {
        assert pkg != null;
        return pkg.pkgWitness();
    }

    /**
     * Native implementation of the {@code unary--} ACL2 function.
     */
    private static Acl2Number execUnaryMinus(Acl2Value x) {
        assert x != null;
        return x.negate();
    }

    /**
     * Native implementation of the {@code unary-/} ACL2 function.
     */
    private static Acl2Number execUnarySlash(Acl2Value x) {
        assert x != null;
        return x.reciprocate();
    }

    /**
     * Native implementation of the {@code binary-+} ACL2 function.
     */
    private static Acl2Number execBinaryPlus(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        return x.add(y);
    }

    /**
     * Native implementation of the {@code binary-*} ACL2 function.
     */
    private static Acl2Number execBinaryStar(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        return x.multiply(y);
    }

    /**
     * Native implementation of the {@code <} ACL2 function.
     */
    private static Acl2Symbol execLessThan(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        int realCmp = x.realpart().compareTo(y.realpart());
        if (realCmp < 0 ||
                realCmp == 0 && x.imagpart().compareTo(y.imagpart()) < 0)
            return Acl2Symbol.T;
        else
            return Acl2Symbol.NIL;
    }

    /**
     * Native implementation of the {@code complex} ACL2 function.
     */
    private static Acl2Number execComplex(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        return Acl2Number.make(x.rfix(), y.rfix());
    }

    /**
     * Native implementation of the {@code realpart} ACL2 function.
     */
    private static Acl2Rational execRealpart(Acl2Value x) {
        assert x != null;
        return x.realpart();
    }

    /**
     * Native implementation of the {@code imagpart} ACL2 function.
     */
    private static Acl2Rational execImagpart(Acl2Value x) {
        assert x != null;
        return x.imagpart();
    }

    /**
     * Native implementation of the {@code numerator} ACL2 function.
     */
    private static Acl2Integer execNumerator(Acl2Value x) {
        assert x != null;
        return x.numerator();
    }

    /**
     * Native implementation of the {@code denominator} ACL2 function.
     */
    private static Acl2Integer execDenominator(Acl2Value x) {
        assert x != null;
        return x.denominator();
    }

    /**
     * Native implementation of the {@code cons} ACL2 function.
     */
    private static Acl2ConsPair execCons(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        return Acl2ConsPair.make(x, y);
    }

    /**
     * Native implementation of the {@code car} ACL2 function.
     */
    private static Acl2Value execCar(Acl2Value x) {
        assert x != null;
        return x.car();
    }

    /**
     * Native implementation of the {@code cdr} ACL2 function.
     */
    private static Acl2Value execCdr(Acl2Value x) {
        assert x != null;
        return x.cdr();
    }

    /**
     * Native implementation of the {@code equal} ACL2 function.
     */
    private static Acl2Value execEqual(Acl2Value x, Acl2Value y) {
        assert x != null && y != null;
        if (x.equals(y))
            return Acl2Symbol.T;
        else
            return Acl2Symbol.NIL;
    }

    /**
     * Native implementation of the {@code bad-atom<=} ACL2 function.
     * The ACL2 manual does not really document this function,
     * but the release notes for Version 2.9.1 of ACL2 say that
     * this function returns {@code nil} on values that are not bad atoms.
     * This is confirmed by inspecting
     * the Common Lisp code that implements this function
     * in the sources of the latest version of ACL2.
     * Since ACL2 values in AIJ are never bad atoms
     * because there is no way to construct them without modifying AIJ
     * (in particular, {@link Acl2Value} and its subclasses
     * cannot be subclassed outside the AIJ package).
     * Thus, this native implementation simply returns {@code nil}.
     */
    private static Acl2Value execBadAtomLessThanOrEqualTo(Acl2Value x,
                                                          Acl2Value y) {
        assert x != null && y != null;
        return Acl2Symbol.NIL;
    }

    //////////////////////////////////////// package-private members:

    /**
     * Calls the named primitive function on the given values.
     *
     * @throws Acl2EvaluationException if function is not the name of
     *                                 a primitive function,
     *                                 or the length of values
     *                                 differs from the function's arity,
     *                                 or the primitive function fails
     * @throws IllegalStateException   if the package witness is not set yet
     */
    static Acl2Value call(Acl2Symbol function, Acl2Value[] values)
            throws Acl2EvaluationException {
        assert function != null && values != null;
        for (Acl2Value value : values) assert value != null;
        if (function.equals(Acl2Symbol.CHARACTERP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CHARACTERP on "
                                + values.length
                                + " arguments.");
            return execCharacterp(values[0]);
        }
        if (function.equals(Acl2Symbol.STRINGP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called STRINGP on "
                                + values.length
                                + " arguments.");
            return execStringp(values[0]);
        }
        if (function.equals(Acl2Symbol.SYMBOLP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called SYMBOLP on "
                                + values.length
                                + " arguments.");
            return execSymbolp(values[0]);
        }
        if (function.equals(Acl2Symbol.INTEGERP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called INTEGERP on "
                                + values.length
                                + " arguments.");
            return execIntegerp(values[0]);
        }
        if (function.equals(Acl2Symbol.RATIONALP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called RATIONALP on "
                                + values.length
                                + " arguments.");
            return execRationalp(values[0]);
        }
        if (function.equals(Acl2Symbol.COMPLEX_RATIONALP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called COMPLEX-RATIONALP on "
                                + values.length
                                + " arguments.");
            return execComplexRationalp(values[0]);
        }
        if (function.equals(Acl2Symbol.ACL2_NUMBERP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called ACL2-NUMBERP on "
                                + values.length
                                + " arguments.");
            return execAcl2Numberp(values[0]);
        }
        if (function.equals(Acl2Symbol.CONSP)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CONSP on "
                                + values.length
                                + " arguments.");
            return execConsp(values[0]);
        }
        if (function.equals(Acl2Symbol.CHAR_CODE)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CHAR-CODE on "
                                + values.length
                                + " arguments.");
            return execCharCode(values[0]);
        }
        if (function.equals(Acl2Symbol.CODE_CHAR)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CODE-CHAR on "
                                + values.length
                                + " arguments.");
            return execCodeChar(values[0]);
        }
        if (function.equals(Acl2Symbol.COERCE)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called COERCE on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execCoerce(values[0], values[1]);
        }
        if (function.equals
                (Acl2Symbol.INTERN_IN_PACKAGE_OF_SYMBOL)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called INTERN-IN-PACKAGE-OF-SYMBOL on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execInternInPackageOfSymbol(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.SYMBOL_PACKAGE_NAME)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called SYMBOL-PACKAGE-NAME on "
                                + values.length
                                + " arguments.");
            return execSymbolPackageName(values[0]);
        }
        if (function.equals(Acl2Symbol.SYMBOL_NAME)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called SYMBOL-NAME on "
                                + values.length
                                + " arguments.");
            return execSymbolName(values[0]);
        }
        if (function.equals(Acl2Symbol.PKG_IMPORTS)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called PKG-IMPORTS on "
                                + values.length
                                + " arguments.");
            return execPkgImports(values[0]);
        }
        if (function.equals(Acl2Symbol.PKG_WITNESS)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called PKG-WITNESS on "
                                + values.length
                                + " arguments.");
            return execPkgWitness(values[0]);
        }
        if (function.equals(Acl2Symbol.UNARY_MINUS)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called UNARY-- on "
                                + values.length
                                + " arguments.");
            return execUnaryMinus(values[0]);
        }
        if (function.equals(Acl2Symbol.UNARY_SLASH)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called UNARY-/ on "
                                + values.length
                                + " arguments.");
            return execUnarySlash(values[0]);
        }
        if (function.equals(Acl2Symbol.BINARY_PLUS)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called BINARY-+ on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execBinaryPlus(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.BINARY_TIMES)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called BINARY-* on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execBinaryStar(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.LESS_THAN)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called < on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execLessThan(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.COMPLEX)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called COMPLEX on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execComplex(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.REALPART)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called REALPART on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execRealpart(values[0]);
        }
        if (function.equals(Acl2Symbol.IMAGPART)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called IMAGPART on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execImagpart(values[0]);
        }
        if (function.equals(Acl2Symbol.NUMERATOR)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called NUMERATOR on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execNumerator(values[0]);
        }
        if (function.equals(Acl2Symbol.DENOMINATOR)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called DENOMINATOR on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execDenominator(values[0]);
        }
        if (function.equals(Acl2Symbol.CONS)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called CONS on "
                                + values.length
                                + (values.length == 1 ?
                                " argument." : " arguments."));
            return execCons(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.CAR)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CAR on "
                                + values.length
                                + " arguments.");
            return execCar(values[0]);
        }
        if (function.equals(Acl2Symbol.CDR)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called CDR on "
                                + values.length
                                + " arguments.");
            return execCdr(values[0]);
        }
        if (function.equals(Acl2Symbol.EQUAL)) {
            if (values.length != 2)
                throw new Acl2EvaluationException
                        ("Called EQUAL on "
                                + values.length
                                + " arguments.");
            return execEqual(values[0], values[1]);
        }
        if (function.equals(Acl2Symbol.BAD_ATOM_LESS_THAN_OR_EQUAL_TO)) {
            if (values.length != 1)
                throw new Acl2EvaluationException
                        ("Called BAD-ATOM<= on "
                                + values.length
                                + " arguments.");
            return execBadAtomLessThanOrEqualTo(values[0], values[1]);
        }
        throw new Acl2EvaluationException
                ("Called non-primitive function: \"" + function + "\".");
    }
}
