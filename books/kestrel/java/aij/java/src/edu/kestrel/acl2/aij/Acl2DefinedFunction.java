/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Representation of ACL2 defined functions in ACL2 terms.
 * These are functions that have ACL2 definitions in {@link Acl2Environment},
 * as opposed to the functions natively implemented in Java
 * (see {@link Acl2NativeFunction}).
 */
final class Acl2DefinedFunction extends Acl2NamedFunction {

    //////////////////////////////////////// private members:

    /**
     * Constructs an ACL2 defined function from its name.
     * The name is never the one of
     * the {@code if} ACL2 primitive function
     * or the {@code or} ACL2 "pseudo-function"
     * (see {@link Acl2FunctionApplication#eval(Acl2Value[])}),
     * because these are represented as
     * instances of {@link Acl2NativeFunction}.
     */
    private Acl2DefinedFunction(Acl2Symbol name) {
        super(name);
        assert !name.equals(Acl2Symbol.IF) && !name.equals(Acl2Symbol.OR);
    }

    //////////////////////////////////////// package-private members:

    /**
     * Checks if this defined function is
     * the {@code if} ACL2 primitive function.
     * This is never the case, because of the invariant discussed in
     * {@link #Acl2DefinedFunction(Acl2Symbol)}.
     */
    @Override
    boolean isIf() {
        return false;
    }

    /**
     * Checks if this defined function is
     * the {@code or} ACL2 "pseudo-function".
     * This is never the case, because of the invariant discussed in
     * {@link #Acl2DefinedFunction(Acl2Symbol)}.
     */
    @Override
    boolean isOr() {
        return false;
    }

    /**
     * Applies this ACL2 defined function to the given ACL2 values.
     * The definition of the function is retrieved by the environment.
     * The resulting lambda expression is applied to the values.
     *
     * @throws Acl2EvaluationException if the call to this function fails
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException {
        assert values != null;
        for (Acl2Value value : values) assert value != null;
        Acl2LambdaExpression def = Acl2Environment.getFunctionDef(this.name);
        if (def == null)
            throw new Acl2EvaluationException
                    ("Undefined function: " + this.name + ".");
        return def.apply(values);
    }

    /**
     * Return an ACL2 defined function with the given name.
     */
    static Acl2DefinedFunction getInstance(Acl2Symbol name) {
        assert name != null;
        return new Acl2DefinedFunction(name);
    }
}
