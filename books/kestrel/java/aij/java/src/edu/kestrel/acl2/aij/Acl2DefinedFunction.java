/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.Map;

/**
 * Representation of ACL2 defined functions in ACL2 terms.
 * These are functions that are defined via ACL2 terms,
 * as opposed to the functions natively implemented in Java
 * (see {@link Acl2NativeFunction}).
 */
final class Acl2DefinedFunction extends Acl2NamedFunction {

    //////////////////////////////////////// private members:

    /**
     * Constructs an ACL2 defined function with the given name.
     * The name is never that of an ACL2 function
     * that is implemented natively in Java,
     * because such functions are represented as
     * instances of {@link Acl2NativeFunction}.
     *
     * @param name The name of the function.
     */
    private Acl2DefinedFunction(Acl2Symbol name) {
        super(name);
    }

    /**
     * All the ACL2 defined functions created so far.
     * These are stored as values of a map
     * that has the symbols that name the functions as keys:
     * each key-value pair is such that
     * the key is the {@link Acl2NamedFunction#getName()} field of the value.
     * The values of the map are reused
     * by the {@link #getInstance(Acl2Symbol)} method.
     * In other words, all the ACL2 defined functions are interned.
     * This field is never {@code null}.
     */
    private static final Map<Acl2Symbol, Acl2DefinedFunction> functions =
            new HashMap<>();

    /**
     * Definiens of this function.
     * This is set, once, to the lambda expression that defines this function
     * by {@link #define(Acl2Symbol[], Acl2Term)}.
     */
    private Acl2LambdaExpression definiens = null;

    /**
     * Flag saying whether this function has a validated definition.
     * This is set once by {@link #validateDefinition()},
     * and never changes back to {@code false}.
     */
    private boolean validated = false;

    //////////////////////////////////////// package-private members:

    /**
     * Returns the number of parameters of this defined function.
     *
     * @return The number of parameters of this defined function.
     * @throws IllegalStateException if this defined function
     *                               has no actual definition yet
     */
    @Override
    int getArity() {
        if (this.definiens == null)
            throw new IllegalStateException
                    ("Attempting to retrieve the arity of function "
                            + this.getName() + ", which is not defined yet.");
        return this.definiens.getArity();
    }

    /**
     * Ensure that this function has a valid definition.
     * This means that all the function calls in the body of the function
     * are validated, i.e. the arguments match the arities
     * (see @{@link Acl2Term#validateFunctionCalls()}).
     * Returns quickly if the function is already validated.
     *
     * @throws IllegalStateException if the check fails
     */
    void validateDefinition() {
        if (validated)
            return;
        this.definiens.validateFunctionCalls();
        validated = true;
    }

    /**
     * Ensure that all the defined functions created so far
     * have valid definitions.
     * We call {@link #validateDefinition()}
     * on all the functions created so far.
     */
    static void validateAllDefinitions() {
        for (Acl2DefinedFunction function : functions.values())
            function.validateDefinition();
        Acl2NamedFunction.setValidatedAll(true);
    }

    /**
     * Checks if this defined function is
     * the {@code if} ACL2 primitive function.
     * This is never the case, because that function is represented as
     * an instance of {@link Acl2NativeFunction}.
     *
     * @return {@code false}
     */
    @Override
    boolean isIf() {
        return false;
    }

    /**
     * Checks if this defined function is
     * the {@code or} ACL2 "pseudo-function".
     * This is never the case, because that function is represented as
     * an instance of {@link Acl2NativeFunction}.
     *
     * @return {@code false}
     */
    @Override
    boolean isOr() {
        return false;
    }

    /**
     * Applies this ACL2 defined function to the given ACL2 values.
     * The defining lambda expression is applied to the values.
     * This is never called if the definiens is not set or validated.
     *
     * @param values The actual arguments to pass to the function.
     * @return The result of the function on the given arguments.
     * @throws Acl2EvaluationException if a call of {@code pkg-imports}
     *                                 or {@code pkg-witness} fails
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2EvaluationException {
        return definiens.apply(values);
    }

    /**
     * Returns an ACL2 defined function with the given name.
     *
     * @param name The name of the ACL2 defined function.
     * @return The ACL2 defined function.
     */
    static Acl2DefinedFunction getInstance(Acl2Symbol name) {
        Acl2DefinedFunction function = functions.get(name);
        if (function != null)
            return function;
        function = new Acl2DefinedFunction(name);
        functions.put(name, function);
        Acl2NamedFunction.setValidatedAll(false);
        return function;
    }

    //////////////////////////////////////// public members:

    /**
     * Defines this ACL2 defined function.
     * That is, actually sets the definition of the function.
     * The indices of the variables in the definiens are set
     * (see {@link Acl2Variable}).
     *
     * @param parameters The formal parameters of the function definition.
     * @param body       The body of the function definition.
     * @throws IllegalArgumentException if parameters or body is null
     *                                  or the function definition is malformed
     *                                  in a way that
     *                                  some valid variable index cannot be set
     * @throws IllegalStateException    if the function is already defined,
     *                                  or some variable index is already set
     */
    @Override
    public void define(Acl2Symbol[] parameters, Acl2Term body) {
        Acl2Symbol name = this.getName();
        if (this.definiens != null)
            throw new IllegalStateException
                    ("Function already defined: \"" + name + "\".");
        Acl2LambdaExpression definiens =
                Acl2LambdaExpression.make(parameters, body);
        definiens.setVariableIndices();
        this.definiens = definiens;
    }

}
