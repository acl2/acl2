/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import java.util.HashMap;
import java.util.Map;

/**
 * Representation of ACL2 defined functions in terms.
 * These are functions that are defined via terms,
 * as opposed to the functions natively implemented in Java
 * (see {@link Acl2NativeFunction}).
 */
final class Acl2DefinedFunction extends Acl2NamedFunction {

    //////////////////////////////////////// private members:

    /**
     * Constructs a defined function with the given name.
     * The name is never that of a function
     * that is implemented natively in Java,
     * because such functions are represented as
     * instances of {@link Acl2NativeFunction}.
     *
     * @param name The name of the function.
     *             Invariant: not null.
     */
    private Acl2DefinedFunction(Acl2Symbol name) {
        super(name);
    }

    /**
     * All the defined functions created so far.
     * These are stored as values of a map
     * that has the symbols that name the functions as keys:
     * each key-value pair is such that
     * the key is the {@link Acl2NamedFunction#getName()} of the value.
     * The values of the map are reused
     * by the {@link #getInstance(Acl2Symbol)} method.
     * In other words, all the defined functions are interned.
     * Invariant: not null, no null keys, no null values.
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
     * Flag saying whether all the function calls
     * in this function's definition
     * are valid.
     * This is set once by {@link #validateFunctionCallsInDefinition()},
     * and never changes back to {@code false}.
     */
    private boolean validatedFunctionCalls = false;

    //////////////////////////////////////// package-private members:

    /**
     * Returns the number of parameters of this defined function.
     *
     * @return The number of parameters of this defined function.
     * If the function is not defined yet, -1 is returned.
     */
    @Override
    int getArity() {
        if (this.definiens == null)
            return -1;
        else
            return this.definiens.getArity();
    }

    /**
     * Ensure that all the function calls in this function's definition
     * are valid.
     * This means that all the function calls in the body of the function
     * are validated.
     * Returns quickly if this validation has already been performed.
     *
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    void validateFunctionCallsInDefinition() {
        if (validatedFunctionCalls)
            return;
        this.definiens.validateFunctionCalls();
        validatedFunctionCalls = true;
    }

    /**
     * Ensure that all the defined functions created so far
     * have valid definitions.
     * We call {@link #validateFunctionCallsInDefinition()}
     * on all the functions created so far.
     *
     * @throws Acl2InvalidFunctionCallException If some call is invalid.
     */
    static void validateFunctionCallsInAllDefinitions() {
        for (Acl2DefinedFunction function : functions.values())
            function.validateFunctionCallsInDefinition();
        Acl2NamedFunction.setValidatedAllFunctionCalls(true);
    }

    /**
     * Checks if this defined function is
     * the {@code if} ACL2 primitive function.
     * This is never the case, because {@code if} is represented as
     * an instance of {@link Acl2NativeFunction}.
     *
     * @return {@code false}.
     */
    @Override
    boolean isIf() {
        return false;
    }

    /**
     * Checks if this defined function is
     * the {@code or} ACL2 "pseudo-function".
     * This is never the case, because {@code if} is represented as
     * an instance of {@link Acl2NativeFunction}.
     *
     * @return {@code false}.
     */
    @Override
    boolean isOr() {
        return false;
    }

    /**
     * Applies this defined function to the given values.
     * The defining lambda expression is applied to the values.
     * This is never called if the definiens is not set or validated.
     *
     * @param values The actual arguments to pass to the function.
     *               Invariants: not null, no null elements.
     * @return The result of the function on the given arguments.
     * @throws Acl2UndefinedPackageException If a call of {@code pkg-imports}
     *                                       or {@code pkg-witness} fails.
     */
    @Override
    Acl2Value apply(Acl2Value[] values) throws Acl2UndefinedPackageException {
        return definiens.apply(values);
    }

    /**
     * Returns a defined function with the given name.
     * The function is created and interned, if it does not exist.
     *
     * @param name The name of the defined function.
     *             Invariant: not null.
     * @return The defined function.
     */
    static Acl2DefinedFunction getInstance(Acl2Symbol name) {
        Acl2DefinedFunction function = functions.get(name);
        if (function != null)
            return function;
        function = new Acl2DefinedFunction(name);
        functions.put(name, function);
        Acl2NamedFunction.setValidatedAllFunctionCalls(false);
        return function;
    }

    //////////////////////////////////////// public members:

    /**
     * Defines this defined function.
     * That is, actually sets the definition of the function.
     * The indices of the variables in the definiens are set
     * (see {@link Acl2Variable}).
     *
     * @param parameters The formal parameters of the function definition.
     * @param body       The body of the function definition.
     * @throws IllegalArgumentException If {@code parameters} is null,
     *                                  or any of its elements is null,
     *                                  or {@code body} is null,
     *                                  or the function definition
     *                                  (viewed as a lambda expression)
     *                                  contains some variable
     *                                  that has its index already set
     *                                  or that is not bound in the formals of
     *                                  its smallest enclosing
     *                                  lambda expression.
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
