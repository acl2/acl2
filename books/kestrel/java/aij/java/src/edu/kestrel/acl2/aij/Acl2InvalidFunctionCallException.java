/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

/**
 * Exceptions thrown when a function definition has an invalid function call.
 * These exceptions may be thrown
 * when using {@link Acl2NamedFunction#validateAllFunctionCalls()}
 * to validate function calls in function definitions.
 * A function call is invalid if
 * either it references a function that is neither defined nor native,
 * or it has a number of actual arguments different from the function's arity;
 * the exception message will convey which of these two cases occurred.
 * This exception is unchecked
 * (by extending {@link RuntimeException} instead of {@link Exception}),
 * because it signals problems with
 * the function definitions supplied to AIJ by some calling code,
 * which are entirely under the calling code's control
 * (unlike, say, an I/O exception, which depends on external factors):
 * the calling code would not expect this exception to be thrown,
 * being presumably designed to provide valid function definitions,
 * and so it should not have to declare or handle this exception.
 */
public class Acl2InvalidFunctionCallException extends RuntimeException {

    /**
     * Constructs an invalid function call exception
     * with a {@code null} detail message.
     */
    public Acl2InvalidFunctionCallException() {
        super();
    }

    /**
     * Constructs an invalid function call exception
     * with the given detail message.
     *
     * @param message The detail message for the exception.
     */
    public Acl2InvalidFunctionCallException(String message) {
        super(message);
    }

}
