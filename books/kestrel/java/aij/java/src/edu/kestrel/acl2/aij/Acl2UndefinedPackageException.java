/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

 /**
 * Exceptions thrown when attempting to operate on an undefined ACL2 package.
 * In ACL2, calling the primitive functions
 * {@code pkg-imports} and {@code pkg-witness}
 * on a string that is not the name of a defined package
 * causes an error.
 * In AIJ, that error is represented via this exception class.
 */
public final class Acl2UndefinedPackageException extends Exception {

    /**
     * Constructs an undefined package exception
     * with a {@code null} detail message.
     */
    public Acl2UndefinedPackageException() {
        super();
    }

    /**
     * Constructs an undefined package exception
     * with the given detail message.
     *
     * @param message The detail message for the exception.
     */
    public Acl2UndefinedPackageException(String message) {
        super(message);
    }

    /**
     * Constructs an undefined package exception
     * with the given detail message and cause.
     *
     * @param message The detail message for the exception.
     * @param cause   The cause of the exception.
     */
    public Acl2UndefinedPackageException(String message, Throwable cause) {
        super(message, cause);
    }

}
