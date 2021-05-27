/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

/**
 * AIJ (ACL2 In Java) is a deep embedding of ACL2 in Java.
 * More precisely, it is a deep embedding in Java
 * of the executable, side-effect-free, non-stobj-accessing
 * subset of the ACL2 language without guards.
 * This may be extended in the future.
 * <p>
 * The implementation was initially written
 * more for simplicity and clarity than for performance.
 * It has undergone some optimizations, and it may undergo more in the future.
 * <p>
 * AIJ consists of a single Java package.
 * The package is sealed (as specified in the manifest file),
 * i.e. all the classes of the package must come from the same JAR file
 * when the JVM is run.
 * <p>
 * The Javadoc documentation states some preconditions for some public methods
 * as well as some invariants for some non-public fields
 * and invariants for some non-public method arguments and results.
 * The invariants generally assume the satisfaction of the preconditions.
 * Calling a public method outside its precondition causes undefined behaviors
 * as far as AIJ documents.
 */
package edu.kestrel.acl2.aij;
