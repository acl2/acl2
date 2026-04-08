; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../portcullis")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test* (x)
  :parents (proof-support)
  :short "Wrapper for contextual tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some proofs, it is useful to wrap certain contextual tests
     to prevent ACL2 from making use of them in unwanted ways.
     For instance, when ACL2 has a hypothesis @('(not <term>)') in context,
     it rewrites occurrences of @('<term>') with @('nil'):
     this is generally good for interactive proofs,
     but not if that prevents a previously proved theorem from applying,
     about a subterm that is supposed not to be simplified;
     this is particularly the case when programmatically generating
     theorems with proofs that are never supposed to fail.")
   (xdoc::p
    "So this @('test*') identity function can be used to wrap such tests.
     For instance, @(tsee atc-contextualize) wraps tests
     from the context premises with this identity function,
     to prevent ACL2 from making use of them,
     in the generated modular theorems,
     to simplify things in ways that interfere with the compositional proofs.")
   (xdoc::p
    "This is a more general notion than C,
     so it could be moved to a more general library.
     We could also simply use the built-in @(tsee identity) function,
     but the name @('test*') is a bit more descriptive.")
   (xdoc::p
    "We provide a theorem @('test*-of-t'),
     which may be useful to obtain the truth of @('(test* t)'),
     e.g. as resulting from some simplification,
     while keeping @('test*') disabled."))
  x

  ///

  (defruled test*-of-t
    (test* t)))
