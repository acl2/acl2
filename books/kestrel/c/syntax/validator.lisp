; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")

(include-book "kestrel/std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator
  :parents (syntax-for-tools)
  :short "Validator of the C abstract syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides syntactic validity,
     C code must satisfy a number of additional constraints
     in order to be compiled.
     These constraints form the static semantics of C.
     C compilers check that the code satisfies these constraints
     prior to translating it.")
   (xdoc::p
    "Here we provide a validator of C code,
     whose purpose is to check those constraints,
     i.e. to check whether the C code is valid and compilable.
     This work has just started:
     we may start with a partial validator,
     which we will extend to a full validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO
