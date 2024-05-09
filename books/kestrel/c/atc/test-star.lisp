; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test* (x)
  :parents (atc-event-and-code-generation)
  :short "Wrapper for contextual tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "In @(tsee atc-contextualize),
     we wrap tests from the context premises with this identity function,
     to prevent ACL2 from making use of them,
     in the generated modular theorems,
     to simplify things in ways that interfere with the compositional proofs.
     For instance, when ACL2 has a hypothesis @('(not <term>)') in context,
     it rewrites occurrences of @('<term>') with @('nil'):
     this is generally good for interactive proofs,
     but not if that prevents a previously proved theorem from applying,
     about a subterm that is supposed not to be simplified."))
  x

  ///

  (defruled test*-of-t
    (test* t)))
