; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc errors
  :parents (dynamic-semantics)
  :short "Error indications generated in the dynamic semantics of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize a defensive semantics of Leo,
     which means that, before executing any Leo construct (operations etc.),
     we check that all its preconditions are satisfied.
     In particular, we check
     that every operation is always applied to operands of appropriate types,
     that every referenced variable exists in the environment,
     and so on.
     When any of these preconditions fail,
     the ACL2 functions that formalize our dynamic semantics
     return ACL2 values that indicate errors,
     distinct from the ACL2 values that model the Leo values, environments, etc.
     (which are returned by the ACL2 functions
     when all the preconditions are satisfied).")
   (xdoc::p
    "For now we do not define any ACL2 fixtype for errors.
     Instead, we define, where appropriate, tagged sum types
     that consist of the ``normal'' results plus the error results.
     We use the fixtype @('any') (see @(tsee any-p)) for the error summand,
     so that we can put there any kind of information.
     In the future, we may refine this,
     for instance by introducing broad categories of errors,
     in particular to facilitate the formulation of type soundness theorems
     asserting that static semantics checks ensure
     the absence of certain categories of dynamic errors.")))
