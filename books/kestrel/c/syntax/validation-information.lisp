; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "initializer-validation")
(include-book "validation-tables")
(include-book "validation-annotations")
(include-book "null-pointer-constants")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (validation)
  :short "Information calculated and used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see validator) calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes.")
   (xdoc::p
    "We also introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
  :order-subtopics t
  :default-parent t)
