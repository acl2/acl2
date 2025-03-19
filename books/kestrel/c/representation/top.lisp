; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")
(include-book "integer-conversions")
(include-book "integer-operations")
(include-book "shallow-deep-relation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ representation
  :parents (c)
  :short "A representation of C in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 representations of C constructs,
     which is a shallow embedding of (a subset of) C in ACL2.")
   (xdoc::p
    "This is related to, but different from,
     the deep embedding of C in ACL2,
     i.e. the "
    (xdoc::seetopic "language" "formalization of (a subset of) C in ACL2")
    ".")
   (xdoc::p
    "This shallow embedding is used by "
    (xdoc::seetopic "atc" "ATC")
    " to generate C from ACL2.
     It could be also used by a future lifter from C code to ACL2;
     it is more general than code generation,
     as it is also usable for code lifting.
     For this reason, we are in the process of moving this shallow embedding
     from the @('atc') subdirectory to this @('representation') subdirectory."))
  :order-subtopics t
  :default-parent t)
