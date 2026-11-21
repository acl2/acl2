; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validator-correctness")
(include-book "dimension-polynomials-properties")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator-correctness
  :parents (static-semantics)
  :short "Correctness of the Remora validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress."))
  :order-subtopics (ispace-validator-correctness
                    dimension-polynomials-properties))
