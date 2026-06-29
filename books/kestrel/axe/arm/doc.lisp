; Gathering documentation for the ARM variant of Axe
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more doc for this variant

(include-book "unroller")
;; (include-book "loop-lifter")
;; (include-book "prove-equivalence")
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

;; todo: extend this
(defxdoc axe-arm
  :parents (axe)
  :short "The ARM variant of Axe."
  :long (xdoc::topparas
          "The ARM variant of Axe covers a growing set of ARM32 instructions.

           The main tool provided is @(tsee a::def-unrolled).

           See @('[books]/kestrel/axe/arm/examples/') for examples of ARM code lifted and verified by Axe."))
