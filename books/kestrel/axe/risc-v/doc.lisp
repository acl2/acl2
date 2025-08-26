; Gathering documentation for the RISC-V variant of Axe
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more doc for this variant

(include-book "unroll")
;(include-book "prove-equivalence")

;; todo: extend this
(defxdoc axe-risc-v
  :parents (axe)
  :short "The RISC-V variant of Axe."
)
