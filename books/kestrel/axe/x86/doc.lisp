; Gathering documentation for the x86 variant of Axe
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more doc for this variant

(include-book "unroll-x86-code")

;; todo: extend this
(defxdoc axe-x86
  :parents (axe)
  :short "The x86 variant of Axe."
)
