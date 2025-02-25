; bls12-377-curves Library
;
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "primes/top")
(include-book "ecurve/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reminder: new xdoc topics in books/projects
; must be mentioned in projects/include-doc.lisp
;
(defxdoc bls12-377-curves
  :parents (acl2::projects)
  :short "A library for elliptic curves: BLS12-377 and Edwards-BLS12.")
