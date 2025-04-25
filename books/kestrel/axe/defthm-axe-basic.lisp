; A simple variant of defthm-axe
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in defthm-axe-tests.lisp

(include-book "prover-basic") ; defines the clause processor function
(include-book "register-and-wrap-clause-processor-simple")

;; Creates defthm-axe-basic, which uses the basic prover.
;; This is similar to the old, deprecated utility defthm-with-prover-basic-clause-processor.
(register-and-wrap-clause-processor-simple basic) ; ttag
