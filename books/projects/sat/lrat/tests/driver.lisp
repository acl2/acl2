; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Test driver for ../lrat-checker.lisp.

; (depends-on "example-4-vars.cnf")
; (depends-on "example-4-vars.lrat")
; (depends-on "uuf-100-1.cnf")
; (depends-on "uuf-100-1.lrat")
; (depends-on "uuf-100-2.cnf")
; (depends-on "uuf-100-2.lrat")
; (depends-on "uuf-100-3.cnf")
; (depends-on "uuf-100-3.lrat")
; (depends-on "uuf-100-4.cnf")
; (depends-on "uuf-100-4.lrat")
; (depends-on "uuf-100-5.cnf")
; (depends-on "uuf-100-5.lrat")
; (depends-on "uuf-30-1.cnf")
; (depends-on "uuf-30-1.lrat")

(in-package "ACL2")
(include-book "../lrat-parser")
(make-event
 (er-let* ((okp (lrat-test
                 (("example-4-vars.cnf" "example-4-vars.lrat")
                  ("uuf-100-1.cnf" "uuf-100-1.lrat")
                  ("uuf-100-2.cnf" "uuf-100-2.lrat")
                  ("uuf-100-3.cnf" "uuf-100-3.lrat")
                  ("uuf-100-4.cnf" "uuf-100-4.lrat")
                  ("uuf-100-5.cnf" "uuf-100-5.lrat")
                  ("uuf-100-5.cnf" "uuf-100-5-partial.lrat" t) ; partial proof
                  ("uuf-30-1.cnf" "uuf-30-1.lrat")))))
   (if okp
       (value '(value-triple :success))
     (er soft 'top
         "LRAT-TEST failed!"))))
