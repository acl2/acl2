; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Test driver for the lrat checker.

; (depends-on "../tests/example-4-vars.cnf")
; (depends-on "../tests/example-4-vars.lrat")
; (depends-on "../tests/uuf-100-1.cnf")
; (depends-on "../tests/uuf-100-1.lrat")
; (depends-on "../tests/uuf-100-2.cnf")
; (depends-on "../tests/uuf-100-2.lrat")
; (depends-on "../tests/uuf-100-3.cnf")
; (depends-on "../tests/uuf-100-3.lrat")
; (depends-on "../tests/uuf-100-4.cnf")
; (depends-on "../tests/uuf-100-4.lrat")
; (depends-on "../tests/uuf-100-5.cnf")
; (depends-on "../tests/uuf-100-5.lrat")
; (depends-on "../tests/uuf-100-5-partial.lrat")
; (depends-on "../tests/uuf-30-1.cnf")
; (depends-on "../tests/uuf-30-1.lrat")

(in-package "LRAT")
(include-book "lrat-parser")

; Test driver

(program)
(set-state-ok t)

(defun main-test-fn (doublets dir okp chan state)
  (cond
   ((endp doublets)
    (pprogn (fms "OVERALL RESULT: ~s0~|~%"
                 (list (cons #\0 (if okp "success" "FAILURE")))
                 chan state nil)
            (value okp)))
   (t (let* ((d (car doublets))
             (cnf (concatenate 'string dir (car d)))
             (lrat (concatenate 'string dir (cadr d)))
             (incomplete-okp (caddr d)))
        (pprogn
         (fms "Starting ~x0.~|"
              (list (cons #\0 `(lrat-verify-proof ,cnf ,lrat ,@(cddr d))))
              chan state nil)
         (er-let* ((val (lrat-verify-proof cnf lrat incomplete-okp)))
           (pprogn
            (princ$ "Result: " chan state)
            (princ$ (if val "success" "FAILURE") chan state)
            (newline chan state)
            (main-test-fn (cdr doublets) dir (and val okp) chan state))))))))

(defmacro main-test (doublets &optional (dir '""))

; This should be run in the tests/ directory, or else in the directory dir
; relative to the current directory (e.g., "../tests" or "../tests/").

  (declare (xargs :guard (stringp dir))) ; partial guard
  (let ((dir (if (and (not (equal dir ""))
                      (not (eql (char dir (1- (length dir)))
                                #\/)))
                 (concatenate 'string dir "/")
               dir)))
    `(main-test-fn ',doublets ',dir t (standard-co state) state)))

(make-event
 (er-let* ((okp (main-test
                 (("example-4-vars.cnf" "example-4-vars.lrat")
                  ("example-5-vars.cnf" "example-5-vars.lrat")
                  ("uuf-100-1.cnf" "uuf-100-1.lrat")
                  ("uuf-100-2.cnf" "uuf-100-2.lrat")
                  ("uuf-100-3.cnf" "uuf-100-3.lrat")
                  ("uuf-100-4.cnf" "uuf-100-4.lrat")
                  ("uuf-100-5.cnf" "uuf-100-5.lrat")
                  ("uuf-100-5.cnf" "uuf-100-5-partial.lrat" t) ; partial proof
                  ("uuf-30-1.cnf" "uuf-30-1.lrat")
                  ("uuf-50-2.cnf" "uuf-50-2.lrat")
                  ("uuf-50-3.cnf" "uuf-50-3.lrat"))
                 "../tests")))
   (if okp
       (value '(value-triple :success))
     (er soft 'top
         "MAIN-TEST failed!"))))
