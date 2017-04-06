; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Test driver for the lrat checker.

; (depends-on "../tests/example-4-vars.cnf")
; (depends-on "../tests/example-4-vars.clrat")
; (depends-on "../tests/uuf-100-1.cnf")
; (depends-on "../tests/uuf-100-1.clrat")
; (depends-on "../tests/uuf-100-2.cnf")
; (depends-on "../tests/uuf-100-2.clrat")
; (depends-on "../tests/uuf-100-3.cnf")
; (depends-on "../tests/uuf-100-3.clrat")
; (depends-on "../tests/uuf-100-4.cnf")
; (depends-on "../tests/uuf-100-4.clrat")
; (depends-on "../tests/uuf-100-5.cnf")
; (depends-on "../tests/uuf-100-5.clrat")
; (depends-on "../tests/uuf-100-5-partial.clrat")
; (depends-on "../tests/uuf-30-1.cnf")
; (depends-on "../tests/uuf-30-1.clrat")

(in-package "LRAT")
(include-book "soundness")

; Test driver

(program)
(set-state-ok t)

(defun keyword-value (key l default)
  (let ((tail (assoc-keyword key l)))
    (if tail
        (cadr tail)
      default)))

(defun test-fn (doublets dir okp chan state)
  (cond
   ((endp doublets)
    (pprogn (fms "OVERALL RESULT: ~s0~|~%"
                 (list (cons #\0 (if okp "success" "FAILURE")))
                 chan state nil)
            (value okp)))
   (t (let* ((d (car doublets))
             (cnf (concatenate 'string dir (car d)))
             (clrat (concatenate 'string dir (cadr d)))
             (options (cddr d))
             (incomplete-okp (keyword-value :incomplete-okp options nil))
             (chunk-size (keyword-value :chunk-size options *default-chunk-size*))
             (debug (keyword-value :debug options
                                   nil)))
        (pprogn
         (fms "Starting ~x0.~|"
              (list (cons #\0
                          `(proved-formula ,cnf ,clrat ,chunk-size ,debug
                                           ,incomplete-okp 'test state)))
              chan state nil)
         (mv-let
           (erp val state)
           (proved-formula cnf clrat chunk-size debug incomplete-okp 'test
                           state)
           (pprogn
            (princ$ "Result: " chan state)
            (princ$ (if (and (null erp) val) "success" "FAILURE") chan state)
            (newline chan state)
            (test-fn (cdr doublets) dir (and val okp) chan state))))))))

(defmacro test (doublets &optional (dir '""))

; This should be run in the tests/ directory, or else in the directory dir
; relative to the current directory (e.g., "../tests" or "../tests/").

  (declare (xargs :guard (stringp dir))) ; partial guard
  (let ((dir (if (and (not (equal dir ""))
                      (not (eql (char dir (1- (length dir)))
                                #\/)))
                 (concatenate 'string dir "/")
               dir)))
    `(test-fn ',doublets ',dir t (standard-co state) state)))

(make-event
 (er-let* ((okp (test
                 (("example-4-vars.cnf" "example-4-vars.clrat")
                  ("example-5-vars.cnf" "example-5-vars.clrat")
                  ("uuf-100-1.cnf" "uuf-100-1.clrat")
                  ("uuf-100-2.cnf" "uuf-100-2.clrat")
                  ("uuf-100-3.cnf" "uuf-100-3.clrat")
                  ("uuf-100-4.cnf" "uuf-100-4.clrat")
                  ("uuf-100-5.cnf" "uuf-100-5.clrat")
                  ("uuf-100-5.cnf" "uuf-100-5-partial.clrat"
                   :incomplete-okp t)
                  ("uuf-30-1.cnf" "uuf-30-1.clrat")
                  ("uuf-50-2.cnf" "uuf-50-2.clrat")
                  ("uuf-50-3.cnf" "uuf-50-3.clrat"))
                 "../tests")))
   (if okp
       (value '(value-triple :success))
     (er soft 'top
         "TEST failed!"))))
