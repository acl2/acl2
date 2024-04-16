; Utilities for testing prove-with-stp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prove-with-stp" :ttags :all)

;; Ensures that STP can prove the TERM.
;; Returns (mv erp result state) where if things go well, RESULT is an empty progn.
(defun must-prove-with-stp-fn (name term counterexamplep max-conflicts print state)
  (declare (xargs :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :mode :program ;because this ultimately calls translate-term
                  :stobjs state))
  (mv-let (result state)
    (translate-and-prove-term-with-stp term counterexamplep nil max-conflicts print (symbol-name name) state)
    (if (eq *error* result)
        (prog2$ (er hard? 'must-prove-with-stp "Error ~x0 running test." name)
                (mv (erp-t) :error state))
      (if (not (eq *valid* result))
          (prog2$ (er hard? 'must-prove-with-stp "Test ~x0 was supposed to prove." name)
                  (mv (erp-t) :fail state))
        (prog2$ (cw "TEST ~x0 PASSED.~%" name)
                (mv (erp-nil) '(progn) state))))))

;; Ensures that STP can prove the TERM.
;; Returns (mv erp result state) where if things go well, RESULT is an empty progn.
(defmacro must-prove-with-stp (name term
                                    &key
                                    (counterexample 't)
                                    (max-conflicts '*default-stp-max-conflicts*)
                                    (print 'nil))
  `(make-event (must-prove-with-stp-fn ',name ,term ',counterexample ,max-conflicts ',print state)))

;fixme test the new depth bound when the prover calls stp? huh?

;; Ensures that STP cannot prove the TERM.
;; Returns (mv erp result state) where if things go well, RESULT is an empty progn.
(defun must-not-prove-with-stp-fn (name term counterexamplep max-conflicts print state)
  (declare (xargs :stobjs state
                  :mode :program ;because this ultimately calls translate-term
                  :guard (and (symbolp name)
                              (booleanp counterexamplep)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))))
  (mv-let (result state)
    (translate-and-prove-term-with-stp term counterexamplep nil max-conflicts print (symbol-name name) state)
    (if (eq *error* result)
        (prog2$ (er hard? 'must-not-prove-with-stp "Error running test ~x0." name)
                (mv (erp-t) :error state))
      (if (eq *valid* result)
          (prog2$ (er hard? 'must-not-prove-with-stp "Test ~x0 was supposed to fail" name)
                  (mv (erp-t) :fail state))
        (prog2$ (cw "TEST ~x0 PASSED" name)
                (mv (erp-nil) '(progn) state))))))

;; Ensures that STP cannot prove the TERM.
;; Returns (mv erp result state) where if things go well, RESULT is an empty progn.
;; We could perhaps use must-fail, but this more informative messages.
(defmacro must-not-prove-with-stp (name term
                                        &key
                                        (counterexample 't)
                                        (max-conflicts '*default-stp-max-conflicts*)
                                        (print 'nil))
  `(make-event (must-not-prove-with-stp-fn ',name ,term ',counterexample ,max-conflicts ',print state)))
