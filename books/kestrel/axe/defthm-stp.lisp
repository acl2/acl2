; A tool for proving an ACL2 theorem using STP.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Warning: This uses skip-proofs to introduce the theorem if STP says it is
;; true.

;; See tests in defthm-stp-tests.lisp

(include-book "prove-with-stp")

;returns (mv erp event state)
(defun defthm-stp-fn (name theorem-body rule-classes counterexamplep max-conflicts print state)
  (declare (xargs :mode :program
                  :guard (and (booleanp counterexamplep)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :stobjs state))
  (b* (((mv result state)
        (translate-and-prove-term-with-stp theorem-body counterexamplep max-conflicts
                                           print (symbol-name name) state)))
    (if (eq result *valid*)
        (mv nil ;no error
            ;; create an event:
            `(skip-proofs
              (defthm ,name
                ,theorem-body
                :rule-classes ,rule-classes)) ;todo: suppress if (:rewrite) is given?
            state)
      (prog2$ (er hard? 'defthm-stp "Failed to prove the theorem ~x0.  Result was ~x1." name result)
              (mv t ;error
                  nil state)))))

;TODO: Compare to defthm-with-stp-clause-processor!  That one uses a clause processor but seems to not see into IMPLIES.
(defmacro defthm-stp (name theorem-body
                            &key
                            (rule-classes '(:rewrite))
                            (counterexample 'nil)
                            (max-conflicts '*default-stp-max-conflicts*)
                            (print 'nil))
  `(make-event (defthm-stp-fn ',name ',theorem-body ',rule-classes ',counterexample ,max-conflicts ',print state)))
