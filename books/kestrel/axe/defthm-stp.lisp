; A tool for proving an ACL2 theorem using STP.
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

;; Warning: This uses skip-proofs to introduce the theorem if STP says it is
;; true.

;; TODO: Consider using the clause processor instead of introducing a
;; skip-proofs.

;; See tests in defthm-stp-tests.lisp

(include-book "prove-with-stp")

;returns (mv erp event state)
;; Splits TERM into hyps and a conclusion when it is an IMPLIES.
(defun defthm-stp-fn (name term rule-classes counterexamplep max-conflicts print state)
  (declare (xargs :guard (and (symbolp name)
                              ;; term is an untranslated term
                              ;; check the rule-classes?
                              (booleanp counterexamplep)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (print-levelp print))
                  :mode :program ; because this translates the term
                  :stobjs state))
  (b* (((mv result state)
        (translate-and-prove-term-with-stp term counterexamplep
                                           nil ; print-cex-as-signedp
                                           max-conflicts
                                           print (symbol-name name) state)))
    (if (eq result *valid*)
        (mv nil ;no error
            ;; create an event:
            `(skip-proofs
               (defthm ,name
                 ,term
                 :rule-classes ,rule-classes)) ;todo: suppress if (:rewrite) is given?
            state)
      (prog2$ (er hard? 'defthm-stp "Failed to prove the theorem ~x0.  Result was ~X12." name result nil)
              (mv t ;error
                  nil state)))))

;TODO: Compare to defthm-with-stp-clause-processor!  That one uses a clause processor but seems to not see into IMPLIES.
(defmacro defthm-stp (name
                      term
                      &key
                      (rule-classes '(:rewrite))
                      (max-conflicts '*default-stp-max-conflicts*)
                      (counterexample 'nil)
                      (print 'nil))
  `(make-event (defthm-stp-fn ',name ',term ',rule-classes ',counterexample ,max-conflicts ',print state)))
