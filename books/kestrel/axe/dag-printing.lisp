; Printing DAGs
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/system/untranslate-dollar" :dir :system)
(include-book "dags")
(include-book "dag-size")
(include-book "dag-to-term")
(include-book "kestrel/lists-light/len-at-least" :dir :system)

(defund print-as-term-or-dag (dag-or-quotep
                             max-size
                             maybe-actual-size ; if non-nil, this is the dag-size of DAG-OR-QUOTEP
                             maybe-term ; if non-nil, this is a term equivalent to DAG-OR-QUOTEP
                             descriptor ; a string describing DAG-OR-QUOTEP (e.g., "Result")
                             untranslatep
                             state ; because of untranslate$ (uses magic-ev-fncall)
                             )
  (declare (xargs :guard (and (or (pseudo-dagp dag-or-quotep) ; todo: name this disjunction
                                  (myquotep dag-or-quotep))
                              (natp max-size) ; allow nil for no limit?
                              (or (null maybe-actual-size)
                                  (natp maybe-actual-size))
                              (or (null maybe-term)
                                  (pseudo-termp maybe-term))
                              (stringp descriptor)
                              (booleanp untranslatep))
                  :stobjs state))
  (let ((quotep (quotep dag-or-quotep)))
    (if (or quotep
            (and (not (acl2::len-at-least 1152921504606846974 dag-or-quotep)) ; not too big to call dag-size
                 (if maybe-actual-size
                     (<= maybe-actual-size max-size)
                   (<= (dag-size dag-or-quotep) max-size))))
        ;; Print as a term (preferred if not too big):
        (let ((term (if quotep
                        dag-or-quotep
                      (let ((term (or maybe-term (dag-or-quotep-to-term dag-or-quotep))))
                        (if untranslatep
                            (untranslate$ term nil state)
                          term)))))
          (progn$ (cw "(~s0:~%" descriptor)
                  (cw "~X01" term nil)
                  (cw ")~%")))
      ;; Print as a DAG because the term would be too big:
      (progn$ (cw "(~s0:~%" descriptor)
              (cw "~X01" dag-or-quotep nil)
              (cw ")~%")))))
