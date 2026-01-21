; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The evaluation of (hol-theory-print chan state), where chan is a :character
; output channel (e.g., *standard-co*), results in the translations of defhol
; forms as stored in the :hol-theory table.

(in-package "ZF")

(include-book "projects/hol-in-acl2/acl2/theories" :dir :system)
(include-book "kestrel/auto-termination/fms-bang-list" :dir :system)

(defun defgoal-form-lst (goals tbl acc)
  (declare (xargs :mode :program))
  (cond ((endp goals) acc)
        (t (defgoal-form-lst
             (cdr goals)
             tbl
             (cons (defgoal-form1 (caar goals) (cdar goals) tbl)
                   acc)))))

(defun hol-theory-print (chan state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((wrld (w state))
         (tbl (table-alist :hol-theory wrld))
         (goals (cdr (assoc-eq :goals tbl)))
         (axioms (cdr (assoc-eq :axioms tbl)))
         (theorems (cdr (assoc-eq :theorems tbl))))
    (pprogn (princ$ "; Axioms:" chan state)
            (if axioms
                (pprogn (newline chan state)
                        (acl2::fms!-lst (reverse axioms) chan state))
              (princ$ "  none." chan state))
            (newline chan state)
            (newline chan state)
            (princ$ "; Theorems:" chan state)
            (if theorems
                (pprogn (newline chan state)
                        (acl2::fms!-lst (reverse theorems) chan state))
              (princ$ "  none." chan state))
            (newline chan state)
            (newline chan state)
            (princ$ "; Goals:" chan state)
            (if goals
                (pprogn (newline chan state)
                        (newline chan state)
                        (princ$ "#|" chan state)
                        (acl2::fms!-lst (defgoal-form-lst goals tbl nil)
                                        chan
                                        state)
                        (newline chan state)
                        (princ$ "|#" chan state))
              (princ$ "  none." chan state))
            (newline chan state))))
