; Tests and examples for subsumes.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in subsumes.lisp.  This book
;; is not included by top.lisp.

(include-book "subsumes")

;; Without a limit, CLAUSE-SET-SUBSUMES is correct
;; (clause-set-subsumes-correct-when-no-limit, in subsumes.lisp).  But with a
;; limit, CLAUSE-SET-SUBSUMES in the sources can return T when it gave up on a
;; clause, if it then succeeds on a later clause.  Here the
;; valid clause ((EQUAL X X)) "subsumes" the clause ((EQUAL Y '1) (EQUAL Z '2)),
;; which is false when Y and Z are 0, because with a limit of 2 calls of
;; one-way-unify1, the check gives up on that clause ('?) but then succeeds on
;; the next one.  This was a soundness bug: the check for :EQUIVALENCE rules
;; uses a limit, and a non-symmetric relation could be accepted as an
;; equivalence relation, which led to a proof of NIL.  The fixed version
;; returns '?.
(defthm clause-set-subsumes-can-give-up-and-return-t
  (let ((cl-set1 '(((equal x x))))
        (cl-set2 '(((equal y '1) (equal z '2))
                   ((equal a a)))))
    (and (equal (some-member-subsumes 2 cl-set1 (car cl-set2) nil) '?)
         (equal (clause-set-subsumes 2 cl-set1 cl-set2) t)
         (not (subsumes-eval (conjoin-clauses cl-set2) '((y . 0) (z . 0))))
         (equal (clause-set-subsumes-fixed 2 cl-set1 cl-set2) '?)))
  :rule-classes nil)

;; The clause ((EQUAL X X)) is indeed valid:
(defthm subsumes-eval-valid-clausep-of-equal-x-x
  (subsumes-eval-valid-clausep '((equal x x)))
  :hints (("Goal" :in-theory (enable subsumes-eval-valid-clausep))))
