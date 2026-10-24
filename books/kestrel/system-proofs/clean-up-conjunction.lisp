; Correctness of the ACL2 system functions that clean up the tests of
; induction machines for loop$ recursion
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; CLEAN-UP-LOOP$-RECURSION-INDUCTION-MACHINE (in defuns.lisp) cleans up an
;; induction machine, a list of TESTS-AND-CALLS records, each giving the tests
;; that govern a case and the recursive calls made in it.  It drops each case
;; whose tests CLEAN-UP-CONJUNCTION finds contradictory, and replaces the
;; tests of each other case with the result of CLEAN-UP-CONJUNCTION, which
;; removes double negations (with CLEAN-UP-NOTS) and duplicate tests.
;;
;; This book proves that these functions are correct, in terms of an
;; evaluator: CLEAN-UP-NOTS preserves the truth (though not always the value)
;; of a term; CLEAN-UP-CONJUNCTION returns :CONTRADICTION only for tests that
;; cannot all be true, and otherwise returns tests that are all true exactly
;; when the original tests are; and so, under any assignment, the cleaned-up
;; machine has exactly the cases of the original machine whose tests are true,
;; with the same calls.  None of this needs any hypotheses: not even that the
;; tests are terms.
;;
;; (As of this writing, nothing calls CLEAN-UP-LOOP$-RECURSION-INDUCTION-MACHINE:
;; its comment says that it is for induction machines of loop$ recursive
;; functions, but ACL2 does not build such machines; see the comments in
;; INDUCTION-MACHINES.)

(include-book "clause-sets") ; for member-term and member-complement-term
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersectp-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination clean-up-nots)
(verify-termination clean-up-nots-lst)
(verify-termination clean-up-conjunction1)
(verify-termination clean-up-conjunction)
(verify-termination clean-up-loop$-recursion-induction-machine)

;; An evaluator that knows the functions that these functions treat
;; specially:
(defevaluator+ cleanup-eval if not equal iff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; CLEAN-UP-NOTS

;; Clean-up-nots preserves the truth of a term.
(defthm clean-up-nots-correct
  (iff (cleanup-eval (clean-up-nots p) a)
       (cleanup-eval p a))
  :hints (("Goal" :in-theory (enable clean-up-nots))))

(local (in-theory (disable clean-up-nots)))

;; But not always its value, since (NOT (NOT X)) is T or NIL and X need not
;; be: see clean-up-nots-does-not-preserve-value in
;; clean-up-conjunction-tests.lisp.

;; Clean-up-nots-lst applies clean-up-nots to each term, reversing the list
;; onto ANS, so the terms in the result are all true exactly when those of
;; LST and ANS are.
(defthm all-eval-to-true-with-cleanup-eval-of-clean-up-nots-lst
  (equal (all-eval-to-true-with-cleanup-eval (clean-up-nots-lst lst ans) a)
         (and (all-eval-to-true-with-cleanup-eval lst a)
              (all-eval-to-true-with-cleanup-eval ans a)))
  :hints (("Goal" :in-theory (enable clean-up-nots-lst
                                     all-eval-to-true-with-cleanup-eval)
           :induct (clean-up-nots-lst lst ans))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; MEMBER-TERM and MEMBER-COMPLEMENT-TERM, for conjunctions

;; If the tests in CL are all true, then any member of CL (modulo commuting
;; EQUAL or IFF) is true, and any term whose complement is a member of CL is
;; false.

(local
 (defthm member-term2-lemma-for-conjunction
   (implies (and (member-term2 fn lhs rhs cl)
                 (all-eval-to-true-with-cleanup-eval cl a))
            (and (implies (equal fn 'equal)
                          (equal (cleanup-eval lhs a)
                                 (cleanup-eval rhs a)))
                 (implies (equal fn 'iff)
                          (iff (cleanup-eval lhs a)
                               (cleanup-eval rhs a)))))
   :hints (("Goal" :in-theory (enable member-term2 comm-equal
                                      all-eval-to-true-with-cleanup-eval)))))

(local
 (defthm member-complement-term2-lemma-for-conjunction
   (implies (and (member-complement-term2 fn lhs rhs cl)
                 (all-eval-to-true-with-cleanup-eval cl a))
            (and (implies (equal fn 'equal)
                          (not (equal (cleanup-eval lhs a)
                                      (cleanup-eval rhs a))))
                 (implies (equal fn 'iff)
                          (not (iff (cleanup-eval lhs a)
                                    (cleanup-eval rhs a))))))
   :hints (("Goal" :in-theory (enable member-complement-term2 comm-equal
                                      all-eval-to-true-with-cleanup-eval)))))

(local
 (defthm not-cleanup-eval-when-member-complement-term1
   (implies (and (member-complement-term1 lit cl)
                 (all-eval-to-true-with-cleanup-eval cl a))
            (not (cleanup-eval lit a)))
   :hints (("Goal" :in-theory (enable member-complement-term1
                                      all-eval-to-true-with-cleanup-eval)))))

(local (make-flag member-term))

(defthm-flag-member-term
  (defthm cleanup-eval-when-member-term-and-all-true
    (implies (and (member-term lit cl)
                  (all-eval-to-true-with-cleanup-eval cl a))
             (cleanup-eval lit a))
    :flag member-term)
  (defthm not-cleanup-eval-when-member-complement-term-and-all-true
    (implies (and (member-complement-term lit cl)
                  (all-eval-to-true-with-cleanup-eval cl a))
             (not (cleanup-eval lit a)))
    :flag member-complement-term)
  :hints (("Goal" :in-theory (enable member-term member-complement-term
                                     all-eval-to-true-with-cleanup-eval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; CLEAN-UP-CONJUNCTION1 and CLEAN-UP-CONJUNCTION

;; Clean-up-conjunction1 returns :CONTRADICTION only when the terms in LST
;; cannot all be true (or when ANS is :CONTRADICTION and LST is empty).
(defthm not-all-eval-to-true-with-cleanup-eval-when-clean-up-conjunction1-contradiction
  (implies (and (equal (clean-up-conjunction1 lst ans) :contradiction)
                (not (equal ans :contradiction)))
           (not (all-eval-to-true-with-cleanup-eval lst a)))
  :hints (("Goal" :in-theory (e/d (clean-up-conjunction1
                                   all-eval-to-true-with-cleanup-eval)
                                  (member-complement-term))
           :induct (clean-up-conjunction1 lst ans))))

;; Otherwise, it removes duplicates from LST, reversing the rest onto ANS, so
;; the terms in the result are all true exactly when those of LST and ANS are.
(defthm all-eval-to-true-with-cleanup-eval-of-clean-up-conjunction1
  (implies (not (equal (clean-up-conjunction1 lst ans) :contradiction))
           (equal (all-eval-to-true-with-cleanup-eval (clean-up-conjunction1 lst ans) a)
                  (and (all-eval-to-true-with-cleanup-eval lst a)
                       (all-eval-to-true-with-cleanup-eval ans a))))
  :hints (("Goal" :in-theory (e/d (clean-up-conjunction1
                                   all-eval-to-true-with-cleanup-eval)
                                  (member-complement-term))
           :induct (clean-up-conjunction1 lst ans))))

;; Clean-up-conjunction returns :CONTRADICTION only for tests that cannot all
;; be true...
(defthm clean-up-conjunction-contradiction-correct
  (implies (equal (clean-up-conjunction lst) :contradiction)
           (not (cleanup-eval (conjoin lst) a)))
  :hints (("Goal" :in-theory (e/d (clean-up-conjunction)
                                  (not-all-eval-to-true-with-cleanup-eval-when-clean-up-conjunction1-contradiction))
           :use (:instance not-all-eval-to-true-with-cleanup-eval-when-clean-up-conjunction1-contradiction
                           (lst (clean-up-nots-lst lst nil))
                           (ans nil)))))

;; ...and otherwise returns tests that are all true exactly when the original
;; tests are.
(defthm clean-up-conjunction-correct
  (implies (not (equal (clean-up-conjunction lst) :contradiction))
           (iff (cleanup-eval (conjoin (clean-up-conjunction lst)) a)
                (cleanup-eval (conjoin lst) a)))
  :hints (("Goal" :in-theory (enable clean-up-conjunction))))

(local
 (defthm not-all-eval-to-true-with-cleanup-eval-when-clean-up-conjunction-contradiction
   (implies (equal (clean-up-conjunction lst) :contradiction)
            (not (all-eval-to-true-with-cleanup-eval lst a)))
   :hints (("Goal" :use clean-up-conjunction-contradiction-correct
            :in-theory (disable clean-up-conjunction-contradiction-correct)))))

(local (in-theory (disable clean-up-conjunction)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; CLEAN-UP-LOOP$-RECURSION-INDUCTION-MACHINE

;; The calls of the cases of an induction machine whose tests are true.
(defund applicable-calls (tc-list a)
  (if (endp tc-list)
      nil
    (if (cleanup-eval (conjoin (access tests-and-calls (car tc-list) :tests)) a)
        (cons (access tests-and-calls (car tc-list) :calls)
              (applicable-calls (cdr tc-list) a))
      (applicable-calls (cdr tc-list) a))))

;; Under any assignment, the cleaned-up machine has exactly the cases of the
;; original machine whose tests are true, in the same order and with the
;; same calls.
(defthm applicable-calls-of-clean-up-loop$-recursion-induction-machine
  (equal (applicable-calls (clean-up-loop$-recursion-induction-machine tc-list) a)
         (applicable-calls tc-list a))
  :hints (("Goal" :in-theory (enable clean-up-loop$-recursion-induction-machine
                                     applicable-calls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; What the functions return

;; Clean-up-nots applied to each term:
(defund clean-up-nots-list (lst)
  (if (endp lst)
      nil
    (cons (clean-up-nots (car lst))
          (clean-up-nots-list (cdr lst)))))

(defthm clean-up-nots-lst-becomes-revappend
  (equal (clean-up-nots-lst lst ans)
         (revappend (clean-up-nots-list lst) ans))
  :hints (("Goal" :in-theory (enable clean-up-nots-lst clean-up-nots-list revappend))))

;; Whether some term in LST has its complement (modulo commuting EQUAL or IFF)
;; among the later terms:
(defund complement-later-p (lst)
  (if (endp lst)
      nil
    (or (and (member-complement-term (car lst) (cdr lst)) t)
        (complement-later-p (cdr lst)))))

;; Clean-up-conjunction1 returns :CONTRADICTION exactly when some term has its
;; complement among the later terms, and otherwise it removes duplicates from
;; LST (keeping the last occurrence of each term) and reverses the result onto
;; ANS.
(defthm clean-up-conjunction1-contradiction-iff
  (implies (not (equal ans :contradiction))
           (equal (equal (clean-up-conjunction1 lst ans) :contradiction)
                  (complement-later-p lst)))
  :hints (("Goal" :in-theory (e/d (clean-up-conjunction1 complement-later-p)
                                  (member-complement-term))
           :induct (clean-up-conjunction1 lst ans))))

(defthm clean-up-conjunction1-when-not-complement-later-p
  (implies (not (complement-later-p lst))
           (equal (clean-up-conjunction1 lst ans)
                  (revappend (remove-duplicates-equal lst) ans)))
  :hints (("Goal" :in-theory (e/d (clean-up-conjunction1 complement-later-p revappend)
                                  (member-complement-term))
           :induct (clean-up-conjunction1 lst ans))))

;; So clean-up-conjunction returns :CONTRADICTION exactly when some cleaned-up
;; test has its complement among the earlier ones, and otherwise it returns the
;; cleaned-up tests, in order, without duplicates (keeping the first
;; occurrence of each).
(defthm clean-up-conjunction-contradiction-iff
  (equal (equal (clean-up-conjunction lst) :contradiction)
         (complement-later-p (revappend (clean-up-nots-list lst) nil)))
  :hints (("Goal" :in-theory (enable clean-up-conjunction))))

(defthm clean-up-conjunction-when-not-contradiction
  (implies (not (equal (clean-up-conjunction lst) :contradiction))
           (equal (clean-up-conjunction lst)
                  (revappend (remove-duplicates-equal
                              (revappend (clean-up-nots-list lst) nil))
                             nil)))
  :hints (("Goal" :in-theory (enable clean-up-conjunction))))

(local
 (defthm member-equal-of-revappend
   (iff (member-equal x (revappend y z))
        (or (member-equal x y)
            (member-equal x z)))
   :hints (("Goal" :in-theory (enable revappend)))))

(local
 (defthm no-duplicatesp-equal-of-revappend
   (implies (and (no-duplicatesp-equal y)
                 (no-duplicatesp-equal z)
                 (not (intersectp-equal y z)))
            (no-duplicatesp-equal (revappend y z)))
   :hints (("Goal" :in-theory (enable revappend intersectp-equal)
            :induct (revappend y z)))))

(local
 (defthm member-equal-of-remove-duplicates-equal
   (iff (member-equal a (remove-duplicates-equal x))
        (member-equal a x))
   :hints (("Goal" :in-theory (enable remove-duplicates-equal)))))

(local
 (defthm no-duplicatesp-equal-of-remove-duplicates-equal
   (no-duplicatesp-equal (remove-duplicates-equal x))
   :hints (("Goal" :in-theory (enable remove-duplicates-equal)))))

(defthm no-duplicatesp-equal-of-clean-up-conjunction
  (implies (not (equal (clean-up-conjunction lst) :contradiction))
           (no-duplicatesp-equal (clean-up-conjunction lst))))

(defthm member-equal-of-clean-up-conjunction
  (implies (not (equal (clean-up-conjunction lst) :contradiction))
           (iff (member-equal x (clean-up-conjunction lst))
                (member-equal x (clean-up-nots-list lst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Well-formedness

(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(defthm pseudo-termp-of-clean-up-nots
  (implies (pseudo-termp p)
           (pseudo-termp (clean-up-nots p)))
  :hints (("Goal" :in-theory (enable clean-up-nots))))

(defthm termp-of-clean-up-nots
  (implies (and (termp p w)
                (equal (arity 'not w) 1))
           (termp (clean-up-nots p) w))
  :hints (("Goal" :in-theory (enable clean-up-nots))))

(local
 (defthm pseudo-term-listp-of-clean-up-nots-list
   (implies (pseudo-term-listp lst)
            (pseudo-term-listp (clean-up-nots-list lst)))
   :hints (("Goal" :in-theory (enable clean-up-nots-list)))))

(local
 (defthm term-listp-of-clean-up-nots-list
   (implies (and (term-listp lst w)
                 (equal (arity 'not w) 1))
            (term-listp (clean-up-nots-list lst) w))
   :hints (("Goal" :in-theory (enable clean-up-nots-list)))))

(local
 (defthm term-listp-of-revappend
   (implies (and (term-listp x w)
                 (term-listp y w))
            (term-listp (revappend x y) w))
   :hints (("Goal" :in-theory (enable revappend)))))

(local
 (defthm pseudo-term-listp-of-remove-duplicates-equal
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (remove-duplicates-equal x)))))

(local
 (defthm term-listp-of-remove-duplicates-equal
   (implies (term-listp x w)
            (term-listp (remove-duplicates-equal x) w))))

(defthm pseudo-term-listp-of-clean-up-conjunction
  (implies (and (pseudo-term-listp lst)
                (not (equal (clean-up-conjunction lst) :contradiction)))
           (pseudo-term-listp (clean-up-conjunction lst))))

(defthm term-listp-of-clean-up-conjunction
  (implies (and (term-listp lst w)
                (equal (arity 'not w) 1)
                (not (equal (clean-up-conjunction lst) :contradiction)))
           (term-listp (clean-up-conjunction lst) w)))

;; An induction machine whose tests and calls are terms:
(defund tests-and-calls-term-listsp (tc-list w)
  (if (endp tc-list)
      t
    (and (term-listp (access tests-and-calls (car tc-list) :tests) w)
         (term-listp (access tests-and-calls (car tc-list) :calls) w)
         (tests-and-calls-term-listsp (cdr tc-list) w))))

(defthm tests-and-calls-term-listsp-of-clean-up-loop$-recursion-induction-machine
  (implies (and (tests-and-calls-term-listsp tc-list w)
                (equal (arity 'not w) 1))
           (tests-and-calls-term-listsp (clean-up-loop$-recursion-induction-machine tc-list) w))
  :hints (("Goal" :in-theory (e/d (clean-up-loop$-recursion-induction-machine
                                   tests-and-calls-term-listsp)
                                  (clean-up-conjunction-when-not-contradiction)))))
