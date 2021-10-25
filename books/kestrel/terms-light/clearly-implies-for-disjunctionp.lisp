; A utility to check for clear implication between disjunctions

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "term-is-disjunctionp")
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

;move?
;; Skip any leading disjuncts in DISJ that are not D.  DISJ is an IF-nest.
(defund skip-disjuncts-before (d disj)
  (declare (xargs :guard (and (pseudo-termp d)
                              (pseudo-termp disj))
                  :hints (("Goal" :in-theory (enable term-is-disjunctionp)))
                  :guard-hints (("Goal" :in-theory (enable term-is-disjunctionp)))))
  (if (not (term-is-disjunctionp disj))
      disj ; no more disjuncts
    ;; look for (if x 't y) ; todo: the 't could instead be x
    (if (equal d (farg1 disj))
        disj
      (skip-disjuncts-before d (farg3 disj)))))

(defthm pseudo-termp-of-skip-disjuncts-before
  (implies (pseudo-termp disj)
           (pseudo-termp (skip-disjuncts-before d disj)))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before))))

(defthm skip-disjuncts-before-correct
  (implies (if-and-not-eval (skip-disjuncts-before d disj) a)
           (if-and-not-eval disj a))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before))))

(defthm skip-disjuncts-lemma-helper
  (implies (term-is-disjunctionp (skip-disjuncts-before d disj))
           (equal (farg1 (skip-disjuncts-before d disj))
                  d))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before
                                     TERM-IS-DISJUNCTIONP))))

(defthm skip-disjuncts-lemma
  (implies (and (if-and-not-eval d a)
                (term-is-disjunctionp (skip-disjuncts-before d disj)))
           (if-and-not-eval (skip-disjuncts-before d disj) a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ;skip-disjuncts-before
                              ;TERM-IS-DISJUNCTIONP
                              ))))

(defund among-disjunctsp (d disj)
  (declare (xargs :guard (and (pseudo-termp d)
                              (pseudo-termp disj))))
  (if (not (term-is-disjunctionp disj))
      (equal d disj) ; no more disjuncts
    ;; look for (if d 't y) or (if d d y), which both mean "d or y"
    (or (equal d (farg1 disj))
        (among-disjunctsp d (farg3 disj)))))

(defthm among-disjunctsp-before-correct
  (implies (among-disjunctsp d disj)
           (implies (if-and-not-eval d a)
                    (if-and-not-eval disj a)))
  :hints (("Goal" :in-theory (enable among-disjunctsp))))

;move
;; Check whether disj1 clearly implies disj2.
;; Assumes the disjuncts are in the same order, but that disj2 may have extras.
;; Essentially checks that the disjuncts of DISJ1 are a subset of those of DISJ2 in the same order.
(defun clearly-implies-for-disjunctionsp (disj1 disj2)
  (declare (xargs :guard (and (pseudo-termp disj1)
                              (pseudo-termp disj2))
                  :guard-hints (("Goal" :in-theory (enable term-is-disjunctionp)))
                  :hints (("Goal" :in-theory (enable term-is-disjunctionp)))
                  ))
  (if (not (term-is-disjunctionp disj1))
      ;; disj1 is a single disjunct. check whether it is a disjunct of disj2:
      (among-disjunctsp disj1 disj2)
    ;; disj1 has at least 2 disjuncts:
    (let* ((d1 (farg1 disj1))
           (disj2 (skip-disjuncts-before d1 disj2)))
      ;; disj2 must be a disjunction, its first disjunct must be d1 (implied by
      ;; the fact that it's the result of skip-disjuncts-before), and the rest
      ;; of disj1 must imply the rest of disj2:
      (and (term-is-disjunctionp disj2)
           ;; (equal d1 (farg1 disj2)) ;todo: is this guaranteed to be true?
           (clearly-implies-for-disjunctionsp (farg3 disj1) (farg3 disj2))))))

(defthm clearly-implies-for-disjunctionsp-correct
  (implies (clearly-implies-for-disjunctionsp disj1 disj2)
           (implies (if-and-not-eval disj1 a)
                    (if-and-not-eval disj2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable clearly-implies-for-disjunctionsp))))

(defund clearly-implied-by-some-disjunctionp (disj disjs)
  (declare (xargs :guard (and (pseudo-termp disj)
                              (pseudo-term-listp disjs))))
  (if (endp disjs)
      nil
    (or (clearly-implies-for-disjunctionsp (first disjs) disj)
        (clearly-implied-by-some-disjunctionp disj (rest disjs)))))

(defthm if-and-not-eval-when-clearly-implied-by-some-disjunctionp
  (implies (and (clearly-implied-by-some-disjunctionp term true-terms)
                (all-eval-to-true-with-if-and-not-eval true-terms a))
           (if-and-not-eval term a))
  :hints (("Goal" :in-theory (enable clearly-implied-by-some-disjunctionp))))
