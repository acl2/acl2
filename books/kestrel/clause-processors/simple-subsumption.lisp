; A clause processor that performs a simple form of subsumption

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Handles goal like (implies (and a_1 a_2 ...) (and b_1 b_2 ...)) where the as
;; and bs are, in general, disjunctions and the a_i obviously imply some of the
;; b_i (in the sense that som b_i has the all the disjuncts of some a_i, in the
;; same order, but may have additional disjuncts).  (The extra disjuncts may
;; often mention the flag variable in a defthm-flag proof.)

(include-book "subst-flag") ; todo: reduce
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable pseudo-termp-when-symbolp)))

(local (in-theory (disable disjoin
                           symbol-alistp
                           strip-cdrs
                           assoc-equal)))

;todo: use more
(defund term-is-disjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (equal *t* (farg2 term)) ; todo: allow (if x x y)
       ))

(defthm simple-eval-when-term-is-disjunctionp
  (implies (term-is-disjunctionp disj)
           (iff (simple-eval disj a)
                (or (simple-eval (farg1 disj) a)
                    (simple-eval (farg3 disj) a))))
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm simple-eval-of-cadddr-when-term-is-disjunctionp-forward
  (implies (and (simple-eval (cadddr disj) a)
                (term-is-disjunctionp disj))
           (simple-eval disj a))
  :rule-classes :forward-chaining)

(defund term-is-conjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (equal *nil* (farg3 term)) ; todo: allow (if x y nil)
       ))

(defthm term-is-conjunctionp-forward-to-consp
  (implies (term-is-conjunctionp term)
           (consp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm term-is-conjunctionp-forward-to-pseudo-termp-of-cadr
  (implies (and (term-is-conjunctionp term)
                (pseudo-termp term))
           (pseudo-termp (cadr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm term-is-conjunctionp-forward-to-pseudo-termp-of-caddr
  (implies (and (term-is-conjunctionp term)
                (pseudo-termp term))
           (pseudo-termp (caddr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm simple-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (simple-eval conj a)
                (and (simple-eval (farg1 conj) a)
                     (simple-eval (farg2 conj) a))))
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

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
  (implies (simple-eval (skip-disjuncts-before d disj) a)
           (simple-eval disj a))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before))))

(defthm skip-disjuncts-lemma-helper
  (implies (term-is-disjunctionp (skip-disjuncts-before d disj))
           (equal (farg1 (skip-disjuncts-before d disj))
                  d))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before
                                     TERM-IS-DISJUNCTIONP))))

(defthm skip-disjuncts-lemma
  (implies (and (simple-eval d a)
                (term-is-disjunctionp (skip-disjuncts-before d disj)))
           (simple-eval (skip-disjuncts-before d disj) a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ;skip-disjuncts-before
                              ;TERM-IS-DISJUNCTIONP
                              ))))

(defund among-disjunctsp (d disj)
  (declare (xargs :guard (and (pseudo-termp d)
                              (pseudo-termp disj))))
  (if (not (and (call-of 'if disj)
                (= 3 (len (fargs disj)))))
      (equal d disj) ; no more disjuncts
    ;; look for (if d 't y), which is "d or y" ; todo: the 't could instead be d
    (if (equal *t* (farg2 disj))
        (or (equal d (farg1 disj))
            (among-disjunctsp d (farg3 disj)))
      nil)))

(defthm among-disjunctsp-before-correct
  (implies (among-disjunctsp d disj)
           (implies (simple-eval d a)
                    (simple-eval disj a)))
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
           (implies (simple-eval disj1 a)
                    (simple-eval disj2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable clearly-implies-for-disjunctionsp))))

(defund clearly-implied-by-some-disjunctionp (disj disjs)
  (declare (xargs :guard (and (pseudo-termp disj)
                              (pseudo-term-listp disjs))))
  (if (endp disjs)
      nil
    (or (clearly-implies-for-disjunctionsp (first disjs) disj)
        (clearly-implied-by-some-disjunctionp disj (rest disjs)))))

(defthm simple-eval-when-clearly-implied-by-some-disjunctionp
  (implies (and (clearly-implied-by-some-disjunctionp term true-terms)
                (all-eval-to-true-with-simple-eval true-terms a))
           (simple-eval term a))
  :hints (("Goal" :in-theory (enable clearly-implied-by-some-disjunctionp))))

;; In general, the conjuncts of CONJ and the TRUE-TERMS are disjunctions.
(defun remove-true-conjuncts (conj true-terms)
  (declare (xargs :guard (and (pseudo-termp conj)
                              (pseudo-term-listp true-terms))))
  (if (not (term-is-conjunctionp conj))
      (if (member-equal conj true-terms)
          *t*
        conj)
    ;; conj is a conjunction:
    (let ((c (farg1 conj)))
      (if (clearly-implied-by-some-disjunctionp c true-terms)
          (remove-true-conjuncts (farg2 conj) true-terms)
        `(if ,c ,(remove-true-conjuncts (farg2 conj) true-terms) 'nil)))))

(defthm remove-true-conjuncts-correct
  (implies (all-eval-to-true-with-simple-eval true-terms a)
           (iff (simple-eval (remove-true-conjuncts conj true-terms) a)
                (simple-eval conj a)))
  :hints (("Goal" :in-theory (enable remove-true-conjuncts))))

;; In general, the TRUE-TERMS are disjunctions.
(defund remove-true-conjuncts-in-clause (clause true-terms)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-listp true-terms))))

  (if (endp clause)
      nil
    (let* ((lit (first clause))
           (new-lit (remove-true-conjuncts lit true-terms)))
      (cons new-lit
            (remove-true-conjuncts-in-clause (rest clause)
                                             (if (and (call-of 'not lit)
                                                      (= 1 (len (fargs lit))))
                                                 ;; if the clause is (or (not A) ...)
                                                 ;; we can assume A when processing ...
                                                 (cons (farg1 lit) true-terms)
                                               true-terms))))))

(defthm disjoin-when-not-consp
  (IMPLIES (NOT (CONSP CLAUSE))
           (equal (DISJOIN CLAUSE)
                  *nil*))
  :hints (("Goal" :in-theory (enable disjoin))))

(defthm remove-true-conjuncts-in-clause-correct
  (implies (all-eval-to-true-with-simple-eval true-terms a)
           (iff (simple-eval (disjoin (remove-true-conjuncts-in-clause clause true-terms)) a)
                (simple-eval (disjoin clause) a)))
  :hints (("Goal" :in-theory (enable remove-true-conjuncts
                                     remove-true-conjuncts-in-clause
                                     ;disjoin
                                     ))))

(defun simple-subsumption-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (list (remove-true-conjuncts-in-clause clause nil)))

;todo: add :well-formedness proof
(defthm simple-subsumption-clause-processor-correct
  (implies (and; (pseudo-term-listp clause)
                ;(alistp a)
                (simple-eval (conjoin-clauses (simple-subsumption-clause-processor clause)) a))
           (simple-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable sublis-var-and-simplify-clause-processor))))
