; A clause processor that performs a simple form of subsumption

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename this to resolve-ifs??  it's more than just subsumption
;; we use earlier facts to resolve later facts

;; Handles goal like (implies (and a_1 a_2 ...) (and b_1 b_2 ...)) where the as
;; and bs are, in general, disjunctions and the a_i obviously imply some of the
;; b_i (in the sense that som b_i has the all the disjuncts of some a_i, in the
;; same order, but may have additional disjuncts).  (The extra disjuncts may
;; often mention the flag variable in a defthm-flag proof.)

(include-book "handle-constant-literals")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/evaluators/equality-eval" :dir :system)
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

(local (in-theory (enable pseudo-termp-when-symbolp)))

(local (in-theory (disable disjoin
                           symbol-alistp
                           strip-cdrs
                           assoc-equal)))

(defthm disjoin-when-not-consp
  (IMPLIES (NOT (CONSP CLAUSE))
           (equal (DISJOIN CLAUSE)
                  *nil*))
  :hints (("Goal" :in-theory (enable disjoin))))

;todo: use more
(defund term-is-disjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (equal *t* (farg2 term)) ; todo: allow (if x x y)
       ))

(defthm equality-eval-when-term-is-disjunctionp
  (implies (term-is-disjunctionp disj)
           (iff (equality-eval disj a)
                (or (equality-eval (farg1 disj) a)
                    (equality-eval (farg3 disj) a))))
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm equality-eval-of-cadddr-when-term-is-disjunctionp-forward
  (implies (and (equality-eval (cadddr disj) a)
                (term-is-disjunctionp disj))
           (equality-eval disj a))
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

(defthm equality-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (equality-eval conj a)
                (and (equality-eval (farg1 conj) a)
                     (equality-eval (farg2 conj) a))))
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
  (implies (equality-eval (skip-disjuncts-before d disj) a)
           (equality-eval disj a))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before))))

(defthm skip-disjuncts-lemma-helper
  (implies (term-is-disjunctionp (skip-disjuncts-before d disj))
           (equal (farg1 (skip-disjuncts-before d disj))
                  d))
  :hints (("Goal" :in-theory (enable skip-disjuncts-before
                                     TERM-IS-DISJUNCTIONP))))

(defthm skip-disjuncts-lemma
  (implies (and (equality-eval d a)
                (term-is-disjunctionp (skip-disjuncts-before d disj)))
           (equality-eval (skip-disjuncts-before d disj) a))
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
           (implies (equality-eval d a)
                    (equality-eval disj a)))
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
           (implies (equality-eval disj1 a)
                    (equality-eval disj2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable clearly-implies-for-disjunctionsp))))

(defund clearly-implied-by-some-disjunctionp (disj disjs)
  (declare (xargs :guard (and (pseudo-termp disj)
                              (pseudo-term-listp disjs))))
  (if (endp disjs)
      nil
    (or (clearly-implies-for-disjunctionsp (first disjs) disj)
        (clearly-implied-by-some-disjunctionp disj (rest disjs)))))

(defthm equality-eval-when-clearly-implied-by-some-disjunctionp
  (implies (and (clearly-implied-by-some-disjunctionp term true-terms)
                (all-eval-to-true-with-equality-eval true-terms a))
           (equality-eval term a))
  :hints (("Goal" :in-theory (enable clearly-implied-by-some-disjunctionp))))

(defun make-if-term (test then else)
  (declare (xargs :guard (and (pseudo-termp test)
                              (pseudo-termp then)
                              (pseudo-termp else))))
  (if (equal then else)
      then
    `(if ,test ,then ,else)))

;; In general, the conjuncts of CONJ and the TRUE-TERMS are disjunctions.
(defun resolve-ifs-in-term (term true-terms)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp true-terms))
                  :verify-guards nil ; done below
                  ))
  (if (quotep term)
      term
    (if (clearly-implied-by-some-disjunctionp term true-terms) ;or should we do this on new-if below?
        *t*
      (if (and (call-of 'if term)
               (= 3 (len (fargs term))))
          (let ((new-test (resolve-ifs-in-term (farg1 term) true-terms)))
            (if (quotep new-test)
                (if (unquote new-test)
                    (resolve-ifs-in-term (farg2 term) true-terms)
                  (resolve-ifs-in-term (farg3 term) true-terms))
              (if (clearly-implied-by-some-disjunctionp new-test true-terms)
                  (resolve-ifs-in-term (farg2 term) true-terms)
                ;; todo: what if we can resolve the test to false?
                ;;todo: clean up this if:
                (let ((new-if (make-if-term new-test
                                            (resolve-ifs-in-term (farg2 term) true-terms)
                                            (resolve-ifs-in-term (farg3 term) true-terms))))
                  new-if))))
        (if (clearly-implied-by-some-disjunctionp term true-terms)
            *t*
          term)))))

(defthm pseudo-termp-of-resolve-ifs-in-term
  (implies (pseudo-termp term)
           (pseudo-termp (resolve-ifs-in-term term true-terms)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-term))))

(verify-guards resolve-ifs-in-term :hints (("Goal" :in-theory (enable len-when-pseudo-termp-and-quotep))))

(defthm resolve-ifs-in-term-correct
  (implies (all-eval-to-true-with-equality-eval true-terms a)
           (iff (equality-eval (resolve-ifs-in-term term true-terms) a)
                (equality-eval term a)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-term))))

;; In general, the TRUE-TERMS are disjunctions.
;; Returns a new clause
;; TODO: Stop if any literal becomes *t*
(defund resolve-ifs-in-clause (clause true-terms)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-listp true-terms))))

  (if (endp clause)
      nil
    (let* ((lit (first clause)))
      (cons (resolve-ifs-in-term lit true-terms)
            (resolve-ifs-in-clause (rest clause)
                                   ;; todo: what about things that are not calls of not?  track false-terms too?
                                   (if (and (call-of 'not lit)
                                            (= 1 (len (fargs lit))))
                                       ;; if the clause is (or (not A) ...)
                                       ;; we can assume A when processing ...
                                       (cons (farg1 lit) true-terms)
                                     true-terms))))))

(defthm resolve-ifs-in-clause-correct
  (implies (all-eval-to-true-with-equality-eval true-terms a)
           (iff (equality-eval (disjoin (resolve-ifs-in-clause clause true-terms)) a)
                (equality-eval (disjoin clause) a)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-term
                                     resolve-ifs-in-clause))))

(defthm resolve-ifs-in-clause-correct-special
  (iff (equality-eval (disjoin (resolve-ifs-in-clause clause nil)) a)
       (equality-eval (disjoin clause) a)))

(defthm pseudo-term-listp-of-resolve-ifs-in-clause
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (resolve-ifs-in-clause clause true-terms)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-clause))))

(defund simple-subsumption-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (resolve-ifs-in-clause clause nil))
         (clause (handle-constant-literals clause)))
    (clause-to-clause-list clause)))

;todo: add :well-formedness proof
(defthm simple-subsumption-clause-processor-correct
  (implies (equality-eval (conjoin-clauses (simple-subsumption-clause-processor clause)) a)
           (equality-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable simple-subsumption-clause-processor))))
