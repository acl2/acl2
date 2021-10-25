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

;; TODO: Use a simple evaluator (one with IF and NOT)?

;; Handles goal like (implies (and a_1 a_2 ...) (and b_1 b_2 ...)) where the as
;; and bs are, in general, disjunctions and the a_i obviously imply some of the
;; b_i (in the sense that som b_i has the all the disjuncts of some a_i, in the
;; same order, but may have additional disjuncts).  (The extra disjuncts may
;; often mention the flag variable in a defthm-flag proof.)

(include-book "handle-constant-literals")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/conjuncts-and-disjuncts0" :dir :system)
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)
(local (include-book "kestrel/utilities/conjuncts-and-disjuncts0-proof" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/disjoin" :dir :system))

(local (in-theory (enable pseudo-termp-when-symbolp)))

(local (in-theory (disable symbol-alistp
                           strip-cdrs
                           assoc-equal)))

;; This requires the TEST to not be constant, because we can do better if it may be.
(defun make-if-term (test then else)
  (declare (xargs :guard (and (pseudo-termp test)
                              (not (quotep test))
                              (pseudo-termp then)
                              (pseudo-termp else))))
  (if (equal then else)
      then
    `(if ,test ,then ,else)))

;; just changes the evaluator
(defthm if-and-not-eval-of-disjoin-of-handle-constant-literals
  (iff (if-and-not-eval (disjoin (handle-constant-literals clause)) a)
       (if-and-not-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance if-eval-of-disjoin-of-handle-constant-literals
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

;; just changes the evaluator
(defthm if-and-not-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
  (iff (if-and-not-eval (conjoin (disjoin-lst (clause-to-clause-list clause))) a)
       (if-and-not-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance if-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

;; ;; just changes the evaluator
;; (defthm all-eval-to-true-with-if-and-not-eval-of-get-conjuncts-of-term
;;   (iff (all-eval-to-true-with-if-and-not-eval (get-conjuncts-of-term term) a)
;;        (if-and-not-eval term a))
;;   :hints (("Goal" :use (:functional-instance all-eval-to-true-with-if-and-not-eval-of-get-conjuncts-of-term
;;                                              (if-and-not-eval if-and-not-eval)
;;                                              (if-and-not-eval-list if-and-not-eval-list)
;;                                              (all-eval-to-true-with-if-and-not-eval all-eval-to-true-with-if-and-not-eval)))))

;; (defthm all-eval-to-false-with-if-and-not-eval-of-get-disjuncts-of-term
;;   (iff (all-eval-to-false-with-if-and-not-eval (get-disjuncts-of-term term) a)
;;        (not (if-and-not-eval term a)))
;;   :hints (("Goal" :use (:functional-instance all-eval-to-false-with-if-and-not-eval-of-get-disjuncts-of-term
;;                                              (if-and-not-eval if-and-not-eval)
;;                                              (if-and-not-eval-list if-and-not-eval-list)
;;                                              (all-eval-to-false-with-if-and-not-eval all-eval-to-false-with-if-and-not-eval)))))


(defthm all-eval-to-false-with-if-and-not-eval-of-negate-terms
  (iff (all-eval-to-false-with-if-and-not-eval (negate-terms terms) a)
       (all-eval-to-true-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable negate-terms negate-term))))

(defthm all-eval-to-false-with-if-and-not-eval-of-negate-disjunct-list
  (iff (all-eval-to-false-with-if-and-not-eval (negate-disjunct-list terms) a)
       (all-eval-to-true-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable negate-disjunct-list
                                     ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL))))



;todo: use more
(defund term-is-disjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (equal *t* (farg2 term)) ; todo: allow (if x x y)
       ))

(defthm if-and-not-eval-when-term-is-disjunctionp
  (implies (term-is-disjunctionp disj)
           (iff (if-and-not-eval disj a)
                (or (if-and-not-eval (farg1 disj) a)
                    (if-and-not-eval (farg3 disj) a))))
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm if-and-not-eval-of-cadddr-when-term-is-disjunctionp-forward
  (implies (and (if-and-not-eval (cadddr disj) a)
                (term-is-disjunctionp disj))
           (if-and-not-eval disj a))
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

(defthm if-and-not-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (if-and-not-eval conj a)
                (and (if-and-not-eval (farg1 conj) a)
                     (if-and-not-eval (farg2 conj) a))))
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

(defthm if-and-not-eval-of-cadddr-when-term-is-conjunctionp-forward
  (implies (and (not (if-and-not-eval (caddr conj) a))
                (term-is-conjunctionp conj))
           (not (if-and-not-eval conj a)))
  :rule-classes :forward-chaining)

(defthm if-and-not-eval-of-cadddr-when-term-is-conjunctionp
  (implies (and (if-and-not-eval conj a)
                (term-is-conjunctionp conj))
         (if-and-not-eval (caddr conj) a))
)

;move?
;; Skip any leading conjuncts in CONJ that are not D.  CONJ is an IF-nest.
(defund skip-conjuncts-before (d conj)
  (declare (xargs :guard (and (pseudo-termp d)
                              (pseudo-termp conj))
                  :hints (("Goal" :in-theory (enable term-is-conjunctionp)))
                  :guard-hints (("Goal" :in-theory (enable term-is-conjunctionp)))))
  (if (not (term-is-conjunctionp conj))
      conj ; no more conjuncts
    ;; look for (if x y 'nil)
    (if (equal d (farg1 conj))
        conj
      (skip-conjuncts-before d (farg2 conj)))))

(defthm pseudo-termp-of-skip-conjuncts-before
  (implies (pseudo-termp conj)
           (pseudo-termp (skip-conjuncts-before d conj)))
  :hints (("Goal" :in-theory (enable skip-conjuncts-before))))

(defthm skip-conjuncts-before-correct
  (implies (not (if-and-not-eval (skip-conjuncts-before d conj) a))
           (not (if-and-not-eval conj a)))
  :hints (("Goal" :in-theory (enable skip-conjuncts-before))))

(defthm skip-conjuncts-lemma-helper
  (implies (term-is-conjunctionp (skip-conjuncts-before d conj))
           (equal (farg1 (skip-conjuncts-before d conj))
                  d))
  :hints (("Goal" :in-theory (enable skip-conjuncts-before
                                     TERM-IS-CONJUNCTIONP))))

(defthm skip-conjuncts-lemma
  (implies (and (not (if-and-not-eval d a))
                (term-is-conjunctionp (skip-conjuncts-before d conj)))
           (not (if-and-not-eval (skip-conjuncts-before d conj) a)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ;skip-conjuncts-before
                              ;TERM-IS-CONJUNCTIONP
                              ))))

(defund among-conjunctsp (d conj)
  (declare (xargs :guard (and (pseudo-termp d)
                              (pseudo-termp conj))))
  (if (not (and (call-of 'if conj)
                (= 3 (len (fargs conj)))))
      (equal d conj) ; no more conjuncts
    ;; look for (if d y 'nil), which is "d and y"
    (if (equal *nil* (farg3 conj))
        (or (equal d (farg1 conj))
            (among-conjunctsp d (farg2 conj)))
      nil)))

(defthm among-conjunctsp-before-correct
  (implies (among-conjunctsp d conj)
           (implies (not (if-and-not-eval d a))
                    (not (if-and-not-eval conj a))))
  :hints (("Goal" :in-theory (enable among-conjunctsp))))

;move
;; Check whether conj1 being false clearly implies conj2 is false.
;; Assumes the conjuncts are in the same order, but that conj2 may have extras.
;; Essentially checks that the conjuncts of CONJ1 are a subset of those of CONJ2 in the same order.
(defun clearly-unimplies-for-conjunctionsp (conj1 conj2)
  (declare (xargs :guard (and (pseudo-termp conj1)
                              (pseudo-termp conj2))
                  :guard-hints (("Goal" :in-theory (enable term-is-conjunctionp)))
                  :hints (("Goal" :in-theory (enable term-is-conjunctionp)))
                  ))
  (if (not (term-is-conjunctionp conj1))
      ;; conj1 is a single conjunct. check whether it is a conjunct of conj2:
      (among-conjunctsp conj1 conj2)
    ;; conj1 has at least 2 conjuncts:
    (let* ((d1 (farg1 conj1))
           (conj2 (skip-conjuncts-before d1 conj2)))
      ;; conj2 must be a conjunction, its first conjunct must be d1 (implied by
      ;; the fact that it's the result of skip-conjuncts-before), and the rest
      ;; of conj1 must unimply the rest of conj2:
      (and (term-is-conjunctionp conj2)
           ;; (equal d1 (farg1 conj2)) ;todo: is this guaranteed to be true?
           (clearly-unimplies-for-conjunctionsp (farg2 conj1) (farg2 conj2))))))

(defthm clearly-unimplies-for-conjunctionsp-correct
  (implies (clearly-unimplies-for-conjunctionsp conj1 conj2)
           (implies (not (if-and-not-eval conj1 a))
                    (not (if-and-not-eval conj2 a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable clearly-unimplies-for-conjunctionsp))))

(defund clearly-unimplied-by-some-conjunctionp (conj conjs)
  (declare (xargs :guard (and (pseudo-termp conj)
                              (pseudo-term-listp conjs))))
  (if (endp conjs)
      nil
    (or (clearly-unimplies-for-conjunctionsp (first conjs) conj)
        (clearly-unimplied-by-some-conjunctionp conj (rest conjs)))))

(defthm if-and-not-eval-when-clearly-unimplied-by-some-conjunctionp
  (implies (and (clearly-unimplied-by-some-conjunctionp term false-terms)
                (all-eval-to-false-with-if-and-not-eval false-terms a))
           (not (if-and-not-eval term a)))
  :hints (("Goal" :in-theory (enable clearly-unimplied-by-some-conjunctionp))))

;; In general, the TRUE-TERMS may be disjunctions (a true-term that is a
;; conjunction should have been flattened into multiple true-terms).  This goes
;; through the top-level IF-nest of TERM, resolving both tests and also then-
;; or else-branches whenever it can (we only preserve iff on TERM and therefore
;; on its then- and else-branches).
(defund resolve-ifs-in-term (term true-terms false-terms)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp true-terms)
                              (pseudo-term-listp false-terms))
                  :verify-guards nil ; done below
                  ))
  (if (quotep term)
      term
    (if (clearly-implied-by-some-disjunctionp term true-terms)
        *t*
      (if (clearly-unimplied-by-some-conjunctionp term false-terms)
          *nil*
        (if (and (call-of 'if term)
                 (= 3 (len (fargs term))))
            (let ((new-test (resolve-ifs-in-term (farg1 term) true-terms false-terms)))
              (if (quotep new-test)
                  (if (unquote new-test)
                      (resolve-ifs-in-term (farg2 term) true-terms false-terms)
                    (resolve-ifs-in-term (farg3 term) true-terms false-terms))
                (if (clearly-implied-by-some-disjunctionp new-test true-terms)
                    (resolve-ifs-in-term (farg2 term) true-terms false-terms)
                  (if (clearly-unimplied-by-some-conjunctionp new-test false-terms)
                      (resolve-ifs-in-term (farg3 term) true-terms false-terms)
                    (let ((new-if (make-if-term new-test
                                                ;; TODO: Consider assuming the test / negated test here:
                                                (resolve-ifs-in-term (farg2 term) true-terms false-terms)
                                                (resolve-ifs-in-term (farg3 term) true-terms false-terms))))
                      ;; TODO: Call clearly-implied-by-some-disjunctionp on this if different?:
                      new-if)))))
          ;; TODO: Consider resolving IF tests inside this:
          term)))))

(defthm pseudo-termp-of-resolve-ifs-in-term
  (implies (pseudo-termp term)
           (pseudo-termp (resolve-ifs-in-term term true-terms false-terms)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-term))))

(verify-guards resolve-ifs-in-term :hints (("Goal" :in-theory (enable len-when-pseudo-termp-and-quotep))))

(defthm resolve-ifs-in-term-correct
  (implies (and (all-eval-to-true-with-if-and-not-eval true-terms a)
                (all-eval-to-false-with-if-and-not-eval false-terms a))
           (iff (if-and-not-eval (resolve-ifs-in-term term true-terms false-terms) a)
                (if-and-not-eval term a)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-term))))

;; In general, the TRUE-TERMS are disjunctions.
;; Returns a new clause
;; TODO: Stop if any literal becomes *t*
(defund resolve-ifs-in-clause (clause true-terms false-terms)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-listp true-terms)
                              (pseudo-term-listp false-terms))))
  (if (endp clause)
      nil
    (let* ((lit (first clause))
           (new-lit (resolve-ifs-in-term lit true-terms false-terms)))
      (cons new-lit
            (resolve-ifs-in-clause (rest clause)
                                   ;; TODO: What about constants in these lists?:
                                   ;; TODO: Use new-lit here:
                                   ;; TODO: Consider union-equal instead of append
                                   (if (and (call-of 'not lit)
                                            (= 1 (len (fargs lit))))
                                       ;; if the clause is (or (not A) ...rest...)
                                       ;; we can assume A when processing rest
                                       (append (get-conjuncts-of-term (farg1 lit))
                                               true-terms)
                                     true-terms)
                                   ;; TODO: Extract all known true/false things from LIT:
                                   (if (and (call-of 'not lit)
                                            (= 1 (len (fargs lit))))
                                       false-terms
                                     (append (get-disjuncts-of-term lit)
                                             false-terms)))))))

(defthm resolve-ifs-in-clause-correct
  (implies (and (all-eval-to-true-with-if-and-not-eval true-terms a)
                (all-eval-to-false-with-if-and-not-eval false-terms a))
           (iff (if-and-not-eval (disjoin (resolve-ifs-in-clause clause true-terms false-terms)) a)
                (if-and-not-eval (disjoin clause) a)))
  :hints (("Goal" :expand (DISJOIN CLAUSE)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable resolve-ifs-in-clause))))

(defthm resolve-ifs-in-clause-correct-special
  (iff (if-and-not-eval (disjoin (resolve-ifs-in-clause clause nil nil)) a)
       (if-and-not-eval (disjoin clause) a)))

(defthm pseudo-term-listp-of-resolve-ifs-in-clause
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (resolve-ifs-in-clause clause true-terms false-terms)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-clause))))

(defund simple-subsumption-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (resolve-ifs-in-clause clause nil nil))
         (clause (handle-constant-literals clause)))
    (clause-to-clause-list clause)))

;todo: add :well-formedness proof
(defthm simple-subsumption-clause-processor-correct
  (implies (if-and-not-eval (conjoin-clauses (simple-subsumption-clause-processor clause)) a)
           (if-and-not-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable simple-subsumption-clause-processor))))
