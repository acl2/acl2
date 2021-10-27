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
(include-book "kestrel/terms-light/term-is-disjunctionp" :dir :system)
(include-book "kestrel/terms-light/term-is-conjunctionp" :dir :system)
(include-book "kestrel/terms-light/clearly-implies-for-disjunctionp" :dir :system)
(include-book "kestrel/terms-light/make-if-term" :dir :system)
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

(defthm if-and-not-eval-when-clearly-implied-by-some-disjunctionp
  (implies (and (clearly-implied-by-some-disjunctionp term true-terms)
                (all-eval-to-true-with-if-and-not-eval true-terms a))
           (if-and-not-eval term a))
  :hints (("Goal" :use (:functional-instance if-eval-when-clearly-implied-by-some-disjunctionp
                                             (all-eval-to-true-with-if-eval all-eval-to-true-with-if-and-not-eval)
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))


(defthm if-and-not-eval-of-cadddr-when-term-is-conjunctionp-forward
  (implies (and (not (if-and-not-eval (caddr conj) a))
                (term-is-conjunctionp conj))
           (not (if-and-not-eval conj a)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:functional-instance if-eval-of-cadddr-when-term-is-conjunctionp-forward
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

(defthm if-and-not-eval-of-cadddr-when-term-is-conjunctionp
  (implies (and (if-and-not-eval conj a)
                (term-is-conjunctionp conj))
           (if-and-not-eval (caddr conj) a))
  :hints (("Goal" :use (:functional-instance if-eval-of-cadddr-when-term-is-conjunctionp
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))


;;changes the evaluator
(defthm if-and-not-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (if-and-not-eval conj a)
                (and (if-and-not-eval (farg1 conj) a)
                     (if-and-not-eval (farg2 conj) a))))
  :hints (("Goal" :use (:functional-instance if-eval-when-term-is-conjunctionp
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

;; just changes the evaluator
;drop?
(defthm all-eval-to-false-with-if-and-not-eval-of-handle-constant-literals
  (equal (all-eval-to-false-with-if-and-not-eval (handle-constant-literals clause) a)
         (all-eval-to-false-with-if-and-not-eval clause a))
  :hints (("Goal" :use (:functional-instance all-eval-to-false-with-if-eval-of-handle-constant-literals
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

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

;move?
;; Skip any leading conjuncts in CONJ that are not D.  CONJ is usually an IF-nest.
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
  :hints (("Goal" :expand (disjoin clause)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable resolve-ifs-in-clause))))

(defthm resolve-ifs-in-clause-correct-special
  (iff (if-and-not-eval (disjoin (resolve-ifs-in-clause clause nil nil)) a)
       (if-and-not-eval (disjoin clause) a)))

(defthm pseudo-term-listp-of-resolve-ifs-in-clause
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (resolve-ifs-in-clause clause true-terms false-terms)))
  :hints (("Goal" :in-theory (enable resolve-ifs-in-clause))))

;; The main clause processor defined in this book:
;; TODO: Start by calling simplify-assumptions-in-clause?
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
