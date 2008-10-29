;; join-thms.lisp
;; by Sol Swords

;; Provides a macro which, when invoked, proves several useful theorems about
;; an evaluator, involving that evaluator's actions on conjoin, disjoin, etc.
;; The evaluator should recognize IF for this to work.

;; Example (from null-fail-hints.lisp:)
;; (defevaluator null-fail-hint-ev null-fail-hint-evl ((if a b c)))
;; (def-join-thms null-fail-hint-ev)


(in-package "ACL2")
  
(defthm conjoin-clauses-of-one
  (equal (conjoin-clauses (list x))
         (disjoin x)))

(in-theory (disable conjoin-clauses conjoin disjoin))

(defthm pseudo-termp-disjoin
  (implies (pseudo-term-listp x)
           (pseudo-termp (disjoin x)))
  :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp disjoin)
          :induct (disjoin x))))

(defmacro def-join-thms (ev)
  `(encapsulate
    nil
    (local (in-theory (enable conjoin disjoin)))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-CONJOIN-CLAUSES-OF-TWO-OR-MORE")
              ev)
      (iff (,ev (conjoin-clauses (cons x (cons y z))) a)
           (and (,ev (disjoin x) a)
                (,ev (conjoin-clauses (cons y z)) a)))
      :hints (("goal" :in-theory (enable conjoin-clauses conjoin disjoin))))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-DISJOIN-1")
              ev)
      (iff (,ev (disjoin (cons x y)) a)
           (or (,ev x a)
               (,ev (disjoin y) a))))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-CONJOIN-1")
              ev)
      (iff (,ev (conjoin (cons x y)) a)
           (and (,ev x a)
                (,ev (conjoin y) a))))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-DISJOIN-2")
              ev)
      (implies (not (consp x))
               (equal (,ev (disjoin x) a) nil)))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-CONJOIN-2")
              ev)
      (implies (not (consp x))
               (equal (,ev (conjoin x) a) t)))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-DISJOIN-3")
              ev)
      (implies (consp x)
               (iff (,ev (disjoin x) a)
                    (or (,ev (car x) a)
                        (,ev (disjoin (cdr x)) a))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm ,(intern-in-package-of-symbol
              (concatenate 'string
                           (symbol-name ev)
                           "-OF-CONJOIN-3")
              ev)
      (implies (consp x)
               (iff (,ev (conjoin x) a)
                    (and (,ev (car x) a)
                         (,ev (conjoin (cdr x)) a))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))))
