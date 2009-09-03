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

(defthm pseudo-termp-conjoin
  (implies (pseudo-term-listp x)
           (pseudo-termp (conjoin x)))
  :hints(("Goal" :in-theory (enable conjoin pseudo-termp pseudo-term-listp))))

(defthm pseudo-term-listp-disjoin-lst
  (implies (pseudo-term-list-listp x)
           (pseudo-term-listp (disjoin-lst x))))

(defthm pseudo-termp-conjoin-clauses
  (implies (pseudo-term-list-listp clauses)
           (pseudo-termp (conjoin-clauses clauses)))
  :hints(("Goal" :in-theory (e/d (conjoin-clauses) (disjoin-lst)))))



(defmacro def-join-thms (ev)
  `(encapsulate
     nil
     (local (in-theory (e/d (conjoin disjoin)
                            (default-car default-cdr))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-DISJOIN-CONS")
               ev)
       (iff (,ev (disjoin (cons x y)) a)
            (or (,ev x a)
                (,ev (disjoin y) a))))

     (defthmd ,(intern-in-package-of-symbol
                (concatenate 'string
                             (symbol-name ev)
                             "-DISJOIN-WHEN-CONSP")
                ev)
       (implies (consp x)
                (iff (,ev (disjoin x) a)
                     (or (,ev (car x) a)
                         (,ev (disjoin (cdr x)) a)))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-DISJOIN-ATOM")
               ev)
       (implies (not (consp x))
                (equal (,ev (disjoin x) a)
                       nil))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-DISJOIN-APPEND")
               ev)
       (iff (,ev (disjoin (append x y)) a)
            (or (,ev (disjoin x) a)
                (,ev (disjoin y) a)))
       :hints (("goal" :induct (append x y)
                :in-theory (disable disjoin))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-CONS")
               ev)
       (iff (,ev (conjoin (cons x y)) a)
            (and (,ev x a)
                 (,ev (conjoin y) a))))

     (defthmd ,(intern-in-package-of-symbol
                (concatenate 'string
                             (symbol-name ev)
                             "-CONJOIN-WHEN-CONSP")
                ev)
       (implies (consp x)
                (iff (,ev (conjoin x) a)
                     (and (,ev (car x) a)
                          (,ev (conjoin (cdr x)) a)))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-ATOM")
               ev)
       (implies (not (consp x))
                (equal (,ev (conjoin x) a)
                       t))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-APPEND")
               ev)
       (iff (,ev (conjoin (append x y)) a)
            (and (,ev (conjoin x) a)
                 (,ev (conjoin y) a)))
       :hints (("goal" :induct (append x y)
                :in-theory (disable conjoin))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-CLAUSES-CONS")
               ev)
       (iff (,ev (conjoin-clauses (cons x y)) a)
            (and (,ev (disjoin x) a)
                 (,ev (conjoin-clauses y) a)))
       :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst))))


     (defthmd ,(intern-in-package-of-symbol
                (concatenate 'string
                             (symbol-name ev)
                             "-CONJOIN-CLAUSES-WHEN-CONSP")
                ev)
       (implies (consp x)
                (iff (,ev (conjoin-clauses x) a)
                     (and (,ev (disjoin (car x)) a)
                          (,ev (conjoin-clauses (cdr x)) a)))))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-CLAUSES-ATOM")
               ev)
       (implies (not (consp x))
                (equal (,ev (conjoin-clauses x) a)
                       t))
       :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst)))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string
                            (symbol-name ev)
                            "-CONJOIN-CLAUSES-APPEND")
               ev)
       (iff (,ev (conjoin-clauses (append x y)) a)
            (and (,ev (conjoin-clauses x) a)
                 (,ev (conjoin-clauses y) a)))
       :hints (("goal" :induct (append x y))))))
