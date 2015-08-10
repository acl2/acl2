
(in-package "ACL2")

(set-state-ok t)

;; This clause processor lets one replace one of the hyps (i.e. the negation of
;; one of the literals of the clause) with something that hyp provably
;; implies.  See the comment above (defun replace-impl ... ) below.

(defevaluator use-impl-ev use-impl-ev-list
  ((not x) (if a b c) (implies a b)))

(defthm conjoin-clauses-of-one
  (equal (conjoin-clauses (list x))
         (disjoin x)))

(defthm use-impl-ev-conjoin-clauses-of-two-or-more
  (iff (use-impl-ev (conjoin-clauses (cons x (cons y z))) a)
       (and (use-impl-ev (disjoin x) a)
            (use-impl-ev (conjoin-clauses (cons y z)) a))))

(in-theory (disable conjoin-clauses))

(defthm use-impl-ev-of-disjoin1
  (iff (use-impl-ev (disjoin (cons x y)) a)
       (or (use-impl-ev x a)
           (use-impl-ev (disjoin y) a))))

(defthm use-impl-ev-of-conjoin1
  (iff (use-impl-ev (conjoin (cons x y)) a)
       (and (use-impl-ev x a)
            (use-impl-ev (conjoin y) a))))

(defthm use-impl-ev-of-disjoin2
  (implies (not (consp x))
           (equal (use-impl-ev (disjoin x) a) nil)))

(defthm use-impl-ev-of-conjoin2
  (implies (not (consp x))
           (equal (use-impl-ev (conjoin x) a) t)))

(defthm pseudo-term-listp-cons
  (iff (pseudo-term-listp (cons x y))
       (and (pseudo-termp x)
            (pseudo-term-listp y))))

(in-theory (disable conjoin disjoin pseudo-term-listp))

(defun replace-impl-fn (hyp sense repl clause)
  (declare (xargs :guard t))
  (if (atom clause)
      (mv t clause)
    (let ((lit (car clause)))
      (if sense
          (if (equal lit hyp)
              (mv nil (cons (list 'not repl) (cdr clause)))
            (mv-let (samep rest)
              (replace-impl-fn hyp sense repl (cdr clause))
              (if samep
                  (mv t clause)
                (mv nil (cons (car clause) rest)))))
        (if (and (consp lit)
                 (eq (car lit) 'not)
                 (consp (cdr lit))
                 (equal (cadr lit) hyp))
            (mv nil (cons (list 'not repl) (cdr clause)))
          (mv-let (samep rest)
              (replace-impl-fn hyp sense repl (cdr clause))
              (if samep
                  (mv t clause)
                (mv nil (cons (car clause) rest)))))))))

(defthm replace-impl-fn-same
  (implies (mv-nth 0 (replace-impl-fn hyp sense repl clause))
           (equal (mv-nth 1 (replace-impl-fn hyp sense repl clause))
                  clause)))

(defthm replace-impl-fn-correct
  (implies (and (use-impl-ev (disjoin (mv-nth 1 (replace-impl-fn
                                                 hyp sense repl clause))) a)
                (or (if sense
                        (use-impl-ev hyp a)
                      (not (use-impl-ev hyp a)))
                    (use-impl-ev repl a)))
           (use-impl-ev (disjoin clause) a))
  :rule-classes :forward-chaining)


(defun replace-impl-cp (clause term)
  (declare (xargs :guard t))
  (if (eql (len term) 2)
      (let ((hyp (car term))
            (repl (cadr term)))
        (mv-let (samep cl)
          (if (and (consp hyp) (eq (car hyp) 'not) (consp (cdr hyp)))
              (replace-impl-fn (cadr hyp) t repl clause)
            (replace-impl-fn hyp nil repl clause))
          (if samep
              (list clause)
            (list cl (list `(not ,hyp) repl)))))
    (list clause)))

(defthm replace-impl-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (use-impl-ev (conjoin-clauses
                              (replace-impl-cp cl term))
                             a))
           (use-impl-ev (disjoin cl) a))
  :rule-classes :clause-processor)


(mutual-recursion
 (defun term-sublis (al x)
   (declare (xargs :guard (and (alistp al)
                               (pseudo-termp x))
                   :mode :program))
   (cond ((atom x)
          (let ((entry (assoc x al)))
            (if entry (cdr entry) x)))
         ((eq (car x) 'quote) x)
         (t
          ;; Don't dive into lambdas, but do term-sublis the args.
          (cons (car x) (term-list-sublis al (cdr x))))))
 (defun term-list-sublis (al x)
   (declare (xargs :guard (and (alistp al)
                               (pseudo-term-listp x))))
   (if (atom x)
       nil
     (cons (term-sublis al (car x))
           (term-list-sublis al (cdr x))))))


(defun find-instance-fn (x sense cl)
  (declare (xargs :mode :program))
  (if (atom cl)
      (mv nil nil nil)
    (if sense
        (mv-let (okp al)
          (one-way-unify x (car cl))
          (if okp
              (mv okp (list 'not (car cl)) al)
            (find-instance-fn x sense (cdr cl))))
      (if (and (consp (car cl))
               (eq (car (car cl)) 'not))
          (mv-let (okp al)
            (one-way-unify x (cadr (car cl)))
            (if okp
                (mv okp (cadr (car cl)) al)
              (find-instance-fn x sense (cdr cl))))
        (find-instance-fn x sense (cdr cl))))))

(defun find-instance (hyp-pat concl-pat cl)
  (declare (xargs :mode :program))
  (mv-let (ok hyp alst)
    (if (and (consp hyp-pat)
             (eq (car hyp-pat) 'not))
        (find-instance-fn (cadr hyp-pat) t cl)
      (find-instance-fn hyp-pat nil cl))
    (mv ok hyp (and ok (term-sublis alst concl-pat)))))

;; This is a computed hint which searches cl for a negated literal HYP that
;; unifies with (the translated version of) hyp-pat.  It then replaces this
;; literal with the result CONCL of substituting the variables of concl-pat for
;; the ones that matched in hyp-pat.  It is then also necessary to prove that
;; HYP implies CONCL.
(defun replace-impl (hyp-pat concl-pat cl state)
  (declare (xargs :mode :program))
  (er-let* ((hyp-pat (translate hyp-pat t t t 'replace-impl (w state) state))
            (concl-pat (translate concl-pat t t t 'replace-impl (w state) state)))
           (mv-let (ok hyp concl)
             (find-instance hyp-pat concl-pat cl)
             (value
              (and ok
                   `(:clause-processor (replace-impl-cp clause
                                                        ',(list hyp concl))))))))






