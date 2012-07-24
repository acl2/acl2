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

(defconst *def-join-thms-body*
  '(encapsulate
     nil
     (local (in-theory nil))
     (local (in-theory (e/d (append
                             conjoin disjoin car-cons cdr-cons
                             disjoin2 conjoin2 iff if-rule quote-rule
                             endp atom car-cdr-elim)
                            (default-car default-cdr))))

     (defthm disjoin-cons
       (iff (ev (disjoin (cons x y)) a)
            (or (ev x a)
                (ev (disjoin y) a))))

     (defthmd disjoin-when-consp
       (implies (consp x)
                (iff (ev (disjoin x) a)
                     (or (ev (car x) a)
                         (ev (disjoin (cdr x)) a)))))

     (defthm disjoin-atom
       (implies (not (consp x))
                (equal (ev (disjoin x) a)
                       nil))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm disjoin-append
       (iff (ev (disjoin (append x y)) a)
            (or (ev (disjoin x) a)
                (ev (disjoin y) a)))
       :hints (("goal" :induct (append x y)
                :in-theory (e/d (disjoin-when-consp)
                                (disjoin)))))
     
     (defthm conjoin-cons
       (iff (ev (conjoin (cons x y)) a)
            (and (ev x a)
                 (ev (conjoin y) a))))

     (defthmd conjoin-when-consp
       (implies (consp x)
                (iff (ev (conjoin x) a)
                     (and (ev (car x) a)
                          (ev (conjoin (cdr x)) a)))))

     (defthm conjoin-atom
       (implies (not (consp x))
                (equal (ev (conjoin x) a)
                       t))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm conjoin-append
       (iff (ev (conjoin (append x y)) a)
            (and (ev (conjoin x) a)
                 (ev (conjoin y) a)))
       :hints (("goal" :induct (append x y)
                :in-theory (e/d (conjoin-when-consp)
                                (conjoin)))))

     (defthm conjoin-clauses-cons
       (iff (ev (conjoin-clauses (cons x y)) a)
            (and (ev (disjoin x) a)
                 (ev (conjoin-clauses y) a)))
       :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst))))


     (defthmd conjoin-clauses-when-consp
       (implies (consp x)
                (iff (ev (conjoin-clauses x) a)
                     (and (ev (disjoin (car x)) a)
                          (ev (conjoin-clauses (cdr x)) a)))))

     (defthm conjoin-clauses-atom
       (implies (not (consp x))
                (equal (ev (conjoin-clauses x) a)
                       t))
       :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst)))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm conjoin-clauses-append
       (iff (ev (conjoin-clauses (append x y)) a)
            (and (ev (conjoin-clauses x) a)
                 (ev (conjoin-clauses y) a)))
       :hints (("goal" :induct (append x y))))))



;; Rewrite-rule fields: 
;; rune nume hyps equiv lhs rhs subclass heuristic-info backchain-limit-lst
;; var-info match-free


(defun find-matching-rule (hyps equiv lhs rhs lemmas)
  (if (atom lemmas)
      nil
    (or (let* ((rune  (access rewrite-rule (car lemmas) :rune))
               (rhyps  (access rewrite-rule (car lemmas) :hyps))
               (rlhs   (access rewrite-rule (car lemmas) :lhs))
               (rrhs   (access rewrite-rule (car lemmas) :rhs))
               (requiv (access rewrite-rule (car lemmas) :equiv)))
          (and (or (not hyps)  (equal rhyps hyps))
               (or (not lhs)   (equal rlhs lhs))
               (or (not rhs)   (equal rrhs rhs))
               (or (not equiv) (equal requiv equiv))
               rune))
        (find-matching-rule hyps equiv lhs rhs (cdr lemmas)))))

;; (defun ev-find-fncall-rule1 (ev fn lemmas)
;;   (if (atom lemmas)
;;       nil
;;     (or (and (let* ((equiv (access rewrite-rule (car lemmas) :equiv))
;;                     (hyps (access rewrite-rule (car lemmas) :hyps))
;;                     (lhs (access rewrite-rule (car lemmas) :lhs))
;;                     (rhs (access rewrite-rule (car lemmas) :rhs))
;;                     (rune (access rewrite-rule (car lemmas) :rune))
;;                     (subclass (access rewrite-rule (car lemmas) :subclass))
;;                     (backchain (access rewrite-rule (car lemmas) :backchain-limit-lst)))
;;                (and (case-match hyps (('(consp x) ('equal '(car x) ('quote !fn))) t))
;;                     (eq equiv 'equal)
;;                     (case-match lhs ((!ev . '(x a)) t))
;;                     (case-match rhs ((!fn . &) t))
;;                     (eq subclass 'backchain)
;;                     (eq backchain nil)
;;                     (eq (car rune) :rewrite)
;;                     rune)))
;;         (ev-find-fncall-rule1 ev fn (cdr lemmas)))))

(defun ev-find-fncall-rule-in-lemmas (ev fn lemmas)
  (find-matching-rule
   `((consp x) (equal (car x) ',fn))        ;; hyps
   'equal
   `(,ev x a)                               ;; lhs
   nil
   lemmas))

(defun ev-find-fncall-rule (ev fn world)
  (find-matching-rule
   `((consp x) (equal (car x) ',fn))        ;; hyps
   'equal
   `(,ev x a)                               ;; lhs
   nil
   (fgetprop ev 'lemmas nil world)))




(defun ev-mk-rulename (ev name)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name ev) "-"
                (symbol-name name))
   ev))

(defun ev-pair-rulenames (ev names)
  (if (atom names)
      nil
    (cons (cons (car names) (ev-mk-rulename ev (car names)))
          (ev-pair-rulenames ev (cdr names)))))

(defmacro def-join-thms (ev)
  (let ((alist `((ev . ,ev)
                 . ,(ev-pair-rulenames ev '(disjoin-cons
                                            disjoin-when-consp
                                            disjoin-atom
                                            disjoin-append
                                            conjoin-cons
                                            conjoin-when-consp
                                            conjoin-atom
                                            conjoin-append
                                            conjoin-clauses-cons
                                            conjoin-clauses-when-consp
                                            conjoin-clauses-atom
                                            conjoin-clauses-append)))))
    `(make-event
      (let* ((if-rule (ev-find-fncall-rule ',ev 'if (w state)))
             (quote-rule (ev-find-fncall-rule ',ev 'quote (w state)))
             (alist (list* (cons 'if-rule if-rule)
                           (cons 'quote-rule quote-rule)
                           ',alist)))
        (cond ((not if-rule)
               (er soft 'def-join-thms
                   (msg "Unable to find a rewrite rule for (~x0 X A) when ~
                         (CAR X) is IF~%" ',ev)))
              ((not quote-rule)
               (er soft 'def-join-thms
                   (msg "Unable to find a rewrite rule for (~x0 X A) when ~
                         (CAR X) is QUOTE~%" ',ev)))
              (t (value (sublis alist *def-join-thms-body*))))))))

