
(in-package "ACL2")
(include-book "unify-subst")
(include-book "tools/bstar" :dir :system)
(include-book "ev-theoremp")
(include-book "use-by-hint")

;; This could be made much more sophisticated.  However, at the moment we just
;; expand term with an EQUAL-based definition.

(defun just-expand-cp-hint-get-rule (rule fn w)
  (declare (xargs :mode :program))
  (if (not rule)
      (b* ((def (def-body fn w))
           ((unless (and def (not (access def-body def :hyp))))
            (er hard? 'just-expand-cp "couldn't find a hyp-free definition for ~x0"
                fn)
            nil))
        (list (cons fn (access def-body def :formals)) ;; lhs
              (access def-body def :concl)
              (access def-body def :rune)))
    (b* ((lemmas (getprop fn 'lemmas nil 'current-acl2-world w))
         (lemma (if (symbolp rule)
                    (find-named-lemma
                     (deref-macro-name rule (macro-aliases w))
                     lemmas t)
                  (find-runed-lemma rule lemmas)))
         ((unless (and lemma
                       (not (access rewrite-rule lemma :hyps))
                       (eq (access rewrite-rule lemma :equiv) 'equal)))
          (er hard? 'just-expand-cp "the definition has hyps or is not EQUAL-based")
          nil))
      (list (access rewrite-rule lemma :lhs)
            (access rewrite-rule lemma :rhs)
            (access rewrite-rule lemma :rune)))))

(defun just-expand-cp-finish-hint (rule vars term w)
  (declare (xargs :mode :program))
  (b* (((when (atom term))
        (er hard? 'just-expand-cp "atom in term position in hints: ~x0~%" term)) ;; error
       ((mv erp trans-term)
        (translate-cmp term t nil nil 'just-expand-cp w 
                       (default-state-vars nil)))
       ((when erp)
        (er hard? 'just-expand-cp "translate failed: ~@0~%" trans-term))
       ((list lhs rhs rune) (just-expand-cp-hint-get-rule rule (car trans-term)
                                                          w))
       (trans-term-vars (simple-term-vars trans-term))
       (nonfree-vars (set-difference-eq trans-term-vars vars)))
    (cons trans-term `((lhs . ,lhs)
                       (rhs . ,rhs)
                       (rune . ,rune)
                       (subst . ,(pairlis$ nonfree-vars nonfree-vars))))))

(defun just-expand-cp-parse-hint (hint w)
  (declare (xargs :mode :program))
  (case-match hint
    ((':with rule (':free vars term))
     (just-expand-cp-finish-hint rule vars term w))
    ((':free vars (':with rule term))
     (just-expand-cp-finish-hint rule vars term w))
    ((':free vars term)
     (just-expand-cp-finish-hint nil vars term w))
    ((':with rule term)
     (just-expand-cp-finish-hint rule nil term w))
    (& (just-expand-cp-finish-hint nil nil hint w))))
       

(defun just-expand-cp-parse-hints (hints w)
  (declare (Xargs :mode :program))
  (if (atom hints)
      nil
    (cons (just-expand-cp-parse-hint (car hints) w)
          (just-expand-cp-parse-hints (cdr hints) w))))


(defevaluator expev expev-lst ((if a b c) (equal a b) (not a) (use-by-hint a)))

(def-ev-theoremp expev)


(defun hint-alist-okp (alist)
  (declare (xargs :guard t))
  (and (alistp alist)
       (pseudo-termp (cdr (assoc 'lhs alist)))
       (pseudo-termp (cdr (assoc 'rhs alist)))
       (alistp (cdr (assoc 'subst alist)))))

(defun hints-okp (hints)
  (declare (xargs :guard t))
  (or (atom hints)
      (and (consp (car hints))
           (pseudo-termp (caar hints))
           (hint-alist-okp (cdar hints))
           (hints-okp (cdr hints)))))

(defun apply-expansion (term pattern alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp pattern)
                              (hint-alist-okp alist))))
  (b* ((subst (cdr (assoc 'subst alist)))
       ((mv pat-ok &) (simple-one-way-unify pattern term subst))
       ((unless pat-ok) term)
       (lhs (cdr (assoc 'lhs alist)))
       ((mv lhs-ok subst) (simple-one-way-unify lhs term nil))
       ((unless lhs-ok) term)
       (rhs (cdr (assoc 'rhs alist))))
    (substitute-into-term rhs subst)))

(defund hint-alist-to-clause (alist)
  (declare (xargs :guard (alistp alist)))
  `((not (use-by-hint ',(cdr (assoc 'rune alist))))
    (equal ,(cdr (assoc 'lhs alist))
           ,(cdr (assoc 'rhs alist)))))

(local (defthm hint-alist-to-clause-correct
         (implies (expev-theoremp (disjoin (hint-alist-to-clause alist)))
                  (equal (expev (cdr (assoc 'lhs alist)) a)
                         (expev (cdr (assoc 'rhs alist)) a)))
         :hints(("Goal" :in-theory (enable hint-alist-to-clause
                                           use-by-hint)
                 :use ((:instance expev-falsify
                        (x (disjoin (hint-alist-to-clause alist)))
                        (a a)))))))

(defun expev-alist (x a)
  (if (atom x)
      nil
    (cons (cons (caar x) (expev (cdar x) a))
          (expev-alist (cdr x) a))))

(defthm simple-one-way-unify-of-expev
  (mv-let (ok newalist)
    (simple-one-way-unify template term alist)
    (implies (and ok
                  (pseudo-termp term)
                  (pseudo-termp template))
             (equal (expev term a)
                    (expev template
                              (expev-alist newalist a)))))
  :hints (("goal" :use ((:functional-instance simple-one-way-unify-usage
                         (unify-ev expev)
                         (unify-ev-lst expev-lst)
                         (unify-ev-alist expev-alist))))
          (and stable-under-simplificationp
               '(:in-theory (enable expev-constraint-0)))))

(defthm substitute-into-term-correct-of-expev
  (implies
   (pseudo-termp x)
   (equal (expev (substitute-into-term x subst) a)
          (expev x (expev-alist subst a))))
  :hints (("goal" :use ((:functional-instance substitute-into-term-correct
                         (unify-ev expev)
                         (unify-ev-lst expev-lst)
                         (unify-ev-alist expev-alist))))))

(defthm apply-expansion-correct
  (implies (and (expev-theoremp (disjoin (hint-alist-to-clause alist)))
                (pseudo-termp term)
                (pseudo-termp pattern)
                (hint-alist-okp alist))
           (equal (expev (apply-expansion term pattern alist) a)
                  (expev term a)))
  :hints (("goal" :do-not-induct t)))

(defthm pseudo-termp-apply-expansion
  (implies (and (pseudo-termp term)
                (hint-alist-okp alist))
           (pseudo-termp (apply-expansion term pattern alist))))

(local (in-theory (disable apply-expansion hint-alist-okp)))


(defun hint-alists-to-clauses (hints)
  (declare (xargs :guard (hints-okp hints)
                  :guard-hints(("Goal" :in-theory (enable hint-alist-okp)))))
  (if (atom hints)
      nil
    (cons (hint-alist-to-clause (cdar hints))
          (hint-alists-to-clauses (cdr hints)))))


(defun apply-expansions (term hints)
  (declare (xargs :guard (and (pseudo-termp term)
                              (hints-okp hints))))
  (if (atom hints)
      term
    (apply-expansions
     (apply-expansion term (caar hints) (cdar hints))
     (cdr hints))))

(defthm apply-expansions-correct
  (implies (and (expev-theoremp (conjoin-clauses (hint-alists-to-clauses hints)))
                (hints-okp hints)
                (pseudo-termp term))
           (equal (expev (apply-expansions term hints) a)
                  (expev term a))))

(defthm pseudo-termp-apply-expansions
  (implies (and (pseudo-termp term)
                (hints-okp hints))
           (pseudo-termp (apply-expansions term hints))))

(in-theory (disable apply-expansions hints-okp))

(mutual-recursion
 (defun term-apply-expansions (x hints)
   (declare (xargs :guard (and (pseudo-termp x)
                               (hints-okp hints))
                   :verify-guards nil))
   (if (or (variablep x)
           (fquotep x))
       x
     (let ((args (termlist-apply-expansions (fargs x) hints))
           (fn (ffn-symb x)))
       (if (flambdap fn)
           ;; NOTE: this is a little odd because it doesn't consider the lambda
           ;; substitution.  Sound, but arguably expands the wrong terms (for
           ;; some value of "wrong").
           (let* ((body (term-apply-expansions (lambda-body fn) hints)))
             (cons (make-lambda (lambda-formals fn) body)
                   args))
         (apply-expansions (cons fn args) hints)))))
 (defun termlist-apply-expansions (x hints)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (hints-okp hints))))
   (if (atom x)
       nil
     (cons (term-apply-expansions (car x) hints)
           (termlist-apply-expansions (cdr x) hints)))))

(make-flag term-apply-expansions-flg term-apply-expansions
           :flag-mapping ((term-apply-expansions . term)
                          (termlist-apply-expansions . list)))

(defthm len-of-termlist-apply-expansions
  (equal (len (termlist-apply-expansions x hints))
         (len x))
  :hints (("goal" :induct (len x)
           :expand (termlist-apply-expansions x hints))))

(defthm-term-apply-expansions-flg
  (defthm pseudo-termp-term-apply-expansions
    (implies (and (pseudo-termp x)
                  (hints-okp hints))
             (pseudo-termp (term-apply-expansions x hints)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (a b) (pseudo-termp (cons a b)))))))
    :flag term)
  (defthm pseudo-term-listp-termlist-apply-expansions
    (implies (and (pseudo-term-listp x)
                  (hints-okp hints))
             (pseudo-term-listp (termlist-apply-expansions x hints)))
    :flag list))

(mutual-recursion
 (defun term-apply-expansions-correct-ind (x hints a)
   (if (or (variablep x)
           (fquotep x))
       (list x a)
     (let ((args (termlist-apply-expansions (fargs x) hints))
           (ign (termlist-apply-expansions-correct-ind
                 (fargs x) hints a))
           (fn (ffn-symb x)))
       (declare (ignore ign))
       (if (flambdap fn)
           (term-apply-expansions-correct-ind
            (lambda-body fn) hints
            (pairlis$ (lambda-formals fn)
                      (expev-lst args a)))
         (apply-expansions (cons fn args) hints)))))
 (defun termlist-apply-expansions-correct-ind (x hints a)
   (if (atom x)
       nil
     (cons (term-apply-expansions-correct-ind (car x) hints a)
           (termlist-apply-expansions-correct-ind (cdr x) hints a)))))

(make-flag term-apply-expansions-correct-flg term-apply-expansions-correct-ind
           :flag-mapping ((term-apply-expansions-correct-ind . term)
                          (termlist-apply-expansions-correct-ind . list)))



(defthm-term-apply-expansions-correct-flg
  (defthm term-apply-expansions-correct
    (implies (and (pseudo-termp x)
                  (hints-okp hints)
                  (expev-theoremp (conjoin-clauses (hint-alists-to-clauses hints))))
             (equal (expev (term-apply-expansions x hints) a)
                    (expev x a)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable expev-constraint-0)
                   :expand ((:free (a b) (pseudo-termp (cons a b)))))))
    :flag term)
  (defthm termlist-apply-expansions-correct
    (implies (and (pseudo-term-listp x)
                  (hints-okp hints)
                  (expev-theoremp (conjoin-clauses (hint-alists-to-clauses hints))))
             (equal (expev-lst (termlist-apply-expansions x hints) a)
                    (expev-lst x a)))
    :flag list))

(verify-guards term-apply-expansions
  :hints ((and stable-under-simplificationp
               '(:expand ((:free (a b) (pseudo-termp (cons a b))))))))

(in-theory (disable term-apply-expansions))

(defthm expev-of-disjoin
  (iff (expev (disjoin x) a)
       (or-list (expev-lst x a)))
  :hints(("Goal" :in-theory (enable or-list)
          :induct (len x))))

(defun just-expand-cp (clause hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (hints-okp hints))
        (er hard? 'just-expand-cp "bad hints")
        (list clause))
       (hint-clauses (hint-alists-to-clauses hints))
       (expanded-clause
        (termlist-apply-expansions clause hints)))
    (cons expanded-clause hint-clauses)))

(defthm just-expand-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (expev-theoremp
                 (conjoin-clauses (just-expand-cp clause hints))))
           (expev (disjoin clause) a))
  :hints (("goal" :do-not-induct t
           :use ((:instance expev-falsify
                  (x (disjoin (car (just-expand-cp clause hints))))))))
  :rule-classes :clause-processor)

(defmacro just-expand (expand-lst)
  `(let ((hints (just-expand-cp-parse-hints ',expand-lst (w state))))
     `(:computed-hint-replacement
       ((use-by-computed-hint clause))
       :clause-processor (just-expand-cp clause ',hints))))

(local
 (defthm foo (implies (consp x)
                      (equal (len x) (+ 1 (len (cdr x)))))
   :hints (("goal" :do-not '(simplify preprocess eliminate-destructors))
           (just-expand ((len x)))
           '(:do-not nil))))

(defmacro just-induct-and-expand (term &key expand-others)
  `'(:computed-hint-replacement
     ((and (equal (car id) '(0))
           '(:induct ,term))
      (and (equal (car id) '(0 1))
           (just-expand (,term . ,expand-others)))
      '(:do-not nil))
     :do-not '(preprocess simplify)))


(local
 (progn
   ;; just a test

   (defun ind (x y z)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x)
         (list z y)
       (if (eq y nil)
           (cons x z)
         (ind (cdr x) (nthcdr z y) z))))

   ;; The following fails because y gets substituted out too quickly:
   ;; (defthm true-listp-ind
   ;;   (implies (true-listp z)
   ;;            (true-listp (ind x y z)))
   ;;   :hints (("goal" :in-theory (disable (:definition ind))
   ;;            :induct (ind x y z)
   ;;            :expand ((ind x y z)))))

   (defthm true-listp-ind
     (implies (true-listp z)
              (true-listp (ind x y z)))
     :hints (("goal" :in-theory (disable (:definition ind))
              :do-not-induct t)
             (just-induct-and-expand (ind x y z))))))
