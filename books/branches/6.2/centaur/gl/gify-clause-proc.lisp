
(in-package "GL")

(include-book "g-if")
(include-book "clause-processors/unify-subst" :dir :system)
(local (include-book "tools/def-functional-instance" :dir :system))
(include-book "tools/defevaluator-fast" :dir :system)

(local (defun dummy-for-g-if-ev-start () nil))


(acl2::defevaluator-fast g-if-ev g-if-ev-lst
  ((g-if-marker$inline x)
   (g-or-marker$inline x)
   (g-test-marker$inline x)
   (g-branch-marker$inline x)
   (g-hyp-marker$inline x)
   (if a b c)
   (not x)
   (gtests test hyp)
   (gtests-nonnil gtests)
   (gtests-unknown gtests)
   (acl2::return-last x y z)
   (bfr-binary-and x y)
   (bfr-binary-or x y)
   (bfr-not x)
   (hyp-fix x hyp)
   (gtests-obj gtests)
   (gobj-ite-merge c x y hyp)
   (mk-g-ite test then else)
   (mk-g-bdd-ite test then else hyp)
   (mk-g-boolean bdd)
   (cons a b)
   (binary-+ a b)
;   (generic-geval x env)
   (hide x)
   (bfr-eval x env)
   (car x)
   (equal x y))
  :namedp t)

(local (encapsulate nil
         (local (acl2::def-join-thms g-if-ev))
         (local (defun test-clause-proc (clause)
                  (list clause)))
         (local (defthm test-clause-proc-correct
                  (implies (and (pseudo-term-listp clause)
                                (alistp a)
                                (g-if-ev (conjoin-clauses (test-clause-proc
                                                           clause))
                                         a))
                           (g-if-ev (disjoin clause) a))
                  :rule-classes :clause-processor))))

(local
 (progn
   (def-ruleset! g-if-ev-constraints
     (set-difference-theories (universal-theory :here)
                              (universal-theory 'dummy-for-g-if-ev-start)))

   (acl2::def-unify g-if-ev g-if-ev-alist)

   (defthm assoc-equal-g-if-ev-alist
     (equal (cdr (assoc-equal k (g-if-ev-alist x a)))
            (g-if-ev (cdr (assoc-equal k x)) a)))

   (acl2::def-functional-instance
    g-if-ev-alist-pairlis$
    acl2::unify-ev-alist-pairlis$
    ((acl2::unify-ev g-if-ev)
     (acl2::unify-ev-lst g-if-ev-lst)
     (acl2::unify-ev-alist g-if-ev-alist)))

   (in-theory (disable g-if-ev-alist-pairlis$))))




(mutual-recursion
 (defun beta-reduce-to-fns (x stop-fns)
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         ((consp (car x))
          (let ((args (beta-reduce-to-fns-lst (cdr x) stop-fns))
                (fn (beta-reduce-to-fns (caddar x) stop-fns)))
            (acl2::substitute-into-term
             fn (pairlis$ (cadar x) args))))
         ((member (car x) stop-fns) x)
         (t (cons (car x) (beta-reduce-to-fns-lst (cdr x) stop-fns)))))

 (defun beta-reduce-to-fns-lst (x stop-fns)
   (if (atom x)
       nil
     (cons (beta-reduce-to-fns (car x) stop-fns)
           (beta-reduce-to-fns-lst (cdr x) stop-fns)))))

(local
 (progn
   (flag::make-flag beta-reduce-to-fns-flg beta-reduce-to-fns)


   (defthm-beta-reduce-to-fns-flg
     beta-reduce-to-fns-pseudo-termp-flg
     (beta-reduce-to-fns
      (implies (pseudo-termp x)
               (pseudo-termp (beta-reduce-to-fns x stop)))
      :name beta-reduce-to-fns-pseudo-termp)
     (beta-reduce-to-fns-lst
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (beta-reduce-to-fns-lst x stop)))
      :name beta-reduce-to-fns-lst-pseudo-term-listp)
     :hints (("goal" :induct (beta-reduce-to-fns-flg flag x stop))))


   (mutual-recursion
    (defun g-if-ev-term-alist-ind (x a)
      (cond ((atom x) x)
            ((eq (car x) 'quote) a)
            ((consp (car x))
             (list (g-if-ev-term-alist-ind
                    (caddar x)
                    (pairlis$ (cadar x)
                              (g-if-ev-lst (cdr x) a)))
                   (g-if-ev-term-alist-ind-lst (cdr x) a)))
            (t (g-if-ev-term-alist-ind-lst (cdr x) a))))
    (defun g-if-ev-term-alist-ind-lst (x a)
      (if (atom x)
          nil
        (cons (g-if-ev-term-alist-ind (car x) a)
              (g-if-ev-term-alist-ind-lst (cdr x) a)))))

   (flag::make-flag g-if-ev-term-alist-ind-flg g-if-ev-term-alist-ind)

   (defthm-g-if-ev-term-alist-ind-flg
     beta-reduce-to-fns-correct-flg
     (g-if-ev-term-alist-ind
      (implies (pseudo-termp x)
               (equal (g-if-ev (beta-reduce-to-fns x stop) a)
                      (g-if-ev x a)))
      :name beta-reduce-to-fns-correct)
     (g-if-ev-term-alist-ind-lst
      (implies (pseudo-term-listp x)
               (equal (g-if-ev-lst (beta-reduce-to-fns-lst x stop) a)
                      (g-if-ev-lst x a)))
      :name beta-reduce-to-fns-lst-correct)
     :hints (("goal" :induct (g-if-ev-term-alist-ind-flg flag x a)
              :in-theory (enable g-if-ev-alist-pairlis$))
             (and stable-under-simplificationp
                  '(:in-theory (enable g-if-ev-of-fncall-args)))))))


(mutual-recursion
 (defun remove-return-lasts (x)
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         ((eq (car x) 'acl2::return-last)
          (remove-return-lasts (cadddr x)))
         ((consp (car x))
          `((lambda ,(cadar x)
              ,(remove-return-lasts (caddar x)))
            . ,(remove-return-lasts-lst (cdr x))))
         (t (cons (car x) (remove-return-lasts-lst (cdr x))))))
 (defun remove-return-lasts-lst (x)
   (if (atom x)
       nil
     (cons (remove-return-lasts (car x))
           (remove-return-lasts-lst (cdr x))))))

(local
 (progn
   (flag::make-flag remove-return-lasts-flag remove-return-lasts)


   (defthm-g-if-ev-term-alist-ind-flg
     remove-return-lasts-correct-lemma
     (g-if-ev-term-alist-ind
      (equal (g-if-ev (remove-return-lasts x) a)
             (g-if-ev x a))
      :name remove-return-lasts-correct)
     (g-if-ev-term-alist-ind-lst
      (equal (g-if-ev-lst (remove-return-lasts-lst x) a)
             (g-if-ev-lst x a))
      :name remove-return-lasts-lst-correct)
     :hints (("goal" :induct (g-if-ev-term-alist-ind-flg flag x a)
              :expand ((remove-return-lasts x)))
             (and stable-under-simplificationp
                  '(:in-theory (enable g-if-ev-of-fncall-args)))))

   (defthm len-remove-return-lasts-lst
     (equal (len (remove-return-lasts-lst x))
            (len x)))

   (defthm-remove-return-lasts-flag
     remove-return-lasts-pseudo-termp-lemma
     (remove-return-lasts
      (implies (pseudo-termp x)
               (pseudo-termp (remove-return-lasts x)))
      :name remove-return-lasts-pseudo-termp)
     (remove-return-lasts-lst
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (remove-return-lasts-lst x)))
      :name remove-return-lasts-lst-pseudo-term-listp)
     :hints (("goal" :induct (remove-return-lasts-flag flag x))))))

(make-event
 (b* (((er trans)
       (acl2::translate '(g-or test-term else-term) :stobjs-out nil nil
                 'g-or-pattern (w state) state))
      (term (beta-reduce-to-fns trans '(g-branch-marker$inline g-test-marker$inline)))
      (term (remove-return-lasts term)))
   (value
    `(defconst *g-or-pattern*
       ',term))))

(make-event
 (b* (((er trans)
       (acl2::translate '(g-if test-term then-term else-term) :stobjs-out nil nil
                        'g-if-pattern (w state) state))
      (term (beta-reduce-to-fns trans '(g-branch-marker$inline g-test-marker$inline)))
      (term (remove-return-lasts term)))
   (value
    `(defconst *g-if-pattern*
       ',term))))


(local (include-book "gtype-thms"))


(encapsulate
  (((geval-for-meta * *) => *))
  (local (defun geval-for-meta (x env)
           (generic-geval x env)))

  (local (in-theory (disable generic-geval)))

  (defthm geval-for-meta-nil
    (equal (geval-for-meta nil env) nil)
    :hints(("Goal" :in-theory (enable generic-geval))))

  (defthm geval-for-meta-gobj-ite-merge-correct
    (implies (bfr-eval (double-rewrite hyp) (car env))
             (equal (geval-for-meta (gobj-ite-merge c x y hyp)
                                    env)
                    (if (bfr-eval c (car env))
                        (geval-for-meta x env)
                      (geval-for-meta y env)))))

  (defthm geval-for-meta-gtests-nonnil-correct
    (implies (and (not (bfr-eval (gtests-unknown (gtests x hyp))
                                 (car env)))
                  (bfr-eval (double-rewrite hyp) (car env)))
             (equal (bfr-eval (gtests-nonnil (gtests x hyp))
                              (car env))
                    (if (geval-for-meta x env) t nil))))

  (defthm geval-for-meta-gtests-obj-correct
    (implies (and (bfr-eval (gtests-unknown (gtests x hyp))
                            (car env))
                  (bfr-eval (double-rewrite hyp) (car env)))
             (iff (geval-for-meta (gtests-obj (gtests x hyp))
                                 env)
                  (geval-for-meta x env))))

  (defthm geval-for-meta-mk-g-boolean-correct
    (equal (geval-for-meta (mk-g-boolean x) env)
           (bfr-eval (double-rewrite x) (car env))))

  (defthm geval-for-meta-mk-g-ite-correct
    (equal (geval-for-meta (mk-g-ite c x y) b)
           (if (geval-for-meta c b)
               (geval-for-meta x b)
             (geval-for-meta y b)))))

         



(local
 (progn
   ;; (table acl2::evisc-table `',*g-or-pattern* "*g-or-pattern*")
   ;; (table acl2::evisc-table `',*g-if-pattern* "*g-if-pattern*")



   (encapsulate nil
     (local (bfr-reasoning-mode t))
     (local (add-bfr-pat (gtests-nonnil . &)))
     (local (add-bfr-pat (gtests-unknown . &)))
     (local (add-bfr-pat (bfr-fix . &)))
     (local (in-theory (disable bfr-eval-booleanp
                                equal-of-booleans-rewrite)))
 


     (defthm geval-for-meta-mk-g-bdd-ite-correct
       (implies (bfr-eval (double-rewrite hyp) (car env))
                (equal (geval-for-meta (mk-g-bdd-ite bdd then else hyp) env)
                       (if (bfr-eval bdd (car env))
                           (geval-for-meta then env)
                         (geval-for-meta else env))))
       :hints(("Goal" :in-theory (enable true-under-hyp
                                         false-under-hyp
                                         mk-g-bdd-ite)
               :do-not-induct t)
              (bfr-reasoning)))

     (defthm geval-for-meta-of-g-or-pattern
       (implies (bfr-eval (cdr (assoc-equal 'hyp alist)) (car env))
                (equal (geval-for-meta (g-if-ev *g-or-pattern* alist) env)
                       (or (geval-for-meta (cdr (assoc-equal 'test-term alist)) env)
                           (geval-for-meta (cdr (assoc-equal 'else-term alist)) env))))
       :hints (("goal" :do-not-induct t
                :expand ((:free (x) (hide x)))
                :in-theory (e/d* ( g-test-marker g-branch-marker
                                          g-or-marker g-hyp-marker)
                                 (default-car default-cdr assoc-equal
                                  (:rules-of-class :type-prescription :here))))))

     (defthm geval-for-meta-of-g-if-pattern
       (implies (bfr-eval (cdr (assoc-equal 'hyp alist)) (car env))
                (equal (geval-for-meta (g-if-ev *g-if-pattern* alist) env)
                       (if (geval-for-meta (cdr (assoc-equal 'test-term alist)) env)
                           (geval-for-meta (cdr (assoc-equal 'then-term alist)) env)
                         (geval-for-meta (cdr (assoc-equal 'else-term alist)) env))))
       :hints (("goal" :do-not-induct t
                :expand ((:free (x) (hide x)))
                :in-theory (e/d* ( g-test-marker g-branch-marker
                                          g-if-marker g-hyp-marker)
                                 (default-car default-cdr assoc-equal
                                  (:rules-of-class :type-prescription :here)))))))

   ;; (defthm gobjectp-of-g-or-pattern
   ;;   (gobjectp (g-if-ev *g-or-pattern* alist))
   ;;   :hints (("goal" :do-not-induct t
   ;;              :expand ((:free (x) (hide x)))
   ;;            :in-theory (e/d* ( g-test-marker g-branch-marker
   ;;                                      g-or-marker g-hyp-marker)
   ;;                             (default-car default-cdr assoc-equal
   ;;                              (:rules-of-class :type-prescription :here))))))

   ;; (defthm gobjectp-of-g-if-pattern
   ;;   (gobjectp (g-if-ev *g-if-pattern* alist))
   ;;   :hints (("goal" :do-not-induct t
   ;;            :expand ((:free (x) (hide x)))
   ;;            :in-theory (e/d* ( g-test-marker g-branch-marker
   ;;                                      g-if-marker g-hyp-marker)
   ;;                             (default-car default-cdr assoc-equal
   ;;                              (:rules-of-class :type-prescription :here))))))




   (in-theory (disable pseudo-termp acl2::simple-one-way-unify acl2::substitute-into-term
                       assoc-equal))




   ;; (defthm gobjectp-of-g-if-term-subst
   ;;   (b* (((mv ok &)
   ;;         (acl2::simple-one-way-unify *g-if-pattern* term nil)))
   ;;     (implies (and (pseudo-termp term)
   ;;                   ok)
   ;;              (gobjectp (g-if-ev term al))))
   ;;   :hints (("goal" :in-theory
   ;;            (disable* (:ruleset g-if-ev-constraints)
   ;;                      gobjectp-def))))




   ;; (defthm gobjectp-of-g-or-term-subst
   ;;   (b* (((mv ok &)
   ;;         (acl2::simple-one-way-unify *g-or-pattern* term nil)))
   ;;     (implies (and (pseudo-termp term)
   ;;                   ok)
   ;;              (gobjectp (g-if-ev term al))))
   ;;   :hints (("goal" :in-theory
   ;;            (disable* (:ruleset g-if-ev-constraints)
   ;;                      gobjectp-def))))
   ))



(defthm geval-for-meta-of-g-if-term-subst
  (b* (((mv ok subst)
        (acl2::simple-one-way-unify *g-if-pattern* term nil))
       (test-res (g-if-ev (cdr (assoc-equal 'test-term subst)) al))
       (then-res (g-if-ev (cdr (assoc-equal 'then-term subst)) al))
       (else-res (g-if-ev (cdr (assoc-equal 'else-term subst)) al))
       (hyp-res  (g-if-ev (cdr (assoc-equal 'hyp subst)) al)))
    (implies (and (pseudo-termp term)
                  ok
                  (bfr-eval hyp-res (car env)))
             (equal (geval-for-meta (g-if-ev term al) env)
                    (if (geval-for-meta test-res env)
                        (geval-for-meta then-res env)
                      (geval-for-meta else-res env)))))
  :hints (("goal" :in-theory
           (disable* (:ruleset g-if-ev-constraints)))))


(defthm geval-for-meta-of-g-or-term-subst
  (b* (((mv ok subst)
        (acl2::simple-one-way-unify *g-or-pattern* term nil))
       (test-res (g-if-ev (cdr (assoc-equal 'test-term subst)) al))
       (else-res (g-if-ev (cdr (assoc-equal 'else-term subst)) al))
       (hyp-res  (g-if-ev (cdr (assoc-equal 'hyp subst)) al)))
    (implies (and (pseudo-termp term)
                  ok
                  (bfr-eval hyp-res (car env)))
             (equal (geval-for-meta (g-if-ev term al) env)
                    (or (geval-for-meta test-res env)
                        (geval-for-meta else-res env)))))
  :hints (("goal" :in-theory
           (disable* (:ruleset g-if-ev-constraints)))))



(defun g-if-simp (x dummy)
  (declare (ignore dummy))
  (mv t (beta-reduce-to-fns
         (remove-return-lasts x)
         '(g-test-marker$inline g-branch-marker$inline g-hyp-marker$inline))))

;; Trick: When the rewriter attempts to apply this rule, the extra
;; dummy arg to g-if-simp forces it to match it as a free variable, so
;; the rule will only be applied if there is a hyp matching
;; (mv-nth 0 (g-if-simp x dummy)).  Otherwise at every occurrence of
;; (g-if-ev x a), this rule would backchain on (mv-nth 0 (g-if-simp
;; x)) which might be quite expensive.
(defthm g-if-simp-correct
  (mv-let (ok simp)
    (g-if-simp x dummy)
    (implies (and ok (pseudo-termp x))
             (equal (g-if-ev x a)
                    (g-if-ev simp a)))))

(defthm pseudo-termps-g-if-simp-correct
  (mv-let (ok term)
    (g-if-simp x dummy)
    (declare (ignore ok))
    (implies (pseudo-termp x)
             (pseudo-termp term)))
  :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)
          :do-not-induct t)))


(in-theory (disable g-if-simp))




(local (acl2::def-join-thms g-if-ev))







;; (defun g-or-gobjectp-extract (x dummy)
;;   (declare (ignore dummy))
;;   (case-match x
;;     (('g-or-marker ('gobjectp ('hide term . &) . &) . &)
;;      (mv t term))
;;     (& (mv nil nil))))

;; (local
;;  (progn
;;    (defthm g-or-gobjectp-extract-correct
;;      (mv-let (ok term)
;;        (g-or-gobjectp-extract x dummy)
;;        (implies ok
;;                 (equal (g-if-ev x a)
;;                        (gobjectp (g-if-ev term a)))))
;;      :hints(("Goal" :in-theory (enable g-or-marker)
;;              :expand ((:free (x) (hide x))))))

;;    (defthm pseudo-termps-g-or-gobjectp-extract-correct
;;      (mv-let (ok term)
;;        (g-or-gobjectp-extract x dummy)
;;        (declare (ignore ok))
;;        (implies (pseudo-termp x)
;;                 (pseudo-termp term)))
;;      :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)
;;              :do-not-induct t)))))

;; (in-theory (disable g-or-gobjectp-extract))
  

;; (defun g-or-gobjectp-meta-hyp (x)
;;   (b* (((mv ok term) (g-or-gobjectp-extract x 'extract))
;;        ((unless ok) ''nil)
;;        ((mv ok term) (g-if-simp term 'simp))
;;        ((unless ok) ''nil)
;;        ((mv ok &)
;;         (acl2::simple-one-way-unify *g-or-pattern* term nil))
;;        ((unless ok) ''nil))
;;     ''t))

;; ;;        (test-term (cdr (assoc-equal 'test-term subst)))
;; ;;        (else-term (cdr (assoc-equal 'else-term subst)))
;; ;;        (hyp-term  (cdr (assoc-equal 'hyp subst))))
;; ;;     (acl2::conjoin2 `(gobjectp ,test-term)
;; ;;               (acl2::conjoin2 `(gobjectp ,else-term)
;; ;;                         `(bfr-p ,hyp-term)))))


;; (defun g-or-gobjectp-meta (x)
;;   (declare (ignore x))''t)


;; (defthm g-or-gobjectp-meta-correct
;;   (implies (and (pseudo-termp x)
;;                 (g-if-ev (g-or-gobjectp-meta-hyp x) a))
;;            (equal (g-if-ev x a)
;;                   (g-if-ev (g-or-gobjectp-meta x) a)))
;;   :hints(("Goal" :expand ((:free (x) (hide x)))
;;           :in-theory (disable gobjectp-def)))
;;   :rule-classes ((:meta :trigger-fns (g-or-marker))))









;; (defun g-if-gobjectp-extract (x dummy)
;;   (declare (ignore dummy))
;;   (case-match x
;;     (('g-if-marker ('gobjectp ('hide term . &) . &) . &)
;;      (mv t term))
;;     (& (mv nil nil))))

;; (local
;;  (progn
;;    (defthm g-if-gobjectp-extract-correct
;;      (mv-let (ok term)
;;        (g-if-gobjectp-extract x dummy)
;;        (implies ok
;;                 (equal (g-if-ev x a)
;;                        (gobjectp (g-if-ev term a)))))
;;      :hints(("Goal" :in-theory (enable g-if-marker)
;;              :expand ((:free (x) (hide x))))))

;;    (defthm pseudo-termps-g-if-gobjectp-extract-correct
;;      (mv-let (ok term)
;;        (g-if-gobjectp-extract x dummy)
;;        (declare (ignore ok))
;;        (implies (pseudo-termp x)
;;                 (pseudo-termp term)))
;;      :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)
;;              :do-not-induct t)))))

;; (in-theory (disable g-if-gobjectp-extract))
  

;; (defun g-if-gobjectp-meta-hyp (x)
;;   (b* (((mv ok term) (g-if-gobjectp-extract x 'extract))
;;        ((unless ok) ''nil)
;;        ((mv ok term) (g-if-simp term 'simp))
;;        ((unless ok) ''nil)
;;        ((mv ok &)
;;         (acl2::simple-one-way-unify *g-if-pattern* term nil))
;;        ((unless ok) ''nil))
;;     ''t))

;; (defun g-if-gobjectp-meta (x)
;;   (declare (ignore x))
;;   ''t)


;; (defthm g-if-gobjectp-meta-correct
;;   (implies (and (pseudo-termp x)
;;                 (g-if-ev (g-if-gobjectp-meta-hyp x) a))
;;            (equal (g-if-ev x a)
;;                   (g-if-ev (g-if-gobjectp-meta x) a)))
;;   :hints(("Goal" :expand ((:free (x) (hide x)))
;;           :in-theory (disable gobjectp-def)))
;;   :rule-classes ((:meta :trigger-fns (g-if-marker))))




(defconst *g-if-and-or-meta-template*
  '(encapsulate
     nil
     (local (defun before-g-if-or-meta-template-evaluator () nil))
     (acl2::defevaluator-fast
      eval eval-lst
      ((g-if-marker$inline x)
       (g-or-marker$inline x)
       (g-test-marker$inline x)
       (g-branch-marker$inline x)
       (g-hyp-marker$inline x)
       (if a b c)
       (not x)
       (gtests test hyp)
       (gtests-nonnil gtests)
       (gtests-unknown gtests)
       (acl2::return-last x y z)
       (bfr-binary-and x y)
       (bfr-binary-or x y)
       (bfr-not x)
       (hyp-fix x hyp)
       (gtests-obj gtests)
       (gobj-ite-merge c x y hyp)
       (mk-g-ite test then else)
       (mk-g-bdd-ite test then else hyp)
       (mk-g-boolean bdd)
       (hide x)
       (cons a b)
       (binary-+ a b)
       (bfr-eval x env)
       (car x)
       (equal x y)
       (geval x env))
      :namedp t)

     (local (def-ruleset! g-if-or-meta-evaluator-constraints
              (set-difference-theories
               (current-theory :here)
               (current-theory 'before-g-if-or-meta-template-evaluator))))

     (local (in-theory (e/d* ((:ruleset g-if-or-meta-evaluator-constraints)
                              car-cons cdr-cons acl2::disjoin2
                              acl2::conjoin2
                              append (:theory minimal-theory)
                              car-cdr-elim
                              pseudo-termps-g-if-simp-correct
                              g-if-simp-correct)
                             (mv-nth))))

     (local (acl2::def-join-thms eval))

     (local
      (defthm g-if-simp-correct-meta
        (mv-let (ok simp)
          (g-if-simp x dummy)
          (implies (and ok (pseudo-termp x))
                   (equal (eval x a)
                          (eval simp a))))
        :hints (("goal"
                 :by (:functional-instance
                      g-if-simp-correct
                      (g-if-ev eval)
                      (g-if-ev-lst eval-lst)))
                (and stable-under-simplificationp
                     '(:in-theory
                       (enable eval-of-fncall-args))))))

     (local
      (defthm geval-of-g-if-term-subst
        (b* (((mv ok subst)
              (acl2::simple-one-way-unify *g-if-pattern* term nil))
             (test-res (eval (cdr (assoc-equal 'test-term subst)) al))
             (then-res (eval (cdr (assoc-equal 'then-term subst)) al))
             (else-res (eval (cdr (assoc-equal 'else-term subst)) al))
             (hyp-res  (eval (cdr (assoc-equal 'hyp subst)) al)))
          (implies (and (pseudo-termp term)
                        ok
                        (bfr-eval hyp-res (car env)))
                   (equal (geval (eval term al) env)
                          (if (geval test-res env)
                              (geval then-res env)
                            (geval else-res env)))))
        :hints (("goal"
                 :in-theory (disable geval-for-meta-gtests-nonnil-correct)
                 :by (:functional-instance
                      geval-for-meta-of-g-if-term-subst
                      (geval-for-meta geval)
                      (g-if-ev eval)
                      (g-if-ev-lst eval-lst))))))
     

     (local
      (defthm geval-of-g-or-term-subst
        (b* (((mv ok subst)
              (acl2::simple-one-way-unify *g-or-pattern* term nil))
             (test-res (eval (cdr (assoc-equal 'test-term subst)) al))
             (else-res (eval (cdr (assoc-equal 'else-term subst)) al))
             (hyp-res  (eval (cdr (assoc-equal 'hyp subst)) al)))
          (implies (and (pseudo-termp term)
                        ok
                        (bfr-eval hyp-res (car env)))
                   (equal (geval (eval term al) env)
                          (or (geval test-res env)
                              (geval else-res env)))))
        :hints (("goal"
                 :by (:functional-instance
                      geval-for-meta-of-g-or-term-subst
                      (geval-for-meta geval)
                      (g-if-ev eval)
                      (g-if-ev-lst eval-lst))))))




     (defun g-or-geval-extract (x dummy)
       (declare (ignore dummy))
       (case-match x
         (('g-or-marker$inline ('geval ('hide term . &) env . &) . &)
          (mv t term env))
         (& (mv nil nil nil))))

     (local
      (progn
        (defthm g-or-geval-extract-correct
          (mv-let (ok term env)
            (g-or-geval-extract x dummy)
            (implies ok
                     (equal (eval x a)
                            (geval (eval term a)
                                   (eval env a)))))
          :hints(("Goal" :in-theory (enable g-or-marker)
                  :expand ((:free (x) (hide x))))))

        (defthm pseudo-termps-g-or-geval-extract-correct
          (mv-let (ok term env)
            (g-or-geval-extract x dummy)
            (declare (ignore ok))
            (implies (pseudo-termp x)
                     (and (pseudo-termp term)
                          (pseudo-termp env))))
          :hints(("Goal" :expand ((pseudo-termp x)
                                  (pseudo-termp nil)
                                  (pseudo-term-listp (cdr x))
                                  (pseudo-termp (cadr x))
                                  (pseudo-term-listp (cdadr x))
                                  (pseudo-termp (cadadr x))
                                  (pseudo-term-listp (cdr (cadadr x)))
                                  (pseudo-term-listp (cddadr x)))
                  :in-theory (e/d** (minimal-theory
                                     g-or-geval-extract
                                     mv-nth-cons-meta)
                                    (mv-nth))
                  :do-not-induct t)))))

     (in-theory (disable g-or-geval-extract))


     (defun g-or-geval-meta-subterms (x dummy)
       (declare (ignore dummy))
       (b* (((mv ok term env)
             (g-or-geval-extract x 'extract))
            ((unless ok) (mv nil nil nil nil nil))
            ((mv ok term) (g-if-simp term 'simp))
            ((unless ok) (mv nil nil nil nil nil))
            ((mv ok subst)
             (acl2::simple-one-way-unify *g-or-pattern* term nil))
            ((unless ok) (mv nil nil nil nil nil))
            (test-term (cdr (assoc-equal 'test-term subst)))
            (else-term (cdr (assoc-equal 'else-term subst)))
            (hyp-term (cdr (assoc-equal 'hyp subst))))
         (mv t hyp-term test-term else-term env)))

     (defun g-or-geval-meta-subterms-wrapper (x)
       (declare (xargs :guard t))
       (ec-call (g-or-geval-meta-subterms x 'subterms)))
    

     (defthm g-or-geval-meta-subterms-correct
       (mv-let (ok hyp test else env)
         (g-or-geval-meta-subterms x dummy)
         (implies (and ok
                       (pseudo-termp x)
                       (bfr-eval (eval hyp a)
                                 (car (eval env a))))
                  (equal (eval x a)
                         (or (geval (eval test a)
                                    (eval env a))
                             (geval (eval else a)
                                    (eval env a))))))
       :hints (("goal" :expand ((:free (x) (hide x)))
                :in-theory (disable geval))))

     (in-theory (disable g-or-geval-meta-subterms))

     (memoize 'g-or-geval-meta-subterms-wrapper :condition nil)
             
     (defun g-or-geval-meta-hyp (x)
       (b* (((mv ok hyp & & env)
             (g-or-geval-meta-subterms-wrapper x))
            ((unless ok) ''nil)
;;             (- (clear-memoize-table
;;                 'g-or-geval-meta-subterms-wrapper))
            )
         `(bfr-eval ,hyp (car ,env))))

     (defun g-or-geval-meta-res (x)
       (b* (;; (- (clear-memoize-table
;;                 'g-or-geval-meta-subterms-wrapper))
            ((mv ok & test else env)
             (g-or-geval-meta-subterms-wrapper x))
            ((unless ok) x))
         `(if (geval ,test ,env)
              (geval ,test ,env)
            (geval ,else ,env))))


     (defthm g-or-geval-meta-correct
       (implies (and (pseudo-termp x)
                     (eval
                      (g-or-geval-meta-hyp x) a))
                (equal (eval x a)
                       (eval (g-or-geval-meta-res x)
                             a)))
       :hints (("goal" :expand ((:free (x) (hide x)))
                :in-theory (disable geval)))
       :rule-classes ((:meta :trigger-fns (g-or-marker))))


     (defun g-if-geval-extract (x dummy)
       (declare (ignore dummy))
       (case-match x
         (('g-if-marker$inline ('geval ('hide term . &) env . &) . &)
          (mv t term env))
         (& (mv nil nil nil))))

     (local
      (progn
        (defthm g-if-geval-extract-correct
          (mv-let (ok term env)
            (g-if-geval-extract x dummy)
            (implies ok
                     (equal (eval x a)
                            (geval (eval term a)
                                   (eval env a)))))
          :hints(("Goal" :in-theory (enable g-if-marker)
                  :expand ((:free (x) (hide x))))))

        (defthm pseudo-termps-g-if-geval-extract-correct
          (mv-let (ok term env)
            (g-if-geval-extract x dummy)
            (declare (ignore ok))
            (implies (pseudo-termp x)
                     (and (pseudo-termp term)
                          (pseudo-termp env))))
          :hints(("Goal" :expand ((pseudo-termp x)
                                  (pseudo-termp nil)
                                  (pseudo-term-listp (cdr x))
                                  (pseudo-termp (cadr x))
                                  (pseudo-term-listp (cdadr x))
                                  (pseudo-termp (cadadr x))
                                  (pseudo-term-listp (cdr (cadadr x)))
                                  (pseudo-term-listp (cddadr x)))
                  :in-theory (e/d** (minimal-theory
                                     g-if-geval-extract
                                     mv-nth-cons-meta)
                                    (mv-nth))
                  :do-not-induct t)))))

     (in-theory (disable g-if-geval-extract))
  

     (defun g-if-geval-meta-subterms (x dummy)
       (declare (ignore dummy))
       (b* (((mv ok term env)
             (g-if-geval-extract x 'extract))
            ((unless ok) (mv nil nil nil nil nil nil))
            ((mv ok term) (g-if-simp term 'simp))
            ((unless ok) (mv nil nil nil nil nil nil))
            ((mv ok subst)
             (acl2::simple-one-way-unify *g-if-pattern* term nil))
            ((unless ok) (mv nil nil nil nil nil nil))
            (test-term (cdr (assoc-equal 'test-term subst)))
            (then-term (cdr (assoc-equal 'then-term subst)))
            (else-term (cdr (assoc-equal 'else-term subst)))
            (hyp-term (cdr (assoc-equal 'hyp subst))))
         (mv t hyp-term test-term then-term else-term env)))

     (defun g-if-geval-meta-subterms-wrapper (x)
       (declare (xargs :guard t))
       (ec-call (g-if-geval-meta-subterms x 'subterms)))
    

     (defthm g-if-geval-meta-subterms-correct
       (mv-let (ok hyp test then else env)
         (g-if-geval-meta-subterms x dummy)
         (implies (and ok
                       (pseudo-termp x)
                       (bfr-eval (eval hyp a)
                                 (car (eval env a))))
                  (equal (eval x a)
                         (if (geval (eval test a)
                                    (eval env a))
                             (geval (eval then a)
                                    (eval env a))
                           (geval (eval else a)
                                  (eval env a))))))
       :hints (("goal" :expand ((:free (x) (hide x)))
                :in-theory (disable geval))))

     (in-theory (disable g-if-geval-meta-subterms))

     (memoize 'g-if-geval-meta-subterms-wrapper :condition nil)
             
     (defun g-if-geval-meta-hyp (x)
       (b* (((mv ok hyp & & & env)
             (g-if-geval-meta-subterms-wrapper x))
            ((unless ok) ''nil)
;;             (- (clear-memoize-table
;;                 'g-if-geval-meta-subterms-wrapper))
            )
         `(bfr-eval ,hyp (car ,env))))

     (defun g-if-geval-meta-res (x)
       (b* (;; (- (clear-memoize-table
;;                 'g-if-geval-meta-subterms-wrapper))
            ((mv ok & test then else env)
             (g-if-geval-meta-subterms-wrapper x))
            ((unless ok) x))
         `(if (geval ,test ,env)
              (geval ,then ,env)
            (geval ,else ,env))))


     (defthm g-if-geval-meta-correct
       (implies (and (pseudo-termp x)
                     (eval
                      (g-if-geval-meta-hyp x) a))
                (equal (eval x a)
                       (eval (g-if-geval-meta-res x)
                             a)))
       :hints (("goal" :expand ((:free (x) (hide x)))
                :in-theory (disable geval)))
       :rule-classes ((:meta :trigger-fns (g-if-marker))))


     (defthm geval-g-if-marker
       (equal (geval (g-if-marker x) env)
              (g-if-marker (geval (hide (g-if-marker x)) env)))
       :hints(("Goal" :in-theory (e/d (g-if-marker) (geval))
               :expand ((:free (x) (hide x))))))

     (defthm geval-g-or-marker
       (equal (geval (g-or-marker x) env)
              (g-or-marker (geval (hide (g-or-marker x)) env)))
       :hints(("Goal" :in-theory (e/d (g-or-marker) (geval))
               :expand ((:free (x) (hide x))))))

     (defthm geval-g-test-marker
       (equal (geval (g-test-marker x) env)
              (geval x env))
       :hints(("Goal" :in-theory (e/d (g-test-marker) (geval)))))

     (defthm geval-g-branch-marker
       (equal (geval (g-branch-marker x) env)
              (geval x env))
       :hints(("Goal" :in-theory (e/d (g-branch-marker) (geval)))))))

(defun def-geval-name-bindings (names geval)
  (if (atom names)
      nil
    (cons (cons (car names)
                (intern-in-package-of-symbol
                 (concatenate 'string
                              (symbol-name (car names)) "-"
                              (symbol-name geval))
                 geval))
          (def-geval-name-bindings (cdr names) geval))))

(defun def-geval-meta-fn (geval eval eval-lst)
  (declare (xargs :mode :program))
  (b* ((subst `((geval . ,geval)
                (eval . ,eval)
                (eval-lst . ,eval-lst)
                (eval-of-fncall-args
                 . ,(intern-in-package-of-symbol
                     (concatenate
                      'string (symbol-name eval) "-OF-FNCALL-ARGS")
                     eval))
                . ,(def-geval-name-bindings
                     '(g-or-geval-extract
                       g-or-geval-meta-subterms
                       g-or-geval-meta-subterms-wrapper
                       g-or-geval-meta-subterms-correct
                       g-or-geval-meta-hyp
                       g-or-geval-meta-res
                       g-or-geval-meta-correct
                       g-if-geval-extract
                       g-if-geval-meta-subterms
                       g-if-geval-meta-subterms-wrapper
                       g-if-geval-meta-subterms-correct
                       g-if-geval-meta-hyp
                       g-if-geval-meta-res
                       g-if-geval-meta-correct
                       geval-g-if-marker
                       geval-g-or-marker
                       geval-g-test-marker
                       geval-g-branch-marker)
                     geval))))
    (sublis subst *g-if-and-or-meta-template*)))

(defmacro def-geval-meta (geval eval eval-lst)
  (def-geval-meta-fn geval eval eval-lst))

;; test.
(local (def-geval-meta generic-geval generic-gify-ev generic-gify-ev-lst))
                                  












;; ;; We'll deal here with three kinds of "predicates", which we'll attempt to
;; ;; resolve to T,
;; ;; (gobjectp x)
;; ;; (bfr-p x)
;; ;; (bfr-eval x (car env))
;; ;; and (equal (generic-geval x env) y).


;; ;; Sort the hyps into the above categories.
;; (defun gify-sort-hyps (hyps)
;;   (if (atom hyps)
;;       (mv nil nil nil nil)
;;     (b* ((hyp (car hyps))
;;          ((mv gobj gnorm bfr-eval eval-g)
;;           (gify-sort-hyps (cdr hyps))))
;;       (case-match hyp
;;         (('gobjectp x)
;;          (mv (cons x gobj) gnorm bfr-eval eval-g))
;;         (('bfr-p x)
;;          (mv gobj (cons x gnorm) bfr-eval eval-g))
;;         (('bfr-eval x '(car env))
;;          (mv gobj gnorm (cons x bfr-eval) eval-g))
;;         (('equal ('generic-geval x 'env) y)
;;          (mv gobj gnorm bfr-eval (cons (cons x y) eval-g)))
;;         (& (mv gobj gnorm bfr-eval eval-g))))))




;; (mutual-recursion
;;  (defun gify-reduce-gobjectp (x gobj-assms gnorm-assms obligs world)
;;    (if (member-equal x gobj-assms)
;;        (mv nil gobj-assms gnorm-assms obligs)
;;      (if (atom x)
;;          (mv "unknown var" gobj-assms gnorm-assms obligs)
;;        (case-match x
;;         (('quote obj . &)
;;          (if (gobjectp obj)
;;              ;; Faster to just run every time than add to assms and check membership?
;;              (mv nil gobj-assms gnorm-assms obligs)
;;            (mv (acl2::msg "not gobjectp: ~x0~%" obj)
;;                gobj-assms gnorm-assms obligs)))
;;         (('gtests-obj ('gtests test hyp . &) . &)
;;          (b* (((mv erp gobj-assms gnorm-assms obligs)
;;                (gify-reduce-bfr-p hyp gobj-assms gnorm-assms obligs world))
;;               ((when erp) (mv erp gobj-assms gnorm-assms obligs)))
;;            (gify-reduce-gobjectp test gobj-assms gnorm-assms obligs world)))
;;         (('g-if-marker . &)
;;          (mv-let (ok subst)
;;            (g-if-subst x)
;;            (if ok
;;                (let ((test (cdr (assoc-equal 'test-term subst)))
;;                      (then (cdr (assoc-equal 'then-term subst)))
;;                      (else (cdr (assoc-equal 'else-term subst)))
;;                      (hyp (cdr (assoc-equal 'hyp subst))))
;;                  (b* (((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-bfr-p hyp gobj-assms gnorm-assms obligs world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs))
;;                       ((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-gobjectp test gobj-assms gnorm-assms obligs
;;                                              world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs))
;;                       ((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-gobjectp then gobj-assms gnorm-assms obligs
;;                                              world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs))
;;                       ((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-gobjectp else gobj-assms gnorm-assms obligs
;;                                              world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs)))
;;                    (mv erp (cons x gobj-assms) gnorm-assms obligs)))
;;              (mv "bad if" gobj-assms gnorm-assms obligs))))
;;         (('g-or-marker . &)
;;          (mv-let (ok subst)
;;            (g-or-subst x)
;;            (if ok
;;                (let ((test (cdr (assoc-equal 'test-term subst)))
;;                      (else (cdr (assoc-equal 'else-term subst)))
;;                      (hyp (cdr (assoc-equal 'hyp subst))))
;;                  (b* (((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-bfr-p hyp gobj-assms gnorm-assms obligs world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs))
;;                       ((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-gobjectp test gobj-assms gnorm-assms obligs
;;                                              world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs))
;;                       ((mv erp gobj-assms gnorm-assms obligs)
;;                        (gify-reduce-gobjectp else gobj-assms gnorm-assms
;;                                              obligs world))
;;                       ((when erp) (mv erp gobj-assms gnorm-assms obligs)))
;;                    (mv erp (cons x gobj-assms) gnorm-assms obligs)))
;;              (mv "bad or" gobj-assms gnorm-assms obligs))))
;;         (&
         
         
              
        



;; (defun gify-clause-proc (clause hints)
;;   (b* ((hyps (butlast clause 1))
;;        (concl (car (last clause)))
;;        ((mv gobj-assms gnorm-assms bfr-eval-assms eval-g-assms)
;;         (gify-sort-hyps hyps)))
;;     (case-match concl
;;       (('equal ('generic-geval x 'env) y)
;;        (b* ((mv errp res obligs)
;;             (gify-reduce-generic-geval
;;              x gobj-assms gnorm-assms bfr-eval-assms eval-g-assms nil))
;;          (if (equal res y)
;;              (obligs-to-clauses obligs)
;;            (list clause))))
;;       (('gobjectp x)
;;        (mv-let (errp obligs)
;;          (gify-reduce-gobjectp x gobj-assms gnorm-assms nil)
;;          (if errp
;;              (list clause)
;;            (obligs-to-clauses obligs))))
;;       (& (list clause)))))




