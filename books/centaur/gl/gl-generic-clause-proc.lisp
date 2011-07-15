
(in-package "GL")


(include-book "param")
(include-book "g-if")
(include-book "gify")
(include-book "bfr-sat")
(include-book "glcp-templates")

(include-book "misc/untranslate-patterns" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/decomp-hint" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)

(local (include-book "general-object-thms"))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (include-book "tools/with-quoted-forms" :dir :system))
(local (include-book "hyp-fix-logic"))
(local (in-theory (disable* gobjectp-def
                            sets::double-containment)))




(defun gl-cp-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable gl-cp-hint (:type-prescription gl-cp-hint) (gl-cp-hint)))

(defmacro glcp-value (res)
  `(mv nil obligs ,res state))

;; (defmacro glcp-er-let* (alist body)
;;   (declare (xargs :guard (and (acl2::doubleton-list-p alist)
;;                               (symbol-alistp alist))))
;;   (if (null alist)
;;       `(check-vars-not-free
;;         (glcp-er-let*-use-nowhere-else)
;;         ,body)
;;     `(mv-let (glcp-er-let*-use-nowhere-else
;;               obligs ,(caar alist) state)
;;        ,(cadar alist)
;;        (if glcp-er-let*-use-nowhere-else
;;            (mv glcp-er-let*-use-nowhere-else
;;                obligs ,(caar alist) state)
;;          (glcp-er-let* ,(cdr alist) ,body)))))

(defmacro patbind-glcp-er (args bindings expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(b* (((mv patbind-glcp-er-error obligs ,(car args) state)
         ,(car bindings))
        ((when patbind-glcp-er-error)
         (mv patbind-glcp-er-error obligs nil state)))
     (check-vars-not-free
      (patbind-glcp-er-error) ,expr)))

(verify-termination acl2::evisc-tuple)
(verify-guards acl2::evisc-tuple)

(defmacro glcp-if (test then else)
  `(b* (((glcp-er test) ,test)
        (gtests (gtests test hyp))
        (then-hyp (hf (bfr-or (gtests-unknown gtests)
                               (gtests-nonnil gtests))))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        ((glcp-er then)
         (if then-hyp
             (let ((hyp (bfr-and hyp then-hyp)))
               (declare (ignorable hyp))
               ,then)
           (glcp-value nil)))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (declare (ignorable hyp))
               ,else)
           (glcp-value nil)))
        (merge (gobj-ite-merge (gtests-nonnil gtests) then else
                               (bfr-and (bfr-not (gtests-unknown gtests))
                                         hyp))))
     (if (hf (gtests-unknown gtests))
         (glcp-value
          (mk-g-ite (mk-g-boolean (gtests-unknown gtests))
                    (mk-g-ite (gtests-obj gtests) then else)
                    merge))
       (glcp-value merge))))


(defmacro glcp-or (test else)
  `(b* (((glcp-er test) ,test)
        (gtests (gtests test hyp))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (declare (ignorable hyp))
               ,else)
           (glcp-value nil)))
        (merge (gobj-ite-merge (gtests-nonnil gtests) test else
                               (bfr-and (bfr-not (gtests-unknown gtests))
                                         hyp))))
     (if (hf (gtests-unknown gtests))
         (glcp-value
          (mk-g-ite (mk-g-boolean (gtests-unknown gtests))
                    (mk-g-ite (gtests-obj gtests) test else)
                    merge))
       (glcp-value merge))))


(local
 (defthmd gl-eval-of-atom
   (implies (atom x)
            (equal (generic-geval x env) x))
   :hints (("goal" :in-theory (enable tag)
            :expand ((generic-geval x env)
                     (gobj-fix x))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(set-state-ok t)

(encapsulate
  (((glcp-generic-run-gified * * * * state) => (mv * * state))
   ((glcp-generic-apply-concrete * * state) => (mv * * state))
   ((glcp-generic-ev * *) => *)
   ((glcp-generic-ev-lst * *) => *)
   ((glcp-generic-geval * *) => *)
   ((glcp-generic-geval-name) => *)
   ((glcp-generic-clause-proc-name) => *))

  (local (defun glcp-generic-geval (x env)
           (generic-geval x env)))

  (local (defun glcp-generic-run-gified (fn actuals hyp clk state)
           (declare (ignore fn actuals hyp clk)
                    (xargs :stobjs state))
           (mv nil nil state)))

  (local (defun glcp-generic-apply-concrete (fn actuals state)
           (declare (ignore fn actuals)
                    (xargs :stobjs state))
           (mv nil nil state)))

  (local (defun glcp-generic-geval-name () 'glcp-generic-geval))

  (local (defevaluator glcp-generic-ev glcp-generic-ev-lst
           ((if a b c)
            (gl-cp-hint x)
            (shape-spec-obj-in-range a b)
            (return-last fn arg1 arg2)
            (use-by-hint x)
            (equal a b)
            (not x)
            (cons a b)
            (gl-aside x)
            (gl-ignore x)
            (gl-error x)
            ;; (glcp-generic-geval x env)
            )))

  (local (defun glcp-generic-clause-proc-name () 'glcp-generic))

  (defthm glcp-generic-run-gified-correct
    (implies (and (bfr-eval hyp (car env))
                  (gobject-listp actuals)
                  (mv-nth 0 (glcp-generic-run-gified fn actuals hyp
                                                     clk state)))
             (equal (glcp-generic-geval
                     (mv-nth 1 (glcp-generic-run-gified
                                fn actuals hyp clk state))
                     env)
                    (glcp-generic-ev
                     (cons fn
                           (acl2::kwote-lst
                            (glcp-generic-geval actuals env))) nil))))
  
  (defthm glcp-generic-apply-concrete-correct
    (implies (mv-nth 0 (glcp-generic-apply-concrete fn args state))
             (equal (mv-nth 1 (glcp-generic-apply-concrete fn args state))
                    (glcp-generic-ev (cons fn (acl2::kwote-lst args))
                                     nil))))

  (defthm glcp-generic-run-gified-gobjectp
    (gobjectp (mv-nth 1 (glcp-generic-run-gified fn actuals hyp
                                                 clk state))))

  (defthm true-listp-glcp-generic-run-gified
    (true-listp (glcp-generic-run-gified fn actuals hyp clk state)))

  (defthm state-p1-glcp-generic-run-gified
    (implies (state-p1 state)
             (state-p1 (mv-nth 2 (glcp-generic-run-gified
                                  fn actuals hyp clk state)))))

  (defthm true-listp-glcp-generic-apply-concrete
    (true-listp (glcp-generic-apply-concrete fn actuals state)))

  (defthm state-p1-glcp-generic-apply-concrete
    (implies (state-p1 state)
             (state-p1 (mv-nth 2 (glcp-generic-apply-concrete fn actuals
                                                              state)))))

  (make-event
   `(progn
      . ,(acl2::defevaluator-form/defthms
          'glcp-generic-ev "GLCP-GENERIC-EV-CONSTRAINT-"
          0 (acl2::evaluator-clauses
             'glcp-generic-ev 'glcp-generic-ev-lst
             '((if a b c)
               (gl-cp-hint x)
               (shape-spec-obj-in-range a b)
               (return-last fn arg1 arg2)
               (use-by-hint x)
               (equal a b)
               (not x)
               (cons a b)
               (gl-aside x)
               (gl-ignore x)
               (gl-error x))))))

;;   (defthm glcp-generic-ev-constraint-19
;;     (implies (and (consp x)
;;                   (equal (car x)
;;                          (glcp-generic-geval-name)))
;;              (equal (glcp-generic-ev x a)
;;                     (glcp-generic-geval
;;                      (glcp-generic-ev (cadr x) a)
;;                      (glcp-generic-ev (caddr x) a)))))

  (defthm glcp-generic-geval-name-not-quote
    (not (equal (glcp-generic-geval-name) 'quote)))

  (defthm glcp-generic-geval-atom
    (implies (atom x)
             (equal (glcp-generic-geval x env) x))
    :hints(("Goal" :in-theory (enable gl-eval-of-atom)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm glcp-generic-geval-mk-g-boolean-correct
    (equal (glcp-generic-geval (mk-g-boolean x) env)
           (bfr-eval x (car env))))


  (defthmd glcp-generic-geval-of-gobject-car
    (implies (and (gobjectp x)
                  (consp x)
                  (gobjectp (car x)))
             (equal (glcp-generic-geval x env)
                    (cons (glcp-generic-geval (car x) env)
                          (glcp-generic-geval (cdr x) env))))
    :hints (("goal" :expand ((glcp-generic-geval x env)
                             (generic-geval x env))
             :in-theory (enable gobjectp-car-impl-not-g-types))))


  (defthm glcp-generic-geval-gobj-ite-merge-correct
    (implies (bfr-eval hyp (car env))
             (equal (glcp-generic-geval (gobj-ite-merge c x y hyp)
                                        env)
                    (if (bfr-eval c (car env))
                        (glcp-generic-geval x env)
                      (glcp-generic-geval y env))))
    :hints(("Goal" :in-theory (disable generic-geval))))

  (defthmd glcp-generic-geval-gtests-nonnil-correct
    (implies (and (not (bfr-eval (gtests-unknown (gtests x hyp))
                                 (car env)))
                  (bfr-eval hyp (car env)))
             (equal (bfr-eval (gtests-nonnil (gtests x hyp))
                              (car env))
                    (if (glcp-generic-geval x env) t nil)))
    :hints (("goal" :expand ((glcp-generic-geval x env))
             :in-theory (e/d** (gtests-nonnil-correct)))))

  (defthm glcp-generic-geval-gtests-obj-correct
    (implies (and (bfr-eval (gtests-unknown (gtests x hyp))
                            (car env))
                  (bfr-eval hyp (car env)))
             (iff (glcp-generic-geval (gtests-obj (gtests x hyp))
                                      env)
                  (glcp-generic-geval x env)))
    :hints (("Goal" :in-theory
             (e/d** (glcp-generic-geval
                     gtests-obj-correct)))))

  (defthm glcp-generic-geval-mk-g-ite-correct
    (equal (glcp-generic-geval (mk-g-ite c x y) b)
           (if (glcp-generic-geval c b)
               (glcp-generic-geval x b)
             (glcp-generic-geval y b)))
    :hints (("Goal" :in-theory
             (e/d** (glcp-generic-geval
                     mk-g-ite-correct)))))

  (defthm glcp-generic-geval-gobj-fix
    (equal (glcp-generic-geval (gobj-fix x) env)
           (glcp-generic-geval x env))
    :hints(("Goal" :in-theory
            (e/d** (glcp-generic-geval
                    generic-geval-gobj-fix)))))

  (defthm glcp-generic-geval-mk-g-concrete-correct
    (equal (glcp-generic-geval (mk-g-concrete x) env)
           x)
    :hints (("goal" :in-theory
             (e/d** (glcp-generic-geval mk-g-concrete-correct)))))

  (defthm glcp-generic-geval-general-concrete-obj-correct
    (implies (general-concretep x)
             (equal (glcp-generic-geval x env)
                    (general-concrete-obj x)))
    :hints (("goal" :in-theory
             (e/d** (glcp-generic-geval general-concrete-obj-correct)))))

  (defthm glcp-generic-geval-shape-spec-to-gobj-eval-env
    (implies (and (shape-specp x)
                  (no-duplicatesp-equal (shape-spec-indices x))
                  (no-duplicatesp-equal (shape-spec-vars x))
                  (shape-spec-obj-in-range x obj))
             (equal (glcp-generic-geval
                     (shape-spec-to-gobj x)
                     (shape-spec-to-env x obj))
                    obj))
    :hints (("goal" :in-theory
             (e/d** (glcp-generic-geval
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                      acl2::no-duplicatesp-is-no-duplicatesp-equal
                     shape-spec-to-gobj-eval-env)))))

  (defthm glcp-generic-geval-gobj-to-param-space-correct
    (implies (and (gobjectp x)
                  (bfr-eval p (car env)))
             (equal (glcp-generic-geval (gobj-to-param-space x p)
                                        (genv-param p env))
                    (glcp-generic-geval x env)))
    :hints (("goal" :in-theory
             (e/d** (glcp-generic-geval
                     gobj-to-param-space-correct))))))

(local (in-theory (enable glcp-generic-geval-gtests-nonnil-correct)))

(defun glcp-generic-run-gified-guard-wrapper (fn actuals hyp clk state)
  (declare (xargs :guard (and (symbolp fn)
                              (gobject-listp actuals)
                              (bfr-p hyp)
                              (natp clk))
                  :stobjs state))
  (ec-call (glcp-generic-run-gified fn actuals hyp clk state)))

(defun glcp-generic-apply-concrete-guard-wrapper
  (fn actuals state)
  (declare (xargs :guard (true-listp actuals)
                  :stobjs state))
  (ec-call (glcp-generic-apply-concrete fn actuals state)))


(local
 (progn
   (defun glcp-generic-geval-lst (x env)
     (if (atom x)
         nil
       (cons (glcp-generic-geval (car x) env)
             (glcp-generic-geval-lst (cdr x) env))))

   (defthmd glcp-generic-geval-of-gobject-list
     (implies (gobject-listp x)
              (equal (glcp-generic-geval x env)
                     (glcp-generic-geval-lst x env)))
     :hints
     (("goal" :induct (gobject-listp x)
       :in-theory (enable gobject-listp-impl-gobjectp
                          glcp-generic-geval-of-gobject-car
                          gobject-listp))))






   (defthm nonnil-symbol-listp-impl-eqlable-listp
     (implies (nonnil-symbol-listp x)
              (eqlable-listp x))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))




   (defthm glcp-generic-run-gified-wrapper-unwrap
     (equal (glcp-generic-run-gified-guard-wrapper fn actuals hyp clk state)
            (glcp-generic-run-gified fn actuals hyp clk state)))




   (defthm glcp-generic-apply-concrete-wrapper-unwrap
     (equal (glcp-generic-apply-concrete-guard-wrapper fn actuals state)
            (glcp-generic-apply-concrete fn actuals state)))

   (in-theory (disable glcp-generic-run-gified-guard-wrapper
                       glcp-generic-apply-concrete-guard-wrapper))))




(defun general-concrete-listp (x)
  (declare (xargs :guard (gobject-listp x)
                  :guard-hints (("goal" :in-theory
                                 (enable gobject-listp)))))
  (if (atom x)
      (eq x nil)
    (and (general-concretep (car x))
         (general-concrete-listp (cdr x)))))

(defun general-concrete-obj-list (x)
  (declare (xargs :guard (and (gobject-listp x)
                              (general-concrete-listp x))
                  :guard-hints (("goal" :in-theory
                                 (enable gobject-listp)))))
  (if (atom x)
      nil
    (cons (general-concrete-obj (car x))
          (general-concrete-obj-list (cdr x)))))


(mutual-recursion
 (defun sublis-into-term (x alist)
   (declare (xargs :guard t))
   (cond ((null x) nil)
         ((atom x)
          (let ((look (hons-assoc-equal x alist)))
            (if look (acl2::kwote (cdr look)) x)))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (sublis-into-list (cdr x) alist)))))
 (defun sublis-into-list (x alist)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (cons (sublis-into-term (car x) alist)
           (sublis-into-list (cdr x) alist)))))

(local (flag::make-flag sublis-into-term-flg sublis-into-term))

;; (defthm assoc-equal-nonnil-of-append
;;   (implies x
;;            (equal (assoc-equal x (append a b))
;;                   (or (assoc-equal x a)
;;                       (assoc-equal x b))))
;;   :hints(("Goal" :in-theory (enable append assoc-equal))))

;; (defthm-sublis-into-term-flg
;;   sublis-into-term-correct-lemma
;;   (sublis-into-term
;;    (implies (pseudo-termp x)
;;             (equal (glcp-generic-ev (sublis-into-term x subst) alist)
;;                    (glcp-generic-ev x (append subst alist))))
;;    :name sublis-into-term-correct)
;;   (sublis-into-list
;;    (implies (pseudo-term-listp x)
;;             (equal (glcp-generic-ev-lst (sublis-into-list x subst) alist)
;;                    (glcp-generic-ev-lst x (append subst alist))))
;;    :name sublis-into-list-correct)
;;   :hints (("goal" :induct (sublis-into-term-flg flag x alist))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable glcp-generic-ev-constraint-0)))))

(local
 (progn
   (defthm len-sublis-into-list
     (implies (pseudo-term-listp x)
              (equal (length (sublis-into-list x subst))
                     (length x)))
     :hints (("goal" :induct (len x)
              :in-theory (enable length))))

   (defthm-sublis-into-term-flg
     sublis-into-term-pseudo-term-lemma
     (sublis-into-term
      (implies (pseudo-termp x)
               (pseudo-termp (sublis-into-term x subst)))
      :name pseudo-termp-sublis-into-term)
     (sublis-into-list
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (sublis-into-list x subst)))
      :name pseudo-term-listp-sublis-into-list)
     :hints (("goal" :induct (sublis-into-term-flg flag x alist)
              :expand ((pseudo-termp x)
                       (:free (args) (pseudo-termp (cons (car x)
                                                         args)))))))))


(defconst *glcp-generic-template-subst*
  `((interp-term . glcp-generic-interp-term)
    (interp-list . glcp-generic-interp-list)
    (run-cases . glcp-generic-run-cases)
    (run-parametrized . glcp-generic-run-parametrized)
    (clause-proc . glcp-generic)
    (clause-proc-name . (glcp-generic-clause-proc-name))
    (geval-name . (glcp-generic-geval-name))
    (run-gified . glcp-generic-run-gified-guard-wrapper)
    (apply-concrete . glcp-generic-apply-concrete-guard-wrapper)))

(defund gl-aside-wormhole (term alist)
  (declare (xargs :guard t))
  (wormhole 'glcp-interp-gl-aside
            '(lambda (whs) whs)
            nil
            `(prog2$ ,(sublis-into-term
                       term alist)
                     (value :q))
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil
            :ld-verbose nil))

(defun glcp-interp-error-fn (msg state)
  (declare (xargs :guard t))
  (mv msg nil nil state))

(defmacro glcp-interp-error (msg)
  (declare (xargs :guard t))
  `(glcp-interp-error-fn ,msg state))

(add-macro-alias glcp-interp-error glcp-interp-error-fn)


(defthmd acl2-count-last-cdr-when-cadr-hack
  (implies (< 1 (len x))
           (< (acl2-count (car (last x)))
              (+ 1 (acl2-count (cdr x)))))
  :rule-classes (:rewrite :linear))

(defun gobject-vals-alistp (x)
  (declare (Xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (or (atom (car x))
             (gobjectp (cdar x)))
         (gobject-vals-alistp (cdr x)))))


(defthm lookup-in-gobject-vals-alistp
  (implies (gobject-vals-alistp x)
           (gobjectp (cdr (hons-assoc-equal k x)))))

(defthm gobject-vals-alistp-pairlis$
  (implies (gobject-listp vals)
           (gobject-vals-alistp (pairlis$ keys vals)))
  :hints(("Goal" :in-theory (enable gobject-listp))))


(make-event
 (sublis *glcp-generic-template-subst*
         *glcp-interp-template*))

(in-theory (disable glcp-generic-interp-term glcp-generic-interp-list))

(local (in-theory (disable* general-concretep-def acl2-count
;                            sets::double-containment
                            integer-abs booleanp-gobjectp
;                            sets::nonempty-means-set
                            equal-of-booleans-rewrite
                            (:ruleset gl-wrong-tag-rewrites)
                            put-global
                            acl2::true-list-listp-forward-to-true-listp-assoc-equal)))

(defchoose glcp-generic-ev-falsify (a) (x)
  (not (glcp-generic-ev x a)))


(defthmd gobject-listp-true-listp
  (implies (gobject-listp x)
           (true-listp x))
  :hints(("Goal" :in-theory (enable gobject-listp)))
  :rule-classes (:rewrite :forward-chaining))

(local
 (progn
   (acl2::def-ev-theoremp glcp-generic-ev)



   (defun glcp-generic-geval-alist (al env)
     (if (atom al)
         nil
       (if (consp (car al))
           (cons (cons (caar al)
                       (glcp-generic-geval (cdar al)
                                           env))
                 (glcp-generic-geval-alist (cdr al) env))
         (glcp-generic-geval-alist (cdr al) env))))

   (defthm glcp-generic-geval-alist-pairlis$
     (equal (glcp-generic-geval-alist
             (pairlis$ formals actuals)
             env)
            (pairlis$ formals
                      (glcp-generic-geval-lst actuals env)))
     :hints(("Goal" :in-theory (enable default-cdr)
             :induct (pairlis$ formals actuals))))

           

   (flag::make-flag glcp-generic-interp-flg glcp-generic-interp-term
                    :hints (("goal" :in-theory
                             (e/d (acl2-count
                                   acl2-count-last-cdr-when-cadr-hack)
                                  (last)))))

   (defthm-glcp-generic-interp-flg
     glcp-generic-interp-gobjectp-lemma
     (glcp-generic-interp-term
      (implies (and (bfr-p hyp)
                    (not (mv-nth 0 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))))
               (gobjectp (mv-nth 2 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))))
      :name gobjectp-glcp-generic-interp-term)

     (glcp-generic-interp-list
      (implies (and (bfr-p hyp)
                    (not (mv-nth 0 (glcp-generic-interp-list
                                    x alist hyp clk obligs overrides world state))))
               (gobject-listp (mv-nth 2 (glcp-generic-interp-list
                                         x alist hyp clk obligs overrides world state))))
      :name gobject-listp-glcp-generic-interp-list)
     :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs overrides world state)
              :expand ((glcp-generic-interp-term x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-term nil alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list nil alist hyp clk obligs overrides world state)
                       (gobject-listp nil)
                       (:free (a b) (gobject-listp (cons a b))))
              :in-theory (e/d** ( ;; gobjectp-gobj-ite-merge
                                 ;;                               gobjectp-cons
                                 ;;                               gtests-wfp
                                 ;;                               bfr-p-of-bfr-and
                                 ;;                               bfr-p-of-bfr-not
                                 ;;                               bfr-p-of-bfr-or
                                 ;;                               hyp-fix-bfr-p
                                 ;;                               (gobjectp)
                                 gobjectp-g-apply
                                 gobjectp-gobj-fix
                                 gtests-wfp
                                 gobjectp-cons
                                 bfr-p-bfr-binary-and
                                 bfr-p-bfr-not
                                 bfr-p-bfr-binary-or
                                 gobjectp-mk-g-concrete
                                 hyp-fix-bfr-p
                                 gl-aside gl-ignore gl-error-is-nil
                                 gobjectp-of-atomic-constants
                                 gobjectp-gobj-ite-merge
                                 gobjectp-mk-g-ite
                                 gobjectp-mk-g-boolean
                                 glcp-generic-run-gified-wrapper-unwrap
                                 glcp-generic-run-gified-gobjectp
                                 car-cons cdr-cons (bfr-p)
                                 glcp-interp-error
                                 glcp-generic-interp-flg-equivalences
                                 (:induction glcp-generic-interp-flg)
                                 booleanp-compound-recognizer
                                 bfr-p-bfr-binary-or
                                 gobjectp-mk-g-boolean
                                 (g-keyword-symbolp)))
              :do-not-induct t)))





   (defthm pseudo-termp-car
     (implies (pseudo-term-listp x)
              (pseudo-termp (car x))))

   (defthm pseudo-term-listp-cdr
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (cdr x))))

   (defthmd pseudo-term-listp-cdr-pseudo-term
     (implies (and (pseudo-termp x)
                   (consp x)
                   (not (equal (car x) 'quote)))
              (pseudo-term-listp (cdr x))))

   (defthmd pseudo-termp-symbolp-car-x
     (implies (and (pseudo-termp x)
                   (not (consp (car x))))
              (symbolp (car x))))

   (defthmd pseudo-termp-lambda-body
     (implies (and (pseudo-termp x)
                   (consp (car x)))
              (pseudo-termp (caddar x))))
   
   (defthmd pseudo-termp-car-last-of-pseudo-term-listp
     (implies (and (pseudo-term-listp x)
                   (consp x))
              (pseudo-termp (car (last x)))))

   (defthm pseudo-termp-car-last
     (implies (and (pseudo-termp x)
                   (< 1 (len x))
                   (not (equal (car x) 'quote)))
              (pseudo-termp (car (last x))))
     :hints(("Goal" :expand ((pseudo-termp x))
             :in-theory (enable pseudo-termp-car-last-of-pseudo-term-listp))))
                

   (defthm-glcp-generic-interp-flg
     glcp-generic-interp-obligs-okp-lemma
     (glcp-generic-interp-term
      (implies (and (pseudo-termp x)
                    (acl2::interp-defs-alistp obligs)
                    (acl2::interp-defs-alistp overrides)
                    (not (mv-nth 0 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))))
               (acl2::interp-defs-alistp
                (mv-nth 1 (glcp-generic-interp-term
                           x alist hyp clk obligs overrides world state))))
      :name obligs-okp-glcp-generic-interp-term)

     (glcp-generic-interp-list
      (implies (and (pseudo-term-listp x)
                    (acl2::interp-defs-alistp obligs)
                    (acl2::interp-defs-alistp overrides)
                    (not (mv-nth 0 (glcp-generic-interp-list
                                    x alist hyp clk obligs overrides world state))))
               (acl2::interp-defs-alistp
                (mv-nth 1 (glcp-generic-interp-list
                           x alist hyp clk obligs overrides world state))))
      :name obligs-okp-glcp-generic-interp-list)
     :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs overrides world state)
              :expand ((glcp-generic-interp-term x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-term nil alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list nil alist hyp clk obligs overrides world state)
                       (:free (a b) (acl2::interp-defs-alistp (cons a b))))
              :in-theory (e/d** (glcp-generic-interp-flg-equivalences
                                 car-cons cdr-cons ; pseudo-termp
; pseudo-term-listp
                                 pseudo-termp-car
                                 pseudo-termp-car-last
                                 pseudo-term-listp-cdr
                                 pseudo-term-listp-cdr-pseudo-term
                                 pseudo-termp-symbolp-car-x
                                 pseudo-termp-lambda-body
                                 glcp-interp-error
                                 ;; Jared: changed from hons-get-fn-do-hopy to hons-get for new hons
                                 hons-get
                                 hons-acons hons-copy
                                 acl2::hons-assoc-equal-interp-defs-alistp
                                 acl2::interp-function-lookup-wfp
                                 acl2::interp-function-lookup-defs-alistp
                                 glcp-generic-run-gified-wrapper-unwrap
                                 (:induction glcp-generic-interp-flg))))))





   (in-theory (disable equal-of-booleans-rewrite))

   (defthm true-listp-glcp-generic-interp-list
     (implies (and (bfr-p hyp)
                   (not (mv-nth 0 (glcp-generic-interp-list
                                   x alist hyp clk obligs overrides world state))))
              (true-listp (mv-nth 2 (glcp-generic-interp-list
                                     x alist hyp clk obligs overrides world state))))
     :hints(("Goal" :in-theory (enable gobject-listp-true-listp))))


   (include-book "centaur/misc/f-put-global" :dir :system)

   (defthm-glcp-generic-interp-flg
     glcp-generic-interp-state-p1-lemma
     (glcp-generic-interp-term
      (implies (state-p1 state)
               (state-p1
                (mv-nth 3 (glcp-generic-interp-term
                           x alist hyp clk obligs overrides world state))))
      :name state-p1-glcp-generic-interp-term)

     (glcp-generic-interp-list
      (implies (state-p1 state)
               (state-p1
                (mv-nth 3 (glcp-generic-interp-list
                           x alist hyp clk obligs overrides world state))))
      :name state-p1-glcp-generic-interp-list)
     :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs overrides world state)
              :expand ((glcp-generic-interp-term x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-term nil alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list nil alist hyp clk obligs overrides world state))
              :in-theory (e/d** (glcp-generic-interp-flg-equivalences
                                 acl2::state-p1-put-global
                                 glcp-interp-error-fn
                                 state-p1-glcp-generic-run-gified
                                 state-p1-glcp-generic-apply-concrete
                                 glcp-generic-run-gified-guard-wrapper
                                 glcp-generic-apply-concrete-guard-wrapper
                                 (:induction glcp-generic-interp-flg))))))))


(local
 (defthm consp-last
   (equal (consp (last x))
          (consp x))))



(set-ignore-ok t)

(make-event
 (b* (((er &) (in-theory nil))
      ((er thm) (get-guard-verification-theorem 'glcp-generic-interp-term state)))
   (value
    `(defthm glcp-generic-interp-guards-ok
       ,thm
       :hints (("goal" :in-theory
                (e/d* (gobjectp-g-apply
                       gobjectp-gobj-fix
                       gtests-wfp
                       gobjectp-cons
                       bfr-p-bfr-binary-and
                       bfr-p-bfr-not
                       bfr-p-bfr-binary-or
                       gobjectp-mk-g-concrete
                       hyp-fix-bfr-p
                       pseudo-termp-car-last-of-pseudo-term-listp
                       gl-aside gl-ignore gl-error-is-nil
                       gobjectp-of-atomic-constants)
                      (glcp-generic-interp-term
                       glcp-generic-interp-list
                       consp-assoc-equal
                       pseudo-term-listp
                       nonnil-symbol-listp-pseudo-term-listp
                       bfr-p true-listp symbol-listp
                       not no-duplicatesp-equal
                       fgetprop plist-worldp
                       hons-assoc-equal
;                       bfr-and-is-bfr-and
;                       bfr-not-is-bfr-not
;                       bfr-p-is-bfr-p
                       assoc table-alist
                       general-concrete-listp
                       general-concretep-def
                       state-p-implies-and-forward-to-state-p1
                       (:rules-of-class :forward-chaining :here)
                       (:rules-of-class :type-prescription :here)
                       (force))
                      ((:type-prescription glcp-generic-interp-term)
                       (:type-prescription glcp-generic-interp-list)
                       (:type-prescription acl2::interp-function-lookup)
                       (:type-prescription general-concrete-obj-list)
                       (:type-prescription hons-assoc-equal)))
                :do-not-induct t))
       :rule-classes nil))))



(local (defthm car-last-when-length-4
         (implies (equal (len x) 4)
                  (equal (car (last x))
                         (cadddr x)))
         :hints(("Goal" :in-theory (enable len last)))))

(local
 (progn
   (include-book "tools/def-functional-instance" :dir :system)

   (acl2::def-functional-instance
    glcp-generic-interp-function-lookup-correct
    acl2::interp-function-lookup-correct
    ((acl2::ifl-ev glcp-generic-ev)
     (acl2::ifl-ev-lst glcp-generic-ev-lst)
     (acl2::ifl-ev-falsify glcp-generic-ev-falsify))
    :hints (("Subgoal 2" :use glcp-generic-ev-constraint-0)
            ("Subgoal 1" :use glcp-generic-ev-falsify)))

   (acl2::def-functional-instance
    glcp-generic-interp-function-lookup-theoremp-defs-history
    acl2::interp-function-lookup-theoremp-defs-history
    ((acl2::ifl-ev glcp-generic-ev)
     (acl2::ifl-ev-lst glcp-generic-ev-lst)
     (acl2::ifl-ev-falsify glcp-generic-ev-falsify)))



   (defthm glcp-generic-interp-function-lookup-theoremp-defs-history-rev
     (b* (((mv erp & & out-defs)
           (acl2::interp-function-lookup fn in-defs overrides world)))
       (implies (and (not (glcp-generic-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses in-defs))))
                     (not erp))
                (not (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-defs)))))))

   (defthm-glcp-generic-interp-flg
     glcp-generic-bad-obligs-lemma
     (glcp-generic-interp-term
      (implies (and (not (glcp-generic-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses obligs))))
                    (not (mv-nth 0 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))))
               (not (glcp-generic-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (mv-nth 1 (glcp-generic-interp-term
                                  x alist hyp clk obligs overrides world state)))))))
      :name glcp-generic-interp-term-bad-obligs)
     (glcp-generic-interp-list
      (implies (and (not (glcp-generic-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses obligs))))
                    (not (mv-nth 0 (glcp-generic-interp-list
                                    x alist hyp clk obligs overrides world state))))
               (not (glcp-generic-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (mv-nth 1 (glcp-generic-interp-list
                                  x alist hyp clk obligs overrides world state)))))))
      :name glcp-generic-interp-list-bad-obligs)
     :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs overrides world state)
              :expand ((glcp-generic-interp-term x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-term nil alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list nil alist hyp clk obligs overrides world state))
              :in-theory (e/d** (glcp-generic-interp-flg-equivalences
                                 hons-acons car-cons cdr-cons
                                 glcp-interp-error           
                                 glcp-generic-interp-function-lookup-correct
                                 glcp-generic-interp-function-lookup-theoremp-defs-history
                                 acl2::interp-function-lookup-defs-alistp
                                 (:induction
                                  glcp-generic-interp-flg))))))


   (defthm glcp-generic-interp-term-ok-obligs
     (implies (and (not (glcp-generic-ev-theoremp
                         (conjoin-clauses
                          (acl2::interp-defs-alist-clauses obligs))))
                   (glcp-generic-ev-theoremp
                    (conjoin-clauses
                     (acl2::interp-defs-alist-clauses
                      (mv-nth 1 (glcp-generic-interp-term
                                 x alist hyp clk obligs overrides world state))))))
              (mv-nth 0 (glcp-generic-interp-term
                         x alist hyp clk obligs overrides
                         world state))))


   (defthm-glcp-generic-interp-flg
     glcp-generic-interp-list-len-lemma
     (glcp-generic-interp-term t :skip t)
     (glcp-generic-interp-list
      (mv-let (erp obligs res)
        (glcp-generic-interp-list
         x alist hyp clk obligs overrides world state)
        (declare (ignore obligs))
        (implies (not erp)
                 (equal (len res)
                        (len x))))
      :name len-glcp-generic-interp-list)
     :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs
                                                      overrides world state)
              :expand ((glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                       (glcp-generic-interp-list nil alist hyp clk obligs overrides world state)))))
           

   (defthm glcp-generic-obligs-okp-final-implies-start
     (implies (and (glcp-generic-ev-theoremp
                    (conjoin-clauses
                     (acl2::interp-defs-alist-clauses
                      (mv-nth 1 (glcp-generic-interp-term
                                 x alist hyp clk obligs overrides world state)))))
                   (not (mv-nth 0 (glcp-generic-interp-term
                                   x alist hyp clk obligs overrides world state))))
              (glcp-generic-ev-theoremp
               (conjoin-clauses
                (acl2::interp-defs-alist-clauses
                 obligs))))
     :rule-classes :forward-chaining)


   (defthm assoc-eq-glcp-generic-geval-alist
     (implies (alistp alist)
              (equal (cdr (assoc-eq x (glcp-generic-geval-alist alist env)))
                     (glcp-generic-geval (cdr (hons-assoc-equal x alist)) env))))



   (defthm glcp-generic-geval-lst-general-concrete-obj-list
     (implies (general-concrete-listp x)
              (equal (glcp-generic-geval-lst x env)
                     (general-concrete-obj-list x))))


   (defthm glcp-generic-ev-nil
     (equal (glcp-generic-ev nil a) nil))


   (defun glcp-generic-ev-constraint-hint (clause)
     (declare (xargs :guard (true-listp clause)))
     (cond
      ((member-equal '(not (equal flag 'glcp-generic-interp-term)) clause)
       (cond
        ((member-equal '(not (consp x)) clause)
         (cond
          ((member-equal '(not (equal (car x) 'if)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-6)))
          ((member-equal '(not (equal (car x) 'return-last)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-9)))
          ((member-equal '(not (equal (car x) 'gl-aside)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-14)))
          ((member-equal '(not (equal (car x) 'gl-ignore)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-15)))
          ((member-equal '(not (equal (car x) 'gl-error)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-16)))
          ((member-equal '(not (equal (car x) 'quote)) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-2)))
          ((member-equal '(not (consp (car x))) clause)
           '(:in-theory (enable glcp-generic-ev-constraint-3)))))
        ((member-equal '(not (symbolp x)) clause)
         '(:in-theory (enable glcp-generic-ev-constraint-1)))))
      ((member-equal '(equal flag 'glcp-generic-interp-term) clause)
       (cond
        ((member-equal '(consp x) clause)
         '(:in-theory (enable glcp-generic-ev-constraint-4)))
        ((member-equal '(not (consp x)) clause)
         '(:in-theory (enable glcp-generic-ev-constraint-5)))))))

   (encapsulate nil
     (local 
      (in-theory (e/d** (glcp-generic-geval-gobj-ite-merge-correct
                         ; glcp-generic-geval-atom
                         (:rules-of-class :executable-counterpart :here)
                         gobjectp-g-apply
                         gobjectp-gobj-fix
                         gtests-wfp
                         gobjectp-cons
                         bfr-p-bfr-binary-and
                         bfr-p-bfr-not
                         bfr-p-bfr-binary-or
                         gobjectp-mk-g-concrete
                         pseudo-termp-car-last
                         car-last-when-length-4
                         hyp-fix-bfr-p
                         gl-aside gl-ignore gl-error-is-nil
                         gobjectp-of-atomic-constants
                         (:induction glcp-generic-interp-flg)
                         gobjectp-gobj-ite-merge
                         gobjectp-mk-g-ite
                         gobjectp-mk-g-boolean
                         glcp-generic-interp-flg-equivalences
                         glcp-generic-apply-concrete-correct
                         alistp-pairlis
                         acl2::cons-car-cdr
                         glcp-generic-ev-nil
                         glcp-interp-error
                         glcp-generic-geval-lst-general-concrete-obj-list
                         acl2::hons-assoc-equal-interp-defs-alistp
                         obligs-okp-glcp-generic-interp-list
                         assoc-eq-glcp-generic-geval-alist
                         ;; glcp-generic-ev-constraint-9
                         ;;                       glcp-generic-ev-constraint-3
                         ;;                       glcp-generic-ev-constraint-6
                         ;;                       glcp-generic-ev-constraint-2
                         ;;                       glcp-generic-ev-constraint-1
                         ;;                       glcp-generic-ev-constraint-5
                         ;;                       glcp-generic-ev-constraint-4
                         pseudo-termp-car
                         pseudo-term-listp-cdr
                         pseudo-termp-symbolp-car-x
                         len-glcp-generic-interp-list
                         pseudo-term-listp-cdr-pseudo-term
                         pseudo-termp-lambda-body
                         car-cons cdr-cons hons-equal
                         glcp-generic-run-gified-wrapper-unwrap
                         glcp-generic-apply-concrete-wrapper-unwrap
                         glcp-generic-geval-alist-pairlis$
                         obligs-okp-glcp-generic-interp-term
                         obligs-okp-glcp-generic-interp-list
                         acl2::interp-function-lookup-defs-alistp
                         acl2::interp-function-lookup-wfp
                         glcp-generic-interp-function-lookup-correct
                         glcp-generic-interp-function-lookup-theoremp-defs-history-rev
                         ;; Jared: blah blah hons-get-fn-do-hopy
                         hons-get
                         eql
                         glcp-generic-obligs-okp-final-implies-start
                         glcp-generic-interp-term-bad-obligs
                         glcp-generic-interp-list-bad-obligs
                         ;; glcp-generic-obligs-okp-implies-glcp-generic-ev-fncall-equals-body-arbitrary-args
                         ;; glcp-generic-ev-theoremp-implies-glcp-generic-ev-fncall-equals-body-arbitrary-args
                         ;;glcp-generic-obligs-okp-hons-acons-implies
                         ;;glcp-generic-obligs-okp-hons-assoc-equal
                         ;; glcp-generic-ev-lst-pairlis-nonnil-symbol-list
                         glcp-generic-run-gified-correct
                         gobject-listp-glcp-generic-interp-list
                         gobjectp-glcp-generic-interp-term
                         gtests-wfp (bfr-p)
                         bfr-p-bfr-binary-or
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                          acl2::no-duplicatesp-is-no-duplicatesp-equal
                         gobjectp-mk-g-boolean
                         gobjectp-mk-g-ite
; bfr-eval-nonnil-forward
                         bfr-eval-consts
                         bfr-and-of-nil (bfr-not) 
                         bfr-eval-bfr-not bfr-eval-bfr-binary-and
                         bfr-eval-bfr-binary-or
                         glcp-generic-geval-mk-g-boolean-correct
                         glcp-generic-geval-mk-g-ite-correct
                         glcp-generic-geval-gtests-nonnil-correct
                         hyp-fix-correct
                         glcp-generic-geval-gtests-obj-correct
                         glcp-generic-geval-mk-g-concrete-correct
                         glcp-generic-geval-gobj-fix
                         gobjectp-of-atomic-constants)
                        ())))


     (local
      (encapsulate nil
        (local (bfr-reasoning-mode t))
        (local (acl2::set-bdd-patterns '((hyp-fix . &) 't 'nil)))
        (defthm bfr-eval-gtests-unknown
          (implies (and (not (hf (gtests-unknown (gtests test hyp))))
                        (bfr-eval hyp env))
                   (not (bfr-eval (gtests-unknown (gtests test hyp)) env))))

        (defthm bfr-eval-gtests-unknown-or
          (implies (and (not (hf (bfr-or (gtests-unknown (gtests test hyp)) other)))
                        (bfr-eval hyp env))
                   (not (bfr-eval (gtests-unknown (gtests test hyp)) env))))


        (defthm geval-of-interp-res-hyp-fix-unknown-false
          (implies (and (not (glcp-generic-geval interp-res env))
                        (bfr-eval hyp (car env)))
                   (hyp-fix (bfr-or
                             (gtests-unknown (gtests interp-res hyp))
                             (bfr-not
                              (gtests-nonnil (gtests interp-res hyp))))
                            hyp)))

        (defthm geval-of-interp-res-hyp-fix-unknown-true
          (implies (and (glcp-generic-geval interp-res env)
                        (bfr-eval hyp (car env)))
                   (hyp-fix (bfr-or
                             (gtests-unknown (gtests interp-res hyp))
                             (gtests-nonnil (gtests interp-res hyp)))
                            hyp)))

        (defthm gtests-nonnil-or-not
          (implies
           (and
            (bfr-eval hyp (car env))
            (not
             (hyp-fix
              (bfr-or
               (gtests-unknown (gtests test hyp))
               (gtests-nonnil (gtests test hyp)))
              hyp)))
           (hyp-fix
            (bfr-or
             (gtests-unknown (gtests test hyp))
             (bfr-not (gtests-nonnil (gtests test hyp))))
            hyp)))))

     ;;   (local (add-bfr-fn-pat hyp-fix))
     ;;   (local (add-bfr-fn-pat bfr-and))
     ;;   (local (add-bfr-fn-pat bfr-or))
     ;;   (local (add-bfr-fn-pat bfr-not))
     ;;   (local (add-bfr-fn-pat gtests-unknown))
     ;;   (local (add-bfr-fn-pat gtests-nonnil))
     ;;   (local (bfr-reasoning-mode t))
     
;;      (local (defthm hyp-fix-iff-bfr-and
;;               (iff (hyp-fix x hyp)
;;                    (bfr-and x hyp))
;;               :hints(("Goal" :in-theory (enable hyp-fix acl2::bfr-and-of-nil
;;                                                 bfr-and)))))

     (defthm-glcp-generic-interp-flg
       glcp-generic-interp-correct-lemma
       (glcp-generic-interp-term
        (implies (and (bfr-p hyp)
                      (bfr-eval hyp (car env))
                      (alistp alist)
                      (pseudo-termp x)
                      (not (mv-nth 0 (glcp-generic-interp-term
                                      x alist hyp clk obligs overrides world state)))
                      (acl2::interp-defs-alistp obligs)
                      (acl2::interp-defs-alistp overrides)
                      (glcp-generic-ev-theoremp
                       (conjoin-clauses
                        (acl2::interp-defs-alist-clauses
                         (mv-nth 1 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))))))
                 (equal (glcp-generic-geval
                         (mv-nth 2 (glcp-generic-interp-term
                                    x alist hyp clk obligs overrides world state))
                         env)
                        (glcp-generic-ev x (glcp-generic-geval-alist alist env))))
        :name glcp-generic-interp-term-correct)

       (glcp-generic-interp-list
        (implies (and (bfr-p hyp)
                      (bfr-eval hyp (car env))
                      (not (mv-nth 0 (glcp-generic-interp-list
                                      x alist hyp clk obligs overrides world state)))
                      (acl2::interp-defs-alistp obligs)
                      (acl2::interp-defs-alistp overrides)
                      (alistp alist)
                      (pseudo-term-listp x)
                      (glcp-generic-ev-theoremp
                       (conjoin-clauses
                        (acl2::interp-defs-alist-clauses
                         (mv-nth 1 (glcp-generic-interp-list
                                    x alist hyp clk obligs overrides world state))))))
                 (equal (glcp-generic-geval-lst
                         (mv-nth 2 (glcp-generic-interp-list
                                    x alist hyp clk obligs overrides world state))
                         env)
                        (glcp-generic-ev-lst x (glcp-generic-geval-alist alist env))))
        :name glcp-generic-interp-list-correct)
       :hints (("goal" :induct (glcp-generic-interp-flg flag x alist hyp clk obligs overrides world state)
                :expand
                ((glcp-generic-interp-term x alist hyp clk obligs overrides world state)
                 (glcp-generic-interp-list x alist hyp clk obligs overrides world state)
                 (glcp-generic-interp-term nil alist hyp clk obligs overrides world state)
                 (glcp-generic-interp-list nil alist hyp clk obligs overrides world state)
                 (:free (a b) (glcp-generic-geval-lst (cons a b) env))
                 (glcp-generic-geval-lst nil env))
                :do-not '(generalize fertilize)
                :do-not-induct t)
               (glcp-generic-ev-constraint-hint clause)
               (and stable-under-simplificationp
                    (case-match id
                      ((('0 '1) (n . &) . &)
                       '(:in-theory
                         (enable
                          glcp-generic-ev-constraint-0
                          glcp-generic-geval-of-gobject-list)))))
;;                (if stable-under-simplificationp
;;                    (let ((state (acl2::f-put-global
;;                                  'evbdd-cp-clauses
;;                                  (cons clause
;;                                        (and (boundp-global 'evbdd-cp-clauses
;;                                                            state)
;;                                             (@ evbdd-cp-clauses)))
;;                                  state)))
;;                     (value '(:clause-processor
;;                              (acl2::bfr-eval-cp
;;                               clause
;;                               (list '('t 'nil)
;;                                     '((hyp-fix . &)
;;                                ;;       (bfr-or . &)
;; ;;                                      (bfr-not . &)
;; ;;                                      (bfr-and . &)
;; ;;                                      (gtests-unknown . &)
;; ;;                                      (gtests-nonnil . &)
;; ;;                                      'nil 't
;;                                       )
;;                                     ;; '((car env))
;;                                     t)))))
;;                  (value nil))
               )))))

(in-theory (disable glcp-generic-interp-term))


(defun strip-cadrs (x)
  (if (atom x)
      nil
    (cons (cadr (car x))
          (strip-cadrs (cdr x)))))
                  

(mutual-recursion
 (defun collect-vars (x)
   (cond ((null x) nil)
         ((atom x) (list x))
         ((eq (car x) 'quote) nil)
         (t (collect-vars-list (cdr x)))))
 (defun collect-vars-list (x)
   (if (atom x)
       nil
     (union-equal (collect-vars (car x))
                  (collect-vars-list (cdr x))))))


(defun shape-spec-bindingsp (x)
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (not (keywordp (caar x)))
         (caar x)
         (consp (cdar x))
         (shape-specp (cadar x))
         (shape-spec-bindingsp (cdr x)))))


(defun gobj-alist-to-param-space (alist p)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (gobj-to-param-space (cdar alist) p))
          (gobj-alist-to-param-space (cdr alist) p))))





(set-state-ok t)


(local
 (progn
   (defthm alistp-shape-specs-to-interp-al
     (alistp (shape-specs-to-interp-al x)))

   (defun norm-alist (vars alist)
     (if (atom vars)
         nil
       (let ((look (assoc-equal (car vars) alist)))
         (cons (cons (car vars) (cdr look))
               (norm-alist (cdr vars) alist)))))



   (defthm car-assoc-equal
     (equal (car (assoc-equal x a))
            (and (assoc-equal x a)
                 x)))

   (defthm assoc-equal-norm-alist
     (equal (cdr (assoc-equal v (norm-alist vars alist)))
            (and (member-equal v vars)
                 (cdr (assoc-equal v alist)))))

   (flag::make-flag collect-vars-flg collect-vars)

   (defthm subsetp-equal-union-equal
     (iff (subsetp-equal (union-equal a b) c)
          (and (subsetp-equal a c)
               (subsetp-equal b c)))
     :hints ((acl2::set-reasoning)))

   (defthm-collect-vars-flg
     glcp-generic-ev-norm-alist-collect-vars-lemma
     (collect-vars
      (implies (and (pseudo-termp x)
                    (subsetp-equal (collect-vars x) vars))
               (equal (glcp-generic-ev x (norm-alist vars alist))
                      (glcp-generic-ev x alist)))
      :name glcp-generic-ev-norm-alist-collect-vars1)
     (collect-vars-list
      (implies (and (pseudo-term-listp x)
                    (subsetp-equal (collect-vars-list x) vars))
               (equal (glcp-generic-ev-lst x (norm-alist vars alist))
                      (glcp-generic-ev-lst x alist)))
      :name glcp-generic-ev-lst-norm-alist-collect-vars-list1)
     :hints (("goal" :induct (collect-vars-flg flag x)
              :in-theory (enable subsetp-equal))
             ("Subgoal *1/3"
              :in-theory (enable glcp-generic-ev-constraint-0))))


        

   (encapsulate nil
     (local (defthm member-equal-second-revappend
              (implies (member-equal x b)
                       (member-equal x (revappend a b)))))
     (defthm member-equal-revappend
       (iff (member-equal x (revappend a b))
            (or (member-equal x a)
                (member-equal x b)))))

   (defthm revappend-set-equiv-union
     (acl2::set-equivp (revappend a b) (union-equal a b))
     :hints ((acl2::set-reasoning)))


   (defun gobject-alistp (x)
     (if (atom x)
         (equal x nil)
       (and (consp (car x))
            (symbolp (caar x))
            (not (keywordp (caar x)))
            (caar x)
            (gobjectp (cdar x))
            (gobject-alistp (cdr x)))))

   (defthm gobject-alistp-shape-specs-to-interp-al
     (implies (shape-spec-bindingsp x)
              (gobject-alistp (shape-specs-to-interp-al x)))
     :hints(("Goal" :in-theory (enable shape-specs-to-interp-al))))

   (defthm gobject-listp-strip-cdrs
     (implies (gobject-alistp x)
              (gobject-listp (strip-cdrs x)))
     :hints(("Goal" :in-theory (enable strip-cdrs gobject-listp))))

   (defthm glcp-generic-geval-alist-gobject-alistp
     (implies (gobject-alistp x)
              (equal (glcp-generic-geval-alist x env)
                     (pairlis$ (strip-cars x)
                               (glcp-generic-geval (strip-cdrs x) env))))
     :hints(("Goal" :in-theory
             (enable glcp-generic-geval-of-gobject-car
                     strip-cdrs gobject-listp-impl-gobjectp))))

   (defthm strip-cdrs-shape-specs-to-interp-al
     (implies (shape-spec-bindingsp x)
              (equal (strip-cdrs (shape-specs-to-interp-al x))
                     (shape-spec-to-gobj (strip-cadrs x))))
     :hints(("Goal" :in-theory (enable strip-cdrs
                                       shape-specs-to-interp-al
                                       shape-spec-to-gobj tag)
             :induct (strip-cadrs x)
             :expand ((:free (a b)
                             (shape-spec-to-gobj (cons a b)))))))


   (defthm gobject-alistp-gobj-alist-to-param-space
     (implies (gobject-alistp x)
              (gobject-alistp (gobj-alist-to-param-space x p))))

   (defthm strip-cars-gobj-alist-to-param-space
     (equal (strip-cars (gobj-alist-to-param-space x p))
            (strip-cars x)))

   (defthm strip-cdrs-gobj-alist-to-param-space
     (implies (gobject-alistp x)
              (equal (strip-cdrs (gobj-alist-to-param-space x p))
                     (gobj-to-param-space (strip-cdrs x) p)))
     :hints(("Goal" :in-theory (enable strip-cdrs 
                                       gobj-to-param-space
                                       tag)
             :induct (gobj-alist-to-param-space x p)
             :expand ((:free (a b) (gobj-to-param-space (cons a b) p))))))

   (defthm alistp-gobj-alist-to-param-space
     (alistp (gobj-alist-to-param-space x p)))


   (defthm nonnil-symbol-listp-strip-cars-shape-spec-bindings
     (implies (shape-spec-bindingsp x)
              (nonnil-symbol-listp (strip-cars x)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))


   (defthm shape-spec-listp-strip-cadrs
     (implies (shape-spec-bindingsp x)
              (shape-spec-listp (strip-cadrs x))))

   (defthm shape-specp-strip-cadrs-bindings
     (implies (shape-spec-bindingsp x)
              (shape-specp (strip-cadrs x)))
     :hints(("Goal" :in-theory (enable shape-specp tag)
             :induct (shape-spec-bindingsp x)
             :expand ((:free (a b) (shape-specp (cons a b)))))))))



(defun quote-if-needed (obj)
  (declare (xargs :mode :logic :guard t))
  (if (or (booleanp obj)
          (keywordp obj)
          (acl2-numberp obj)
          (characterp obj)
          (stringp obj))
      obj
    (list 'quote obj)))

(defun bindings-quote-if-needed (bindings)
  (if (atom bindings)
      nil
    (cons (list (caar bindings)
                (quote-if-needed (cadar bindings)))
          (bindings-quote-if-needed (cdr bindings)))))

(defun glcp-make-pretty-bindings (alist)
  (if (atom alist)
      nil
    (cons (list (caar alist) (quote-if-needed (cdar alist)))
          (glcp-make-pretty-bindings (cdr alist)))))


(defun max-max-max-depth (x)
  (if (atom x)
      0
    (max (acl2::max-max-depth (car x))
         (max-max-max-depth (cdr x)))))


;; Gets the maximum depth of a BDD in gobject X.
(defund gobj-max-depth (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) (max-depth b))
      ((g-number n) (max-max-max-depth n))
      ((g-ite if then else)
       (max (gobj-max-depth if)
            (max (gobj-max-depth then)
                 (gobj-max-depth else))))
      ((g-apply & args) (gobj-max-depth args))
      ((g-var &) 0)
      (& (max (gobj-max-depth (car x))
              (gobj-max-depth (cdr x)))))))

(defun max-list (x)
  (if (atom x)
      0
    (max (car x) (max-list (cdr x)))))

(defun max-list-list (x)
  (if (atom x)
      0
    (max (max-list (car x))
         (max-list-list (cdr x)))))

(defund inspec-max-index (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) b)
      ((g-number n) (max-list-list n))
      ((g-ite if then else)
       (max (inspec-max-index if)
            (max (inspec-max-index then)
                 (inspec-max-index else))))
      ((g-apply & args) (inspec-max-index args))
      ((g-var &) 0)
      (& (max (inspec-max-index (car x))
              (inspec-max-index (cdr x)))))))




(defun bool-to-bit (x)
  (cond ((eq x t) 1)
        ((eq x nil) 0)
        (t x)))


(defun nth-list-bits (x lst)
  (if (atom x)
      nil
    (cons (bool-to-bit (nth (car x) lst))
          (nth-list-bits (cdr x) lst))))

(defun nth-list-list-bits (x lst)
  (if (atom x)
      nil
    (cons (nth-list-bits (car x) lst)
          (nth-list-list-bits (cdr x) lst))))






;; To-satisfying-assign-spec generates the same satisfying assignment as
;; to-satisfying-assign given the same lst and bdd, except that when a
;; variable's value is irrelevant (car and cdr are equal), we put X in the list
;; instead of T or NIL.
(defun to-satisfying-assign-spec (lst bdd)
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))))
  (cond ((atom bdd) lst)
        ((eq (cdr bdd) nil) (cons t (to-satisfying-assign-spec lst (car bdd))))
        ((eq (car bdd) nil) (cons nil (to-satisfying-assign-spec lst (cdr bdd))))
        ((hqual (car bdd) (cdr bdd))
         (cons 'x (to-satisfying-assign-spec (cdr lst) (car bdd))))
        (t (cons (car lst) (to-satisfying-assign-spec
                            (cdr lst)
                            (if (car lst) (car bdd) (cdr bdd)))))))




;; For each index N in an shape spec, this substitutes the Nth value found in
;; lst.  In the number case, it substitutes 1 and 0 for booleans.
(defund inspec-show-assign-spec (x lst)
  (if (atom x)
      x
    (pattern-match x
      ((g-concrete &) x)
      ((g-boolean b) (g-boolean (nth b lst)))
      ((g-number n) (g-number (nth-list-list-bits n lst)))
      ((g-ite if then else)
       (g-ite (inspec-show-assign-spec if lst)
              (inspec-show-assign-spec then lst)
              (inspec-show-assign-spec else lst)))
      ((g-apply fn args) (g-apply fn (inspec-show-assign-spec args lst)))
      ((g-var &) x)
      (& (cons (inspec-show-assign-spec (car x) lst)
               (inspec-show-assign-spec (cdr x) lst))))))



;; (defun glcp-run-evfn (evfn obj env state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (b* ((term `(,evfn ',obj ',env))
;;        ((er (cons & val))
;;         (acl2::simple-translate-and-eval
;;          term nil nil (acl2::msg "glcp-run-evfn ~x0" evfn)
;;          'glcp-run-evfn (w state) state)))
;;     (value val)))

;; (defun glcp-run-evfn-alist (evfn alist env state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (if (atom alist)
;;       (value nil)
;;     (b* (((er val) (glcp-run-evfn evfn (cdar alist) env state))
;;          ((er rest) (glcp-run-evfn-alist evfn (cdr alist) env state)))
;;       (value (cons (cons (caar alist) val) rest)))))

(include-book "centaur/misc/vecs-ints" :dir :system)

;; (defun glcp-satisfying-assignment (evfn bdd alist bound rand state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (b* ((bdd-assign (to-satisfying-assign (acl2::nat-to-v rand bound) bdd)))
;;     (glcp-run-evfn-alist evfn alist (list bdd-assign) state)))

;; (defun glcp-n-satisfying-assignments (n bdd evfn alist bound state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (if (zp n)
;;       (value nil)
;;     (b* (((mv rand state) (acl2::random$ (ash 1 bound) state))
;;          ((er assign)
;;           (glcp-satisfying-assignment evfn bdd alist bound rand state))
;;          ((er rest)
;;           (glcp-n-satisfying-assignments
;;            (1- n) bdd evfn alist bound state)))
;;       (value (cons assign rest)))))

;; (defun glcp-pretty-print-assignments (alists)
;;   (if (atom alists)
;;       nil
;;     (prog2$ (cw "~x0~%~%" (glcp-make-pretty-bindings (car alists)))
;;             (glcp-pretty-print-assignments (cdr alists)))))

(defun n-satisfying-assigns-and-specs (n hyp-bdd bdd bound state)
  (if (zp n)
      (value nil)
    (b* (((mv rand state) (acl2::random$ (ash 1 bound) state))
         (lst (acl2::nat-to-v rand bound))
         ;; From when we passed in the unparametrized counterexample BDD:
;;          (assign (to-satisfying-assign lst bdd))
;;          (assign-spec (to-satisfying-assign-spec lst bdd))
         (assign (acl2::unparam-env hyp-bdd (to-satisfying-assign lst bdd)))
         (assign-spec (acl2::unparam-env hyp-bdd (to-satisfying-assign-spec lst bdd)))
         ((er rest) (n-satisfying-assigns-and-specs (1- n) hyp-bdd bdd bound state)))
      (value (cons (list* "generated randomly:" assign assign-spec) rest)))))


(defun vars-onto-alist (vars val al)
  (if (atom vars)
      al
    (if (hons-get (car vars) al)
        (vars-onto-alist (cdr vars) val al)
      (vars-onto-alist (cdr vars) val (hons-acons (car vars) val al)))))

(defun glcp-gen-assignments (ctrex-info alist hyp-bdd n state)
  (if (and (bfr-mode) ;; AIG mode
           (bfr-counterex-mode)) ;; alist counterexample mode
      (b* ((al (acl2::aig-extract-iterated-assigns-alist hyp-bdd 10))
           ;; Careful: al is memoized so we can't steal it.
           (cex-alist (hons-shrink-alist (append al ctrex-info) nil)))
        (value (list (list "counterexample from SAT:"
                           (vars-onto-alist
                            ;; WRONG:
                            ;; Hmm, logically this isn't really well-typed,
                            ;; because alist consists of real g-objects whereas
                            ;; shape-spec-indices wants shape-specs.  But in the
                            ;; AIG case, parametrization doesn't do anything, so
                            ;; this works.  If we were to apply this in cases
                            ;; where alist was not generated by parametrizing a
                            ;; shape-spec-alist, this would need to be changed.

                            ;; Actually, parametrization gets rid of any AIG
                            ;; variables that are constrained to concrete values.
                            ;; So we need to reproduce the parametrized binding
                            ;; alist here.
                            (shape-spec-indices (strip-cdrs alist)) nil
                            cex-alist)))))
    (b* ((bound (inspec-max-index alist))
         ((er assigns) (n-satisfying-assigns-and-specs
                        (max 0 (- n 2)) hyp-bdd ctrex-info bound state))
         (nils (acl2::nat-to-v 0 bound))
         (ts (acl2::nat-to-v -1 bound)))
      (value (take n
                   (list* (list* "generated by assigning 0/NIL to all possible bits:"
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign nils ctrex-info))
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign-spec nils ctrex-info)))
                          (list* "generated by assigning 1/T to all possible bits:"
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign ts ctrex-info))
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign-spec ts ctrex-info)))
                          assigns)))))) 


(defun glcp-pretty-print-assignments (assigns n alist concl state)
  (declare (xargs :mode :program))
  (if (atom assigns)
      (value nil)
    (b* ((string (caar assigns))
         (assign (cadar assigns))
         (assign-spec (cddar assigns))
         (assign-spec-alist (inspec-show-assign-spec alist assign-spec))
         (assign-alist (generic-geval (shape-spec-to-gobj alist)
                                      (list assign)))
         (bindings (bindings-quote-if-needed assign-alist))
         (- (if (bfr-mode)
                (cw "Example ~x2, ~@0~%Assignment:~%~x1~%~%" string bindings n)
              (cw "Example ~x3, ~@0~%Template:~%~x1~%Assignment:~%~x2~%~%" string assign-spec-alist
                  bindings n)))
         (- (cw "Running conclusion:~%"))
         ((er (cons & val))
          (acl2::simple-translate-and-eval
           `(let ,bindings
              (declare (ignorable . ,(strip-cars bindings)))
              ,concl)
           nil nil "glcp: running conclusion failed"
           'glcp-pretty-print-assignments (w state) state t))
         (- (cw "Result: ~x0~%~%" val)))
      (glcp-pretty-print-assignments (cdr assigns) (1+ n) alist concl state))))

(defun glcp-print-ctrexamples (evfn bdd alist hyp-bdd n warn-err type concl state)
  (declare (xargs :stobjs state
                  :mode :program)
           (ignorable evfn))
  (b* (((er assigns) (glcp-gen-assignments bdd alist hyp-bdd n state))
       (- (cw "
*** SYMBOLIC EXECUTION ~@0 ***: ~@1 found." warn-err type))
       (- (and (not (zp n))
               (if (and (bfr-mode)
                        (bfr-counterex-mode))
                   (cw "~%Showing the example produced by SAT.~%~%")
                 (cw "
Showing ~x0 examples. Each example consists of a template and a
concrete assignment.  The template shows a class of examples, and the
concrete assignment represents a specific example from that
class:~%~%" n))))
       ((er &) (glcp-pretty-print-assignments assigns 1 alist concl state)))
    (value nil)))

(defun glcp-counterexample-wormhole (bdd al hyp-bdd n warn-err type evfn concl)
  (wormhole
   'glcp-counterexample-wormhole
   '(lambda (whs) whs)
   nil
   `(b* (((er &)
          (glcp-print-ctrexamples
           ',evfn ',bdd ',al ',hyp-bdd ',n ',warn-err ',type ',concl state)))
      (value :q))
   :ld-prompt nil
   :ld-pre-eval-print nil
   :ld-post-eval-print nil
   :ld-verbose nil))

(in-theory (disable glcp-counterexample-wormhole))

(defun glcp-error-fn (msg state)
  (declare (xargs :guard t))
  (mv msg nil state))

(defmacro glcp-error (msg)
  `(glcp-error-fn ,msg state))

(add-macro-alias glcp-error glcp-error-fn)

(defun glcp-analyze-interp-result (val al hyp-bdd abort-unknown abort-ctrex n
                                       geval-name clause-proc id concl state)
  (b* ((test (gtests val t))
       (hyp-param (bfr-to-param-space hyp-bdd hyp-bdd))
       (unk (bfr-and hyp-param (gtests-unknown test)))
       (false (bfr-and hyp-param
                       (bfr-not (gtests-unknown test))
                       (bfr-not (gtests-nonnil test))))
       (state (acl2::f-put-global 'glcp-var-bindings al state))
       (state (acl2::f-put-global 'glcp-counterex false state))
       (state (acl2::f-put-global 'glcp-indeterminate unk state))
       ((mv false-sat false-succ false-ctrex) (bfr-sat false))
       ((when (and false-sat false-succ))
        (prog2$ (glcp-counterexample-wormhole
                 false-ctrex al hyp-bdd n "ERROR" "Counterexamples" geval-name
                 concl)
                (if abort-ctrex
                    (glcp-error
                     (acl2::msg "~
~x0: Counterexamples found in ~@1; aborting~%" clause-proc id))
                  (value (list ''nil)))))
       ;; False was either unsat or the check failed.  Either way we check unknown.
       ((mv unk-sat unk-succ unk-ctrex) (bfr-sat unk))
       ((when (and unk-sat unk-succ))
        (prog2$ (glcp-counterexample-wormhole
                 unk-ctrex al hyp-bdd n (if abort-unknown "ERROR" "WARNING")
                 "Indeterminate results" geval-name concl)
                (if abort-unknown
                    (glcp-error
                     (acl2::msg "~
~x0: Indeterminate results found in ~@1; aborting~%"
                                clause-proc id))
                  (value (list ''nil))
                  ;; NOTE: We used to produce the following clause when an
                  ;; unknown result was encountered, giving the user the chance
                  ;; to prove that the resulting symbolic object actually
                  ;; represented something constant-true.  But this seems
                  ;; impractical, and it requires that the evaluator used to
                  ;; prove the clause processor correct recognize geval, which
                  ;; causes soundness problems regarding bfr-mode attachment,
                  ;; because we're producing a term whose meaning depends on
                  ;; the current bfr-mode.
                  ;; 
                  ;; (value `((not (gl-cp-hint 'result))
                  ;;          (,geval-name ',val env)))
                  )))
       ((when (and false-succ unk-succ))
        ;; Both checks succeeded and were UNSAT, so the theorem is proved.
        (value (list ''t))))
    ;; One or both of the SAT checks failed.
    (if abort-unknown
        (glcp-error
         (acl2::msg "~ ~x0: SAT check failed in ~@1; aborting~%"
                    clause-proc id))
      (value (list ''nil))
      ;; NOTE: See above comment about soundness problems with
      ;; geval/bfr-mode/attachment.
;;       (value `((not (gl-cp-hint 'result))
;;                (,geval-name ',val env)))
      )))

(local
 (defthm glcp-analyze-interp-result-irrelevant
   (and (implies (syntaxp (not (and (equal al ''nil)
                                    (equal n ''nil)
                                    (equal geval-name ''nil)
                                    (equal concl ''nil)
                                    (equal st ''nil))))
                 (equal (mv-nth 0 (glcp-analyze-interp-result
                                   val al hyp-bdd abort-unknown abort-ctrex n
                                   geval-name clause-proc id concl st))
                        (mv-nth 0 (glcp-analyze-interp-result
                                   val nil hyp-bdd abort-unknown abort-ctrex nil
                                   nil clause-proc id nil nil))))
        (implies (syntaxp (not (and (equal al ''nil)
                                    (equal n ''nil)
                                    (equal concl ''nil)
                                    (equal st ''nil) 
                                    (equal clause-proc ''nil))))
                 (equal (mv-nth 1 (glcp-analyze-interp-result
                                   val al hyp-bdd  abort-unknown abort-ctrex n
                                   geval-name clause-proc id concl st))
                        (mv-nth 1 (glcp-analyze-interp-result
                                   val nil hyp-bdd abort-unknown abort-ctrex nil
                                   geval-name nil nil nil nil)))))
   :hints(("Goal" :in-theory '(glcp-analyze-interp-result
                               glcp-error)))))

                               



(local
 (defthm glcp-analyze-interp-result-correct
   (implies (and (not (glcp-generic-geval val (cdr (assoc-equal 'env alist))))
                 (bfr-eval (bfr-to-param-space hyp-bdd hyp-bdd)
                           (car (cdr (assoc-equal 'env alist))))
                 (gobjectp val))
            (not (glcp-generic-ev
                  (disjoin
                   (mv-nth 1 (glcp-analyze-interp-result
                              val al hyp-bdd abort-unknown abort-ctrex n 
                              (glcp-generic-geval-name) clause-proc id concl state)))
                  alist)))
   :hints (("goal" :use
            ((:instance glcp-generic-geval-gtests-nonnil-correct
                        (x val) (hyp t)
                        (env (cdr (assoc-equal 'env alist))))
             (:instance
              bfr-sat-unsat
              (prop (bfr-and (bfr-to-param-space hyp-bdd hyp-bdd)
                             (bfr-not (gtests-unknown (gtests val t)))
                             (bfr-not (gtests-nonnil (gtests val t)))))
              (env (cadr (assoc-equal 'env alist))))
             (:instance
              bfr-sat-unsat
              (prop (bfr-and (bfr-to-param-space hyp-bdd hyp-bdd)
                             (gtests-unknown (gtests val t))))
              (env (cadr (assoc-equal 'env alist)))))
            :in-theory (e/d (gl-cp-hint)
                            (glcp-generic-geval-gtests-nonnil-correct
                             gtests-nonnil-correct
                             bfr-sat-unsat))
            :do-not-induct t)
           (bfr-reasoning))
   :otf-flg t))

(local
 (defthm glcp-analyze-interp-result-pseudo-term-listp
   (implies (and (symbolp geval-name)
                 (not (equal geval-name 'quote)))
            (pseudo-term-listp
             (mv-nth 1 (glcp-analyze-interp-result
                        val al hyp-bdd abort-unknown abort-ctrex n geval-name
                        clause-proc id concl state))))))

(in-theory (disable glcp-analyze-interp-result))  

(local
 (progn
   (defun gobj-list-to-param-space (list p)
     (if (atom list)
         nil
       (cons (gobj-to-param-space (car list) p)
             (gobj-list-to-param-space (cdr list) p))))


   (defthm glcp-generic-geval-alist-gobj-alist-to-param-space
     (equal (glcp-generic-geval-alist
             (gobj-alist-to-param-space alist p)
             env)
            (pairlis$ (strip-cars alist)
                      (glcp-generic-geval-lst
                       (gobj-list-to-param-space (strip-cdrs alist) p)
                       env)))
     :hints(("Goal" :in-theory (enable strip-cdrs))))




   (defthmd gobject-listp-gobj-to-param-space
     (implies (gobject-listp lst)
              (gobject-listp (gobj-to-param-space lst p)))
     :hints(("Goal" :in-theory (enable gobj-to-param-space tag
                                       gobject-listp))))

   (defthmd gobj-list-to-param-space-when-gobject-listp
     (implies (gobject-listp lst)
              (equal (gobj-list-to-param-space lst p)
                     (gobj-to-param-space lst p)))
     :hints(("Goal" :in-theory (enable gobj-to-param-space
                                       gobject-listp tag))))

   (defthmd glcp-generic-geval-lst-to-glcp-generic-geval
     (implies (gobject-listp x)
              (equal (glcp-generic-geval-lst x env)
                     (glcp-generic-geval x env)))
     :hints(("Goal" :in-theory (enable glcp-generic-geval-of-gobject-list))))

   (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
     (implies (and (gobject-listp x)
                   (bfr-eval p (car env)))
              (equal (glcp-generic-geval-lst
                      (gobj-list-to-param-space x p)
                      (genv-param p env))
                     (glcp-generic-geval-lst x env)))
     :hints (("goal" :use
              glcp-generic-geval-gobj-to-param-space-correct
              :in-theory (enable gobject-listp-gobj-to-param-space
                                 gobj-list-to-param-space-when-gobject-listp
                                 glcp-generic-geval-lst-to-glcp-generic-geval
                                 gobject-listp-impl-gobjectp))))

   (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
     (implies (and (gobject-listp x)
                   (bfr-eval p (car env)))
              (equal (glcp-generic-geval-lst
                      (gobj-list-to-param-space x p)
                      (genv-param p env))
                     (glcp-generic-geval-lst x env)))
     :hints (("goal" :use
              glcp-generic-geval-gobj-to-param-space-correct
              :in-theory (enable gobject-listp-gobj-to-param-space
                                 gobj-list-to-param-space-when-gobject-listp
                                 glcp-generic-geval-lst-to-glcp-generic-geval
                                 gobject-listp-impl-gobjectp))))

   (defthm strip-cars-shape-specs-to-interp-al
     (equal (strip-cars (shape-specs-to-interp-al al))
            (strip-cars al))
     :hints(("Goal" :in-theory (enable shape-specs-to-interp-al))))))

(defun preferred-defs-to-overrides (alist state)
  (declare (xargs :stobjs state :guard t))
  (if (atom alist)
      (value nil)
    (b* (((when (atom (car alist)))
          (preferred-defs-to-overrides (cdr alist) state))
         ((cons fn defname) (car alist))
         ((unless (and (symbolp fn) (symbolp defname)))
          (glcp-error
           (acl2::msg "~
The GL preferred-defs table contains an invalid entry ~x0.
The key and value of each entry should both be symbols."
                      (car alist))))
         (rule (ec-call (fgetprop defname 'theorem nil (w state))))
         ((unless rule)
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 was not found in the ACL2 world."
                      (car alist) defname)))
         ((unless (case-match rule
                    (('equal (rulefn . &) &) (equal fn rulefn))))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 is not suitable as a GL override.
Either it is a conditional definition rule, it uses a non-EQUAL
equivalence relation, or its format is unexpected.  The rule
found is ~x2." (car alist) defname rule)))
         (formals (cdadr rule))
         (body (caddr rule))
         ((unless (and (nonnil-symbol-listp formals)
                       (acl2::no-dupsp formals)))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The formals used in :definition rule ~x1 either are not all
variable symbols or have duplicates, making this an unsuitable
definition for use in a GL override.  The formals listed are
~x2." (car alist) defname formals)))
         ((unless (pseudo-termp body))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The definition body, ~x1, is not a pseudo-term."
                      (car alist) body)))
         ((er rest) (preferred-defs-to-overrides (cdr alist) state)))
      (value (hons-acons fn (list* formals body defname)
                         rest)))))


(local
 (defthm interp-defs-alistp-preferred-defs-to-overrides
   (mv-let (erp overrides state)
     (preferred-defs-to-overrides alist state)
     (declare (ignore state))
     (implies (not erp)
              (acl2::interp-defs-alistp overrides)))
   :hints(("Goal" :in-theory
           (e/d (acl2::interp-defs-alistp)
                (fgetprop
                 pseudo-term-listp
                 pseudo-term-listp-cdr
                 pseudo-termp-car true-listp))))))

(in-theory (disable preferred-defs-to-overrides))

;; A version of ACL2's dumb-negate-lit that behaves logically wrt an evaluator.
(defun dumb-negate-lit (term)
  (cond ((null term) ''t)
        ((atom term) `(not ,term))
        ((eq (car term) 'quote)
         (acl2::kwote (not (cadr term))))
        ((eq (car term) 'not)
         (cadr term))
        ((eq (car term) 'equal)
         (cond ((or (eq (cadr term) nil)
                    (equal (cadr term) ''nil))
                (caddr term))
               ((or (eq (caddr term) nil)
                    (equal (caddr term) ''nil))
                (cadr term))
               (t `(not ,term))))
        (t `(not ,term))))
                
(local
 (progn
   (defthm glcp-generic-ev-dumb-negate-lit
     (iff (glcp-generic-ev (dumb-negate-lit lit) a)
          (not (glcp-generic-ev lit a))))


   (defthm glcp-generic-ev-list*-macro
     (equal (glcp-generic-ev (list*-macro (append x (list ''nil))) al)
            (glcp-generic-ev-lst x al)))


   (defthm pairlis-eval-alist-is-norm-alist
     (implies (nonnil-symbol-listp vars)
              (equal (pairlis$ vars
                               (glcp-generic-ev-lst vars alist))
                     (norm-alist vars alist)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))



   (defthmd glcp-generic-ev-disjoin-is-or-list-glcp-generic-ev-lst
     (iff (glcp-generic-ev (disjoin lst) env)
          (acl2::or-list (glcp-generic-ev-lst lst env)))
     :hints (("goal" :induct (len lst))))

   (defthm glcp-generic-ev-disjoin-norm-alist
     (implies (and (pseudo-term-listp clause)
                   (subsetp-equal (collect-vars-list clause) vars))
              (iff (glcp-generic-ev (disjoin clause) (norm-alist vars alist))
                   (glcp-generic-ev (disjoin clause) alist)))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-ev-disjoin-is-or-list-glcp-generic-ev-lst))))))




(make-event
 (sublis *glcp-generic-template-subst* *glcp-run-parametrized-template*))

(local (progn
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;          (defthm member-eq-is-member-equal
;            (equal (member-eq x y) (member-equal x y)))
;          
;          (defthm set-difference-eq-is-set-difference-equal
;            (equal (set-difference-eq x y) (set-difference-equal x y))
;            :hints(("Goal" :in-theory (enable set-difference-equal))))

         (defthm set-difference-equal-to-subsetp-equal-iff
           (iff (set-difference-equal x y)
                (not (subsetp-equal x y)))
           :hints(("Goal" :in-theory (enable set-difference-equal subsetp-equal))))))



(local
 (progn
   (defthm bfr-p-bfr-to-param-space
     (implies (and (bfr-p p) (bfr-p x))
              (bfr-p (bfr-to-param-space p x)))
     :hints(("Goal" :in-theory (enable bfr-to-param-space bfr-p))))


   (encapsulate nil
     (local (in-theory
             (e/d (gl-cp-hint)
                  (shape-specs-to-interp-al
                   shape-spec-listp pseudo-term-listp
                   pseudo-termp pairlis$
                   shape-spec-bindingsp
                   dumb-negate-lit
                   no-duplicatesp-equal
                   gobj-alist-to-param-space
                   list*-macro binary-append strip-cadrs strip-cars member-equal))))
     (defthm glcp-generic-run-parametrized-correct
       (b* (((mv erp (cons clauses out-obligs) &)
             (glcp-generic-run-parametrized
              hyp concl untrans-concl vars bindings id abort-unknown
              abort-ctrex nexamples hyp-clk concl-clk obligs overrides world
              state)))
         (implies (and (not (glcp-generic-ev concl alist))
                       (glcp-generic-ev-theoremp
                        (conjoin-clauses
                         (acl2::interp-defs-alist-clauses out-obligs)))
                       (not erp)
                       (glcp-generic-ev hyp alist)
                       (acl2::interp-defs-alistp obligs)
                       (acl2::interp-defs-alistp overrides)
                       (pseudo-termp concl)
                       (pseudo-termp hyp)
                       (equal vars (collect-vars concl)))
                  (not (glcp-generic-ev-theoremp (conjoin-clauses clauses)))))
       :hints (("goal" :do-not-induct
                t
                :in-theory
                (e/d* ()
                      (glcp-generic-geval-alist-gobj-alist-to-param-space
                       glcp-generic-geval-gtests-nonnil-correct
                       glcp-generic-interp-term-bad-obligs
                       shape-spec-listp-impl-shape-spec-to-gobj-list
                       (:rules-of-class :definition :here)
                       (:rules-of-class :type-prescription :here))
                      (gl-cp-hint acl2::clauses-result assoc-equal
                                  glcp-generic-run-parametrized not
                                  glcp-error))
               
                :restrict ((glcp-generic-ev-disjoin-append ((a alist)))))
               (and stable-under-simplificationp
                    (acl2::bind-as-in-definition
                     (glcp-generic-run-parametrized
                      hyp concl untrans-concl (collect-vars concl) bindings id
                      abort-unknown abort-ctrex nexamples hyp-clk concl-clk
                      obligs overrides world state)
                     (cov-clause val-clause hyp-bdd hyp-val)
                     (b* ((binding-env '(shape-spec-to-env
                                         (strip-cadrs bindings)
                                         (glcp-generic-ev-lst
                                          (strip-cars bindings)
                                          alist)))
                          (param-env `(genv-param ,hyp-bdd ,binding-env)))
                       `(:use
                         ((:instance glcp-generic-ev-falsify
                                     (x (disjoin ,cov-clause))
                                     (a alist))
                          (:instance glcp-generic-ev-falsify
                                     (x (disjoin ,val-clause))
                                     (a `((env . ,,param-env))))
                          (:instance glcp-generic-geval-gtests-nonnil-correct
                                     (x ,hyp-val)
                                     (hyp t)
                                     (env ,binding-env)))))))
               (bfr-reasoning))
       :otf-flg t))

   (defthm glcp-generic-run-parametrized-bad-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl untrans-concl vars bindings id abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk obligs overrides world state)))
       (implies (and (not erp)
                     (not (glcp-generic-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))))))

   (defthm glcp-generic-run-parametrized-ok-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl untrans-concl vars bindings id abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk obligs overrides world state)))
       (implies (and (not erp)
                     (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))

   (defthm glcp-generic-run-parametrized-defs-alistp
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl untrans-concl vars bindings id abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk obligs overrides world state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp overrides)
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))))

             
(in-theory (disable glcp-generic-run-parametrized))

(defun glcp-cases-wormhole (term id)
  (wormhole 'glcp-cases-wormhole
            '(lambda (whs) whs)
            nil
            `(prog2$ (let ((id ',id))
                       (declare (ignorable id))
                       ,term)
                     (value :q))
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil
            :ld-verbose nil))

(in-theory (disable glcp-cases-wormhole))



(make-event
 (sublis *glcp-generic-template-subst* *glcp-run-cases-template*))

(local
 (progn
   (defthm glcp-generic-run-cases-interp-defs-alistp
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl untrans-concl vars abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk run-before run-after obligs overrides
            world state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp overrides)
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))
  

   (defthm glcp-generic-run-cases-correct
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl untrans-concl vars abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk run-before run-after obligs overrides
            world state)))
       (implies (and (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not (glcp-generic-ev concl a))
                     (glcp-generic-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp overrides)
                     (pseudo-termp concl)
                     (pseudo-term-listp (strip-cars param-alist))
                     (equal vars (collect-vars concl)))
                (not (glcp-generic-ev-theoremp (conjoin-clauses clauses))))))


   (defthm glcp-generic-run-cases-bad-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl untrans-concl vars abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk run-before run-after obligs overrides
            world state)))
       (implies (and (not erp)
                     (not (glcp-generic-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))))))

   (defthm glcp-generic-run-cases-ok-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl untrans-concl vars abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk run-before run-after obligs overrides
            world state)))
       (implies (and (not erp)
                     (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))))


(in-theory (disable glcp-generic-run-cases))






(defun doubleton-list-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x) (cadar x))
          (doubleton-list-to-alist (cdr x)))))

(defun bindings-to-vars-vals (x)
  (if (atom x)
      (mv nil nil)
    (mv-let (vars vals)
      (bindings-to-vars-vals (cdr x))
      (if (and (symbolp (caar x))
               (pseudo-termp (cadar x)))
          (mv (cons (caar x) vars)
              (cons (cadar x) vals))
        (mv vars vals)))))

(defun bindings-to-lambda (bindings term)
  (mv-let (vars vals)
    (bindings-to-vars-vals bindings)
    `((lambda ,vars ,term) . ,vals)))

(defthm bindings-to-vars-vals-wfp
  (mv-let (vars vals)
    (bindings-to-vars-vals x)
    (and (symbol-listp vars)
         (pseudo-term-listp vals)
         (true-listp vals)
         (equal (len vals) (len vars))
         (not (stringp vars))
         (not (stringp vals)))))

(defthm bindings-to-lambda-pseudo-termp
  (implies (pseudo-termp term)
           (pseudo-termp (bindings-to-lambda bindings term)))
  :hints(("Goal" :in-theory (enable true-listp length))))

(in-theory (disable bindings-to-lambda))

;; Transforms an alist with elements of the form
;; (((param1 val1) (param2 val2)) shape-spec)
;; to the form (parametrized-hyp . shape-spec).
(defun param-bindings-to-alist (hyp bindings)
  (if (atom bindings)
      nil
    (cons (list* (sublis-into-term
                  hyp (doubleton-list-to-alist (caar bindings)))
;;           (bindings-to-lambda (caar bindings) hyp)
           (acl2::msg "case: ~x0" (caar bindings))
           (cadar bindings))
          (param-bindings-to-alist hyp (cdr bindings)))))
(local
 (defthm param-bindings-to-alist-pseudo-term-listp-strip-cars
   (implies (pseudo-termp hyp)
            (pseudo-term-listp (strip-cars (param-bindings-to-alist hyp bindings))))))





(make-event (sublis *glcp-generic-template-subst* *glcp-clause-proc-template*))

(local
 (progn
   (defund glcp-generic-run-parametrized-placeholder (clauses)
     (glcp-generic-ev-theoremp (conjoin-clauses clauses)))

   (defun check-top-level-bind-free (bindings mfc state)
     (declare (ignore state)
              (xargs :stobjs state))
     (and (null (acl2::mfc-ancestors mfc))
          bindings))

   (defthmd glcp-generic-run-parametrized-correct-rw
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl untrans-concl vars bindings id abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk obligs overrides world st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) acl2::mfc state)
                                (alist))
                     (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not erp)
                     (glcp-generic-ev hyp alist)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp overrides)
                     (pseudo-termp concl)
                     (pseudo-termp hyp)
                     (equal vars (collect-vars concl)))
                (iff (glcp-generic-ev-theoremp (conjoin-clauses clauses))
                     (and (glcp-generic-run-parametrized-placeholder
                           clauses)
                          (glcp-generic-ev concl alist)))))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-run-parametrized-placeholder))))

   (defund glcp-generic-run-cases-placeholder (clauses)
     (glcp-generic-ev-theoremp (conjoin-clauses clauses)))

   (defthmd glcp-generic-run-cases-correct-rw
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl untrans-concl vars abort-unknown abort-ctrex
            nexamples hyp-clk concl-clk run-before run-after obligs overrides
            world st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) mfc state) (alist))
                     (glcp-generic-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (glcp-generic-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp overrides)
                     (pseudo-termp concl)
                     (pseudo-term-listp (strip-cars param-alist))
                     (equal vars (collect-vars concl)))
                (iff (glcp-generic-ev-theoremp (conjoin-clauses clauses))
                     (and (glcp-generic-run-cases-placeholder clauses)
                          (glcp-generic-ev concl a)))))
     :hints(("Goal" :in-theory (enable glcp-generic-run-cases-placeholder))))))

(defthm glcp-generic-correct
  (implies (and (pseudo-term-listp clause)
                (alistp alist)
                (glcp-generic-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-generic clause hints state)))
                 (glcp-generic-ev-falsify
                  (conjoin-clauses
                   (acl2::clauses-result
                    (glcp-generic clause hints state))))))
           (glcp-generic-ev (disjoin clause) alist))
  :hints
  (("goal" :do-not-induct
    t
    :in-theory
    (e/d* (glcp-generic-run-cases-correct-rw
           glcp-generic-run-parametrized-correct-rw)
          (glcp-analyze-interp-result-correct
           glcp-generic-geval-alist-gobj-alist-to-param-space
           glcp-generic-geval-gtests-nonnil-correct
           glcp-generic-run-cases-correct
           glcp-generic-run-parametrized-correct
           shape-spec-listp-impl-shape-spec-to-gobj-list
           (:rules-of-class :definition :here))
          (gl-cp-hint
           ;; Jared added acl2::fast-alist-free since that's my new name
           ;; for flush-hons-get-hash-table-link
           fast-alist-free
           flush-hons-get-hash-table-link
           acl2::clauses-result
           glcp-generic glcp-error
           assoc-equal pseudo-term-listp))
               
    :restrict ((glcp-generic-ev-disjoin-append ((a alist)))
               (glcp-generic-ev-disjoin-cons ((a alist)))))
   (and stable-under-simplificationp
        (acl2::bind-as-in-definition
         glcp-generic
         (hyp-clause concl-clause params-cov-term hyp)
         `(:use ((:instance glcp-generic-ev-falsify
                            (x (disjoin ,hyp-clause))
                            (a alist))
                 (:instance glcp-generic-ev-falsify
                            (x (disjoin ,concl-clause))
                            (a alist))
                 (:instance glcp-generic-ev-falsify
                  (x (disjoin (CONS
                               (CONS
                                'NOT
                                (CONS
                                 (CONS 'GL-CP-HINT
                                       (CONS (CONS 'QUOTE (CONS 'CASESPLIT 'NIL))
                                             'NIL))
                                 'NIL))
                               (CONS (CONS 'NOT (CONS ,HYP 'NIL))
                                     (CONS ,PARAMS-COV-TERM 'NIL)))))
                  (a alist)))))))
  :otf-flg t
  :rule-classes nil)




;; Related clause processor which doesn't run the simulation, but
;; produces all the other necessary clauses.  We define this by
;; using a mock interp-term function that just returns T and no
;; obligs, and also a mock analyze-term
(defun glcp-fake-interp-term (x bindings hyp clk obligs overrides
                                world state)
  (declare (ignore x bindings hyp clk overrides world))
  (mv nil obligs t state))

(defun glcp-fake-analyze-interp-result
  (val param-al hyp-bdd abort-unknown abort-ctrex nexamples geval-name clause-proc-name id
       concl state)
  (declare (ignore val param-al hyp-bdd abort-unknown abort-ctrex nexamples geval-name
                   clause-proc-name id concl)
           (xargs :stobjs state))
  (mv nil '('t) state))

(defconst *glcp-side-goals-subst*
  `((interp-term . glcp-fake-interp-term)
    (run-cases . glcp-side-goals-run-cases)
    (run-parametrized . glcp-side-goals-run-parametrized)
    (clause-proc . glcp-side-goals-clause-proc1)
    (clause-proc-name . 'glcp-side-goals-clause-proc)
    (geval-name . 'glcp-fake-geval)
    (glcp-analyze-interp-result . glcp-fake-analyze-interp-result)))

(make-event (sublis *glcp-side-goals-subst*
                    *glcp-run-parametrized-template*))

(make-event (sublis *glcp-side-goals-subst* *glcp-run-cases-template*))

(make-event (sublis *glcp-side-goals-subst*
                    *glcp-clause-proc-template*))

(defun glcp-side-goals-clause-proc (clause hints state)
  ;; The cheat: We only allow this clause processor on the trivially
  ;; true clause ('T).
  (b* (((unless (equal clause '('T)))
        (mv "This clause processor can be used only on clause '('T)."
            nil state))
       ((list* & & hyp & concl &) hints))
    (glcp-side-goals-clause-proc1 
     `((implies ,hyp ,concl)) hints state)))

(defevaluator glcp-side-ev glcp-side-ev-lst ((if a b c)))

(local (acl2::def-join-thms glcp-side-ev))

(defthm glcp-side-goals-clause-proc-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (glcp-side-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-side-goals-clause-proc clause hints state)))
                 a))
           (glcp-side-ev (disjoin clause) a))
  :hints (("goal" :in-theory
           (e/d** ((:rules-of-class :executable-counterpart :here)
                   acl2::clauses-result glcp-side-goals-clause-proc
                   glcp-side-ev-constraint-2
                   car-cons))))
  :rule-classes :clause-processor)




;; GLCP-UNIVERSAL: an unverifiable version of the clause processor
;; that can apply any symbolic counterpart and execute any function.
;; This is actually somewhat slow because simple-translate-and-eval is
;; slower than an apply function with a reasonable number of cases in
;; the style
;; (case fn
;;   (foo  (foo (nth 0 actuals) (nth 1 actuals)))
;;   (bar  (bar (nth 0 actuals)))
;;   ...)
;; But we do avoid interpreter overhead, which is the real killer.

;; Looks up a function in the gl-function-info table to see if it has
;; a symbolic counterpart, and executes it if so.
(defun gl-universal-run-gified (fn actuals hyp clk state)
  (declare (xargs :guard (and (symbolp fn)
                              (gobject-listp actuals)
                              (bfr-p hyp)
                              (natp clk))
                  :mode :program))
  (b* ((world (w state))
       (al (table-alist 'gl-function-info world))
       (look (assoc-eq fn al))
       ((unless look) (mv nil nil state))
       (gfn (cadr look))
       (call (cons gfn (acl2::kwote-lst (append actuals (list hyp clk)))))
       ((mv er (cons & res) state)
        (acl2::simple-translate-and-eval
         call nil nil
         (acl2::msg "gl-universal-run-gified: ~x0" call)
         'gl-universal-run-gified world state t))
       ((when er)
        (prog2$ (cw "GL-UNIVERSAL-RUN-GIFIED: error: ~@0~%" er)
                (mv nil nil state))))
    (mv t res state)))

(defun gl-universal-apply-concrete (fn actuals state)
  (declare (xargs :guard (true-listp actuals)
                  :mode :program))
  (b* ((world (w state))
       (call (cons fn (acl2::kwote-lst actuals)))
       (mvals (len (fgetprop fn 'stobjs-out nil world)))
       (term (if (< 1 mvals) `(mv-list ,mvals ,call) call))
       ((mv er (cons & val) state)
        (acl2::simple-translate-and-eval
         term nil nil
         (acl2::msg "gl-universal-apply-concrete: ~x0" term)
         'gl-universal-apply-concrete world state t))
       ((when er)
        (prog2$ (cw "GL-UNIVERSAL-APPLY-CONCRETE: error: ~@0~%" er)
                (mv nil nil state))))
    (mv t val state)))

(defconst *gl-universal-subst*
  `((run-gified . gl-universal-run-gified)
    (apply-concrete . gl-universal-apply-concrete)
    (interp-term . gl-universal-interp-term)
    (interp-list . gl-universal-interp-list)
    (run-cases . gl-universal-run-cases)
    (run-parametrized . gl-universal-run-parametrized)
    (clause-proc . gl-universal-clause-proc)
    (clause-proc-name . 'gl-universal-clause-proc)
    (geval-name . 'generic-geval)))

(program)

(make-event (sublis *gl-universal-subst* *glcp-interp-template*))

(make-event (sublis *gl-universal-subst*
                    *glcp-run-parametrized-template*))

(make-event (sublis *gl-universal-subst* *glcp-run-cases-template*))

(make-event (sublis *gl-universal-subst*
                    *glcp-clause-proc-template*))

(logic)


;; To install this as a clause processor, run the following.  Note
;; that this creates a ttag.
(defmacro allow-gl-universal-clause-processor ()
  '(acl2::define-trusted-clause-processor
    gl-universal-clause-proc
    nil :ttag gl-universal-clause-proc))

         
       











;; Symbolic interpreter for translated terms, based on the universal clause
;; processor defined above.  X is the term, ALIST gives a
;; list of bindings of variables to g-objects, hyp is a BDD.

(defun gl-interp-term (x alist hyp clk state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))
       ((er overrides)
        (preferred-defs-to-overrides
         (table-alist 'preferred-defs world) state))
       ((mv er obligs ans state)
        (gl-universal-interp-term
         x alist hyp clk nil overrides world state))
       ((when er) (mv er nil state))
       (- (flush-hons-get-hash-table-link obligs)))
    (value ans)))




;; Translate the given term, then run the interpreter.
(defmacro gl-interp-raw (x &optional alist (hyp 't) (clk '100000))
  `(acl2::er-let*
    ((trans (acl2::translate ,x :stobjs-out t t 'gl-interp (w state)
                             state)))
    (gl-interp-term trans ,alist ,hyp ,clk state)))



(defdoc gl-interp-raw
  ":Doc-section ACL2::GL
Symbolically interpret a term using GL.~/

Usage:
~bv[]
 (gl-interp-raw term bindings)
~ev[]

The above form runs a symbolic interpretation of ~c[term] on the symbolic input
~c[bindings].  ~c[bindings] should be an association list mapping variables to
symbolic objects (not to shape specifiers, as in ~il[gl-interp].)  Note also
that bindings is a dotted alist, rather than a doubleton list as in
~il[gl-interp]: each pair is ~c[(CONS VAR BINDING)], not ~c[(LIST VAR BINDING)].~/~/")


(defun gl-parametrize-by-hyp-fn (hyp al state)
  (declare (xargs :mode :program))
  (b* ((al (shape-specs-to-interp-al al))
       ((er hyp-pred) (gl-interp-raw hyp al))
       (hyp-test (gtests hyp-pred t))
       (hyp-bdd (bfr-or (gtests-nonnil hyp-test)
                      (gtests-unknown hyp-test))))
    (value (gobj-to-param-space al hyp-bdd))))

(defmacro gl-parametrize-by-hyp (hyp bindings)
  `(gl-parametrize-by-hyp-fn ,hyp ,bindings state))

(defun gl-interp-fn (hyp term al state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er param-al) (gl-parametrize-by-hyp hyp al))
;;        (al (shape-specs-to-interp-al al))
;;        ((er hyp-pred) (gl-interp-raw hyp al))
;;        (hyp-test (gtests hyp-pred t))
;;        (hyp-bdd (q-or (gtests-nonnil hyp-test)
;;                       (gtests-unknown hyp-test)))
;;        (param-al (gobj-to-param-space al hyp-bdd))
       ((er res) (gl-interp-raw term param-al)))
    (value (cons param-al res))))

(defmacro gl-interp (term al &key (hyp 't))
  `(gl-interp-fn ',hyp ',term ,al state))

(defdoc gl-interp
  ":Doc-section ACL2::GL
Symbolically interpret a term using GL, with inputs generated by parametrization.~/

Usage:
~bv[]
 (gl-interp term bindings :hyp hyp)
~ev[]

The above form runs a symbolic interpretation of ~c[term] on the symbolic input
assignment produced by parametrizing ~c[bindings] using ~c[hyp].  The symbolic
execution run by this form is similar to that run by
~bv[]
 (def-gl-thm <name> :hyp hyp :concl term :g-bindings bindings).
~ev[]
~c[bindings] should be a binding list of the same kind as taken by
~il[def-gl-thm], that is, a list of elements ~c[(var val)] such that ~c[var]
is a variable free in ~c[term], and ~c[val] is a shape specifier
(~l[gl::shape-specs].)

Similar to ~c[def-gl-thm], ~c[term] and ~c[hyp] should be the (unquoted)
terms of interest, whereas ~c[bindings] should be something that evaluates to
the binding list (the quotation of that binding list, for example.)~/

In more detail: First, the input bindings are converted to an assignment of
symbolic inputs to variables.  The hyp term is symbolically interpreted using
this variable assignment, yielding a predicate.  The symbolic input assignment is
parametrized using this predicate to produce a new such assignment whose
coverage is restricted to the subset satisfying the hyp.  The term is then
symbolically interpreted using this assignment, and the result is returned.

This macro expands to a function call taking state, and its return value is an
error triple.

The symbolic interpreter used by ~c[gl-interp] is not one introduced by
def-gl-clause-processor as usual, but a special one which can call any function
on concrete values, and any symbolic counterpart function.  (Other interpreters
can call a fixed list of functions on concrete values and a fixed list of
symbolic counterparts.)  However, typically a fixed interpreter is used when
proving theorems (otherwise a ttag is needed.)  This has some
performance-related consequences:

 - ~c[gl-interp] may interpret a term faster than ~c[def-gl-thm].  This
occurs mainly when some function is run concretely by the universal interpreter
but is not in the fixed list of functions callable by the fixed interpreter.
Determine which function is at fault by looking at a backtrace, and then define
your interpreter so that it can call this function.

 - ~c[gl-interp] may interpret a term slower than ~c[def-gl-thm].  The
universal interpreter uses somewhat more overhead on each function call than
fixed interpreters do, so when interpreter overhead is a large portion of the
runtime relative to BDD operations, ~c[gl-interp] may be a constant factor
slower than a fixed interpreter.

See ~il[gl-interp-raw] for a similar function that does not perform
parametrization.~/")




(defun find-counterexamples-fn (hyp concl al state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er (cons param-al concl-pred))
        (gl-interp-fn hyp concl al state))
       (concl-tests (gtests concl-pred t))
       (neg-concl (bfr-and (bfr-not (gtests-nonnil concl-tests))
                         (bfr-not (gtests-unknown concl-tests))))
       (false-al (gobj-to-param-space param-al neg-concl)))
    (value false-al)))

(defmacro find-counterexamples (concl alist &key (hyp 't))
  `(find-counterexamples-fn ,hyp ,concl ,alist state))






(defun max-max-max-depth (x)
  (if (atom x)
      0
    (max (acl2::max-max-depth (car x))
         (max-max-max-depth (cdr x)))))

(defund gobj-max-depth (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) (max-depth b))
      ((g-number n) (max-max-max-depth n))
      ((g-ite if then else)
       (max (gobj-max-depth if)
            (max (gobj-max-depth then)
                 (gobj-max-depth else))))
      ((g-apply & args) (gobj-max-depth args))
      ((g-var &) 0)
      (& (max (gobj-max-depth (car x))
              (gobj-max-depth (cdr x)))))))




(defun n-random-assignments-fn (n bound obj pred evfn state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (eq pred nil)
      (er soft 'n-random-assignments-fn
          "Unsatisfiable predicate for n-random-assignments~%")
    (if (zp n)
        (value nil)
      (b* (((er rest) (n-random-assignments-fn
                       (1- n) bound obj pred evfn state))
           ((mv envn state) (acl2::random$ bound state))
           (env (list (to-satisfying-assign (n2v envn) pred))))
        (if evfn
            (b* ((term `(,evfn ',obj ',env))
                 ((er (cons & val))
                  (acl2::simple-translate-and-eval
                   term nil nil
                   (acl2::msg "~
GL evaluation with ~x0 in n-random-assignments-fn" evfn)
                   'n-random-assignments-fn (w state) state t)))
              (value (cons val rest)))
          (value (cons (generic-geval obj env) rest)))))))

(defmacro n-random-assignments (n obj &optional (pred 't) evfn)
  `(n-random-assignments-fn
    ,n 
    (expt 2 (gobj-max-depth ,obj))
    ,obj ,pred ,evfn state))





(defun possibly-true (res)
  (let ((test (gl::gtests res t)))
    (bfr-or (gl::gtests-nonnil test)
          (gl::gtests-unknown test))))

(defun known-true (res)
  (let ((test (gl::gtests res t)))
    (bfr-and (gl::gtests-nonnil test)
           (bfr-not (gl::gtests-unknown test)))))


(defun sim-g-thm-fn (hyp concl g-bindings ctrex-info nexamples erp state)
  (declare (xargs :stobjs state :mode :program))
  (b* ((al (shape-specs-to-interp-al g-bindings))
       ((er hyp-pred) (gl-interp-raw hyp al))
       (hyp-possible (possibly-true hyp-pred))
       ((er hyp-possible)
        (if hyp-possible
            (value hyp-possible)
          (er soft 'sim-g-thm-fn "Impossible hyp~%")))
       (hyp-al (gobj-to-param-space al hyp-possible))
       ((er concl-pred) (gl-interp-raw concl hyp-al))
       (concl-definite (known-true concl-pred)))
    (if (eq concl-definite t)
        (value "OK")
      (b* ((ctrex-bdd (bfr-not concl-definite))
           ((er ctrex-info-res) (gl-interp-raw ctrex-info hyp-al))
           ((er ctrexamples)
            (n-random-assignments nexamples (cons hyp-al ctrex-info-res)
                                  ctrex-bdd)))
        (if erp
            (er soft 'sim-g-thm-fn
                "Counterexamples found: ~x0~%" ctrexamples)
          (value ctrexamples))))))

(defmacro sim-g-thm
  (&key hyp concl g-bindings ctrex-term (nexamples '3) (erp 't))
  `(sim-g-thm-fn ',hyp ',concl ,g-bindings ',ctrex-term ,nexamples ,erp state))



(defun param-al-to-interp-al (al)
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al) (mk-g-concrete (cadar al)))
              (param-al-to-interp-al (cdr al)))
      (param-al-to-interp-al (cdr al)))))


(defun sim-param-coverage (param-hyp param-bindings cov-al state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom param-bindings)
      (value nil)
    (b* (((er rest) (sim-param-coverage
                     param-hyp (cdr param-bindings) cov-al state))
         (curr-al (append (param-al-to-interp-al (caar param-bindings))
                          cov-al))
         ((er res) (gl-interp-raw param-hyp curr-al))
         (res-known (known-true res)))
      (value (bfr-or rest res-known)))))


(defun sim-param-coverage-ok (hyp param-hyp param-bindings cov-bindings
                                  nexamples erp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((cov-al (shape-specs-to-interp-al cov-bindings))
       ((er hyp-res) (gl-interp-raw hyp cov-al))
       (hyp-possible (possibly-true hyp-res))
       ((er param-cov) (sim-param-coverage
                        param-hyp param-bindings cov-al state))
       (uncov (bfr-and hyp-possible (bfr-not param-cov))))
    (if uncov
        (b* (((er examples)
              (n-random-assignments nexamples cov-al uncov)))
          (if erp
              (er soft 'sim-param-coverage-ok
                  "Coverage gap found. Examples: ~x0~%" examples)
            (value examples)))
      (value "OK"))))

(defun gl-interp-on-alists (term alists state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom alists)
      (value nil)
    (b* (((er rest) (gl-interp-on-alists term (cdr alists) state))
         ((er (cons & first))
                  (acl2::simple-translate-and-eval
                   term (car alists) nil
                   "gl-interp-on-alists"
                   'gl-interp-on-alists (w state) state t))
;;           (gl-interp term (car alists))
          )
      (value (cons (cons (car alists) first) rest)))))

(defun sim-params (param-bindings param-hyp concl ctrex-info nexamples
                                  run-after-cases state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom param-bindings)
      (value "OK")
    (b* ((- (cw "Param bindings: ~x0~%" (caar param-bindings)))
         (al (shape-specs-to-interp-al (cadar param-bindings)))
         (al-with-params (append (param-al-to-interp-al (caar param-bindings)) al))
         ((er hyp) (gl-interp-raw param-hyp al-with-params))
         (hyp-possible (possibly-true hyp))
         ((er &)
          (if hyp-possible
              (b* ((param-al (gobj-to-param-space al hyp-possible))
                   ((er concl-pred) (gl-interp-raw concl param-al))
                   (concl-known (known-true concl-pred)))
                (if (eq concl-known t)
                    (value "OK")
                  (b* ((ctrex-bdd (bfr-not concl-known))
                       ((er ctrex-alists)
                        (n-random-assignments
                         nexamples param-al ctrex-bdd))
                       ((er ctrexamples)
                        (gl-interp-on-alists ctrex-info ctrex-alists state)))
                    (er soft 'sim-params
                        "Counterexamples found at parameters ~x0: ~x1~%" 
                        (caar param-bindings) ctrexamples))))
            (prog2$ (cw "Note: Param hyp is impossible with settings ~x0~%"
                        (caar param-bindings))
                    (value "OK"))))
         ((er &)
          (acl2::simple-translate-and-eval
           run-after-cases nil nil
           (acl2::msg "~
sim-params: ~x0~%" run-after-cases)
           'sim-params (w state) state t)))
      (sim-params (cdr param-bindings) param-hyp concl ctrex-info nexamples
                  run-after-cases state))))


(defun sim-param-thm-fn (hyp param-hyp concl cov-bindings param-bindings
                          ctrex-info nexamples run-after-cases erp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (er-progn
   (sim-param-coverage-ok hyp param-hyp param-bindings cov-bindings
                          nexamples erp state)
   (sim-params param-bindings param-hyp concl ctrex-info nexamples
               run-after-cases state)))

(defmacro sim-param-thm
  (&key hyp param-hyp concl cov-bindings param-bindings ctrex-term
        (nexamples '3) run-after-cases (erp 't))
  `(sim-param-thm-fn ',hyp ',param-hyp ',concl ,cov-bindings ,param-bindings
                     ',ctrex-term ,nexamples ',run-after-cases ,erp state))
