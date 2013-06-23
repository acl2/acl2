
(in-package "GL")

(include-book "gl-generic-interp-defs")

(include-book "misc/untranslate-patterns" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/decomp-hint" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)

(local (include-book "general-object-thms"))
(local (include-book "tools/with-quoted-forms" :dir :system))
(local (include-book "hyp-fix-logic"))
(local (in-theory (disable* sets::double-containment
                            w)))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(flag::make-flag sublis-into-term-flg sublis-into-term)

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
;;             (equal (glcp-generic-geval-ev (sublis-into-term x subst) alist)
;;                    (glcp-generic-geval-ev x (append subst alist))))
;;    :name sublis-into-term-correct)
;;   (sublis-into-list
;;    (implies (pseudo-term-listp x)
;;             (equal (glcp-generic-geval-ev-lst (sublis-into-list x subst) alist)
;;                    (glcp-generic-geval-ev-lst x (append subst alist))))
;;    :name sublis-into-list-correct)
;;   :hints (("goal" :induct (sublis-into-term-flg flag x alist))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable glcp-generic-geval-ev-constraint-0)))))

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
                                                        args))))))))


(local
 (defthmd gl-eval-of-atom
   (implies (atom x)
            (equal (generic-geval x env) x))
   :hints (("goal" :in-theory (enable tag)
            :expand ((generic-geval x env))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(set-state-ok t)



(defsection glcp-generic-geval

  (local (in-theory (enable glcp-generic-geval)))

  (defthm glcp-generic-geval-atom
    (implies (atom x)
             (equal (glcp-generic-geval x env) x))
    :hints(("Goal" :in-theory (enable gl-eval-of-atom)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (acl2::def-functional-instance
   glcp-generic-geval-mk-g-boolean-correct
   mk-g-boolean-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list))
   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                              (glcp-generic-geval-apply))
             :expand ((glcp-generic-geval x env)
                      (glcp-generic-geval-list x env)))))


  (acl2::def-functional-instance
   glcp-generic-geval-gobj-ite-merge-correct
   gobj-ite-merge-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-gtests-nonnil-correct
   gtests-nonnil-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (in-theory (disable glcp-generic-geval-gtests-nonnil-correct))

  (acl2::def-functional-instance
   glcp-generic-geval-gtests-obj-correct
   gtests-obj-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-mk-g-ite-correct
   mk-g-ite-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-mk-g-concrete-correct
   mk-g-concrete-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-g-concrete-quote-correct
   g-concrete-quote-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-general-concrete-obj-correct
   general-concrete-obj-correct
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))


  (acl2::def-functional-instance
   glcp-generic-geval-of-gl-cons
   generic-geval-gl-cons
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-g-apply
   generic-geval-g-apply
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list)))

  (acl2::def-functional-instance
   glcp-generic-geval-alt-def
   generic-geval-alt-def
   ((generic-geval-ev glcp-generic-geval-ev)
    (generic-geval-ev-lst glcp-generic-geval-ev-lst)
    (generic-geval glcp-generic-geval)
    (generic-geval-list glcp-generic-geval-list))
   ;; :do-not-induct
   ;;   t
   ;;   :expand ((glcp-generic-geval x env))))
   :rule-classes ((:definition :clique (glcp-generic-geval))))

  (in-theory (disable glcp-generic-geval-alt-def)))





(local (in-theory (enable glcp-generic-geval-gtests-nonnil-correct)))

(defsection glcp-generic-geval-list

  (local (in-theory (enable glcp-generic-geval-list)))

  (defthm glcp-generic-geval-list-of-cons
    (equal (glcp-generic-geval-list (cons a b) env)
           (cons (glcp-generic-geval a env)
                 (glcp-generic-geval-list b env))))

  (defthm glcp-generic-geval-list-of-atom
    (implies (not (consp x))
             (equal (glcp-generic-geval-list x env) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm glcp-generic-geval-when-gobj-list
    (implies (gobj-listp x)
             (equal (glcp-generic-geval x env)
                    (glcp-generic-geval-list x env)))
    :hints (("goal" :induct (gobj-listp x)
             :in-theory (enable gobj-listp))
            '(:use ((:instance glcp-generic-geval-of-gl-cons
                     (x (car x)) (y (cdr x))))
              :in-theory (enable gl-cons gobj-listp))))

  (defthm glcp-generic-geval-list-of-gl-cons
    (equal (glcp-generic-geval-list (gl-cons x y) env)
           (cons (glcp-generic-geval x env)
                 (glcp-generic-geval-list y env)))
    :hints(("Goal" :in-theory (e/d (gl-cons) (glcp-generic-geval-alt-def
                                              glcp-generic-geval-general-concrete-obj-correct))
            :expand ((:with glcp-generic-geval (glcp-generic-geval x env))
                     (:with glcp-generic-geval (glcp-generic-geval (g-concrete
                                                                    x)
                                                                   env))))))

  (defthm len-of-glcp-generic-geval-list
    (equal (len (glcp-generic-geval-list x env))
           (len x))))

;; (defun univ-run-gified-guard-wrapper (fn actuals hyp clk state)
;;   (declare (xargs :guard (and (symbolp fn)
;;                               (gobject-listp actuals)
;;                               (bfr-p hyp)
;;                               (natp clk))
;;                   :stobjs state))
;;   (ec-call (univ-run-gified fn actuals hyp clk state)))

;; (defun glcp-generic-apply-concrete-guard-wrapper
;;   (fn actuals state)
;;   (declare (xargs :guard (true-listp actuals)
;;                   :stobjs state))
;;   (ec-call (glcp-generic-apply-concrete fn actuals state)))


(local
 (progn
   ;; (defun-nx glcp-generic-geval-lst (x env)
   ;;   (if (atom x)
   ;;       nil
   ;;     (cons (glcp-generic-geval (car x) env)
   ;;           (glcp-generic-geval-lst (cdr x) env))))

   ;; (defthmd glcp-generic-geval-of-gobj-list
   ;;   (implies (gobj-listp x)
   ;;            (equal (glcp-generic-geval x env)
   ;;                   (glcp-generic-geval-lst x env)))
   ;;   :hints
   ;;   (("goal" :induct (gobject-listp x)
   ;;     :in-theory (enable gobject-listp-impl-gobjectp
   ;;                        glcp-generic-geval-of-gobject-car
   ;;                        gobject-listp))))






   (defthm nonnil-symbol-listp-impl-eqlable-listp
     (implies (nonnil-symbol-listp x)
              (eqlable-listp x))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))




   ;; (defthm univ-run-gified-wrapper-unwrap
   ;;   (equal (univ-run-gified-guard-wrapper fn actuals hyp clk state)
   ;;          (univ-run-gified fn actuals hyp clk state)))




   ;; (defthm glcp-generic-apply-concrete-wrapper-unwrap
   ;;   (equal (glcp-generic-apply-concrete-guard-wrapper fn actuals state)
   ;;          (glcp-generic-apply-concrete fn actuals state)))

   ;; (in-theory (disable univ-run-gified-guard-wrapper 
   ;;                     ;; glcp-generic-apply-concrete-guard-wrapper
   ;;                     ))
   ))









;; (defun gobject-vals-alistp (x)
;;   (declare (Xargs :guard t))
;;   (if (atom x)
;;       (equal x nil)
;;     (and (or (atom (car x))
;;              (gobjectp (cdar x)))
;;          (gobject-vals-alistp (cdr x)))))


;; (defthm lookup-in-gobject-vals-alistp
;;   (implies (gobject-vals-alistp x)
;;            (gobjectp (cdr (hons-assoc-equal k x)))))

;; (defthm gobject-vals-alistp-pairlis$
;;   (implies (gobject-listp vals)
;;            (gobject-vals-alistp (pairlis$ keys vals)))
;;   :hints(("Goal" :in-theory (enable gobject-listp
;;                                     pairlis$))))




(local (in-theory (disable* general-concretep-def acl2-count
;                            sets::double-containment
                            integer-abs 
;                            sets::nonempty-means-set
                            equal-of-booleans-rewrite
                            put-global
                            acl2::true-list-listp-forward-to-true-listp-assoc-equal)))




;; (defthmd gobject-listp-true-listp
;;   (implies (gobject-listp x)
;;            (true-listp x))
;;   :hints(("Goal" :in-theory (enable gobject-listp)))
;;   :rule-classes (:rewrite :forward-chaining))

;; (defthm glcp-generic-geval-of-gobj-list
;;   (implies (and (gobj-listp x)
;;                 (consp x))
;;            (equal (glcp-generic-geval x env)
;;                   (cons (glcp-generic-geval (car x) env)
;;                         (glcp-generic-geval (cdr x) env))))
;;   :hints(("Goal" :use ((:instance glcp-generic-geval-of-gl-cons
;;                         (x (car x)) (y (cdr x))))
;;           :in-theory (enable gl-cons gobj-listp))))


(defund glcp-generic-geval-alist (al env)
  (declare (xargs :guard (consp env)))
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al)
                    (glcp-generic-geval (cdar al)
                                        env))
              (glcp-generic-geval-alist (cdr al) env))
      (glcp-generic-geval-alist (cdr al) env))))

(local
 (defsection glcp-generic-geval-alist

   (local (in-theory (enable glcp-generic-geval-alist)))

   (defthm glcp-generic-geval-alist-pairlis$
     (implies (gobj-listp actuals)
              (equal (glcp-generic-geval-alist
                      (pairlis$ formals actuals)
                      env)
                     (pairlis$ formals
                               (glcp-generic-geval actuals env))))
     :hints(("Goal" :in-theory (enable default-cdr pairlis$ gobj-listp)
             :induct (pairlis$ formals actuals))))

   (defthm glcp-generic-geval-alist-lookup
     (equal (hons-assoc-equal k (glcp-generic-geval-alist al env))
            (and (hons-assoc-equal k al)
                 (cons k (glcp-generic-geval (cdr (hons-assoc-equal k al))
                                             env)))))

   (defthm glcp-generic-geval-alist-of-acons
     (equal (glcp-generic-geval-alist (cons (cons k v) al) env)
            (cons (cons k (glcp-generic-geval v env))
                  (glcp-generic-geval-alist al env))))))

           








(defsection all-keys-bound
  (defund all-keys-bound (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-assoc-equal (car keys) alist)
           (all-keys-bound (cdr keys) alist))))

  (local (in-theory (enable all-keys-bound)))

  (defthmd all-keys-bound-member-implies
    (implies (and (member k keys)
                  (not (hons-assoc-equal k alist)))
             (not (all-keys-bound keys alist))))

  (defthmd all-keys-bound-subset
    (implies (and (subsetp keys1 keys)
                  (all-keys-bound keys alist))
             (all-keys-bound keys1 alist))
    :hints(("Goal" :in-theory (enable all-keys-bound-member-implies
                                      subsetp))))

  (defcong acl2::set-equiv equal (all-keys-bound keys alist) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv)
            :use ((:instance all-keys-bound-subset
                   (keys1 keys) (keys acl2::keys-equiv))
                  (:instance all-keys-bound-subset
                   (keys1 acl2::keys-equiv) (keys keys)))
            :do-not-induct t)))

  (defthm all-keys-bound-append
    (equal (all-keys-bound (append a b) alist)
           (and (all-keys-bound a alist)
                (all-keys-bound b alist))))


  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-acons-when-all-vars-bound
      (implies (and (all-keys-bound (acl2::simple-term-vars x) a)
                    (not (hons-assoc-equal k a))
                    (pseudo-termp x))
               (equal (glcp-generic-geval-ev x (cons (cons k v) a))
                      (glcp-generic-geval-ev x a)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
      :flag acl2::simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-acons-when-all-vars-bound
      (implies (and (all-keys-bound (acl2::simple-term-vars-lst x) a)
                    (not (hons-assoc-equal k a))
                    (pseudo-term-listp x))
               (equal (glcp-generic-geval-ev-lst x (cons (cons k v) a))
                      (glcp-generic-geval-ev-lst x a)))
      :flag acl2::simple-term-vars-lst))

  (defthm all-keys-bound-of-glcp-generic-geval-alist
    (equal (all-keys-bound keys (glcp-generic-geval-alist alist env))
           (all-keys-bound keys alist))))


(defsection glcp-unify-concrete
  (local (defthm assoc-when-nonnil-key
           (implies key
                    (equal (assoc key alist)
                           (hons-assoc-equal key alist)))
           :rule-classes ((:rewrite :backchain-limit-lst 1))))

  (local (in-theory (enable glcp-unify-concrete)))

  (defthm glcp-unify-concrete-preserves-assoc
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (implies (and ok (hons-assoc-equal k alist))
               (equal (hons-assoc-equal k alist1)
                      (hons-assoc-equal k alist)))))

  (defthm alistp-glcp-unify-concrete
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (equal (alistp alist1)
             (or (not ok) (alistp alist)))))

    
  (defthm glcp-unify-concrete-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (local (defthm equal-len
           (implies (syntaxp (quotep y))
                    (Equal (equal (len x) y)
                           (if (zp y)
                               (and (equal y 0) (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- y))))))))

  (defthm all-keys-bound-of-glcp-unify-concrete
    (b* (((mv ok newalist) (glcp-unify-concrete pat x alist)))
      (implies ok
               (all-keys-bound (acl2::simple-term-vars pat) newalist)))
    :hints (("goal" :induct (glcp-unify-concrete pat x alist)
             :in-theory (enable all-keys-bound))))



  (defthm glcp-unify-concrete-preserves-eval
    (b* (((mv ok newalist) (glcp-unify-concrete pat x alist)))
      (implies (and ok
                    (pseudo-termp term)
                    (all-keys-bound (acl2::simple-term-vars term) alist))
               (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                   alist env))))))

  (defthmd glcp-unify-concrete-correct
    (b* (((mv ok alist)
          (glcp-unify-concrete pat x alist)))
      (implies (and ok
                    (pseudo-termp pat))
               (equal (glcp-generic-geval-ev pat
                                             (glcp-generic-geval-alist alist
                                                                       env))
                      x))))

  (local (defthm hons-assoc-equal-to-member-alist-keys
           (iff (hons-assoc-equal k a)
                (member k (acl2::alist-keys a)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal
                                             acl2::alist-keys)))))

  (local (defthm associativity-of-union-equal
           (equal (union-equal (union-equal a b) c)
                  (union-equal a (union-equal b c)))))

  ;; (defthm alist-keys-of-glcp-unify-concrete
  ;;   (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
  ;;     (implies ok
  ;;              (equal (acl2::alist-keys alist1)
  ;;                     (union-equal (acl2::simple-term-vars pat)
  ;;                                  (acl2::alist-keys alist)))))
  ;;   :hints(("Goal" :in-theory (enable acl2::alist-keys))))
  )

(defsection glcp-unify-term/gobj
  (local (in-theory (enable pseudo-termp)))
  (local (defthm assoc-when-nonnil-key
           (implies key
                    (equal (assoc key alist)
                           (hons-assoc-equal key alist)))
           :rule-classes ((:rewrite :backchain-limit-lst 1))))


  (local (in-theory (enable glcp-unify-term/gobj
                            glcp-unify-term/gobj-list)))

  (flag::make-flag glcp-unify-term/gobj-flg glcp-unify-term/gobj
                   :flag-mapping ((glcp-unify-term/gobj . term)
                                  (glcp-unify-term/gobj-list . list)))


  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-assoc
      (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
        (implies (and ok (hons-assoc-equal k alist))
                 (equal (hons-assoc-equal k alist1)
                        (hons-assoc-equal k alist))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-assoc
      (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok (hons-assoc-equal k alist))
                 (equal (hons-assoc-equal k alist1)
                        (hons-assoc-equal k alist))))
      :flag list))

  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-alistp
      (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
        (equal (alistp alist1)
               (or (not ok) (alistp alist))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-alistp
      (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
        (equal (alistp alist1)
               (or (not ok) (alistp alist))))
      :flag list))
    
  (defthm glcp-unify-term/gobj-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (defthm glcp-unify-term/gobj-list-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (local (defthm equal-len
           (implies (syntaxp (quotep y))
                    (Equal (equal (len x) y)
                           (if (zp y)
                               (and (equal y 0) (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- y))))))))

  (defthm-glcp-unify-term/gobj-flg
    (defthm all-keys-bound-of-glcp-unify-term/gobj
      (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
        (implies ok
                 (all-keys-bound (acl2::simple-term-vars pat) newalist)))
      :hints ('(:in-theory (enable all-keys-bound)))
      :flag term)
    (defthm all-keys-bound-of-glcp-unify-term/gobj-list
      (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
        (implies ok
                 (all-keys-bound (acl2::simple-term-vars-lst pat) newalist)))
      :hints ('(:in-theory (enable all-keys-bound)))
      :flag list))


  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-eval
      (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
        (implies (and ok
                      (pseudo-termp term)
                      (all-keys-bound (acl2::simple-term-vars term) alist))
                 (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     newalist env))
                        (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     alist env)))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-eval
      (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok
                      (pseudo-termp term)
                      (all-keys-bound (acl2::simple-term-vars term) alist))
                 (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     newalist env))
                        (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     alist env)))))
      :flag list))

  (defthm glcp-unify-term/gobj-preserves-eval-list
    (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
      (implies (and ok
                    (pseudo-term-listp term)
                    (all-keys-bound (acl2::simple-term-vars-lst term) alist))
               (equal (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                       alist env)))))
    :hints (("goal" :induct (len term)
             :in-theory (e/d () (glcp-unify-term/gobj)))))

  (defthm glcp-unify-term/gobj-list-preserves-eval-list
    (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
      (implies (and ok
                    (pseudo-term-listp term)
                    (all-keys-bound (acl2::simple-term-vars-lst term) alist))
               (equal (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                       alist env)))))
    :hints (("goal" :induct (len term)
             :in-theory (e/d () (glcp-unify-term/gobj-list)))))

  (local (defthm glcp-generic-geval-of-non-kw-cons
           (implies (and (consp x)
                         (not (equal (tag x) :g-concrete))
                         (not (equal (tag x) :g-boolean))
                         (not (equal (tag x) :g-number))
                         (not (equal (tag x) :g-ite))
                         (not (equal (tag x) :g-var))
                         (not (equal (tag x) :g-apply)))
                    (equal (glcp-generic-geval x env)
                           (cons (glcp-generic-geval (car x) env)
                                 (glcp-generic-geval (cdr x) env))))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-non-kw-symbolp
           (implies (and (consp x)
                         (not (g-keyword-symbolp (tag x))))
                    (equal (glcp-generic-geval x env)
                           (cons (glcp-generic-geval (car x) env)
                                 (glcp-generic-geval (cdr x) env))))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-g-apply
           (implies (and (eq (tag x) :g-apply)
                         (not (equal (g-apply->fn x) 'quote)))
                    (equal (glcp-generic-geval x env)
                           (glcp-generic-geval-ev
                            (cons (g-apply->fn x)
                                  (kwote-lst (glcp-generic-geval-list
                                              (g-apply->args x) env)))
                            nil)))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-g-concrete
           (implies (eq (tag x) :g-concrete)
                    (equal (glcp-generic-geval x env)
                           (g-concrete->obj x)))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (in-theory (enable glcp-generic-geval-ev-of-fncall-args)))

  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-correct
      (b* (((mv ok alist)
            (glcp-unify-term/gobj pat x alist)))
        (implies (and ok
                      (pseudo-termp pat))
                 (equal (glcp-generic-geval-ev pat
                                               (glcp-generic-geval-alist alist
                                                                         env))
                        (glcp-generic-geval x env))))
      :hints ((and stable-under-simplificationp
                   (b* (((mv ok lit)
                         (acl2::find-matching-literal-in-clause
                          '(not (mv-nth '0 (glcp-unify-concrete pat x alist)))
                          clause nil))
                        ((unless ok) nil)
                        (pat (second (third (second lit))))
                        (x (third (third (second lit))))
                        (alist (fourth (third (second lit)))))
                     `(:use ((:instance glcp-unify-concrete-correct
                              (pat ,pat) (x ,x) (alist ,alist)))))))
                     
                     
      :flag term)
    (defthm glcp-unify-term/gobj-list-correct
      (b* (((mv ok alist)
            (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok
                      (pseudo-term-listp pat))
                 (equal (glcp-generic-geval-ev-lst pat
                                                   (glcp-generic-geval-alist alist
                                                                             env))
                        (glcp-generic-geval-list x env))))
      :flag list)))

;; (defsection rune
;;   (definlined rune->thmname (rune)
;;     (declare (xargs :guard (symbol-listp rune)))
;;     (mbe :logic (and (symbol-listp rune) (cadr rune))
;;          :exec (cadr rune)))

;;   (local (in-theory (enable rune->thmname)))
  
;;   (defthm symbolp-of-rune->thmname
;;     (symbolp (rune->thmname rune))))



(defsection glcp-relieve-hyp-synp
  (local (in-theory (enable glcp-relieve-hyp-synp)))

  (defthm glcp-relieve-hyp-synp-bindings
    (b* (((mv ?erp ?successp ?bindings1)
          (glcp-relieve-hyp-synp hyp bindings state)))
      (equal bindings1
             (and (not erp) bindings))))

  (defthm glcp-relieve-hyp-synp-correct
    (b* (((mv ?erp ?successp ?bindings1)
          (glcp-relieve-hyp-synp hyp bindings st)))
      (implies (and successp
                    (consp hyp)
                    (eq (car hyp) 'synp)
                    (glcp-generic-geval-ev-meta-extract-global-facts)
                    (equal (w state) (w st)))
               (glcp-generic-geval-ev hyp (glcp-generic-geval-alist bindings env))))))

(defsection glcp-interp-args-split-ite-cond
  (local (in-theory (enable glcp-interp-args-split-ite-cond)))

  (defthm glcp-interp-args-split-ite-cond-correct-list
    (b* (((mv then else)
          (glcp-interp-args-split-ite-cond test args)))
      (implies (gobj-listp args)
               (and (implies (glcp-generic-geval test env)
                             (equal (glcp-generic-geval-list then env)
                                    (glcp-generic-geval-list args env)))
                    (implies (not (glcp-generic-geval test env))
                             (equal (glcp-generic-geval-list else env)
                                    (glcp-generic-geval-list args env))))))
    :hints (("goal" :induct (glcp-interp-args-split-ite-cond test args)
             :expand ((glcp-generic-geval-list args env)
                      (gobj-listp args)
                      (:with glcp-generic-geval (glcp-generic-geval (car args)
                                                                    env))))))

  (defthm gobj-listp-glcp-interp-args-split-ite-cond
    (b* (((mv then else)
          (glcp-interp-args-split-ite-cond test args)))
      (and (gobj-listp then)
           (gobj-listp else)))
    :hints(("Goal" :in-theory (enable gobj-listp))))

  (defthm glcp-interp-args-split-ite-cond-correct
    (b* (((mv then else)
          (glcp-interp-args-split-ite-cond test args)))
      (implies (gobj-listp args)
               (and (implies (glcp-generic-geval test env)
                             (equal (glcp-generic-geval then env)
                                    (glcp-generic-geval args env)))
                    (implies (not (glcp-generic-geval test env))
                             (equal (glcp-generic-geval else env)
                                    (glcp-generic-geval args env))))))))

(defsection glcp-interp-args-split-ite
  (local (in-theory (enable glcp-interp-args-split-ite)))

  (defthm glcp-interp-args-split-ite-correct-list
    (b* (((mv has-ite test then else)
          (glcp-interp-args-split-ite args)))
      (implies (and (gobj-listp args)
                    has-ite)
               (and (implies (glcp-generic-geval test env)
                             (equal (glcp-generic-geval-list then env)
                                    (glcp-generic-geval-list args env)))
                    (implies (not (glcp-generic-geval test env))
                             (equal (glcp-generic-geval-list else env)
                                    (glcp-generic-geval-list args env))))))
    :hints (("goal"
             :induct (glcp-interp-args-split-ite args)
             :expand ((glcp-generic-geval-list args env)
                      (gobj-listp args)
                      (:with glcp-generic-geval (glcp-generic-geval (car args)
                                                                    env))))))

  (defthm gobj-listp-glcp-interp-args-split-ite
    (b* (((mv ?has-if ?test then else)
          (glcp-interp-args-split-ite args)))
      (and (gobj-listp then)
           (gobj-listp else)))
    :hints(("Goal" :in-theory (enable gobj-listp))))

  (defthm glcp-interp-args-split-ite-correct
    (b* (((mv has-ite test then else)
          (glcp-interp-args-split-ite args)))
      (implies (and (gobj-listp args)
                    has-ite)
               (and (implies (glcp-generic-geval test env)
                             (equal (glcp-generic-geval then env)
                                    (glcp-generic-geval args env)))
                    (implies (not (glcp-generic-geval test env))
                             (equal (glcp-generic-geval else env)
                                    (glcp-generic-geval args env))))))))
               
    

(defsection gl-term-to-apply-obj
  (local (defthm assoc-is-hons-assoc
           (implies k
                    (equal (assoc k alist)
                           (hons-assoc-equal k alist)))))

  (local (defthm glcp-generic-geval-of-car-of-gl-cons
           (equal (glcp-generic-geval (car (gl-cons x y)) env)
                  (glcp-generic-geval x env))
           :hints(("Goal" :in-theory (enable gl-cons glcp-generic-geval)))))

  (defthm cdr-of-gl-cons
    (equal (cdr (gl-cons x y)) y)
    :hints(("Goal" :in-theory (enable gl-cons))))


  (defthm-gl-term-to-apply-obj-flag
    (defthm gobj-listp-of-gl-termlist-to-apply-obj-list
      (gobj-listp (gl-termlist-to-apply-obj-list x alist))
      :hints ('(:expand ((gl-termlist-to-apply-obj-list x alist))))
      :flag gl-termlist-to-apply-obj-list)
    :skip-others t)

  (defthm-gl-term-to-apply-obj-flag
    (defthm gl-term-to-apply-obj-correct
      (implies (pseudo-termp x)
               (equal (glcp-generic-geval (gl-term-to-apply-obj x alist) env)
                      (glcp-generic-geval-ev x (glcp-generic-geval-alist alist env))))
      :hints ('(:expand ((gl-term-to-apply-obj nil alist)
                         (gl-term-to-apply-obj x alist)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (glcp-generic-geval-ev-of-fncall-args)
                                     ((g-ite)))))
              (and stable-under-simplificationp
                   '(:expand ((gl-termlist-to-apply-obj-list (cdr x) alist)
                              (gl-termlist-to-apply-obj-list (cddr x) alist)
                              (gl-termlist-to-apply-obj-list (cdddr x) alist)
                              (gl-termlist-to-apply-obj-list (cddddr x) alist)
                              (gl-termlist-to-apply-obj-list nil alist)
                              (:free (x y z)
                               (:with glcp-generic-geval
                                (glcp-generic-geval (g-ite x y z) env)))))))
      :flag gl-term-to-apply-obj)
    (defthm gl-termlist-to-apply-obj-list-correct
      (implies (pseudo-term-listp x)
               (equal (glcp-generic-geval (gl-termlist-to-apply-obj-list x alist) env)
                      (glcp-generic-geval-ev-lst x (glcp-generic-geval-alist alist env))))
      :hints ('(:expand ((gl-termlist-to-apply-obj-list x alist)
                         (gl-termlist-to-apply-obj-list nil alist))))
      :flag gl-termlist-to-apply-obj-list)))



(in-theory (disable glcp-generic-interp-term
                    glcp-generic-interp-if
                    glcp-generic-interp-fncall-ifs
                    glcp-generic-interp-fncall
                    glcp-generic-rewrite-fncall
                    glcp-generic-rewrite-fncall-apply-rules
                    glcp-generic-rewrite-fncall-apply-rule
                    glcp-generic-relieve-hyps
                    glcp-generic-relieve-hyp
                    glcp-generic-interp-list))

(flag::make-flag glcp-generic-interp-flg
                 glcp-generic-interp-term
                 :flag-mapping
                 ((glcp-generic-interp-term . term)
                  (glcp-generic-interp-if . if)
                  (glcp-generic-interp-fncall-ifs . fncall-ifs)
                  (glcp-generic-interp-fncall . fncall)
                  (glcp-generic-rewrite-fncall . rewrite)
                  (glcp-generic-rewrite-fncall-apply-rules . rules)
                  (glcp-generic-rewrite-fncall-apply-rule . rule)
                  (glcp-generic-relieve-hyps . hyps)
                  (glcp-generic-relieve-hyp . hyp)
                  (glcp-generic-interp-list . list))
                 :hints (("goal" :in-theory
                          (e/d (acl2-count
                                acl2-count-last-cdr-when-cadr-hack)
                               (last)))))

(local
 (defthm assoc-in-add-pair
   (implies (not (equal k1 k2))
            (equal (assoc k1 (add-pair k2 v a))
                   (assoc k1 a)))))


(defthm w-of-put-global
  (implies (not (eq var 'current-acl2-world))
           (equal (w (put-global var val state))
                  (w state)))
  :hints(("Goal" :in-theory (enable w put-global add-pair))))

(local (in-theory (disable w)))



(defun def-glcp-interp-thm-body (binder basename kws flag)
  (declare (xargs :mode :program))
  (b* ((fn-kws (cdr (assoc flag (cadr (assoc-keyword :special kws)))))
       (body (or (cadr (assoc-keyword :body fn-kws))
                 (cadr (assoc-keyword :body kws))))
       (hyps (or (cadr (assoc-keyword :hyps fn-kws))
                 (cadr (assoc-keyword :hyps kws))))
       (add-hyps (cadr (assoc-keyword :add-hyps fn-kws)))
       (full-hyps (if hyps
                      (if add-hyps `(and ,hyps ,add-hyps) hyps)
                    add-hyps))
       (full-body (if full-hyps
                      `(implies ,full-hyps ,body)
                    body)))
    `(defthm ,(or (cadr (assoc-keyword :name fn-kws))
                  (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name basename) "-" (symbol-name flag))
                   basename))
       (b* (,binder)
         ,full-body)
       :hints (,@(let ((fn-expand-look (assoc-keyword :expand-call fn-kws)))
                   (and (or (and (cadr (assoc-keyword :expand-calls kws))
                                 (not (and fn-expand-look
                                           (not (cadr fn-expand-look)))))
                            (cadr fn-expand-look))
                        `((acl2::just-expand (,(cadr binder)))
                          '(:do-not nil))))
                 ,@(cadr (assoc-keyword :hints fn-kws)))
       :rule-classes ,(or (cadr (assoc-keyword :rule-classes fn-kws))
                          (cadr (assoc-keyword :rule-classes kws))
                          :rewrite)
       :flag ,flag)))

(defun def-glcp-interp-thm-fn (basename keys)
  (declare (xargs :mode :program))
  `(defthm-glcp-generic-interp-flg
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?val ?state1)
          (glcp-generic-interp-term x alist pathcond clk obligs config state))
        basename keys 'term)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?val ?state1)
          (glcp-generic-interp-if test tbr fbr alist pathcond clk obligs config state))
        basename keys 'if)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?val ?state1)
          (glcp-generic-interp-fncall-ifs fn actuals x pathcond clk obligs config state))
        basename keys 'fncall-ifs)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?val ?state1)
          (glcp-generic-interp-fncall fn actuals x pathcond clk obligs config state))
        basename keys 'fncall)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
          (glcp-generic-rewrite-fncall fn actuals pathcond clk obligs config
                                       state))
        basename keys 'rewrite)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
          (glcp-generic-rewrite-fncall-apply-rules
           fn-rewrites rules fn actuals pathcond clk obligs config state))
        basename keys 'rules)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
          (glcp-generic-rewrite-fncall-apply-rule
           rule fn actuals pathcond clk obligs config state))
        basename keys 'rule)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?successp ?bindings1 ?state1)
          (glcp-generic-relieve-hyps
           hyps bindings pathcond clk obligs config state))
        basename keys 'hyps)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?successp ?bindings1 ?state1)
          (glcp-generic-relieve-hyp
           hyp bindings pathcond clk obligs config state))
        basename keys 'hyp)
     ,(def-glcp-interp-thm-body
        '((mv ?erp ?obligs1 ?vals ?state1)
          (glcp-generic-interp-list x alist pathcond clk obligs config state))
        basename keys 'list)
     :hints (,@(and (cadr (assoc-keyword :expand-calls keys))
                    `(("Goal" :do-not '(simplify preprocess))
                      '(:do-not '(simplify preprocess))))
               ,@(cadr (assoc-keyword :hints keys)))))

(defmacro def-glcp-interp-thm (basename &rest keys)
  (def-glcp-interp-thm-fn basename keys))

         





(def-glcp-interp-thm glcp-generic-interp-w-state-preserved
  :body (equal (w state1) (w state))
  :expand-calls t)



(local
 (defthm-glcp-generic-interp-flg
   (defthm alistp-glcp-generic-rewrite-fncall
     (b* (((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
           (glcp-generic-rewrite-fncall fn actuals pathcond clk obligs config
                                        state)))
       (alistp bindings))
     :hints ('(:expand ((glcp-generic-rewrite-fncall fn actuals pathcond clk obligs config
                                                     state))))
     :flag rewrite)
   (defthm alistp-glcp-generic-apply-rules
     (b* (((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
           (glcp-generic-rewrite-fncall-apply-rules
            fn-rewrites rules fn actuals pathcond clk obligs config state)))
       (alistp bindings))
     :hints ('(:expand ((glcp-generic-rewrite-fncall-apply-rules
                         fn-rewrites rules fn actuals pathcond clk obligs config state))))
     :flag rules)
   (defthm alistp-glcp-generic-apply-rule
     (b* (((mv ?erp ?obligs1 ?successp ?term ?bindings ?state1)
           (glcp-generic-rewrite-fncall-apply-rule
            rule fn actuals pathcond clk obligs config state)))
       (alistp bindings))
     :hints ('(:expand ((:free (fn)
                         (glcp-generic-rewrite-fncall-apply-rule
                          rule fn actuals pathcond clk obligs config state)))))
     :flag rule)
   (defthm alistp-glcp-generic-relieve-hyps
     (b* (((mv ?erp ?obligs1 ?successp ?bindings1 ?state1)
           (glcp-generic-relieve-hyps
            hyps bindings pathcond clk obligs config state)))
       (equal bindings1
              (if erp nil bindings)))
     :hints ('(:expand ((glcp-generic-relieve-hyps
                         hyps bindings pathcond clk obligs config state))))
     :flag hyps)
   (defthm alistp-glcp-generic-relieve-hyp
     (b* (((mv ?erp ?obligs1 ?successp ?bindings1 ?state1)
           (glcp-generic-relieve-hyp
            hyp bindings pathcond clk obligs config state)))
       (equal bindings1
              (if erp nil bindings)))
     :hints ('(:expand ((glcp-generic-relieve-hyp
                         hyp bindings pathcond clk obligs config state))))
     :flag hyp)
   :skip-others t))
   

   ;; (defthm-glcp-generic-interp-flg
   ;;   (defthm gobjectp-glcp-generic-interp-term
   ;;    (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
   ;;                  (equal (w st) (w state))
   ;;                  (sym-counterparts-ok (w st))
   ;;                  (bfr-p hyp)
   ;;                  (not (mv-nth 0 (glcp-generic-interp-term
   ;;                                  x alist pathcond clk obligs config st))))
   ;;             (gobjectp (mv-nth 2 (glcp-generic-interp-term
   ;;                                  x alist pathcond clk obligs config st))))
   ;;    :flag glcp-generic-interp-term)

   ;;   (defthm gobject-listp-glcp-generic-interp-list
   ;;    (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
   ;;                  (equal (w st) (w state))
   ;;                  (sym-counterparts-ok (w st))
   ;;                  (bfr-p hyp)
   ;;                  (not (mv-nth 0 (glcp-generic-interp-list
   ;;                                  x alist pathcond clk obligs config st))))
   ;;             (gobject-listp (mv-nth 2 (glcp-generic-interp-list
   ;;                                       x alist pathcond clk obligs config st))))
   ;;    :flag glcp-generic-interp-list)
   ;;   :hints (("goal" :induct (glcp-generic-interp-flg flag x alist pathcond clk obligs config st)
   ;;            :expand ((glcp-generic-interp-term x alist pathcond clk obligs config st)
   ;;                     (glcp-generic-interp-list x alist pathcond clk obligs config st)
   ;;                     (glcp-generic-interp-term nil alist pathcond clk obligs config st)
   ;;                     (glcp-generic-interp-list nil alist pathcond clk obligs config st)
   ;;                     (gobject-listp nil)
   ;;                     (:free (a b) (gobject-listp (cons a b))))
   ;;            :in-theory (e/d** ( ;; gobjectp-gobj-ite-merge
   ;;                               ;;                               gobjectp-cons
   ;;                               ;;                               gtests-wfp
   ;;                               ;;                               bfr-p-of-bfr-and
   ;;                               ;;                               bfr-p-of-bfr-not
   ;;                               ;;                               bfr-p-of-bfr-or
   ;;                               ;;                               hyp-fix-bfr-p
   ;;                               ;;                               (gobjectp)
   ;;                               gobjectp-g-apply
   ;;                               gobjectp-gobj-fix
   ;;                               gtests-wfp
   ;;                               gobjectp-cons
   ;;                               bfr-p-bfr-binary-and
   ;;                               bfr-p-bfr-not
   ;;                               bfr-p-bfr-binary-or
   ;;                               gobjectp-mk-g-concrete
   ;;                               gobjectp-g-concrete-quote
   ;;                               hyp-fix-bfr-p
   ;;                               glcp-generic-interp-list-w-state-preserved
   ;;                               glcp-generic-interp-term-w-state-preserved
   ;;                               gl-aside gl-ignore gl-error-is-nil
   ;;                               gobjectp-of-atomic-constants
   ;;                               gobjectp-gobj-ite-merge
   ;;                               gobjectp-mk-g-ite
   ;;                               gobjectp-mk-g-boolean
   ;;                               car-cons cdr-cons (bfr-p)
   ;;                               glcp-interp-error
   ;;                               glcp-generic-interp-flg-equivalences
   ;;                               (:induction glcp-generic-interp-flg)
   ;;                               booleanp-compound-recognizer
   ;;                               bfr-p-bfr-binary-or
   ;;                               gobjectp-mk-g-boolean
   ;;                               (g-keyword-symbolp)))
   ;;            :do-not-induct t)))



(progn

  (defthm pseudo-termp-car
    (implies (pseudo-term-listp x)
             (pseudo-termp (car x))))

  (defthm pseudo-term-listp-cdr
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (cdr x))))

  (defthm pseudo-term-listp-cdr-pseudo-term
    (implies (and (pseudo-termp x)
                  (consp x)
                  (not (equal (car x) 'quote)))
             (pseudo-term-listp (cdr x))))

  (defthm pseudo-termp-symbolp-car-x
    (implies (and (pseudo-termp x)
                  (not (consp (car x))))
             (symbolp (car x))))

  (defthm pseudo-termp-lambda-body
    (implies (and (pseudo-termp x)
                  (consp (car x)))
             (pseudo-termp (caddar x))))
  
  (defthm pseudo-termp-car-last-of-pseudo-term-listp
    (implies (pseudo-term-listp x)
             (pseudo-termp (car (last x)))))

  (defthm pseudo-termp-car-last
    (implies (and (pseudo-termp x)
                  (< 1 (len x))
                  (not (equal (car x) 'quote)))
             (pseudo-termp (car (last x))))
    :hints(("Goal" :expand ((pseudo-termp x))
            :in-theory (enable pseudo-termp-car-last-of-pseudo-term-listp)))))



(encapsulate nil
  (local (in-theory (disable 
                     sets::sets-are-true-lists
                     pseudo-term-listp
                     (:t hyp-fix)
                     (:t acl2::interp-defs-alistp)
                     (:t pseudo-termp)
                     (:t glcp-generic-interp-term)
                     (:t gtests)
                     (:t pseudo-term-listp)
                     (:t general-concrete-listp)
                     (:t len)
                     (:t glcp-generic-rewrite-fncall)
                     (:t glcp-generic-interp-list)
                     (:t acl2::interp-function-lookup)
                     general-concrete-listp
                     general-concrete-obj-list
                     not
                     true-listp
                     hyp-fix-of-hyp-fixedp
                     pseudo-termp)))
  (def-glcp-interp-thm glcp-generic-interp-obligs-okp
    :hyps (and (acl2::interp-defs-alistp obligs)
               (acl2::interp-defs-alistp (glcp-config->overrides config))
               (not erp))
    :body (acl2::interp-defs-alistp obligs1)
    :special
    ((term :add-hyps (pseudo-termp x))
     (if :add-hyps (and (pseudo-termp test)
                        (pseudo-termp tbr)
                        (pseudo-termp fbr)))
     (list :add-hyps (pseudo-term-listp x))
     (hyp :add-hyps (pseudo-termp hyp))
     (hyps :add-hyps (pseudo-term-listp hyps))
     (fncall-ifs :add-hyps (and (symbolp fn)
                                (not (eq fn 'quote))))
     (fncall :add-hyps (and (symbolp fn)
                            (not (eq fn 'quote))))
     (rewrite :body (implies (and (symbolp fn)
                                  (not (eq fn 'quote)))
                             (and (acl2::interp-defs-alistp obligs1)
                                  (pseudo-termp term))))
     (rules :body (implies (and (symbolp fn)
                                (not (eq fn 'quote)))
                           (and (acl2::interp-defs-alistp obligs1)
                                (pseudo-termp term))))
     (rule :body (implies (and (symbolp fn)
                               (not (eq fn 'quote)))
                          (and (acl2::interp-defs-alistp obligs1)
                               (pseudo-termp term)))))
    :expand-calls t))




(local
 (defthm-glcp-generic-interp-flg
   (defthm true-listp-glcp-generic-interp-list
     (true-listp (mv-nth 2 (glcp-generic-interp-list
                            x alist pathcond clk obligs config state)))
     :hints('(:expand (glcp-generic-interp-list
                       x alist pathcond clk obligs config state)
              :in-theory (enable gl-cons)))
     :rule-classes :type-prescription
     :flag list)
   :skip-others t))


(local (include-book "system/f-put-global" :dir :system))

(encapsulate nil
  (local (in-theory (disable* pseudo-termp
                              symbol-listp
                              hyp-fix-of-hyp-fixedp
                              state-p-implies-and-forward-to-state-p1
                              (:rules-of-class :type-prescription :here))))
  (def-glcp-interp-thm glcp-generic-interp-state-p1-preserved
    :body (implies (state-p1 state)
                   (state-p1 state1))
    
    :expand-calls t))


(local
 (defthm true-listp-gl-cons
   (equal (true-listp (gl-cons x y))
          (true-listp y))
   :hints(("Goal" :in-theory (enable gl-cons)))))


(local
 (defthm-glcp-generic-interp-flg
   (defthm gobj-listp-glcp-generic-interp-list
     (gobj-listp (mv-nth 2 (glcp-generic-interp-list
                            x alist pathcond clk obligs config state)))
     :hints ('(:expand
               ((glcp-generic-interp-list
                 x alist pathcond clk obligs config state))))
     :flag list)
   :skip-others t))


(local
 (defthm consp-last
   (equal (consp (last x))
          (consp x))))



(set-ignore-ok t)

(defthm plist-worldp-of-w-state
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :hints(("Goal" :in-theory (e/d (state-p1 get-global w)
                                 (all-boundp)))))

;; (defun get-guard-verification-theorem (name state)
;;   (declare (xargs :mode :program
;;                   :stobjs state))
;;   (b* ((wrld (w state))
;;        (ctx 'get-guard-verification-theorem)
;;        ((er names) (acl2::chk-acceptable-verify-guards
;;                     name ctx wrld state))
;;        (ens (acl2::ens state))
;;        ((mv clauses & state)
;;         (acl2::guard-obligation-clauses
;;          names nil ens wrld state))
;;        (term (acl2::termify-clause-set clauses)))
;;     (value term)))


;; (local (defthm symbol-listp-implies-true-listp
;;          (implies (symbol-listp x)
;;                   (true-listp x))
;;          :rule-classes :forward-chaining))

(local (defthm nonnil-symbol-listp-true-listp
         (implies (nonnil-symbol-listp x)
                  (true-listp x))))

(local (defthm gobj-listp-impl-true-listp
         (implies (gobj-listp x)
                  (true-listp x))
         :hints(("Goal" :in-theory (enable gobj-listp)))
         :rule-classes :compound-recognizer))

(local (defthm pseudo-termp-impl-symbol-listp-lambda-formals
         (implies (and (pseudo-termp x)
                       (consp (car x)))
                  (symbol-listp (cadar x)))
         :hints(("Goal" :expand ((pseudo-termp x))))))


(local (defthm symbol-listp-impl-eqlable-listp
         (implies (symbol-listp x)
                  (eqlable-listp x))))

(local (defthm symbol-listp-impl-true-listp
         (implies (symbol-listp x)
                  (true-listp x))))

(local (defthm pseudo-termp-impl-len-lambda-formals
         (implies (and (pseudo-termp x)
                       (consp (car x)))
                  (equal (equal (len (cadar x)) (len (cdr x)))
                         t))
         :hints(("Goal" :expand ((pseudo-termp x))))))


(local
 (progn
  (defthm len-gl-cons
    (equal (len (gl-cons x y))
           (+ 1 (len y)))
    :hints(("Goal" :in-theory (enable gl-cons))))

  (defthm-glcp-generic-interp-flg
    (defthm len-of-glcp-generic-interp-list
      (mv-let (erp obligs res)
        (glcp-generic-interp-list
         x alist pathcond clk obligs config state)
        (declare (ignore obligs))
        (implies (not erp)
                 (equal (len res)
                        (len x))))
      :hints ('(:expand ((glcp-generic-interp-list
                          x alist pathcond clk obligs config state))))
      :flag list)
    :skip-others t)))

(make-event
 (b* (((er &) (in-theory nil))
      ((er thm) (get-guard-verification-theorem 'glcp-generic-interp-term state)))
   (value
    `(defthm glcp-generic-interp-guards-ok
       ,thm
       :hints (("goal" :in-theory
                (e/d* (pseudo-termp-car-last-of-pseudo-term-listp
                       gl-aside gl-ignore gl-error-is-nil)
                      (glcp-generic-interp-term
                       glcp-generic-interp-list
                       acl2::weak-rewrite-rule-p
                       consp-assoc-equal
                       pseudo-term-listp
                       w
                       nonnil-symbol-listp
                       true-listp symbol-listp
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
       :otf-flg t
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
    ((acl2::ifl-ev glcp-generic-geval-ev)
     (acl2::ifl-ev-lst glcp-generic-geval-ev-lst)
     (acl2::ifl-ev-falsify glcp-generic-geval-ev-falsify)
     (acl2::ifl-ev-meta-extract-global-badguy
      glcp-generic-geval-ev-meta-extract-global-badguy))
    :hints ((and stable-under-simplificationp
                 '(:use (glcp-generic-geval-ev-of-fncall-args
                         glcp-generic-geval-ev-falsify
                         glcp-generic-geval-ev-meta-extract-global-badguy)))))

   (acl2::def-functional-instance
    glcp-generic-interp-function-lookup-theoremp-defs-history
    acl2::interp-function-lookup-theoremp-defs-history
    ((acl2::ifl-ev glcp-generic-geval-ev)
     (acl2::ifl-ev-lst glcp-generic-geval-ev-lst)
     (acl2::ifl-ev-falsify glcp-generic-geval-ev-falsify)))



   (defthm glcp-generic-interp-function-lookup-theoremp-defs-history-rev
     (b* (((mv erp & & out-defs)
           (acl2::interp-function-lookup fn in-defs overrides world)))
       (implies (and (not (glcp-generic-geval-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses in-defs))))
                     (not erp))
                (not (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-defs)))))))))

(local (in-theory (disable acl2::interp-defs-alist-clauses)))

(encapsulate nil
  (local (in-theory (disable* (:rules-of-class :type-prescription :here)
                              pseudo-termp)))
  (def-glcp-interp-thm glcp-generic-interp-bad-obligs
    :hyps (and (not (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses obligs))))
               (not erp))
    :body (not (glcp-generic-geval-ev-theoremp
                (conjoin-clauses
                 (acl2::interp-defs-alist-clauses obligs1))))
    :expand-calls t))


(progn
  (defthm glcp-generic-interp-term-ok-obligs
    (implies (and (not (glcp-generic-geval-ev-theoremp
                        (conjoin-clauses
                         (acl2::interp-defs-alist-clauses obligs))))
                  (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses
                     (mv-nth 1 (glcp-generic-interp-term
                                x alist pathcond clk obligs config state))))))
             (mv-nth 0 (glcp-generic-interp-term
                        x alist pathcond clk obligs config state))))



  

  (defthm glcp-generic-obligs-okp-final-implies-start
    (implies (and (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses
                     (mv-nth 1 (glcp-generic-interp-term
                                x alist pathcond clk obligs config state)))))
                  (not (mv-nth 0 (glcp-generic-interp-term
                                  x alist pathcond clk obligs config state))))
             (glcp-generic-geval-ev-theoremp
              (conjoin-clauses
               (acl2::interp-defs-alist-clauses
                obligs))))
    :rule-classes :forward-chaining)


  (defthm assoc-eq-glcp-generic-geval-alist
    (implies (alistp alist)
             (equal (cdr (assoc-eq x (glcp-generic-geval-alist alist env)))
                    (glcp-generic-geval (cdr (hons-assoc-equal x alist))
                                        env)))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-alist
                                      hons-assoc-equal))))


  (defthm glcp-generic-geval-lst-general-concrete-obj-list
    (implies (and (general-concrete-listp x)
                  (gobj-listp x))
             (equal (glcp-generic-geval-list x env)
                    (general-concrete-obj-list x)))
    :hints(("Goal" :in-theory (e/d (gobj-listp) ()))))


  (defthm glcp-generic-geval-ev-nil
    (equal (glcp-generic-geval-ev nil a) nil))


  (defthm glcp-generic-geval-ev-meta-extract-rewrite-rule
    (implies (and (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (member rule (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state)))
                  (equal (w state) (w state0))
                  (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                  (glcp-generic-geval-ev (conjoin (acl2::rewrite-rule->hyps
                                                   rule))
                                         a)
                  (equal (acl2::rewrite-rule->equiv rule) 'equal))
             (equal (glcp-generic-geval-ev
                     (acl2::rewrite-rule->rhs rule) a)
                    (glcp-generic-geval-ev
                     (acl2::rewrite-rule->lhs rule) a)))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-meta-extract-lemma
                           (acl2::rule rule)
                           (acl2::fn fn)
                           (acl2::st state)
                           (state state0)))
             :in-theory (enable acl2::rewrite-rule->rhs
                                acl2::rewrite-rule->lhs
                                acl2::rewrite-rule->hyps
                                acl2::rewrite-rule->equiv
                                acl2::rewrite-rule->subclass)))))

;; (defthm glcp-generic-rewrite-fncall-apply-rule-correct
;;   (let* ((lhs (acl2::rewrite-rule->lhs rule))
;;          (fn (car lhs))
;;          (args (cdr lhs))
;;          (unify-subst (glcp-generic-geval-alist
;;                        (mv-nth 1 (glcp-unify-term/gobj-list
;;                                   args actuals nil))
;;                        env)))
;;     (implies (and (symbolp fn)
;;                   (not (eq fn 'quote))
;;                   (member rule (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state)))
;;                   (glcp-generic-geval-ev
;;                    (conjoin (acl2::rewrite-rule->hyps rule))
;;                    unify-subst)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (equal (w state0) (w state)))
;;              (equal (glcp-generic-geval-ev
;;                      (acl2::rewrite-rule->rhs rule)
;;                      unify-subst)
;;                     (glcp-generic-geval-ev
;;                      (cons fn (kwote-lst (glcp-generic-geval actuals env)))
;;                      nil))))
;;   :hints (("goal" 
                


(local (defthm true-listp-cdr-when-pseudo-termp
         (implies (pseudo-termp x)
                  (true-listp (cdr x)))
         :rule-classes :forward-chaining))

(progn
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
        hyp)))

    (defthmd gtests-known-and-true
      (implies (and (bfr-eval hyp (car env))
                    (equal (gtests-unknown (gtests gobj hyp)) nil)
                    (equal (glcp-generic-geval gobj env) nil))
               (not (equal (gtests-nonnil (gtests gobj hyp)) t)))
      :hints (("goal" :use ((:instance
                             geval-of-interp-res-hyp-fix-unknown-false
                             (interp-res gobj)))
               :in-theory (e/d (hyp-fix)
                               (geval-of-interp-res-hyp-fix-unknown-false))))))


  (defthm len-kwote-lst
    (equal (len (kwote-lst x))
           (len x)))

  (defthm glcp-generic-geval-ev-lst-kwote-lst
    (equal (glcp-generic-geval-ev-lst (kwote-lst args) a)
           (acl2::list-fix args)))

  (defcong acl2::list-equiv equal (pairlis$ x y) 2)

  (defthm glcp-generic-interp-function-lookup-correct-special
    (mv-let (erp body formals out-defs)
      (acl2::interp-function-lookup fn in-defs overrides (w state))
      (implies (and (not erp)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses out-defs)))
                    (acl2::interp-defs-alistp in-defs)
                    (acl2::interp-defs-alistp overrides)
                    (equal (len formals) (len actuals))
                    (not (eq fn 'quote))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                    (equal (w state) (w state1)))
               (equal (glcp-generic-geval-ev body (pairlis$ formals actuals))
                      (glcp-generic-geval-ev (cons fn (kwote-lst actuals))
                                             nil))))
    :hints (("goal" :use ((:instance
                           glcp-generic-interp-function-lookup-correct
                           (acl2::actuals (kwote-lst actuals))
                           (acl2::overrides overrides)
                           (acl2::fn fn)
                           (a nil)
                           (state state1)
                           (acl2::in-defs in-defs))))))

  (defthm glcp-generic-geval-ev-magic-ev-fncall-special
    (b* (((mv erp val)
          (acl2::magic-ev-fncall f args st t nil)))
      (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                    (equal (w st) (w state))
                    (not erp))
               (equal val
                      (glcp-generic-geval-ev (cons f (kwote-lst args)) nil))))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-ev-meta-extract-fncall))))

  (in-theory (disable glcp-generic-geval-ev-meta-extract-fncall)))

(encapsulate nil
  (local (in-theory (disable glcp-generic-interp-term-ok-obligs
                              (:type-prescription hyp-fix)
                              hyp-fix-of-hyp-fixedp
                              pseudo-termp
                              pseudo-term-listp
                              acl2::interp-defs-alist-clauses
                              general-concrete-listp
                              general-concrete-obj-list
                              acl2::weak-rewrite-rule-p
                              acl2::eval-bdd
                              hons-assoc-equal
                              kwote-lst)))

   (local (defthmd equal-len
            (implies (syntaxp (quotep y))
                     (Equal (equal (len x) y)
                            (if (zp y)
                                (and (equal y 0) (atom x))
                              (and (consp x)
                                   (equal (len (cdr x)) (1- y))))))))

   (local (in-theory (disable* glcp-generic-geval-ev-rules len default-car
                               default-cdr
                               alistp
                               no-duplicatesp-equal
                               member-equal
                               last nonnil-symbol-listp
                               fgetprop pairlis$ subsetp-equal
                               (:rules-of-class :type-prescription :here))))

   (local (defthm len-general-concrete-obj-list
            (equal (len (general-concrete-obj-list x))
                   (len x))
            :hints(("Goal" :in-theory (enable general-concrete-obj-list len)))))
   
   (def-glcp-interp-thm glcp-generic-interp-correct
     :hyps (and (bfr-eval pathcond (car env))
                (not erp)
                (acl2::interp-defs-alistp obligs)
                (acl2::interp-defs-alistp (glcp-config->overrides config))
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses
                   obligs1)))
                ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                (equal (w state0) (w state)))
     :special
     ((term :body (implies (and (pseudo-termp x)
                                (alistp alist))
                           (equal (glcp-generic-geval val env)
                                  (glcp-generic-geval-ev x (glcp-generic-geval-alist
                                                            alist env))))
            :hints ('(:in-theory (enable
                                  glcp-generic-geval-ev-of-fncall-args
                                  glcp-generic-geval-ev-of-return-last-call
                                  glcp-generic-geval-ev-of-if-call
                                  glcp-generic-geval-ev-of-gl-ignore-call
                                  glcp-generic-geval-ev-of-gl-aside-call
                                  glcp-generic-geval-ev-of-lambda
                                  glcp-generic-geval-ev-of-variable
                                  glcp-generic-geval-ev-of-quote
                                  equal-len))))
      (if :body (implies
                 (and (pseudo-termp tbr)
                      (pseudo-termp fbr)
                      (pseudo-termp test)
                      (alistp alist))
                 (equal (glcp-generic-geval val env)
                        (if (glcp-generic-geval-ev test (glcp-generic-geval-alist
                                                         alist env))
                            (glcp-generic-geval-ev tbr (glcp-generic-geval-alist
                                                        alist env))
                          (glcp-generic-geval-ev fbr (glcp-generic-geval-alist
                                                      alist env))))))
      (fncall-ifs :body (implies (and (symbolp fn)
                                      (not (eq fn 'quote))
                                      (gobj-listp actuals))
                                 (equal
                                  (glcp-generic-geval val env)
                                  (glcp-generic-geval-ev
                                   (cons fn (kwote-lst (glcp-generic-geval-list actuals env)))
                                   nil))))
      (fncall :body (implies (and (symbolp fn)
                                  (not (eq fn 'quote))
                                  (gobj-listp actuals))
                             (equal
                              (glcp-generic-geval val env)
                              (glcp-generic-geval-ev
                               (cons fn (kwote-lst (glcp-generic-geval-list actuals env)))
                               nil)))
              :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
      (rewrite :body (implies (and (symbolp fn)
                                   (not (eq fn 'quote))
                                   successp)
                              (equal
                               (glcp-generic-geval-ev term
                                                      (glcp-generic-geval-alist
                                                       bindings env))
                               (glcp-generic-geval-ev
                                (cons fn (kwote-lst (glcp-generic-geval-list
                                                     actuals env)))
                                nil))))
      (rules :body (implies (and (symbolp fn)
                                 (not (eq fn 'quote))
                                 successp
                                 (subsetp fn-rewrites
                                          (getprop fn 'acl2::lemmas nil
                                                   'current-acl2-world
                                                   (w state))))
                            (equal
                             (glcp-generic-geval-ev term
                                                    (glcp-generic-geval-alist
                                                     bindings env))
                             (glcp-generic-geval-ev
                              (cons fn (kwote-lst (glcp-generic-geval-list
                                                   actuals env)))
                              nil)))
             :hints ('(:in-theory (enable subsetp))))
      (rule :body (implies (and (symbolp fn)
                                (not (eq fn 'quote))
                                successp
                                (member rule (getprop fn 'acl2::lemmas nil
                                                      'current-acl2-world
                                                      (w state))))
                           (equal
                            (glcp-generic-geval-ev term
                                                   (glcp-generic-geval-alist
                                                    bindings env))
                            (glcp-generic-geval-ev
                             (cons fn (kwote-lst (glcp-generic-geval-list
                                                  actuals env)))
                             nil)))
            :hints((and stable-under-simplificationp
                        '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args)))))
      (hyps :body (implies (and (pseudo-term-listp hyps)
                                (alistp bindings)
                                successp)
                           (glcp-generic-geval-ev
                            (conjoin hyps)
                            (glcp-generic-geval-alist bindings env))))
      (hyp :body (implies (and (pseudo-termp hyp)
                               (alistp bindings)
                               successp)
                          (glcp-generic-geval-ev
                           hyp (glcp-generic-geval-alist bindings env)))
           :hints ((and stable-under-simplificationp
                        '(:in-theory (enable gtests-known-and-true)))))
      (list :body (implies (and (pseudo-term-listp x)
                                (alistp alist))
                           (equal (glcp-generic-geval-list vals env)
                                  (glcp-generic-geval-ev-lst
                                   x (glcp-generic-geval-alist alist
                                                               env))))
            :hints ('(:in-theory (enable glcp-generic-geval-ev-lst-of-cons
                                         glcp-generic-geval-ev-lst-of-atom)))))
     :expand-calls t
     :hints ((and stable-under-simplificationp
                  '(:do-not-induct t
                    :do-not '(generalize))))))

(in-theory (disable glcp-generic-interp-term))





