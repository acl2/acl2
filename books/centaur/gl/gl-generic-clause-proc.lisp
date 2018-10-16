; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "std/stobjs/clone" :dir :system)
(include-book "var-bounds")
(include-book "shape-spec")
(include-book "gl-generic-interp-defs")
(include-book "ctrex-utils")
(include-book "shape-spec")
(include-book "gify")
(include-book "bfr-sat")
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/decomp-hint" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)
(include-book "constraint-db-deps")
(include-book "defsort/duplicated-members" :dir :system)
(include-book "gl-util")
(local (include-book "gl-generic-interp"))
(local (include-book "general-object-thms"))
(local (include-book "hyp-fix"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (include-book "tools/with-quoted-forms" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (disable* set::double-containment w)))


(defun shape-spec-to-gobj-param (spec p)
  (declare (xargs :guard (shape-specp spec)))
  (gobj-to-param-space (shape-spec-to-gobj spec) p))

(defun shape-spec-to-env-param (x obj p)
  (declare (xargs :guard (shape-specp x)))
  (genv-param p (shape-spec-to-env x obj)))



(local
 (defsection glcp-generic-geval
   (local (in-theory (enable glcp-generic-geval)))

   (acl2::def-functional-instance
    glcp-generic-geval-shape-spec-oblig-term-correct
    shape-spec-oblig-term-correct
    ((sspec-geval-ev glcp-generic-geval-ev)
     (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
     (sspec-geval glcp-generic-geval)
     (sspec-geval-list glcp-generic-geval-list))
    :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                               (glcp-generic-geval-apply))
              :expand ((:with glcp-generic-geval (glcp-generic-geval x
                                                                     env))))))

   (acl2::def-functional-instance
    glcp-generic-geval-shape-spec-list-oblig-term-correct
    shape-spec-list-oblig-term-correct
    ((sspec-geval-ev glcp-generic-geval-ev)
     (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
     (sspec-geval glcp-generic-geval)
     (sspec-geval-list glcp-generic-geval-list))
    :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                               (glcp-generic-geval-apply))
              :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

   (acl2::def-functional-instance
    glcp-generic-geval-gobj-to-param-space-correct
    gobj-to-param-space-correct
    ((generic-geval-ev glcp-generic-geval-ev)
     (generic-geval-ev-lst glcp-generic-geval-ev-lst)
     (generic-geval glcp-generic-geval)
     (generic-geval-list glcp-generic-geval-list))
    :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                               (glcp-generic-geval-apply))
              :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))))


;; redundant but included only locally
(make-event
 (b* (((er &) (in-theory nil))
      ((er thm) (get-guard-verification-theorem 'glcp-generic-interp-term nil state)))
   (value
    `(with-output :off (prove event)
       (progn
         (defconst *glcp-generic-interp-guard-thm* ',thm)
         (defthm glcp-generic-interp-guards-ok
           ,thm
           :rule-classes nil))))))





(set-state-ok t)


(local
 (progn

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

   (flag::make-flag simple-term-vars-flg simple-term-vars)

   (defthm subsetp-equal-union-equal
     (iff (subsetp-equal (union-equal a b) c)
          (and (subsetp-equal a c)
               (subsetp-equal b c)))
     :hints ((acl2::set-reasoning)))

   (local (in-theory (enable glcp-generic-geval-ev-of-nonsymbol-atom)))

   (defthm-simple-term-vars-flg
     glcp-generic-geval-ev-norm-alist-simple-term-vars-lemma
     (defthm glcp-generic-geval-ev-norm-alist-simple-term-vars1
      (implies (subsetp-equal (simple-term-vars x) vars)
               (equal (glcp-generic-geval-ev x (norm-alist vars alist))
                      (glcp-generic-geval-ev x alist)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args)
                     :expand ((Simple-term-vars x)))))
      :flag simple-term-vars)
     (defthm glcp-generic-geval-ev-lst-norm-alist-simple-term-vars-lst1
      (implies (subsetp-equal (simple-term-vars-lst x) vars)
               (equal (glcp-generic-geval-ev-lst x (norm-alist vars alist))
                      (glcp-generic-geval-ev-lst x alist)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((simple-term-vars-lst x)))))
      :flag simple-term-vars-lst)
     :hints (("goal" :induct (simple-term-vars-flg flag x)
              :in-theory (enable subsetp-equal))))




   (encapsulate nil
     (local (defthm member-equal-second-revappend
              (implies (member-equal x b)
                       (member-equal x (revappend a b)))))
     (defthm member-equal-revappend
       (iff (member-equal x (revappend a b))
            (or (member-equal x a)
                (member-equal x b)))))

   (defthm revappend-set-equiv-union
     (acl2::set-equiv (revappend a b) (union-equal a b))
     :hints ((acl2::set-reasoning)))



   ;; (defthm gobj-listp-strip-cdrs
   ;;   (implies (gobj-alistp x)
   ;;            (gobj-listp (strip-cdrs x)))
   ;;   :hints(("Goal" :in-theory (enable strip-cdrs gobj-listp))))

   (defun gobj-strip-cdrs (x)
     (declare (xargs :guard (alistp x)))
     (if (atom x)
         nil
       (gl-cons (cdar x)
                (gobj-strip-cdrs (cdr x)))))

   (defthm gobj-listp-gobj-strip-cdrs
     (gobj-listp (gobj-strip-cdrs x)))

   (local (defthm cdr-of-gl-cons
            (equal (cdr (gl-cons x y)) y)
            :hints(("Goal" :in-theory (enable gl-cons)))))

   (local (defthm eval-car-of-gl-cons
            (equal (glcp-generic-geval (car (gl-cons x y)) env)
                   (glcp-generic-geval x env))
            :hints (("goal" :use ((:instance glcp-generic-geval-of-gl-cons)
                                  (:instance
                                   glcp-generic-geval-g-concrete-quote-correct
                                   (b env)))
                     :in-theory (e/d (gl-cons g-concrete-quote g-keyword-symbolp)
                                     (glcp-generic-geval-of-gl-cons
                                      glcp-generic-geval-g-concrete-quote-correct))))))

   (defthm glcp-generic-geval-alist-gobj-alistp
     (implies (alistp x)
              (equal (glcp-generic-geval-alist x env)
                     (pairlis$ (strip-cars x)
                               (glcp-generic-geval-list (strip-cdrs x) env))))
     :hints(("Goal" :in-theory (enable strip-cars glcp-generic-geval-alist))))

   

   ;; (defthm gobject-alistp-gobj-alist-to-param-space
   ;;   (implies (gobject-alistp x)
   ;;            (gobject-alistp (gobj-alist-to-param-space x p))))

   (defthm strip-cars-gobj-alist-to-param-space
     (implies (alistp x)
              (equal (strip-cars (gobj-alist-to-param-space x p))
                     (strip-cars x))))

   (defthm gobj-to-param-space-of-gl-cons
     (equal (gobj-to-param-space (gl-cons a b) p)
            (gl-cons (gobj-to-param-space a p)
                     (gobj-to-param-space b p)))
     :hints(("Goal" :in-theory (enable gobj-to-param-space
                                       g-keyword-symbolp
                                       gl-cons tag)
             :expand ((:free (a b) (gobj-to-param-space (cons a b) p))))))

   ;; (defthm strip-cdrs-gobj-alist-to-param-space
   ;;   (equal (gobj-strip-cdrs (gobj-alist-to-param-space x p))
   ;;          (gobj-to-param-space (gobj-strip-cdrs x) p))
   ;;   :hints(("Goal" :in-theory (enable strip-cdrs
   ;;                                     gobj-to-param-space
   ;;                                     tag)
   ;;           :induct (gobj-alist-to-param-space x p)
   ;;           :expand ((:free (a b) (gobj-to-param-space (cons a b) p))))))

   ;; (defthm alistp-gobj-alist-to-param-space
   ;;   (alistp (gobj-alist-to-param-space x p)))


   (defthm nonnil-symbol-listp-strip-cars-shape-spec-bindings
     (implies (shape-spec-bindingsp x)
              (nonnil-symbol-listp (strip-cars x)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))


   ;; (defthm shape-spec-listp-strip-cadrs
   ;;   (implies (shape-spec-bindingsp x)
   ;;            (shape-spec-listp (strip-cadrs x)))
   ;;   :hints(("Goal" :in-theory (enable shape-spec-listp))))

   (defthm shape-specp-shape-spec-bindings->sspecs
     (implies (shape-spec-bindingsp x)
              (shape-specp (shape-spec-bindings->sspecs x))))))







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
      ((g-integer n) (acl2::max-max-depth n))
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

;; (defund inspec-max-index (x)
;;   (if (atom x)
;;       0
;;     (pattern-match x
;;       ((g-concrete &) 0)
;;       ((g-boolean b) b)
;;       ((g-number n) (max-list-list n))
;;       ((g-ite if then else)
;;        (max (inspec-max-index if)
;;             (max (inspec-max-index then)
;;                  (inspec-max-index else))))
;;       ((g-apply & args) (inspec-max-index args))
;;       ((g-var &) 0)
;;       (& (max (inspec-max-index (car x))
;;               (inspec-max-index (cdr x)))))))



















;; (defun glcp-counterexample-wormhole (ctrexes warn-err type concl execp)
;;   (wormhole
;;    'glcp-counterexample-wormhole
;;    '(lambda (whs) whs)
;;    nil
;;    `(b* (((er &)
;;           (glcp-print-ctrexamples
;;            ',ctrexes ',warn-err ',type ',concl ',execp state)))
;;       (value :q))
;;    :ld-prompt nil
;;    :ld-pre-eval-print nil
;;    :ld-post-eval-print nil
;;    :ld-verbose nil))


;; (in-theory (disable glcp-counterexample-wormhole))




(defun glcp-analyze-interp-result (hyp-bfr concl-bfr constraint al id concl config bvar-db
                                           state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* ((config (glcp-config-update-param hyp-bfr config))
       (config (glcp-config-update-term concl config))
       ((glcp-config config) config)
       (hyp-param (bfr-to-param-space hyp-bfr hyp-bfr))
       (false (bfr-and hyp-param (bfr-and constraint (bfr-not concl-bfr))))
       (state (acl2::f-put-global 'glcp-var-bindings al state))
       (state (acl2::f-put-global 'glcp-concl-bfr false state))
       ((mv false-sat false-succ false-ctrex) (bfr-sat false))
       ((when (and false-sat false-succ))
        (b* (((mv er & state)
              (glcp-gen/print-ctrexamples
               false-ctrex "ERROR" "Counterexamples" config bvar-db state))
             ((when er) (mv er nil state))
             ((when config.abort-ctrex)
              (mv (msg
                   "~x0: Counterexamples found in ~@1; aborting~%"
                   config.clause-proc id)
                  nil state)))
          (value (list ''nil))))
       ((when false-succ)
        ;; Both checks succeeded and were UNSAT, so the theorem is proved
        ;; (modulo side-goals).
        (value (list ''t))))
    ;; The SAT check failed:
    (if config.abort-indeterminate
        (mv
         (msg "~x0: SAT check failed in ~@1; aborting~%"
              config.clause-proc id)
         nil state)
      (value (list ''nil)))))


;; (local
;;  (encapsulate nil
;;    (local (defthm equal-of-cons
;;             (equal (equal (cons a b) c)
;;                    (and (consp c)
;;                         (equal a (car c))
;;                         (equal b (cdr c))))))
;;    (defthm glcp-analyze-interp-result-irrelevant
;;      (and (implies (syntaxp (not (and (equal al ''nil)
;;                                       (equal concl ''nil)
;;                                       (equal st ''nil))))
;;                    (and (equal (mv-nth 0 (glcp-analyze-interp-result
;;                                           val al hyp-bfr id concl config
;;                                           bvar-db st))
;;                                (mv-nth 0 (glcp-analyze-interp-result
;;                                           val nil hyp-bfr id concl config nil nil)))
;;                         (equal (mv-nth 1 (glcp-analyze-interp-result
;;                                           val al hyp-bfr id concl config
;;                                           bvar-db st))
;;                                (mv-nth 1 (glcp-analyze-interp-result
;;                                           val nil hyp-bfr id concl config nil nil)))))
;;           ;; (implies (syntaxp (not (and (equal al ''nil)
;;           ;;                             (equal concl ''nil)
;;           ;;                             (equal st ''nil))))
;;           ;;          (equal (mv-nth 1 (glcp-analyze-interp-result
;;           ;;                            val al hyp-bfr id concl config st))
;;           ;;                 (mv-nth 1 (glcp-analyze-interp-result
;;           ;;                            val nil hyp-bfr abort-unknown abort-ctrex nil nil
;;           ;;                            geval-name nil nil nil nil))))
;;           )
;;      :hints(("Goal" :in-theory '(glcp-analyze-interp-result
;;                                  glcp-gen-ctrexes-does-not-fail
;;                                  glcp-error))))))

(local (in-theory (disable glcp-gen/print-ctrexamples)))

(local
 (defthm glcp-analyze-interp-result-correct
   (implies (and (not (bfr-eval val (cadr (assoc-equal 'env alist))))
                 (bfr-eval (bfr-to-param-space hyp-bfr hyp-bfr)
                           (car (cdr (assoc-equal 'env alist))))
                 (bfr-eval constraint
                           (car (cdr (assoc-equal 'env alist)))))
            (not (glcp-generic-geval-ev
                  (disjoin
                   (mv-nth 1 (glcp-analyze-interp-result
                               hyp-bfr val constraint al id concl config bvar-db state)))
                  alist)))
   :hints (("goal" :use
            ((:instance
              bfr-sat-unsat
              (prop (bfr-and (bfr-to-param-space hyp-bfr hyp-bfr)
                             (bfr-and constraint (bfr-not val))))
              (env (cadr (assoc-equal 'env alist)))))
            :in-theory (e/d (gl-cp-hint)
                            (; glcp-generic-geval-gtests-nonnil-correct
                             gtests-nonnil-correct
                             bfr-sat-unsat))
            :do-not-induct t)
           (bfr-reasoning))
   :otf-flg t))

(defthm w-of-read-acl2-oracle
  (equal (w (mv-nth 2 (read-acl2-oracle state)))
         (w state))
  :hints(("Goal" :in-theory (enable w read-acl2-oracle
                                    get-global
                                    update-acl2-oracle))))

(local
 (defthm w-state-of-n-satisfying-assigns-and-specs
   (equal (w (mv-nth 2 (n-satisfying-assigns-and-specs
                        n  hyp-bfr ctrex-info max-index state)))
          (w state))
   :hints(("Goal" :in-theory (enable random$)))))

(local
 (defthm w-state-of-glcp-gen-assignments
   (equal (w (mv-nth 2 (glcp-gen-assignments ctrex-info config state)))
          (w state))))

(local (in-theory (disable glcp-gen-assignments)))
(local (in-theory (disable glcp-bit-to-obj-ctrexamples)))
(local
 (defthm w-state-of-glcp-gen-ctrexes
   (equal (w (mv-nth 2 (glcp-gen-ctrexes ctrex-info bvar-db config state)))
          (w state))
   :hints(("Goal" :in-theory (enable glcp-gen-ctrexes)))))
(local (in-theory (disable glcp-gen-ctrexes)))

(local (in-theory (disable w put-global)))

;; (local (defthm w-state-of-glcp-pretty-print-assignments
;;          (equal (w (mv-nth 2 (glcp-pretty-print-assignments
;;                               n ctrexes concl execp param-bfr bvar-db state)))
;;                 (w state))
;;          :hints(("Goal" :in-theory (disable glcp-ctrex-check-bvar-db
;;                                             bindings-quote-if-needed
;;                                             acl2::magic-ev
;;                                             magicer-ev)))))

(local
 (defthm w-state-of-glcp-analyze-interp-result
   (equal (w (mv-nth 2 (glcp-analyze-interp-result
                         hyp-bfr val constr al id concl config bvar-db state)))
          (w state))
   :hints(("Goal" :in-theory (enable glcp-analyze-interp-result
                                     glcp-gen/print-ctrexamples)))))

(local
 (defthm glcp-analyze-interp-result-pseudo-term-listp
   (pseudo-term-listp
    (mv-nth 1 (glcp-analyze-interp-result
               hyp-bfr val constr al id concl config bvar-db state)))))

(in-theory (disable glcp-analyze-interp-result))

;; (local
;;  (progn
;;    ;; (defun gobj-list-to-param-space (list p)
;;    ;;   (if (atom list)
;;    ;;       nil
;;    ;;     (gl-cons (gobj-to-param-space (car list) p)
;;    ;;           (gobj-list-to-param-space (cdr list) p))))


;;    (defthm glcp-generic-geval-alist-gobj-alist-to-param-space
;;      (equal (glcp-generic-geval-alist
;;              (gobj-alist-to-param-space alist p)
;;              env)
;;             (pairlis$ (strip-cars alist)
;;                       (glcp-generic-geval-list
;;                        (gobj-list-to-param-space (strip-cdrs alist) p)
;;                        env)))
;;      :hints(("Goal" :in-theory (enable strip-cdrs))))))




   ;; ;; (defthmd gobject-listp-gobj-to-param-space
   ;; ;;   (implies (gobject-listp lst)
   ;; ;;            (gobject-listp (gobj-to-param-space lst p)))
   ;; ;;   :hints(("Goal" :in-theory (enable gobj-to-param-space tag
   ;; ;;                                     gobject-listp))))

   ;; (defthmd gobj-list-to-param-space-when-gobject-listp
   ;;   (implies (gobject-listp lst)
   ;;            (equal (gobj-list-to-param-space lst p)
   ;;                   (gobj-to-param-space lst p)))
   ;;   :hints(("Goal" :in-theory (enable gobj-to-param-space
   ;;                                     gobject-listp tag))))

   ;; (defthmd glcp-generic-geval-lst-to-glcp-generic-geval
   ;;   (implies (gobject-listp x)
   ;;            (equal (glcp-generic-geval-lst x env)
   ;;                   (glcp-generic-geval x env)))
   ;;   :hints(("Goal" :in-theory (enable glcp-generic-geval-of-gobject-list))))

   ;; (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
   ;;   (implies (and (gobject-listp x)
   ;;                 (bfr-eval p (car env)))
   ;;            (equal (glcp-generic-geval-lst
   ;;                    (gobj-list-to-param-space x p)
   ;;                    (genv-param p env))
   ;;                   (glcp-generic-geval-lst x env)))
   ;;   :hints (("goal" :use
   ;;            glcp-generic-geval-gobj-to-param-space-correct
   ;;            :in-theory (enable gobject-listp-gobj-to-param-space
   ;;                               gobj-list-to-param-space-when-gobject-listp
   ;;                               glcp-generic-geval-lst-to-glcp-generic-geval
   ;;                               gobject-listp-impl-gobjectp))))

   ;; (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
   ;;   (implies (and (gobj-listp x)
   ;;                 (bfr-eval p (car env)))
   ;;            (equal (glcp-generic-geval-lst
   ;;                    (gobj-list-to-param-space x p)
   ;;                    (genv-param p env))
   ;;                   (glcp-generic-geval-lst x env)))
   ;;   :hints (("goal" :use
   ;;            glcp-generic-geval-gobj-to-param-space-correct
   ;;            :in-theory (enable gobject-listp-gobj-to-param-space
   ;;                               gobj-list-to-param-space-when-gobject-listp
   ;;                               glcp-generic-geval-lst-to-glcp-generic-geval
   ;;                               gobject-listp-impl-gobjectp))))

(defthm strip-cars-shape-specs-to-interp-al
  (equal (strip-cars (shape-specs-to-interp-al al))
         (alist-keys al))
  :hints(("Goal" :in-theory (enable shape-specs-to-interp-al alist-keys))))


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
(defsection dumb-negate-lit

  (local (in-theory (enable dumb-negate-lit)))
  (defthm glcp-generic-geval-ev-dumb-negate-lit
    (iff (glcp-generic-geval-ev (dumb-negate-lit lit) a)
         (not (glcp-generic-geval-ev lit a))))


  (defthm glcp-generic-geval-ev-list*-macro
    (equal (glcp-generic-geval-ev (list*-macro (append x (list ''nil))) al)
           (glcp-generic-geval-ev-lst x al))
    :hints(("Goal" :in-theory (enable append))))

  

   (defthmd glcp-generic-geval-ev-disjoin-is-or-list-glcp-generic-geval-ev-lst
     (iff (glcp-generic-geval-ev (disjoin lst) env)
          (acl2::or-list (glcp-generic-geval-ev-lst lst env)))
     :hints (("goal" :induct (len lst)))))

(local
 (defsection norm-alist


   (defthm pairlis-eval-alist-is-norm-alist
     (implies (nonnil-symbol-listp vars)
              (equal (pairlis$ vars
                               (glcp-generic-geval-ev-lst vars alist))
                     (norm-alist vars alist)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp
                                       pairlis$))))


   (defthm glcp-generic-geval-ev-disjoin-norm-alist
     (implies (and (pseudo-term-listp clause)
                   (subsetp-equal (simple-term-vars-lst clause) vars))
              (iff (glcp-generic-geval-ev (disjoin clause) (norm-alist vars alist))
                   (glcp-generic-geval-ev (disjoin clause) alist)))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-geval-ev-disjoin-is-or-list-glcp-generic-geval-ev-lst))))))





(local (defthm pbfr-depends-on-t-is-bfr-depends-on
         (equal (pbfr-depends-on k t x)
                (bfr-depends-on k x))
         :hints (("goal" :in-theory (enable pbfr-depends-on
                                            bfr-depends-on
                                            pbfr-semantic-depends-on
                                            bfr-from-param-space)))))

(defthm pbfr-vars-bounded-of-bfr-var
  (implies (and (natp (bfr-varname-fix v))
                (<= (+ 1 (bfr-varname-fix v)) (nfix k)))
           (pbfr-vars-bounded k t (bfr-var v)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(defthm pbfr-list-vars-bounded-of-numlist-to-vars
  (implies (<= (nat-list-max x) (nfix n))
           (pbfr-list-vars-bounded n t (numlist-to-vars x)))
  :hints (("goal" :induct (nat-list-max x)
           :in-theory (disable nfix natp)
           :expand ((nat-listp x)
                    (nat-list-max x)
                    (numlist-to-vars x)))))

;; (defthm pbfr-list-vars-bounded-of-greater
;;   (implies (and (pbfr-list-vars-bounded n p x)
;;                 (<= (nfix n) (nfix k)))
;;            (pbfr-list-vars-bounded k p x))
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))))



(include-book "symbolic-arithmetic")

(defthm pbfr-list-vars-bounded-of-bfr-logapp-nus
  (implies (and (pbfr-list-vars-bounded k p x)
                (pbfr-list-vars-bounded k p y))
           (pbfr-list-vars-bounded k p (bfr-logapp-nus n x y)))
  :hints (("goal" :in-theory (enable pbfr-list-vars-bounded-in-terms-of-witness))))




(defthm-shape-spec-flag
  (defthm gobj-vars-bounded-of-shape-spec-to-gobj
    (implies (<= (shape-spec-max-bvar x) (nfix n))
             (gobj-vars-bounded n t (shape-spec-to-gobj x)))
    :flag ss)
  (defthm gobj-vars-bounded-of-shape-spec-to-gobj-list
    (implies (<= (shape-spec-max-bvar-list x) (nfix n))
             (gobj-list-vars-bounded n t (shape-spec-to-gobj-list x)))
    :flag list)
  :hints (("goal" :do-not '(simplify preprocess)
           :in-theory (disable shape-spec-max-bvar
                               shape-spec-max-bvar-list
                               shape-spec-to-gobj
                               shape-spec-to-gobj-list
                               nat-list-max))
          (acl2::just-expand ((shape-spec-to-gobj-list x)
                              (shape-spec-max-bvar-list x)
                              (shape-spec-to-gobj x)
                              (shape-spec-max-bvar x))
                             :mark-only t :last-only t)
            '(:do-not nil)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::expand-marked-meta)
                                   (shape-spec-max-bvar
                                    shape-spec-max-bvar-list
                                    shape-spec-to-gobj
                                    shape-spec-to-gobj-list
                                    nat-list-max))))))









(local
 (progn
   (defthm bvar-db-fix-env-eval-gobj-list-vars-bounded-unparam-rw
     (implies (and ; (bvar-db-orderedp p bvar-db)
               (bfr-eval p env)
               (bfr-vars-bounded min p)
               (gobj-list-vars-bounded min t x)
               (<= (nfix n) (next-bvar$a bvar-db)))
              (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                             var-env)))
                (equal (glcp-generic-geval-list x (cons (bfr-unparam-env p env-n) var-env))
                       (glcp-generic-geval-list x (cons env var-env)))))
     :hints (("goal" :induct (len x)
              :expand ((:free (env) (glcp-generic-geval-list x env))))))

   (defthm bvar-db-fix-env-eval-gobj-list-vars-bounded-unparam-with-no-param
     (implies (and ; (bvar-db-orderedp p bvar-db)
               (gobj-list-vars-bounded min t x)
               (<= (nfix n) (next-bvar$a bvar-db)))
              (let* ((env-n (bvar-db-fix-env n min bvar-db t env var-env)))
                (equal (glcp-generic-geval-list x (cons env-n var-env))
                       (glcp-generic-geval-list x (cons env var-env)))))
     :hints (("goal" :induct (len x)
              :expand ((:free (env) (glcp-generic-geval-list x env))))))))



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
         (not (stringp vals))))
  :hints(("Goal" :in-theory (disable pseudo-termp))))

(defthm bindings-to-lambda-pseudo-termp
  (implies (pseudo-termp term)
           (pseudo-termp (bindings-to-lambda bindings term)))
  :hints(("Goal" :in-theory (enable true-listp length pseudo-termp))))

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



(make-event
 (sublis *glcp-generic-template-subst* *glcp-clause-proc-template*))

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
 (encapsulate nil
   (local (defthm true-listp-when-nat-listp
            (implies (nat-listp x)
                     (true-listp x))
            :hints(("Goal" :in-theory (enable nat-listp)))))

   (defun shape-spec-bindings-indices (x)
     (declare (xargs :guard (shape-spec-bindingsp x)))
     (if (atom x)
         nil
       (append (shape-spec-indices (cadar x))
               (shape-spec-bindings-indices (cdr x)))))

   (defun shape-spec-bindings-vars (x)
     (declare (xargs :guard (shape-spec-bindingsp x)))
     (if (atom x)
         nil
       (append (shape-spec-vars (cadar x))
               (shape-spec-bindings-vars (cdr x)))))))



(local
 (progn
   (defthm assoc-in-glcp-generic-geval-alist
     (implies (alistp al)
              (equal (assoc k (glcp-generic-geval-alist al env))
                     (and (assoc k al)
                          (cons k (glcp-generic-geval (cdr (assoc k al)) env))))))))



;; (defthm eval-of-shape-spec-to-interp-al-alist
;;   (implies (and (shape-spec-bindingsp bindings)
;;                 (no-duplicatesp (shape-spec-bindings-indices bindings))
;;                 (no-duplicatesp (shape-spec-bindings-vars bindings)))
;;            (equal (glcp-generic-geval-alist
;;                    (shape-specs-to-interp-al bindings)
;;                    (shape-spec-to-env (strip-cadrs bindings)
;;                                       (glcp-generic-geval-ev-lst (strip-cars bindings)
;;                                                       alist)))
;;                   (pairlis$ (strip-cars bindings)
;;                             (glcp-generic-geval-ev-lst (strip-cars bindings) alist))))
;;   hie)

;;                 ((GLCP-GENERIC-GEVAL-ALIST
;;    (SHAPE-SPECS-TO-INTERP-AL BINDINGS)
;;    (SHAPE-SPEC-TO-ENV (STRIP-CADRS BINDINGS)
;;                       (GLCP-GENERIC-GEVAL-EV-LST (STRIP-CARS BINDINGS)
;;                                       ALIST)))

(local
 (defun-nx glcp-generic-run-parametrized-ctrex (alist hyp concl bindings obligs config interp-st state)
   (b* (((glcp-config config) config)
        (obj (shape-spec-bindings->sspecs bindings))
        (config (change-glcp-config config :shape-spec-alist bindings))
        (al (shape-specs-to-interp-al bindings))
        (env-term (shape-spec-list-env-term
                   obj
                   (strip-cars bindings)))
        (env1 (glcp-generic-geval-ev env-term alist))
        (env (cons (slice-to-bdd-env (car env1) nil) (cdr env1)))
        (next-bvar (shape-spec-max-bvar-list
                    (shape-spec-bindings->sspecs bindings)))
        (interp-st (update-is-obligs obligs interp-st))
        (interp-st (update-is-constraint (bfr-constr-init) interp-st))
        (interp-st (update-is-constraint-db
                    (gbc-db-make-fast
                     (table-alist 'gl-bool-constraints (w state)))
                    interp-st))
        (interp-st (update-is-add-bvars-allowed t interp-st))
        (interp-st (update-is-prof-enabledp config.prof-enabledp interp-st)))
     (glcp-generic-interp-hyp/concl-env
      env hyp concl al config.concl-clk config interp-st next-bvar state))))
    ;;    ;; (bvar-db nil)
    ;;    ;; (bvar-db1 nil)
    ;;    (bvar-db (init-bvar-db (shape-spec-max-bvar-list
    ;;                            (shape-spec-bindings->sspecs bindings)) bvar-db))
    ;;    ;; (config1 (glcp-config-update-param t config))
    ;;    ((mv ?er obligs1 hyp-bfr bvar-db state)
    ;;     (glcp-generic-interp-top-level-term hyp al t config.hyp-clk obligs config1 bvar-db state))
    ;;    (env1 (cons (bvar-db-fix-env (next-bvar bvar-db)
    ;;                                (base-bvar bvar-db)
    ;;                                bvar-db t (car env) (cdr env))
    ;;                (cdr env)))
    ;;    (param-env (genv-param hyp-bfr env1))
    ;;    (param-al (gobj-alist-to-param-space al hyp-bfr))
    ;;    (bvar-db1 (parametrize-bvar-db hyp-bfr bvar-db bvar-db1))
    ;;    (hyp-param (bfr-to-param-space hyp-bfr hyp-bfr))
    ;;    (config2 (glcp-config-update-param hyp-bfr config1))
    ;;    ((mv ?er ?obligs2 ?val bvar-db1 ?state)
    ;;     (glcp-generic-interp-top-level-term concl param-al hyp-param config.concl-clk
    ;;                                         obligs1 config2 bvar-db1 state))
    ;;    (env2 (cons (bvar-db-fix-env (next-bvar bvar-db1)
    ;;                                 (next-bvar bvar-db)
    ;;                                 bvar-db1 hyp-bfr (car param-env) (cdr param-env))
    ;;                (cdr param-env))))
    ;; `((env1 . ,env1)
    ;;   (env2 . ,env2)
    ;;   (config1 . ,config1)
    ;;   (config2 . ,config2)
    ;;   (bvar-db . ,bvar-db)
    ;;   (bvar-db1 . ,bvar-db1))))

;; (defun-nx glcp-generic-run-parametrized-ctrex (alist hyp concl bindings obligs
;;                                                      config state)
;;   (cdr (assoc 'env2 (glcp-generic-run-parametrized-ctrex-aux alist hyp concl bindings
;;                                                              obligs config state))))




;; (defthm bvar-db-env-ok-of-bvar-db-fix-env-no-param
;;   (implies (and (bvar-db-orderedp t bvar-db)
;;                 (<= (nfix min) (nfix m))
;;                 (<= (base-bvar$a bvar-db) (nfix m))
;;                 (< (nfix m) (nfix n))
;;                 (<= (nfix n) (next-bvar$a bvar-db)))
;;            (let* ((bfr-env (bvar-db-fix-env n min bvar-db t bfr-env
;;                                             var-env)))
;;              (iff (bfr-lookup m bfr-env)
;;                   (glcp-generic-geval (get-bvar->term m bvar-db)
;;                                       (cons bfr-env var-env)))))
;;   :hints (("Goal" :use ((:instance bvar-db-env-ok-of-bvar-db-fix-env-lemma
;;                          (p t)))
;;            :do-not-induct t)))





;; (defthm glcp-generic-interp-top-level-term-correct-special
;;   (b* (((mv ?erp ?obligs1 ?val ?bvar-db1 ?state1)
;;         (glcp-generic-interp-top-level-term
;;          term alist pathcond clk obligs config bvar-db state))
;;        (bfr-env (bvar-db-fix-env n min bvar-db2 p bfr-env var-env)))
;;     (implies (and (bfr-eval pathcond bfr-env)
;;                   (not erp)
;;                   (acl2::interp-defs-alistp obligs)
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config))
;;                   (glcp-generic-geval-ev-theoremp
;;                    (conjoin-clauses
;;                     (acl2::interp-defs-alist-clauses
;;                      obligs1)))
;;                   ;; (glcp-generic-geval-ev-meta-extract-global-facts)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (glcp-generic-bvar-db-env-ok bvar-db1 config (cons bfr-env var-env))
;;                   (equal (w state0) (w state))
;;                   (pseudo-termp term)
;;                   (alistp alist))
;;              (iff (bfr-eval val bfr-env)
;;                   (glcp-generic-geval-ev term (glcp-generic-geval-alist
;;                                                alist (cons bfr-env var-env))))))
;;   :hints(("Goal" :use ((:instance glcp-generic-interp-top-level-term-correct
;;                         (bfr-env (bvar-db-fix-env n min bvar-db2 p bfr-env
;;                                                   var-env))
;;                         (env (cons (bvar-db-fix-env n min bvar-db2 p bfr-env
;;                                                     var-env)
;;                                    var-env))))
;;           :in-theory (disable glcp-generic-interp-top-level-term-correct))))

;; (defthm bfr-vars-bounded-consts
;;   (and (bfr-vars-bounded k t)
;;        (bfr-vars-bounded k nil))
;;   :hints(("Goal" :in-theory (enable bfr-vars-bounded))))

;; (defthm bvar-db-env-ok-of-bvar-db-fix-env-no-param
;;   (implies (and (bvar-db-orderedp t bvar-db)
;;                 (equal t (glcp-config->param-bfr config))
;;                 (equal n (next-bvar$a bvar-db))
;;                 (equal b (base-bvar$a bvar-db)))
;;            (let ((bfr-env (bvar-db-fix-env n b
;;                                            bvar-db t bfr-env var-env)))
;;              (glcp-generic-bvar-db-env-ok bvar-db config (cons bfr-env var-env))))
;;   :hints (("goal" :use ((:instance bvar-db-env-ok-of-bvar-db-fix-env
;;                          (p t)))
;;            :in-theory (disable bvar-db-env-ok-of-bvar-db-fix-env)
;;            :do-not-induct t)))


;; (defthm bvar-db-ordered-of-glcp-generic-interp-top-level-special
;;   (b* (((mv ?erp ?obligs1 ?val ?bvar-db1 ?state1)
;;         (glcp-generic-interp-top-level-term
;;          term alist pathcond clk obligs config bvar-db state))
;;        (k (next-bvar$a bvar-db)))
;;     (implies (and (equal t (glcp-config->param-bfr config))
;;                   (bvar-db-orderedp t bvar-db)
;;                   (gobj-alist-vars-bounded k t alist))
;;              (bvar-db-orderedp t bvar-db1)))
;;   :hints (("goal" :Use ((:instance
;;                          bvar-db-ordered-of-glcp-generic-interp-top-level
;;                          (p t)))
;;            :in-theory (disable bvar-db-ordered-of-glcp-generic-interp-top-level))))


;; ;; (defthm gobj-alist-vars-bounded-of-shape-specs-to-interp-al
;; ;;   (implies (<= (shape-spec-max-bvar-list (shape-spec-bindings->sspecs bindings)) (nfix n))
;; ;;            (not (gobj-alist-depends-on n t (shape-specs-to-interp-al
;; ;;                                             bindings))))
;; ;;   :hints(("Goal" :in-theory (enable shape-specs-to-interp-al))))

(defthm gobj-alist-vars-bounded-of-shape-specs-to-interp-al
  (implies (<= (shape-spec-max-bvar-list (shape-spec-bindings->sspecs bindings)) (nfix n))
           (gobj-alist-vars-bounded n t (shape-specs-to-interp-al bindings)))
  :hints(("Goal" :in-theory (enable shape-spec-max-bvar-list shape-spec-bindings->sspecs
                                    shape-specs-to-interp-al))))





;; (defthm bfr-vars-bounded-of-glcp-generic-interp-top-level
;;     (b* (((mv ?erp ?obligs1 ?val ?bvar-db1 ?state1)
;;           (glcp-generic-interp-top-level-term
;;            term alist pathcond clk obligs config bvar-db state)))
;;       (implies (and (<= (next-bvar$a bvar-db1) (nfix k))
;;                     (equal t (glcp-config->param-bfr config))
;;                     (gobj-alist-vars-bounded k t alist))
;;                (bfr-vars-bounded k val)))
;;     :hints (("goal" :use ((:instance
;;                            vars-bounded-of-glcp-generic-interp-top-level
;;                            (p t)))
;;              :in-theory (disable vars-bounded-of-glcp-generic-interp-top-level))))



;; (defthm glcp-generic-run-parametrized-bvar-db-env1-ok
;;   (b* (((mv ?erp ?obligs1 ?val ?bvar-db1 ?state1)
;;         (glcp-generic-interp-top-level-term
;;          term alist pathcond clk obligs config bvar-db state))
;;        (bfr-env (bvar-db-fix-env n min bvar-db2 p bfr-env var-env))
;;        (aux (glcp-generic-run-parametrized-ctrex-aux alist hyp concl bindings
;;                                                      obligs config state)))
;;     (implies (and (bfr-eval pathcond bfr-env)
;;                   (not erp)
;;                   (acl2::interp-defs-alistp obligs)
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config))
;;                   (glcp-generic-geval-ev-theoremp
;;                    (conjoin-clauses
;;                     (acl2::interp-defs-alist-clauses
;;                      obligs1)))
;;                   ;; (glcp-generic-geval-ev-meta-extract-global-facts)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (glcp-generic-bvar-db-env-ok bvar-db1 config (cons bfr-env var-env))
;;                   (equal (w state0) (w state))
;;                   (pseudo-termp term)
;;                   (alistp alist))
;;              (glcp-generic-bvar-db-env-ok
;;               (cdr (assoc 'bvar-db aux))
;;               (cdr (assoc 'config1 aux))
;;               (cdr (assoc 'env1 aux)))))
;;   :hints (("goal" :do-not-induct t)
;;           (and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))
;;           (and stable-under-simplificationp
;;                (let ((w (acl2::find-call-lst
;;                          'glcp-generic-bvar-db-env-ok-witness
;;                          clause)))
;;                  `(:clause-processor
;;                    (acl2::simple-generalize-cp
;;                     clause '((,w . idx)))))))
;;   :otf-flg t)


;; (defthm glcp-generic-run-parametrized-bvar-db-env3-ok
;;   (b* (((mv ?erp ?obligs1 ?val ?bvar-db1 ?state1)
;;         (glcp-generic-interp-top-level-term
;;          term alist pathcond clk obligs config bvar-db state))
;;        (bfr-env (bvar-db-fix-env n min bvar-db2 p bfr-env var-env))
;;        (aux (glcp-generic-run-parametrized-ctrex-aux alist hyp concl bindings
;;                                                      obligs config state)))
;;     (implies (and (bfr-eval pathcond bfr-env)
;;                   (not erp)
;;                   (acl2::interp-defs-alistp obligs)
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config))
;;                   (glcp-generic-geval-ev-theoremp
;;                    (conjoin-clauses
;;                     (acl2::interp-defs-alist-clauses
;;                      obligs1)))
;;                   ;; (glcp-generic-geval-ev-meta-extract-global-facts)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (glcp-generic-bvar-db-env-ok bvar-db1 config (cons bfr-env var-env))
;;                   (equal (w state0) (w state))
;;                   (pseudo-termp term)
;;                   (alistp alist))
;;              (glcp-generic-bvar-db-env-ok
;;               (cdr (assoc 'bvar-db1 aux))
;;               (cdr (assoc 'config2 aux))
;;               (cdr (assoc 'env2 aux)))))
;;   :hints (("goal" :do-not-induct t)
;;           (and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))
;;           (and stable-under-simplificationp
;;                (let ((w (acl2::find-call-lst
;;                          'glcp-generic-bvar-db-env-ok-witness
;;                          clause)))
;;                  `(:clause-processor
;;                    (acl2::simple-generalize-cp
;;                     clause '((,w . idx)))))))
;;   :otf-flg t)

;; (defun-nx glcp-generic-run-parametrized-ctrex
;;   (env hyp concl bindings obligs config state)
;;   (b* (((glcp-config config) config)
;;        (al (shape-specs-to-interp-al bindings))
;;        (next-bvar (shape-spec-max-bvar-list (shape-spec-bindings->sspecs bindings)))
;;        (config (glcp-config-update-param t config)))
;;     (glcp-generic-interp-hyp/concl-env
;;      env hyp concl al config.concl-clk obligs config next-bvar state)))
       ;; ((mv er obligs1 hyp-bfr concl-bfr bvar-db bvar-db1 state)
       ;;  (glcp-generic-interp-hyp/concl
       ;;   hyp concl al config.concl-clk obligs config next-bvar bvar-db
       ;;   bvar-db1 state))
       ;;    ((when er)
       ;;     (flush-hons-get-hash-table-link obligs1)
       ;;     (mv er nil state bvar-db bvar-db1))
       ;;    ((mv erp val-clause state)
       ;;     (glcp-analyze-interp-result
       ;;      concl-bfr bindings hyp-bfr id concl config state))
       ;;    ((when erp)
       ;;     (mv erp nil state bvar-db bvar-db1))
       ;;    ((mv erp val state)
       ;;     (value (list val-clause cov-clause obligs1))))
       ;; (mv erp val state bvar-db bvar-db1))


(local (defthm alist-keys-when-shape-spec-bindingsp
         (implies (shape-spec-bindingsp x)
                  (equal (alist-keys x)
                         (strip-cars x)))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp alist-keys)))))




(local (in-theory (disable glcp-generic-interp-hyp/concl-hyp)))

(local (defthm eval-of-bfr-to-param-space-self
         (implies (bfr-eval p (bfr-unparam-env p env))
                  (bfr-eval (bfr-to-param-space p p) env))
         :hints (("goal" :cases ((bdd-mode-or-p-true p env))
                  :in-theory (enable bdd-mode-or-p-true))
                 (and stable-under-simplificationp
                      '(:in-theory (enable bfr-unparam-env))))))

(local
 (defthm glcp-generic-run-parametrized-correct-lemma
   (b* (((mv erp (list val-clause cov-clause out-obligs) & &)
         (glcp-generic-run-parametrized
          hyp concl vars bindings id obligs
          config interp-st state))
        (ctrex-env
         (glcp-generic-run-parametrized-ctrex
          alist hyp concl bindings obligs config interp-st state)))
     (implies (and (glcp-generic-geval-ev hyp alist)
                   (not (glcp-generic-geval-ev concl alist))
                   (glcp-generic-geval-ev-theoremp
                    (conjoin-clauses
                     (acl2::interp-defs-alist-clauses out-obligs)))
                   (not erp)
                   (equal vars (simple-term-vars concl))
                   (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                   (equal (w state) (w state1))
                   (glcp-generic-geval-ev (disjoin cov-clause) alist)
                   )
              (not (glcp-generic-geval-ev
                    (disjoin val-clause)
                    `((env . ,(list ctrex-env)))))))
   :hints (("goal" :do-not-induct t
            :in-theory (e/d (gbc-db-empty-implies-gbc-db-vars-bounded)
                            (simple-term-vars nth update-nth
                                          pseudo-termp
                                          dumb-negate-lit))))))


(local
 (defthm glcp-generic-run-parametrized-correct
   (b* (((mv erp (list val-clause cov-clause out-obligs) &)
         (glcp-generic-run-parametrized
          hyp concl vars bindings id obligs
          config interp-st state)))
     (implies (and (glcp-generic-geval-ev hyp alist)
                   (not (glcp-generic-geval-ev concl alist))
                   (glcp-generic-geval-ev-theoremp
                    (conjoin-clauses
                     (acl2::interp-defs-alist-clauses out-obligs)))
                   (not erp)
                   (equal vars (simple-term-vars concl))
                   (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                   (equal (w state) (w state1))
                   (glcp-generic-geval-ev (disjoin cov-clause) alist)
                   )
              (not (glcp-generic-geval-ev-theoremp
                    (disjoin val-clause)))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable simple-term-vars
                                pseudo-termp
                                dumb-negate-lit
                                glcp-generic-run-parametrized
                                glcp-generic-run-parametrized-ctrex)
            :use ((:instance glcp-generic-geval-ev-falsify
                   (x (disjoin (car (mv-nth 1 (glcp-generic-run-parametrized
                                               hyp concl vars bindings id obligs
                                               config interp-st state)))))
                   (a `((env . ,(list (glcp-generic-run-parametrized-ctrex
                                       alist hyp concl bindings obligs config interp-st state)))))))))))



  ;; :hints (("goal" :do-not-induct
  ;;          t
  ;;          :in-theory
  ;;          (e/d* ()
  ;;                (glcp-generic-geval-alist-gobj-alist-to-param-space
  ;;                 glcp-generic-geval-gtests-nonnil-correct
  ;;                 glcp-generic-interp-bad-obligs-term
  ;;                 ;; shape-spec-listp-impl-shape-spec-to-gobj-list
  ;;                 (:rules-of-class :definition :here)
  ;;                 (:rules-of-class :type-prescription :here))
  ;;                (gl-cp-hint acl2::clauses-result assoc-equal
  ;;                            glcp-generic-run-parametrized not
  ;;                            glcp-error
  ;;                            acl2::fast-no-duplicatesp
  ;;                            acl2::fast-no-duplicatesp-equal))
  ;;          :restrict ((glcp-generic-geval-ev-disjoin-append ((a alist)))))
  ;;         (and stable-under-simplificationp
  ;;              (acl2::bind-as-in-definition
  ;;               (glcp-generic-run-parametrized
  ;;                hyp concl  (simple-term-vars concl) bindings id obligs config state)
  ;;               (cov-clause val-clause hyp-bfr hyp-val)
  ;;               (b* ((binding-env
  ;;                     '(let ((slice (glcp-generic-geval-ev
  ;;                                    (shape-spec-env-term
  ;;                                     (shape-spec-bindings->sspecs bindings)
  ;;                                     (list*-macro (append (strip-cars
  ;;                                                           bindings) '('nil)))
  ;;                                     nil)
  ;;                                    alist)))
  ;;                        (cons (slice-to-bdd-env (car slice) nil)
  ;;                              (cdr slice))))
  ;;                    (param-env `(genv-param ,hyp-bfr ,binding-env)))
  ;;                 `(:use
  ;;                   ((:instance glcp-generic-geval-ev-falsify
  ;;                     (x (disjoin ,cov-clause))
  ;;                     (a alist))
  ;;                    (:instance glcp-generic-geval-ev-falsify
  ;;                     (x (disjoin ,val-clause))
  ;;                     (a `((env . ,,param-env))))
  ;;                    (:instance glcp-generic-geval-gtests-nonnil-correct
  ;;                     (x ,hyp-val)
  ;;                     (hyp t)
  ;;                     (env ,binding-env)))))))
  ;;         (bfr-reasoning)))


(local
 (encapsulate nil
   ;; (defthm bfr-p-bfr-to-param-space
   ;;   (implies (and (bfr-p p) (bfr-p x))
   ;;            (bfr-p (bfr-to-param-space p x)))
   ;;   :hints(("Goal" :in-theory (enable bfr-to-param-space bfr-p))))


   (local (in-theory (disable shape-specs-to-interp-al
                              pseudo-termp pseudo-term-listp
                              shape-spec-bindingsp
                              nth update-nth
                              ; acl2::consp-by-len
                              list*-macro)))

   ;; (encapsulate nil
   ;;   (local (in-theory
   ;;           (e/d (gl-cp-hint)
   ;;                (shape-specs-to-interp-al
   ;;                 shape-spec-listp pseudo-term-listp
   ;;                 pseudo-termp pairlis$
   ;;                 shape-spec-bindingsp
   ;;                 dumb-negate-lit
   ;;                 gtests-nonnil-correct
   ;;                 no-duplicatesp-equal
   ;;                 (bfr-to-param-space)
   ;;                 gobj-alist-to-param-space
   ;;                 list*-macro binary-append shape-spec-bindings->sspecs strip-cars member-equal))))
   ;;   (defthm glcp-generic-run-parametrized-correct
   ;;     (b* (((mv erp (cons clauses out-obligs) &)
   ;;           (glcp-generic-run-parametrized
   ;;            hyp concl  vars bindings id obligs
   ;;            config state)))
   ;;       (implies (and (not (glcp-generic-geval-ev concl alist))
   ;;                     (glcp-generic-geval-ev-theoremp
   ;;                      (conjoin-clauses
   ;;                       (acl2::interp-defs-alist-clauses out-obligs)))
   ;;                     (not erp)
   ;;                     (glcp-generic-geval-ev hyp alist)
   ;;                     (acl2::interp-defs-alistp obligs)
   ;;                     (acl2::interp-defs-alistp (glcp-config->overrides config))
   ;;                     (pseudo-termp concl)
   ;;                     (pseudo-termp hyp)
   ;;                     (equal vars (simple-term-vars concl))
   ;;                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
   ;;                     (equal (w state) (w state1)))
   ;;                (not (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses)))))
   ;;     :hints (("goal" :do-not-induct
   ;;              t
   ;;              :in-theory
   ;;              (e/d* ()
   ;;                    (; glcp-generic-geval-alist-gobj-alist-to-param-space
   ;;                     glcp-generic-geval-gtests-nonnil-correct
   ;;                     glcp-generic-interp-bad-obligs-term
   ;;                     ;; shape-spec-listp-impl-shape-spec-to-gobj-list
   ;;                     (:rules-of-class :definition :here)
   ;;                     (:rules-of-class :type-prescription :here))
   ;;                    (gl-cp-hint acl2::clauses-result assoc-equal
   ;;                                glcp-generic-run-parametrized not
   ;;                                glcp-error
   ;;                                acl2::fast-no-duplicatesp
   ;;                                acl2::fast-no-duplicatesp-equal))
   ;;              :restrict ((glcp-generic-geval-ev-disjoin-append ((a alist)))))
   ;;             (and stable-under-simplificationp
   ;;                  (acl2::bind-as-in-definition
   ;;                   (glcp-generic-run-parametrized
   ;;                    hyp concl  (simple-term-vars concl) bindings id obligs config state)
   ;;                   (cov-clause val-clause hyp-bfr hyp-val)
   ;;                   (b* ((binding-env
   ;;                         '(let ((slice (glcp-generic-geval-ev
   ;;                                        (shape-spec-env-term
   ;;                                         (shape-spec-bindings->sspecs bindings)
   ;;                                         (list*-macro (append (strip-cars
   ;;                                                               bindings) '('nil)))
   ;;                                         nil)
   ;;                                        alist)))
   ;;                            (cons (slice-to-bdd-env (car slice) nil)
   ;;                                  (cdr slice))))
   ;;                        (param-env `(genv-param ,hyp-bfr ,binding-env)))
   ;;                     `(:use
   ;;                       ((:instance glcp-generic-geval-ev-falsify
   ;;                                   (x (disjoin ,cov-clause))
   ;;                                   (a alist))
   ;;                        (:instance glcp-generic-geval-ev-falsify
   ;;                                   (x (disjoin ,val-clause))
   ;;                                   (a `((env . ,,param-env))))
   ;;                        (:instance glcp-generic-geval-gtests-nonnil-correct
   ;;                                   (x ,hyp-val)
   ;;                                   (hyp t)
   ;;                                   (env ,binding-env)))))))
   ;;             (bfr-reasoning))))

   (defthm glcp-generic-run-parametrized-bad-obligs
     (b* (((mv erp (list & & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config interp-st state)))
       (implies (and (not erp)
                     (not (glcp-generic-geval-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))))
     :hints(("Goal" :in-theory (disable simple-term-vars pseudo-termp
                                        dumb-negate-lit))))

   (defthm glcp-generic-run-parametrized-ok-obligs
     (b* (((mv erp (list & & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config interp-st state)))
       (implies (and (not erp)
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))

   (defthm glcp-generic-run-parametrized-defs-alistp
     (b* (((mv erp (list & & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config interp-st state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))

   (defthm glcp-generic-run-paremetrized-w-state
     (equal (w (mv-nth 3 (glcp-generic-run-parametrized
                          hyp concl  vars bindings id obligs config interp-st state)))
            (w state)))))


(in-theory (disable glcp-generic-run-parametrized))



(in-theory (disable glcp-cases-wormhole))



(local
 (encapsulate nil
   (local (in-theory (disable pseudo-termp
                              ;; acl2::consp-by-len
                              shape-spec-bindingsp
                              nonnil-symbol-listp-pseudo-term-listp)))

   (defthm glcp-generic-run-cases-interp-defs-alistp
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config interp-st state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))


   (defthm glcp-generic-run-cases-ok-w-state
     (equal (w (mv-nth 3 (glcp-generic-run-cases
                          param-alist concl  vars obligs config interp-st state)))
            (w state)))

   (defthm glcp-generic-run-cases-correct
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config interp-st state)))
       (implies (and (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not (glcp-generic-geval-ev concl a))
                     (glcp-generic-geval-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (equal vars (simple-term-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w state) (w state1)))
                (not (glcp-generic-geval-ev-theoremp (conjoin-clauses
                                                      clauses)))))
     :hints(("Goal" :in-theory (enable strip-cars
                                       glcp-generic-geval-ev-falsify-sufficient))))


   (defthm glcp-generic-run-cases-bad-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config interp-st state)))
       (implies (and (not erp)
                     (not (glcp-generic-geval-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))))))

   (defthm glcp-generic-run-cases-ok-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config interp-st state)))
       (implies (and (not erp)
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))))


(in-theory (disable glcp-generic-run-cases))










(local
 (progn
   ;; What am I doing here?
   (defund glcp-generic-run-parametrized-placeholder (term)
     (glcp-generic-geval-ev-theoremp term))

   (defun check-top-level-bind-free (bindings mfc state)
     (declare (ignore state)
              (xargs :stobjs state))
     (and (null (acl2::mfc-ancestors mfc))
          bindings))

   (defthmd glcp-generic-run-parametrized-correct-rw
     (b* (((mv erp (list val-clause cov-clause out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config interp-st st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) acl2::mfc state)
                                (alist))
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not erp)
                     (glcp-generic-geval-ev hyp alist)
                     (equal vars (simple-term-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w st) (w state1))
                     (glcp-generic-geval-ev-theoremp (disjoin cov-clause)))
                (iff (glcp-generic-geval-ev-theoremp (disjoin val-clause))
                     (and (glcp-generic-run-parametrized-placeholder
                           (disjoin val-clause))
                          (glcp-generic-geval-ev concl alist)))))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-run-parametrized-placeholder
                                glcp-generic-geval-ev-falsify-sufficient))))

   (defund glcp-generic-run-cases-placeholder (clauses)
     (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses)))

   (defthmd glcp-generic-run-cases-correct-rw
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config interp-st st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) mfc state) (alist))
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (glcp-generic-geval-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (equal vars (simple-term-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w st) (w state1)))
                (iff (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses))
                     (and (glcp-generic-run-cases-placeholder clauses)
                          (glcp-generic-geval-ev concl a)))))
     :hints(("Goal" :in-theory (enable glcp-generic-run-cases-placeholder))))))

(local
 (defthm w-state-of-preferred-defs-to-overrides
   (equal (w (mv-nth 2 (preferred-defs-to-overrides table state)))
          (w state))
   :hints(("Goal" :in-theory (enable preferred-defs-to-overrides)))))


(defthm glcp-generic-correct
  (implies (and (pseudo-term-listp clause)
                (alistp alist)
                (glcp-generic-geval-ev-meta-extract-global-facts)
                (glcp-generic-geval-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-generic clause hints interp-st state)))
                 (glcp-generic-geval-ev-falsify
                  (conjoin-clauses
                   (acl2::clauses-result
                    (glcp-generic clause hints interp-st state))))))
           (glcp-generic-geval-ev (disjoin clause) alist))
  :hints
  (("goal" :do-not-induct
    t
    :in-theory
    (e/d* (glcp-generic-run-cases-correct-rw
           glcp-generic-run-parametrized-correct-rw)
          (glcp-analyze-interp-result-correct
           ;; glcp-generic-geval-alist-gobj-alist-to-param-space
           ;; glcp-generic-geval-gtests-nonnil-correct
           glcp-generic-run-cases-correct
           glcp-generic-run-parametrized-correct
           pseudo-term-listp-cdr
           pseudo-termp-car
           ;; acl2::consp-under-iff-when-true-listp
           glcp-generic-run-cases-bad-obligs
           ;; acl2::consp-by-len
           nfix
           ;; shape-spec-listp-impl-shape-spec-to-gobj-list
           (:rules-of-class :definition :here))
          (gl-cp-hint
           ;; Jared added acl2::fast-alist-free since that's my new name
           ;; for flush-hons-get-hash-table-link
           fast-alist-free
           flush-hons-get-hash-table-link
           acl2::clauses-result
           glcp-generic glcp-error
           assoc-equal))

    :restrict ((glcp-generic-geval-ev-disjoin-append ((a alist)))
               (glcp-generic-geval-ev-disjoin-cons ((a alist)))))
   (and stable-under-simplificationp
        (acl2::bind-as-in-definition
         glcp-generic
         (hyp-clause concl-clause params-cov-term hyp)
         `(:use ((:instance glcp-generic-geval-ev-falsify
                            (x (disjoin ,hyp-clause))
                            (a alist))
                 (:instance glcp-generic-geval-ev-falsify
                            (x (disjoin ,concl-clause))
                            (a alist))
                 (:instance glcp-generic-geval-ev-falsify
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
;  :otf-flg t
  :rule-classes nil)




;; Related clause processor which doesn't run the simulation, but
;; produces all the other necessary clauses.  We define this by
;; using a mock interp-term function that just returns T and no
;; obligs, and also a mock analyze-term
(defun glcp-fake-interp-hyp/concl (hyp concl bindings clk config interp-st
                                       next-bvar bvar-db bvar-db1 state)
  (declare (ignore hyp concl bindings clk config next-bvar)
           (xargs :stobjs (interp-st bvar-db bvar-db1 state)))
  (mv t t bvar-db1 nil interp-st bvar-db state))

(defun glcp-fake-analyze-interp-result
  (hyp-bfr val constr param-al id concl config bvar-db state)
  (declare (ignore val param-al hyp-bfr id concl config bvar-db constr)
           (xargs :stobjs (bvar-db state)))
  (mv nil '('t) state))

(defconst *glcp-side-goals-subst*
  '((interp-hyp/concl . glcp-fake-interp-hyp/concl)
    (run-cases . glcp-side-goals-run-cases)
    (run-parametrized . glcp-side-goals-run-parametrized)
    (clause-proc . glcp-side-goals-clause-proc1)
    (clause-proc-name . 'glcp-side-goals-clause-proc)
    (glcp-analyze-interp-result . glcp-fake-analyze-interp-result)))


(make-event (sublis *glcp-side-goals-subst*
                    *glcp-clause-proc-template*))

(defun glcp-side-goals-clause-proc (clause hints interp-st state)
  ;; The cheat: We only allow this clause processor on the trivially
  ;; true clause ('T).
  (declare (xargs :stobjs (interp-st state)
                  :verify-guards nil))
  (b* (((unless (equal clause '('T)))
        (mv "This clause processor can be used only on clause '('T)."
            nil interp-st state))
       ((list* & & hyp & concl &) hints))
    (glcp-side-goals-clause-proc1
     `((implies ,hyp ,concl)) hints interp-st state)))

(defevaluator glcp-side-ev glcp-side-ev-lst ((if a b c)))

(local (acl2::def-join-thms glcp-side-ev))

(defthm glcp-side-goals-clause-proc-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (glcp-side-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-side-goals-clause-proc clause hints interp-st state)))
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
;; (defun gl-universal-run-gified (fn actuals pathcond clk config bvar-db state)
;;   (declare (xargs :guard (and (symbolp fn)
;;                               (glcp-config-p config)
;;                               (natp clk))
;;                   :stobjs (bvar-db state)
;;                   :mode :program)
;;            (ignorable config bvar-db))
;;   (b* ((world (w state))
;;        (al (table-alist 'gl-function-info world))
;;        (look (assoc-eq fn al))
;;        ((unless look) (mv nil nil))
;;        (gfn (cadr look))
;;        ((mv er res)
;;         (acl2::magic-ev-fncall gfn (append actuals (list pathcond clk config
;;                                                          bvar-db state))
;;                                state t t))
;;        ((when er)
;;         (prog2$ (cw "GL-UNIVERSAL-RUN-GIFIED: error: ~@0~%" er)
;;                 (mv nil nil))))
;;     (mv t res)))

;; (defun gl-universal-apply-concrete (fn actuals state)
;;   (declare (xargs :guard (true-listp actuals)
;;                   :mode :program))
;;   (b* ((world (w state))
;;        (call (cons fn (acl2::kwote-lst actuals)))
;;        (mvals (len (fgetprop fn 'stobjs-out nil world)))
;;        (term (if (< 1 mvals) `(mv-list ,mvals ,call) call))
;;        ((mv er (cons & val) state)
;;         (acl2::simple-translate-and-eval
;;          term nil nil
;;          (acl2::msg "gl-universal-apply-concrete: ~x0" term)
;;          'gl-universal-apply-concrete world state t))
;;        ((when er)
;;         (prog2$ (cw "GL-UNIVERSAL-APPLY-CONCRETE: error: ~@0~%" er)
;;                 (mv nil nil state))))
;;     (mv t val state)))

;; (defconst *gl-universal-subst*
;;   '((run-gified . gl-universal-run-gified)
;;     (interp-term . gl-universal-interp-term)
;;     (interp-fncall-ifs . gl-universal-interp-fncall-ifs)
;;     (interp-fncall . gl-universal-interp-fncall)
;;     (interp-if . gl-universal-interp-if)
;;     (finish-or . gl-universal-finish-or)
;;     (finish-if . gl-universal-finish-if)
;;     (simplify-if-test . gl-universal-simplify-if-test)
;;     (rewrite . gl-universal-rewrite)
;;     (rewrite-apply-rules . gl-universal-rewrite-apply-rules)
;;     (rewrite-apply-rule . gl-universal-rewrite-apply-rule)
;;     (relieve-hyps . gl-universal-relieve-hyps)
;;     (relieve-hyp . gl-universal-relieve-hyp)
;;     (interp-list . gl-universal-interp-list)
;;     (interp-top-level-term . gl-universal-interp-top-level-term)
;;     (interp-concl . gl-universal-interp-concl)
;;     (interp-hyp/concl . gl-universal-interp-hyp/concl)
;;     (run-parametrized . gl-universal-run-parametrized)
;;     (run-cases . gl-universal-run-cases)
;;     (clause-proc . gl-universal)
;;     (clause-proc-name . (gl-universal-clause-proc-name))))

;; (program)

;; (make-event (sublis *gl-universal-subst* *glcp-interp-template*))
;; (make-event (sublis *gl-universal-subst* *glcp-interp-wrappers-template*))

;; (make-event (sublis *gl-universal-subst*
;;                     *glcp-run-parametrized-template*))

;; (make-event (sublis *gl-universal-subst* *glcp-run-cases-template*))

;; (make-event (sublis *gl-universal-subst*
;;                     *glcp-clause-proc-template*))

;; (logic)


;; ;; To install this as a clause processor, run the following.  Note
;; ;; that this creates a ttag.
;; (defmacro allow-gl-universal-clause-processor ()
;;   '(acl2::define-trusted-clause-processor
;;     gl-universal-clause-proc
;;     nil :ttag gl-universal-clause-proc))






;; ;; Symbolic interpreter for translated terms, based on the universal clause
;; ;; processor defined above.  X is the term, ALIST gives a
;; ;; list of bindings of variables to g-objects, hyp is a BDD.

;; (defun gl-interp-term (x alist pathcond clk bvar-db state)
;;   (declare (xargs :mode :program :stobjs (bvar-db state)))
;;   (b* ((world (w state))
;;        ((mv erp overrides state)
;;         (preferred-defs-to-overrides
;;          (table-alist 'preferred-defs world) state))
;;        ((when erp)
;;         (mv erp nil bvar-db state))
;;        ((mv er obligs ans bvar-db state)
;;         (gl-universal-interp-term
;;          x alist pathcond nil clk nil (make-glcp-config :overrides overrides) bvar-db state))
;;        ((when er) (mv er nil bvar-db state))
;;        (- (flush-hons-get-hash-table-link obligs)))
;;     (mv nil ans bvar-db state)))




;; ;; Translate the given term, then run the interpreter.
;; (defmacro gl-interp-raw (x &optional alist (hyp 't) (clk '100000))
;;   `(b* (((mv er trans state)
;;          (acl2::translate ,x t t t 'gl-interp (w state)
;;                           state))
;;         ((when er) (mv er nil bvar-db state)))
;;      (gl-interp-term trans ,alist ,hyp ,clk state)))



;; (defun gl-parametrize-by-hyp-fn (hyp al bvar-db state)
;;   (declare (xargs :mode :program))
;;   (b* ((al (shape-specs-to-interp-al al))
;;        ((er hyp-pred) (gl-interp-raw hyp al))
;;        (hyp-test (gtests hyp-pred t))
;;        (hyp-bfr (bfr-or (gtests-nonnil hyp-test)
;;                       (gtests-unknown hyp-test))))
;;     (value (gobj-to-param-space al hyp-bfr))))

;; (defmacro gl-parametrize-by-hyp (hyp bindings)
;;   `(gl-parametrize-by-hyp-fn ,hyp ,bindings state))


(table latest-greatest-gl-clause-proc nil *glcp-generic-template-subst* :clear)

(defun gl-interp-fn (hyp term al config state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((gobj-al (shape-specs-to-interp-al al))
       ((mv erp overrides state)
        (preferred-defs-to-overrides
         (table-alist 'preferred-defs (w state)) state))
       ((when erp) (mv erp nil nil nil state))
       ((mv erp hyp-trans state)
        (acl2::translate hyp t t t 'gl-interp (w state)
                         state))
       ((when erp) (mv erp nil nil nil state))
       ((mv erp term-trans state)
        (acl2::translate term t t t 'gl-interp (w state)
                         state))
       ((when erp) (mv erp nil nil nil state))
       (config (or config (make-glcp-config :overrides overrides)))
       (interp-fn (cdr (assoc 'interp-term-under-hyp
                              (table-alist 'latest-greatest-gl-clause-proc
                                           (w state)))))
       (next-bvar (shape-spec-max-bvar-list (shape-spec-bindings->sspecs al)))
       (form `(,interp-fn ',hyp-trans ',term-trans ',gobj-al ',next-bvar ',config
                          interp-st bvar-db bvar-db1 state))
       ((mv trans-eval-erp (cons ?stobjs-out
                                 (list hyp-bfr param-al res-obj interp-erp
                                       ;; and some stobj symbols
                                       ))
            state)
        (acl2::trans-eval form 'gl-interp state t))
       ((when trans-eval-erp) (mv trans-eval-erp nil nil nil state))
       ((when interp-erp) (mv interp-erp nil nil nil state)))
    (mv nil hyp-bfr param-al res-obj state)))


(defmacro gl-interp (term al &key (hyp 't) (config 'nil))
  `(gl-interp-fn ',hyp ',term ,al ',config state))

(defxdoc gl-interp
  :parents (reference)
  :short "Symbolically interpret a term using GL, with inputs generated by
parametrization."

  :long "<p>Usage:</p>

@({
 (gl-interp term bindings :hyp hyp)
})

<p>The above form runs a symbolic interpretation of @('term') on the symbolic input
assignment produced by parametrizing @('bindings') using @('hyp').  The symbolic
execution run by this form is similar to that run by</p>

@({
 (def-gl-thm <name> :hyp hyp :concl term :g-bindings bindings).
})

<p>@('bindings') should be a binding list of the same kind as taken by @(see
def-gl-thm), that is, a list of elements @('(var val)') such that @('var') is a
variable free in @('term'), and @('val') is a shape specifier; see @(see
shape-specs).</p>

<p>Similar to @('def-gl-thm'), @('term') and @('hyp') should be the (unquoted)
terms of interest, whereas @('bindings') should be something that evaluates to
the binding list (the quotation of that binding list, for example.)</p>

<p>In more detail: First, the input bindings are converted to an assignment of
symbolic inputs to variables.  The hyp term is symbolically interpreted using
this variable assignment, yielding a predicate.  The symbolic input assignment
is parametrized using this predicate to produce a new such assignment whose
coverage is restricted to the subset satisfying the hyp.  The term is then
symbolically interpreted using this assignment, and the result is returned.</p>

<p>This macro expands to a function call taking state and the bvar-db and
bvar-db1 live stobjs. It returns:</p>

@({
 (mv error-message hyp-bfr param-al result bvar-db bvar-db1 state)
})

<p>The symbolic interpreter used by @('gl-interp') is the latest interpreter
defined using def-gl-clause-processor (as recorded in the
gl::latest-greatest-gl-clause-proc table).</p>")

