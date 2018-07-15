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
(include-book "gl-generic-interp-defs")
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/decomp-hint" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)
(include-book "var-bounds")
(include-book "constraint-db-deps")
(include-book "clause-processors/find-subterms" :dir :system)
(include-book "glcp-unify-thms")
(include-book "glcp-geval-thms")
(local (include-book "bfr-reasoning"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "general-object-thms"))
(local (include-book "tools/with-quoted-forms" :dir :system))
(local (include-book "hyp-fix"))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (in-theory (disable* set::double-containment w)))
(local (include-book "std/util/termhints" :dir :system))
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

(progn ;; sublis-into-term-pseudo-termp
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


(set-state-ok t)

(local (defthm nonnil-symbol-listp-impl-eqlable-listp
         (implies (nonnil-symbol-listp x)
                  (eqlable-listp x))
         :hints(("Goal" :in-theory (enable nonnil-symbol-listp)))))


(local (in-theory (disable* general-concretep-def acl2-count
;                            set::double-containment
                            integer-abs
;                            set::nonempty-means-set
                            equal-of-booleans-rewrite
                            put-global
                            acl2::true-list-listp-forward-to-true-listp-assoc-equal)))


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
               (glcp-generic-geval-ev hyp (glcp-generic-geval-alist bindings env)))))

  (defthm glcp-relieve-hyp-synp-not-unreachable-error
    (not (equal (mv-nth 0 (glcp-relieve-hyp-synp hyp bindings st))
                :unreachable))))

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
      (true-listp (gl-termlist-to-apply-obj-list x alist))
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
               (equal (glcp-generic-geval-list (gl-termlist-to-apply-obj-list x alist) env)
                      (glcp-generic-geval-ev-lst x (glcp-generic-geval-alist alist env))))
      :hints ('(:expand ((gl-termlist-to-apply-obj-list x alist)
                         (gl-termlist-to-apply-obj-list nil alist))))
      :flag gl-termlist-to-apply-obj-list))

  (defthm-gl-term-to-apply-obj-flag
    (defthm gobj-depends-on-of-gl-term-to-apply-obj
      (implies (not (gobj-alist-depends-on k p alist))
               (not (gobj-depends-on k p (gl-term-to-apply-obj x alist))))
      :hints ('(:expand ((gl-term-to-apply-obj nil alist)
                         (gl-term-to-apply-obj x alist))))
      :flag gl-term-to-apply-obj)
    (defthm gobj-depends-on-of-gl-term-to-apply-obj-list
      (implies (not (gobj-alist-depends-on k p alist))
               (not (gobj-list-depends-on k p (gl-termlist-to-apply-obj-list x alist))))
      :hints ('(:expand ((gl-termlist-to-apply-obj-list nil alist)
                         (gl-termlist-to-apply-obj-list x alist))))
      :flag gl-termlist-to-apply-obj-list)))


(make-event
 `(in-theory (disable . ,(glcp-put-name-each 'glcp-generic
                                             (event-form-collect-fn-names
                                              *glcp-interp-template*)))))

(local (in-theory (disable acl2::weak-rewrite-rule-p)))

(with-output :off (prove event) ;; glcp-generic-interp-flg
  (flag::make-flag glcp-generic-interp-flg
                   glcp-generic-interp-term
                   :flag-mapping
                   ((glcp-generic-interp-test . test)
                    (glcp-generic-interp-term-equivs . equivs)
                    (glcp-generic-interp-term . term)
                    ;; (glcp-generic-interp-fncall-ifs . fncall-ifs)
                    ;; (glcp-generic-maybe-interp-fncall-ifs . maybe-fncall-ifs)
                    (glcp-generic-interp-fncall . fncall)
                    (glcp-generic-interp-if/or . if/or)
                    (glcp-generic-maybe-interp . maybe)
                    (glcp-generic-interp-or . or)
                    (glcp-generic-interp-if . if)
                    (glcp-generic-merge-branches . merge)
                    (glcp-generic-merge-branch-subterms . merge-sub)
                    (glcp-generic-merge-branch-subterm-lists . merge-list)
                    (glcp-generic-maybe-simplify-if-test . maybe-test-simp)
                    (glcp-generic-simplify-if-test . test-simp)
                    (glcp-generic-simplify-if-test-fncall . test-simp-fncall)
                    (glcp-generic-add-bvar-constraints . constraints)
                    (glcp-generic-add-bvar-constraint-substs . constraint-substs)
                    (glcp-generic-rewrite . rewrite)
                    (glcp-generic-rewrite-apply-rules . rules)
                    (glcp-generic-rewrite-apply-rule . rule)
                    (glcp-generic-relieve-hyps . hyps)
                    (glcp-generic-relieve-hyp . hyp)
                    (glcp-generic-interp-list . list))
                   :formals-subst ((state . st))
                   :hints (("goal" :in-theory
                            (e/d (acl2-count
                                  acl2-count-of-car-g-apply->args
                                  acl2-count-of-cadr-g-apply->args
                                  acl2-count-last-cdr-when-cadr-hack
                                  acl2-count-of-general-consp-car
                                  acl2-count-of-general-consp-cdr)
                                 (last))))))

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
       (add-concls (append (cadr (assoc-keyword :add-concls kws))
                           (cadr (assoc-keyword :add-concls fn-kws))))
       (add-bindings (cadr (assoc-keyword :add-bindings kws)))
       (skip (cadr (assoc-keyword :skip fn-kws)))
       (full-hyps (if hyps
                      (if add-hyps `(and ,hyps ,add-hyps) hyps)
                    add-hyps))
       (concl (if body
                  `(and ,body . ,add-concls)
                `(and . ,add-concls)))
       (full-body (if full-hyps
                      `(implies ,full-hyps
                                ,concl)
                    concl)))
    `(defthm ,(or (cadr (assoc-keyword :name fn-kws))
                  (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name basename) "-" (symbol-name flag))
                   basename))
       (b* (,binder
            . ,add-bindings)
         ,full-body)
       :hints (,@(let* ((fn-expand-look (assoc-keyword :expand-call fn-kws))
                        (expand (if fn-expand-look
                                    (cadr fn-expand-look)
                                  (cadr (assoc-keyword :expand-calls kws)))))
                   (and expand
                        `((acl2::just-expand (,(cadr binder))
                                             :last-only t
                                             :mark-only ,(eq expand :mark-only))
                          . ,(and (not (or (cadr (assoc-keyword :do-not-undo kws))
                                         (cadr (assoc-keyword :do-not-undo fn-kws))))
                                  '('(:do-not nil))))))
                 ,@(cadr (assoc-keyword :hints fn-kws)))
       :rule-classes ,(or (cadr (assoc-keyword :rule-classes fn-kws))
                          (cadr (assoc-keyword :rule-classes kws))
                          :rewrite)
       :skip ,skip
       :flag ,flag)))

(defconst *glcp-ind-inputs*
  (subst 'st 'state *glcp-common-inputs*))
(defconst *glcp-ind-retvals*
  '(?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1))

(defconst *glcp-generic-interp-signatures*
  ;; flag call returns
  `((test
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-interp-test x alist . ,*glcp-ind-inputs*))
    (term
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-interp-term x alist contexts . ,*glcp-ind-inputs*))
    (equivs
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-interp-term-equivs x alist contexts . ,*glcp-ind-inputs*))
    ;; (fncall-ifs
    ;;  (mv ?val . ,*glcp-ind-retvals*)
    ;;  (glcp-generic-interp-fncall-ifs fn actuals x contexts . ,*glcp-ind-inputs*))
    ;; (maybe-fncall-ifs
    ;;  (mv ?unreachp ?val . ,*glcp-ind-retvals*)
    ;;  (glcp-generic-maybe-interp-fncall-ifs fn actuals x contexts branchcond . ,*glcp-ind-inputs*))
    (fncall
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-interp-fncall fn actuals x contexts . ,*glcp-ind-inputs*))
    (if/or
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-interp-if/or test tbr fbr x alist contexts . ,*glcp-ind-inputs*))
    (maybe
     (mv ?unreachp ?val . ,*glcp-ind-retvals*)
     (glcp-generic-maybe-interp x alist contexts branchcond . ,*glcp-ind-inputs*))
    (if
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-interp-if test tbr fbr x alist contexts . ,*glcp-ind-inputs*))
    (or
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-interp-or test fbr x alist contexts . ,*glcp-ind-inputs*))
    (merge
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-merge-branches test-bfr then else x switchedp contexts . ,*glcp-ind-inputs*))
    (merge-sub
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-merge-branch-subterms test-bfr then else x contexts . ,*glcp-ind-inputs*))
    (merge-list
        (mv ?val . ,*glcp-ind-retvals*)
        (glcp-generic-merge-branch-subterm-lists test-bfr then else x
                                                 . ,*glcp-ind-inputs*))
    (maybe-test-simp
     (mv ?unreachp ?val . ,*glcp-ind-retvals*)
     (glcp-generic-maybe-simplify-if-test test-obj branchcond . ,*glcp-ind-inputs*))
    (test-simp
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-simplify-if-test test-obj . ,*glcp-ind-inputs*))
    (test-simp-fncall
     (mv ?val . ,*glcp-ind-retvals*)
     (glcp-generic-simplify-if-test-fncall fn args . ,*glcp-ind-inputs*))
    (constraints
     (mv . ,*glcp-ind-retvals*)
     (glcp-generic-add-bvar-constraints lit . ,*glcp-ind-inputs*))
    (constraint-substs
     (mv . ,*glcp-ind-retvals*)
     (glcp-generic-add-bvar-constraint-substs substs . ,*glcp-ind-inputs*))
    (rewrite
     (mv ?successp ?term ?bindings . ,*glcp-ind-retvals*)
     (glcp-generic-rewrite fn actuals rwtype contexts . ,*glcp-ind-inputs*))
    (rules
     (mv ?successp ?term ?bindings . ,*glcp-ind-retvals*)
     (glcp-generic-rewrite-apply-rules
      fn-rewrites rules fn actuals contexts . ,*glcp-ind-inputs*))
    (rule
     (mv ?successp ?term ?bindings . ,*glcp-ind-retvals*)
     (glcp-generic-rewrite-apply-rule
      rule fn actuals contexts . ,*glcp-ind-inputs*))
    (hyps
     (mv ?successp ?bindings1 . ,*glcp-ind-retvals*)
     (glcp-generic-relieve-hyps
      rune hyps bindings . ,*glcp-ind-inputs*))
    (hyp
     (mv ?successp ?bindings1 . ,*glcp-ind-retvals*)
     (glcp-generic-relieve-hyp
      rune hyp bindings . ,*glcp-ind-inputs*))
    (list
     (mv ?vals . ,*glcp-ind-retvals*)
     (glcp-generic-interp-list x alist . ,*glcp-ind-inputs*))))


(defun interp-thm-body-calls (list basename keys)
  (declare (xargs :mode :program))
  (if (atom list)
      nil
    (cons (def-glcp-interp-thm-body
            (cdar list) basename keys (caar list))
          (interp-thm-body-calls (cdr list) basename keys))))



(defun def-glcp-interp-thm-fn (basename keys)
  (declare (xargs :mode :program))
  `(with-output :off (prove) ;; induction scheme too big to print
     (defthm-glcp-generic-interp-flg
       ,@(interp-thm-body-calls *glcp-generic-interp-signatures* basename keys)
       :hints (,@(and (cadr (assoc-keyword :expand-calls keys))
                      `(("Goal" :do-not '(simplify preprocess))))
                 ,@(cadr (assoc-keyword :hints keys)))
       :no-induction-hint ,(cadr (assoc-keyword :no-induction-hint keys)))))

(defmacro def-glcp-interp-thm (basename &rest keys)
  (def-glcp-interp-thm-fn basename keys))







(def-glcp-interp-thm glcp-generic-interp-w-state-preserved
  :body (equal (w state1) (w st))
  :expand-calls t)

(def-glcp-interp-thm glcp-generic-interp-pathcond-preserved
  :body (equal pathcond1 (bfr-hyp-fix pathcond))
  :hints(("Goal" :in-theory (disable bfr-hyp-fix-when-hyp$ap)))
  :expand-calls t)

(local (defun def-glcp-pathcond-hyp-fix-thms (fns alist world)
         (if (atom fns)
             nil
           (cons
            (let* ((fn (car fns))
                   (formals (subst 'st 'state (formals fn world)))
                   (flag (cdr (assoc fn alist)))
                   (call1 `(,fn . ,(subst '(bfr-hyp-fix pathcond) 'pathcond
                                         formals)))
                   (call2 `(,fn . ,formals)))
              `(defthm ,(intern-in-package-of-symbol
                         (concatenate 'string (symbol-name fn)
                                      "-OF-BFR-HYP-FIX")
                         fn)
                 (equal ,call1 ,call2)
                 :hints ((acl2::just-expand (,call1 ,call2)
                                             :last-only t)
                         '(:do-not nil))
                 :flag ,flag))
            (def-glcp-pathcond-hyp-fix-thms (cdr fns) alist world)))))

(make-event
 `(with-output
   :off (prove)
   (defthm-glcp-generic-interp-flg
     ,@(def-glcp-pathcond-hyp-fix-thms
         (getprop 'glcp-generic-interp-term
                  'recursivep nil 'current-acl2-world (w state))
         (caddr (assoc 'glcp-generic-interp-term
                       (table-alist 'flag::flag-fns (w state))))
         (w state))
     :hints (("goal" :do-not '(preprocess simplify))))))

(local (defun def-glcp-pathcond-congruences (fns world)
         (if (atom fns)
             nil
           (cons
            (let* ((fn (car fns))
                   (formals (subst 'st 'state (formals fn world)))
                   (call1 `(,fn . ,(subst 'pathcond1 'pathcond
                                         formals)))
                   (call2 `(,fn . ,formals))
                   (bhf-thm (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name fn)
                                          "-OF-BFR-HYP-FIX")
                             fn)))
              `(defthm ,(intern-in-package-of-symbol
                         (concatenate 'string (symbol-name fn)
                                      "-PATHCOND-CONGRUENCE")
                         fn)
                 (implies (bfr-hyp-equiv pathcond1 pathcond)
                          (equal ,call1 ,call2))
                 :hints (("goal" :use ((:instance ,bhf-thm)
                                       (:instance ,bhf-thm
                                        (pathcond pathcond1)))
                          :in-theory (disable ,bhf-thm)))
                 :rule-classes :congruence))
            (def-glcp-pathcond-congruences (cdr fns) world)))))

(make-event
 `(with-output
   :off (prove)
   (progn
     . ,(def-glcp-pathcond-congruences
          (getprop 'glcp-generic-interp-term
                   'recursivep nil 'current-acl2-world (w state))
          (w state)))))




(local ;; alistp-glcp-generic-rewrite
 (with-output :off (prove)
   (defthm-glcp-generic-interp-flg
     (defthm alistp-glcp-generic-rewrite
       (b* (((mv ?successp ?term ?bindings ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
             (glcp-generic-rewrite fn actuals rwtype contexts pathcond clk config interp-st bvar-db st)))
         (alistp bindings))
       :hints ('(:expand ((glcp-generic-rewrite fn actuals rwtype contexts pathcond clk config interp-st
                                                bvar-db st))))
       :flag rewrite)
     (defthm alistp-glcp-generic-apply-rules
       (b* (((mv ?successp ?term ?bindings ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
             (glcp-generic-rewrite-apply-rules
              fn-rewrites rules fn actuals contexts pathcond clk config interp-st bvar-db st)))
         (alistp bindings))
       :hints ('(:expand ((glcp-generic-rewrite-apply-rules
                           fn-rewrites rules fn actuals contexts pathcond clk config interp-st bvar-db st))))
       :flag rules)
     (defthm alistp-glcp-generic-apply-rule
       (b* (((mv ?successp ?term ?bindings ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
             (glcp-generic-rewrite-apply-rule
              rule fn actuals contexts pathcond clk config interp-st bvar-db st)))
         (alistp bindings))
       :hints ('(:expand ((:free (fn)
                           (glcp-generic-rewrite-apply-rule
                            rule fn actuals contexts pathcond clk config interp-st bvar-db st)))))
       :flag rule)
     (defthm alistp-glcp-generic-relieve-hyps
       (b* (((mv ?successp ?bindings1 ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
             (glcp-generic-relieve-hyps
              rune hyps bindings pathcond clk config interp-st bvar-db st)))
         (equal bindings1
                (if erp nil bindings)))
       :hints ('(:expand ((glcp-generic-relieve-hyps
                           rune hyps bindings pathcond clk config interp-st bvar-db st))))
       :flag hyps)
     (defthm alistp-glcp-generic-relieve-hyp
       (b* (((mv ?successp ?bindings1 ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
             (glcp-generic-relieve-hyp
              rune hyp bindings pathcond clk config interp-st bvar-db st)))
         (equal bindings1
                (if erp nil bindings)))
       :hints ('(:expand ((glcp-generic-relieve-hyp
                           rune hyp bindings pathcond clk config interp-st bvar-db st))))
       :flag hyp)
     :skip-others t)))


(local ;; glcp-generic-geval-thms
 (defsection glcp-generic-geval-thms
   (local (in-theory (disable glcp-generic-geval-alt-def)))
   (set-ignore-ok t)

   (acl2::def-functional-instance
     glcp-generic-geval-gobj-ite-merge-correct
     gobj-ite-merge-correct
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x env))
                        (glcp-generic-geval-list x env)))))

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
     glcp-generic-geval-gl-args-split-ite-correct
     gl-args-split-ite-correct
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list)))

   (acl2::def-functional-instance
     glcp-generic-geval-gl-fncall-maybe-split-correct
     gl-fncall-maybe-split-correct
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list)))

   (acl2::def-functional-instance
     glcp-generic-geval-gl-cons-maybe-split-correct
     gl-cons-maybe-split-correct
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list)))))

(local (in-theory (enable glcp-generic-geval-gtests-nonnil-correct)))

(progn ;; pseudo-termp stuff

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
             (pseudo-termp (car (last x))))
    :hints(("Goal" :in-theory (enable last))))

  (defthm pseudo-termp-car-last
    (implies (and (pseudo-termp x)
                  (< 1 (len x))
                  (not (equal (car x) 'quote)))
             (pseudo-termp (car (last x))))
    :hints(("Goal" :expand ((pseudo-termp x))))))



(defsection glcp-generic-interp-obligs-okp
  (local (in-theory (disable
                     set::sets-are-true-lists
                     pseudo-term-listp
                     (:t hyp-fix)
                     (:t acl2::interp-defs-alistp)
                     (:t pseudo-termp)
                     (:t glcp-generic-interp-term)
                     (:t glcp-generic-interp-term-equivs)
                     (:t glcp-generic-interp-test)
                     (:t glcp-generic-interp-if/or)
                     (:t glcp-generic-interp-if)
                     (:t glcp-generic-interp-or)
                     (:t glcp-generic-merge-branches)
                     (:t glcp-generic-merge-branch-subterms)
                     (:t glcp-generic-merge-branch-subterm-lists)
                     (:t gtests)
                     (:t pseudo-term-listp)
                     (:t general-concrete-listp)
                     (:t len)
                     (:t glcp-generic-rewrite)
                     (:t glcp-generic-interp-list)
                     (:t acl2::interp-function-lookup)
                     (:t glcp-generic-simplify-if-test)
                     (:t glcp-generic-simplify-if-test-fncall)
                     acl2::cancel_times-equal-correct
                     acl2::cancel_plus-equal-correct
                     fgetprop
                     len
                     nth update-nth
                     default-car default-cdr
                     true-listp-update-nth
                     no-duplicatesp-equal
                     member-equal
                     hons-assoc-equal
                     acl2::weak-rewrite-rule-p
                     general-concrete-listp
                     general-concrete-obj-list
                     not
                     true-listp
                     hyp-fix-of-hyp-fixedp
                     pseudo-termp)))
  (def-glcp-interp-thm glcp-generic-interp-obligs-okp
    :hyps (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
               (acl2::interp-defs-alistp (glcp-config->overrides config)))
    :body (acl2::interp-defs-alistp (nth *is-obligs* interp-st1))
    :special
    ((test :add-hyps (pseudo-termp x))
     (term :add-hyps (pseudo-termp x))
     (equivs :add-hyps (pseudo-termp x))
     (if/or :add-hyps (and (pseudo-termp test)
                           (pseudo-termp tbr)
                           (pseudo-termp fbr)))
     (maybe :add-hyps (pseudo-termp x))
     (if :add-hyps (and (pseudo-termp test)
                           (pseudo-termp tbr)
                           (pseudo-termp fbr)))
     (or :add-hyps (and (pseudo-termp test)
                        (pseudo-termp fbr)))
     (list :add-hyps (pseudo-term-listp x))
     (hyp :add-hyps (pseudo-termp hyp))
     (hyps :add-hyps (pseudo-term-listp hyps))
     ;; (fncall-ifs :add-hyps (and (symbolp fn)
     ;;                            (not (eq fn 'quote))))
     ;; (maybe-fncall-ifs :add-hyps (and (symbolp fn)
     ;;                                  (not (eq fn 'quote))))
     (fncall :add-hyps (and (symbolp fn)
                            (not (eq fn 'quote))))
     (rewrite :body (implies (and (symbolp fn)
                                  (not (eq fn 'quote)))
                             (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st1))
                                  (pseudo-termp term))))
     (rules :body (implies (and (symbolp fn)
                                (not (eq fn 'quote)))
                           (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st1))
                                (pseudo-termp term))))
     (rule :body (implies (and (symbolp fn)
                               (not (eq fn 'quote)))
                          (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st1))
                               (pseudo-termp term)))))
    :expand-calls t))

(local ;; true-listp-glcp-generic-interp-list
 (with-output :off (prove)
   (defthm-glcp-generic-interp-flg
     (defthm true-listp-glcp-generic-interp-list
       (true-listp (mv-nth 0 (glcp-generic-interp-list
                              x alist pathcond clk config interp-st bvar-db st)))
       :hints('(:expand (glcp-generic-interp-list
                         x alist pathcond clk config interp-st bvar-db st)
                :in-theory (enable gl-cons)))
       :rule-classes :type-prescription
       :flag list)
     :skip-others t)))

(local ;; true-listp-glcp-generic-merge-branch-subterm-lists
 (with-output :off (prove)
   (defthm-glcp-generic-interp-flg
     (defthm true-listp-glcp-generic-merge-branch-subterm-lists
       (true-listp (mv-nth 0 (glcp-generic-merge-branch-subterm-lists
                              test-bfr then else x pathcond clk config interp-st bvar-db st)))
       :hints('(:expand (glcp-generic-merge-branch-subterm-lists
                         test-bfr then else x pathcond clk config interp-st bvar-db st)
                :in-theory (enable gl-cons)))
       :rule-classes :type-prescription
       :flag merge-list)
     :skip-others t)))

(local (include-book "system/f-put-global" :dir :system))
(local (in-theory (disable state-p1-forward)))

(defsection glcp-generic-interp-state-p1-preserved
  (local (in-theory (disable* pseudo-termp
                              symbol-listp
                              hyp-fix-of-hyp-fixedp
                              state-p-implies-and-forward-to-state-p1
                              len nth update-nth
                              default-car default-cdr
                              (:rules-of-class :type-prescription :here))))
  (def-glcp-interp-thm glcp-generic-interp-state-p1-preserved
    :body (implies (state-p1 st)
                   (state-p1 state1))

    :expand-calls t))

(local (defthm true-listp-gl-cons
         (equal (true-listp (gl-cons x y))
                (true-listp y))
         :hints(("Goal" :in-theory (enable gl-cons)))))

(local (defthm consp-last
         (equal (consp (last x))
                (consp x))))

(set-ignore-ok t)

(defthm plist-worldp-of-w-state
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :hints(("Goal" :in-theory (e/d (state-p1 get-global w)
                                 (all-boundp)))))

(local (defthm nonnil-symbol-listp-true-listp
         (implies (nonnil-symbol-listp x)
                  (true-listp x))))

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

(local ;; len-of-glcp-generic-interp-list
 (with-output :off (prove)
   (progn
     (defthm len-gl-cons
       (equal (len (gl-cons x y))
              (+ 1 (len y)))
       :hints(("Goal" :in-theory (enable gl-cons))))

     (defthm-glcp-generic-interp-flg
       (defthm len-of-glcp-generic-interp-list
         (mv-let (res erp)
           (glcp-generic-interp-list
            x alist pathcond clk config interp-st bvar-db st)
           (implies (not erp)
                    (equal (len res)
                           (len x))))
         :hints ('(:expand ((glcp-generic-interp-list
                             x alist pathcond clk config interp-st bvar-db st))))
         :flag list)
       :skip-others t))))

(local (defthmd contextsp-implies-true-listp
         (implies (contextsp x)
                  (true-listp x))
         :rule-classes :forward-chaining))

(defsection glcp-branch-merge-formula-to-rule

  (defthm conjunction-to-list-correct
    (iff (glcp-generic-geval-ev (conjoin (conjunction-to-list x)) a)
         (glcp-generic-geval-ev x a))
    :hints(("Goal" :in-theory (enable conjunction-to-list))))

  (local (in-theory (disable acl2::beta-reduce-full
                             pseudo-termp)))

  (local (in-theory (enable glcp-branch-merge-formula-to-rule)))

  (defthm glcp-branch-merge-formula-to-rule-wfp
    (b* (((mv ok rule)
          (glcp-branch-merge-formula-to-rule name wrld)))
      (implies ok
               (acl2::weak-rewrite-rule-p rule)))
    :hints(("Goal" :in-theory (disable acl2::weak-rewrite-rule-p))))

  (local (defthmd beta-reduce-full-correct-for-glcp-generic-geval-ev
           (implies (pseudo-termp x)
                    (equal (glcp-generic-geval-ev (acl2::beta-reduce-full x) a)
                           (glcp-generic-geval-ev x a)))
           :hints (("goal" :use ((:instance
                                  (:functional-instance
                                   acl2::beta-reduce-full-correct
                                   (acl2::beta-eval glcp-generic-geval-ev)
                                   (acl2::beta-eval-list
                                    glcp-generic-geval-ev-lst))))
                    :in-theory (enable glcp-generic-geval-ev-of-fncall-args)))))


  (defthmd rewrite-rule-term-alt-def
    (equal (acl2::rewrite-rule-term x)
           (if (eq (acl2::rewrite-rule->subclass x) 'acl2::meta)
               ''t
             `(implies ,(conjoin (acl2::rewrite-rule->hyps x))
                       (,(acl2::rewrite-rule->equiv x)
                        ,(acl2::rewrite-rule->lhs x)
                        ,(acl2::rewrite-rule->rhs x)))))
    :hints(("Goal" :in-theory (enable acl2::rewrite-rule->subclass
                                      acl2::rewrite-rule->hyps
                                      acl2::rewrite-rule->equiv
                                      acl2::rewrite-rule->lhs
                                      acl2::rewrite-rule->rhs))))

  (local (in-theory (disable acl2::rewrite-rule-term)))

  ; (local (include-book "arithmetic/top-with-meta" :dir :system))

  (local (defthm equal-of-len
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (and (natp n)
                                (if (equal n 0)
                                    (atom x)
                                  (and (consp x)
                                       (equal (len (cdr x)) (1- n)))))))))



  (defthm glcp-branch-merge-formula-to-rule-correct
    (b* (((mv ok rule)
          (glcp-branch-merge-formula-to-rule name wrld)))
      (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                    (equal wrld (w state))
                    ok)
               (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term rule))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify
                           (x (acl2::meta-extract-formula-w name wrld))
                           (a (glcp-generic-geval-ev-falsify
                               (acl2::rewrite-rule-term
                                (mv-nth 1 (glcp-branch-merge-formula-to-rule
                                           name wrld))))))
                          (:instance
                           beta-reduce-full-correct-for-glcp-generic-geval-ev
                           (x (acl2::meta-extract-formula-w name wrld))
                           (a (glcp-generic-geval-ev-falsify
                               (acl2::rewrite-rule-term
                                (mv-nth 1 (glcp-branch-merge-formula-to-rule
                                           name wrld)))))))
             :expand ((glcp-branch-merge-formula-to-rule name wrld))
             :in-theory (e/d (glcp-generic-geval-ev-of-fncall-args
                              rewrite-rule-term-alt-def)
                             (equal-of-booleans-rewrite
                              default-car default-cdr
                              set::double-containment
                              len kwote-lst
                              w))))))

(defun good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (good-rewrite-rulesp (cdr rules)))))

(defsection glcp-branch-merge-formulas-to-rules

  (local (in-theory (enable glcp-branch-merge-formulas-to-rules)))

  (defthm good-rewrite-rulesp-of-glcp-branch-merge-formulas-to-rules
    (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (good-rewrite-rulesp
              (glcp-branch-merge-formulas-to-rules names wrld)))
    :hints(("Goal" :in-theory (e/d (good-rewrite-rulesp)
                                   (acl2::rewrite-rule-term
                                    rewrite-rule-term-alt-def)))))

  (defthm weak-rewrite-rule-listp-of-glcp-branch-merge-formulas-to-rules
    (weak-rewrite-rule-listp
     (glcp-branch-merge-formulas-to-rules names wrld))))

(defsection good-rewrite-rulesp-of-get-lemmas
  (local (defthmd good-rewrite-rulesp-of-get-lemmas1
           (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                         (subsetp rules (getprop fn 'acl2::lemmas nil
                                                 'current-acl2-world (w state))))
                    (good-rewrite-rulesp rules))
           :hints(("Goal" :in-theory (e/d (subsetp-equal
                                           good-rewrite-rulesp)
                                          (acl2::rewrite-rule-term
                                           rewrite-rule-term-alt-def
                                           w))))))
  (defthm good-rewrite-rulesp-of-get-lemmas
    (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (good-rewrite-rulesp
              (getprop fn 'acl2::lemmas nil
                       'current-acl2-world (w state))))
    :hints (("goal" :use ((:instance good-rewrite-rulesp-of-get-lemmas1
                           (rules
                            (getprop fn 'acl2::lemmas nil
                                     'current-acl2-world (w state)))))))))

(defthm good-rewrite-rules-of-glcp-get-branch-merge-rules
  (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
                (equal wrld (w state)))
           (good-rewrite-rulesp (glcp-get-branch-merge-rules fn wrld)))
  :hints(("Goal" :in-theory (enable glcp-get-branch-merge-rules))))

(defthm weak-rewrite-rule-listp-of-glcp-get-branch-merge-rules
  (weak-rewrite-rule-listp
   (glcp-get-branch-merge-rules fn wrld))
  :hints(("Goal" :in-theory (enable glcp-get-branch-merge-rules))))

(defsection glcp-generic-interp-guards-ok
  (local (defthm len-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (make-event
   (b* (((er &) (in-theory nil))
        ((er thm) (get-guard-verification-theorem 'glcp-generic-interp-term state)))
     (value
      `(with-output :off (prove)
         (defthm glcp-generic-interp-guards-ok
           ,thm
           :hints (("goal" :in-theory
                    (e/d* (pseudo-termp-car-last-of-pseudo-term-listp
                           gl-aside gl-ignore gl-error-is-nil
                           contextsp-implies-true-listp)
                          (glcp-generic-interp-term
                           glcp-generic-interp-list
                           acl2::weak-rewrite-rule-p
                           consp-assoc-equal
                           pseudo-term-listp
                           w
                           nth update-nth
                           contextsp
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
                           (:type-prescription hons-assoc-equal)
                           (:t type-of-get-term->bvar$a)))
                    :do-not-induct t))
           :rule-classes nil))))))

(local (defthm car-last-when-length-4
         (implies (equal (len x) 4)
                  (equal (car (last x))
                         (cadddr x)))
         :hints(("Goal" :in-theory (enable len last)))))

(local ;; glcp-generic-interp-function-lookup-theoremp-defs-history-rev
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
                       (acl2::interp-defs-alist-clauses out-defs)))))))


   ;; (defthm glcp-generic-interp-function-lookup-theoremp-defs-history-fwd
   ;;   (b* (((mv erp & & out-defs)
   ;;         (acl2::interp-function-lookup fn in-defs overrides world)))
   ;;     (implies (and (glcp-generic-geval-ev-theoremp
   ;;                    (conjoin-clauses
   ;;                     (acl2::interp-defs-alist-clauses out-defs)))
   ;;                   (not erp))
   ;;              (glcp-generic-geval-ev-theoremp
   ;;               (conjoin-clauses
   ;;                (acl2::interp-defs-alist-clauses in-defs)))))
   ;;   :rule-classes :forward-chaining)

   ))

(local (in-theory (disable acl2::interp-defs-alist-clauses)))

(defsection glcp-generic-interp-bad-obligs
  (local (in-theory (disable* (:rules-of-class :type-prescription :here)
                              pseudo-termp
                              len nth update-nth default-car default-cdr
                              fgetprop
                              glcp-generic-geval-ev-conjoin-clauses-atom
                              hons-assoc-equal
                              glcp-generic-geval-ev-rules
                              glcp-generic-interp-function-lookup-theoremp-defs-history
                              pseudo-termp-car)))

  (defun find-bad-obligs-lit (clause)
    (declare (xargs :mode :program))
    (if (atom clause)
        nil
      (b* (((mv ok &) (acl2::simple-one-way-unify
                       '(GLCP-GENERIC-GEVAL-EV
                         (CONJOIN-CLAUSES (ACL2::INTERP-DEFS-ALIST-CLAUSES OBLIGS))
                         (GLCP-GENERIC-GEVAL-EV-FALSIFY
                          (CONJOIN-CLAUSES (ACL2::INTERP-DEFS-ALIST-CLAUSES OBLIGS))))
                       (car clause)
                       nil))
           ((when ok) t))
        (find-bad-obligs-lit (cdr clause)))))

  (defun bad-obligs-syntaxp (mfc state)
    (declare (xargs :mode :program :stobjs state))
    (or (acl2::mfc-ancestors mfc)
        (car (acl2::mfc-current-literal mfc state))))
          ;; (and negp
          ;;      (case-match lit
          ;;        (('glcp-generic-geval-ev
          ;;          ('conjoin-clauses
          ;;           ('acl2::interp-defs-alist-clauses . &))
          ;;          ('glcp-generic-geval-ev-falsify . &))
          ;;         t)))))

  (defund interp-defs-ok (obligs)
    (glcp-generic-geval-ev-theoremp
     (conjoin-clauses
      (acl2::interp-defs-alist-clauses obligs))))

  (local (in-theory (enable interp-defs-ok)))

  (def-glcp-interp-thm glcp-generic-interp-bad-obligs
    ;; :hyps (and ;; (syntaxp ((lambda (mfc state)
    ;;            ;;             (find-bad-obligs-lit (mfc-clause mfc)))
    ;;            ;;           mfc state))
    ;;
    :hyps  ;; (and (syntaxp (bad-obligs-syntaxp mfc state))
                (not (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st)))))
  :body (not (glcp-generic-geval-ev-theoremp
              (conjoin-clauses
               (acl2::interp-defs-alist-clauses (nth *is-obligs*
                                                     interp-st1)))))
                   ; (and (interp-defs-ok (nth *is-obligs* interp-st1))
                   ;; (glcp-generic-geval-ev-theoremp
                   ;;  (conjoin-clauses
                   ;;   (acl2::interp-defs-alist-clauses (nth *is-obligs*
                   ;;                                         interp-st)))))
;;    :rule-classes :forward-chaining
    :expand-calls t)

  ;; (defthm glcp-generic-interp-function-lookup-theoremp-defs-history-rev
  ;;   (B* (((MV ERP & & OUT-DEFS)
  ;;         (ACL2::INTERP-FUNCTION-LOOKUP FN IN-DEFS OVERRIDES WORLD)))
  ;;     (implies (not erp)
  ;;              (iff (glcp-generic-geval-ev-theoremp
  ;;                    (conjoin-clauses
  ;;                     (acl2::interp-defs-alist-clauses out-defs)))
  ;;                   (and (interp-defs-ok out-defs)
  ;;                        (glcp-generic-geval-ev-theoremp
  ;;                         (conjoin-clauses
  ;;                          (acl2::interp-defs-alist-clauses in-defs))))))))
)




(progn ;; glcp-generic-obligs-okp-final-implies-start
  (local (in-theory (disable nth update-nth)))
  ;; (defthm glcp-generic-interp-term-ok-obligs
  ;;   (implies (and (not (glcp-generic-geval-ev-theoremp
  ;;                       (conjoin-clauses
  ;;                        (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st)))))
  ;;                 (glcp-generic-geval-ev-theoremp
  ;;                  (conjoin-clauses
  ;;                   (acl2::interp-defs-alist-clauses
  ;;                    (nth *is-obligs*
  ;;                         (mv-nth 2 (glcp-generic-interp-term
  ;;                                    x alist contexts pathcond clk config interp-st bvar-db st)))))))
  ;;            (mv-nth 1 (glcp-generic-interp-term
  ;;                       x alist contexts pathcond clk config interp-st bvar-db
  ;;                       st)))
  ;;   :hints (("goal" :use glcp-generic-interp-bad-obligs-term)))





  ;; (defthm glcp-generic-obligs-okp-final-implies-start
  ;;   (implies (and (glcp-generic-geval-ev-theoremp
  ;;                  (conjoin-clauses
  ;;                   (acl2::interp-defs-alist-clauses
  ;;                    (nth *is-obligs*
  ;;                         (mv-nth 2 (glcp-generic-interp-term-equivs
  ;;                                    x alist pathcond contexts clk config interp-st bvar-db state))))))
  ;;                 (not (mv-nth 1 (glcp-generic-interp-term-equivs
  ;;                                 x alist pathcond contexts clk config interp-st bvar-db state))))
  ;;            (glcp-generic-geval-ev-theoremp
  ;;             (conjoin-clauses
  ;;              (acl2::interp-defs-alist-clauses
  ;;               (nth *is-obligs* interp-st)))))
  ;;   :rule-classes :forward-chaining)

  (defthm glcp-generic-obligs-okp-final-implies-start
    (implies (glcp-generic-geval-ev-theoremp
              (conjoin-clauses
               (acl2::interp-defs-alist-clauses
                (nth *is-obligs*
                     (mv-nth 3 (glcp-generic-interp-term-equivs
                                x alist contexts pathcond clk config
                                (update-nth *is-obligs* obligs interp-st)
                                bvar-db st))))))
             (glcp-generic-geval-ev-theoremp
              (conjoin-clauses
               (acl2::interp-defs-alist-clauses obligs))))
    :hints (("goal" :use ((:instance glcp-generic-interp-bad-obligs-equivs
                           (interp-st (update-nth *is-obligs* obligs interp-st))))))
    :rule-classes :forward-chaining)


  (defthm assoc-eq-glcp-generic-geval-alist
    (implies (alistp alist)
             (equal (cdr (assoc-eq x (glcp-generic-geval-alist alist env)))
                    (glcp-generic-geval (cdr (hons-assoc-equal x alist))
                                        env)))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-alist
                                      hons-assoc-equal))))


  (defthm glcp-generic-geval-lst-general-concrete-obj-list
    (implies (general-concrete-listp x)
             (equal (glcp-generic-geval-list x env)
                    (general-concrete-obj-list x)))
    :hints(("Goal" :in-theory (e/d (gobj-listp) ()))))


  (defthm glcp-generic-geval-ev-nil
    (equal (glcp-generic-geval-ev nil a) nil))


  (defthm glcp-generic-geval-ev-meta-extract-rewrite-rule
    (implies (and (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term rule))
                  (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                  (glcp-generic-geval-ev (conjoin (acl2::rewrite-rule->hyps
                                                   rule))
                                         a)
                  (equal (acl2::rewrite-rule->equiv rule) 'equal))
             (equal (glcp-generic-geval-ev
                     (acl2::rewrite-rule->rhs rule) a)
                    (glcp-generic-geval-ev
                     (acl2::rewrite-rule->lhs rule) a)))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify
                           (x (acl2::rewrite-rule-term rule))))
             :in-theory (enable acl2::rewrite-rule->rhs
                                acl2::rewrite-rule->lhs
                                acl2::rewrite-rule->hyps
                                acl2::rewrite-rule->equiv
                                acl2::rewrite-rule->subclass)))))


(local (defthm true-listp-cdr-when-pseudo-termp
         (implies (pseudo-termp x)
                  (true-listp (cdr x)))
         :rule-classes :forward-chaining))

(progn ;; glcp-generic-geval-ev-magic-ev-fncall-special
  (encapsulate nil
    (local (bfr-reasoning-mode t))
    (local (acl2::set-bdd-patterns '((hyp-fix . &) 't 'nil)))
    (local (add-bfr-eval-pats (bfr-hyp-eval & env)))
    (defthm bfr-eval-gtests-unknown
      (implies (and (not (hf (mv-nth 1 (gtests test hyp))))
                    (bfr-hyp-eval hyp env))
               (not (bfr-eval (mv-nth 1 (gtests test hyp)) env))))

    (defthm bfr-eval-gtests-unknown-or
      (implies (and (not (hf (bfr-or (mv-nth 1 (gtests test hyp)) other)))
                    (bfr-hyp-eval hyp env))
               (not (bfr-eval (mv-nth 1 (gtests test hyp)) env))))


    (defthm geval-of-interp-res-hyp-fix-unknown-false
      (implies (and (not (glcp-generic-geval interp-res env))
                    (bfr-hyp-eval hyp (car env)))
               (hyp-fix (bfr-or
                         (bfr-not
                          (mv-nth 0 (gtests interp-res hyp)))
                         (mv-nth 1 (gtests interp-res hyp)))
                        hyp)))

    (defthm geval-of-interp-res-hyp-fix-unknown-true
      (implies (and (glcp-generic-geval interp-res env)
                    (bfr-hyp-eval hyp (car env)))
               (hyp-fix (bfr-or
                         (mv-nth 1 (gtests interp-res hyp))
                         (mv-nth 0 (gtests interp-res hyp)))
                        hyp)))

    (defthm gtests-nonnil-or-not
      (implies
       (and
        (bfr-hyp-eval hyp (car env))
        (not
         (hyp-fix
          (bfr-or
           (mv-nth 1 (gtests test hyp))
           (mv-nth 0 (gtests test hyp)))
          hyp)))
       (hyp-fix
        (bfr-or
         (mv-nth 1 (gtests test hyp))
         (bfr-not (mv-nth 0 (gtests test hyp))))
        hyp)))

    (defthmd gtests-known-and-true
      (implies (and (bfr-hyp-eval hyp (car env))
                    (equal (mv-nth 1 (gtests gobj hyp)) nil)
                    (equal (glcp-generic-geval gobj env) nil))
               (not (equal (mv-nth 0 (gtests gobj hyp)) t)))
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
                           (acl2::in-defs in-defs)))
             :in-theory (enable interp-defs-ok))))

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


(defun-sk glcp-generic-bvar-db-env-ok (bvar-db p bound env)
  (forall n
          (implies (and (natp n)
                        (<= (base-bvar$a bvar-db) n)
                        (< n bound)
                        (< n (next-bvar$a bvar-db)))
                   (iff (bfr-lookup
                         n (bfr-unparam-env p (car env)))
                        (glcp-generic-geval (get-bvar->term$a n bvar-db) env))))
  :rewrite :direct)

(in-theory (disable glcp-generic-bvar-db-env-ok))

(defthm glcp-generic-bvar-db-env-ok-of-add-term-bvar
  (implies (<= bound (next-bvar$a bvar-db))
           (equal (glcp-generic-bvar-db-env-ok (add-term-bvar$a x bvar-db)
                                               p bound env)
                  (glcp-generic-bvar-db-env-ok bvar-db p bound env)))
  :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok (add-term-bvar$a x bvar-db)
                                                       p bound env)))
          (and stable-under-simplificationp
               (if (eq (caar clause) 'not)
                   `(:expand (,(car (last clause))))
                 `(:expand (,(car clause)))))))

(defthm glcp-generic-bvar-db-env-ok-of-add-term-equiv
  (equal (glcp-generic-bvar-db-env-ok (add-term-equiv x n bvar-db)
                                      p bound env)
         (glcp-generic-bvar-db-env-ok bvar-db p bound env))
  :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok (add-term-equiv x n bvar-db)
                                                       p bound env)))
          (and stable-under-simplificationp
               (if (eq (caar clause) 'not)
                   `(:expand (,(car (last clause))))
                 `(:expand (,(car clause)))))))

(defthm glcp-generic-bvar-db-env-ok-of-add-term-bvar-next
  (implies (not (glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env))
           (not (glcp-generic-bvar-db-env-ok (add-term-bvar$a x bvar-db)
                                             p (+ 1 (next-bvar$a bvar-db)) env)))
  :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env)))))


;; (defthm glcp-generic-bvar-db-env-ok-of-add-term-bvar
;;   (implies (not (glcp-generic-bvar-db-env-ok bvar-db p bound env))
;;            (not (glcp-generic-bvar-db-env-ok (add-term-bvar$a x bvar-db)
;;                                              p bound env)))
;;   :hints (("goal" :use ((:instance glcp-generic-bvar-db-env-ok-necc
;;                          (bvar-db (add-term-bvar$a x bvar-db))
;;                          (n (glcp-generic-bvar-db-env-ok-witness
;;                              bvar-db p bound env))))
;;            :expand ((glcp-generic-bvar-db-env-ok bvar-db p bound env))
;;            :in-theory (disable glcp-generic-bvar-db-env-ok-necc))))

(defthm glcp-generic-bvar-db-env-ok-bound-decr
  (implies (and (glcp-generic-bvar-db-env-ok bvar-db p bound1 env)
                (<= bound bound1))
           (glcp-generic-bvar-db-env-ok bvar-db p bound env))
  :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok bvar-db p bound env)))))

(defsection glcp-generic-interp-bvar-db-lemmas
  (local (in-theory (disable* (:rules-of-class :type-prescription :here)
                              pseudo-termp
                             len
                             ; acl2::nfix-when-natp
                             no-duplicatesp-equal
                             fgetprop
                             general-concrete-listp
                             member-equal
                             hons-assoc-equal pairlis$ last
                             pseudo-term-listp
                             symbol-listp
                             pseudo-termp-symbolp-car-x
                             ; glcp-generic-interp-term-ok-obligs
                             hyp-fix-of-hyp-fixedp
                             nfix
                             default-<-2
                             default-<-1
                             default-car default-cdr
                             ;; rationalp-implies-acl2-numberp
                             ;; acl2::cancel_plus-lessp-correct
                             general-concrete-obj-list
                             ; acl2::nfix-when-not-natp
                             acl2::cancel_times-equal-correct
                             acl2::cancel_plus-equal-correct)))

  (defthm base-bvar-of-maybe-add-equiv-term
    (equal (base-bvar$a (maybe-add-equiv-term test-obj bvar bvar-db state))
           (base-bvar$a bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm next-bvar-of-maybe-add-equiv-term
    (equal (next-bvar$a (maybe-add-equiv-term test-obj bvar bvar-db state))
           (next-bvar$a bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm get-term->bvar-of-maybe-add-equiv-term
    (equal (get-term->bvar$a x (maybe-add-equiv-term test-obj bvar bvar-db state))
           (get-term->bvar$a x bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm get-bvar->term-of-maybe-add-equiv-term
    (equal (get-bvar->term$a x (maybe-add-equiv-term test-obj bvar bvar-db state))
           (get-bvar->term$a x bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm bvar-db-extension-p-of-maybe-add-equiv-term
    (bvar-db-extension-p (maybe-add-equiv-term test bvar bvar-db state) bvar-db)
    :hints(("Goal" :in-theory (enable bvar-db-extension-p
                                      bvar-db-bvar->term-extension-p
                                      bvar-db-term->bvar-extension-p))))

   ;; (def-glcp-interp-thm glcp-generic-interp-base-bvar-preserved
   ;;   :body (equal (base-bvar$a bvar-db1) (base-bvar$a bvar-db))
   ;;   :expand-calls t)
 
   ;; (def-glcp-interp-thm glcp-generic-interp-next-bvar-incr
   ;;   :body (>= (next-bvar$a bvar-db1) (next-bvar$a bvar-db))
   ;;   :rule-classes :linear
   ;;   :expand-calls t)
 
   ;; (def-glcp-interp-thm glcp-generic-interp-get-bvar->term-preserved
   ;;   :body (implies (and (<= (base-bvar$a bvar-db) (nfix n))
   ;;                       (< (nfix n) (next-bvar$a bvar-db)))
   ;;                  (equal (get-bvar->term$a n bvar-db1)
   ;;                         (get-bvar->term$a n bvar-db)))
   ;;   :expand-calls t)
 
   ;; (def-glcp-interp-thm glcp-generic-interp-get-term->bvar-preserved
   ;;   :body (implies (get-term->bvar$a n bvar-db)
   ;;                  (equal (get-term->bvar$a n bvar-db1)
   ;;                         (get-term->bvar$a n bvar-db)))
   ;;   :expand-calls t)

  (local (acl2::use-trivial-ancestors-check))

  (def-glcp-interp-thm glcp-generic-interp-produces-bvar-db-extension
    :body (bvar-db-extension-p bvar-db1 bvar-db)
    :expand-calls t))

(defsection glcp-generic-interp-bvar-db-env-ok-preserved
  (local (in-theory (disable* pseudo-termp pseudo-term-listp
                              pseudo-termp-car
                              default-<-2 default-<-1 fgetprop
                              len
                              hons-assoc-equal
                              (:rules-of-class :type-prescription :here))))

  (defthm glcp-generic-interp-bvar-db-env-ok-of-maybe-add-equiv-term
    (equal (glcp-generic-bvar-db-env-ok
            (maybe-add-equiv-term test-obj bvar bvar-db state)
            p bound env)
           (glcp-generic-bvar-db-env-ok bvar-db p bound env))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm glcp-generic-bvar-db-env-ok-of-bvar-db-extension
    (implies (and (bind-bvar-db-extension new old)
                  (<= bound (next-bvar$a old)))
             (equal (glcp-generic-bvar-db-env-ok new p bound env)
                    (glcp-generic-bvar-db-env-ok old p bound env)))
    :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok new p bound env))
             :in-theory (enable (:t glcp-generic-bvar-db-env-ok)))
            (and stable-under-simplificationp
                 (b* ((look (assoc 'glcp-generic-bvar-db-env-ok clause)))
                   (and look
                        `(:expand (,look)))))))

  ;; (local (deflabel pre-env-ok-preserved))

  ;; (def-glcp-interp-thm glcp-generic-interp-bvar-db-env-ok-preserved
  ;;   :hyps (<= bound (next-bvar$a bvar-db))
  ;;   :body (equal (glcp-generic-bvar-db-env-ok bvar-db1 p bound env)
  ;;                (glcp-generic-bvar-db-env-ok bvar-db p bound env))
  ;;   :expand-calls t)

  ;; (def-ruleset! env-ok-preserved-rules
  ;;   (set-difference-theories
  ;;    (current-theory :here)
  ;;    (current-theory 'pre-env-ok-preserved)))

  ;; (local (deflabel pre-env-ok-special))

  (defthm not-glcp-generic-bvar-db-env-ok-of-bvar-db-extension
    (implies (and (bind-bvar-db-extension new old)
                  (not (glcp-generic-bvar-db-env-ok old p (next-bvar$a old) env)))
             (not (glcp-generic-bvar-db-env-ok new p (next-bvar$a new) env)))
    :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok old p (next-bvar$a old) env))
             :use ((:instance glcp-generic-bvar-db-env-ok-necc
                    (bvar-db new)
                    (bound (next-bvar$a new))
                    (n (glcp-generic-bvar-db-env-ok-witness old p (next-bvar$a old) env)))
                   BVAR-DB-EXTENSION-INCREASES)
             :in-theory (disable glcp-generic-bvar-db-env-ok-necc
                                 bvar-db-extension-increases))))

  ;; (def-glcp-interp-thm glcp-generic-interp-bvar-db-preserved-special
  ;;   :hyps (and ;; (syntaxp ((lambda (mfc state)
  ;;              ;;             (assoc 'glcp-generic-bvar-db-env-ok
  ;;              ;;                 (mfc-clause mfc)))
  ;;              ;;           mfc state))
  ;;              (not (glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env)))
  ;;   :body (not (glcp-generic-bvar-db-env-ok bvar-db1 p (next-bvar$a bvar-db1) env))
  ;;   :expand-calls t)

  ;; (def-ruleset! env-ok-special-rules
  ;;   (set-difference-theories
  ;;    (current-theory :here)
  ;;    (current-theory 'pre-env-ok-special)))

  ;; (in-theory (disable* env-ok-preserved-rules
  ;;                      env-ok-special-rules))
  )

(local (in-theory (disable bfr-to-param-space)))

(defsection glcp-generic-eval-context-equiv*-nil
  (defthm glcp-generic-eval-context-equiv-nil
    (equal (glcp-generic-eval-context-equiv
            nil a b)
           (equal a b))
    :hints(("Goal" :in-theory (enable glcp-generic-eval-context-equiv))))

  (defthm glcp-generic-eval-context-equiv-refl
    (glcp-generic-eval-context-equiv
     equivs a a)
    :hints(("Goal" :in-theory (enable glcp-generic-eval-context-equiv))))

  (local (defthm glcp-generic-eval-context-equiv-chain-nil
           (implies (and (glcp-generic-eval-context-equiv-chain
                          nil x)
                         (equal (car x) a)
                         (equal (car (last x)) b))
                    (equal (equal a b) t))
           :hints(("Goal" :in-theory (enable glcp-generic-eval-context-equiv-chain)))))

  (defthm glcp-generic-eval-context-equiv*-nil
    (equal (glcp-generic-eval-context-equiv* nil a b)
           (equal a b))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (x a) (y b) (chain (list a)) (contexts nil)))
             :in-theory (disable glcp-generic-eval-context-equiv*-suff)
             :expand ((glcp-generic-eval-context-equiv* nil a b))))))


(defsection glcp-generic-eval-context-equiv*-iff
  (defthm glcp-generic-eval-context-equiv-iff
    (equal (glcp-generic-eval-context-equiv
            '(iff) a b)
           (iff* a b))
    :hints(("Goal" :in-theory (enable glcp-generic-eval-context-equiv))))

  (local (defthmd glcp-generic-eval-context-equiv-chain-iff
           (implies (and (glcp-generic-eval-context-equiv-chain
                          '(iff) x)
                         (equal (car x) a)
                         (equal (car (last x)) b))
                    (equal (iff* a b) t))
           :hints(("Goal" :in-theory (enable glcp-generic-eval-context-equiv-chain)))))

  (defthm glcp-generic-eval-context-equiv*-iff
    (equal (glcp-generic-eval-context-equiv* '(iff) a b)
           (iff* a b))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (x a) (y b) (chain (list a b)) (contexts '(iff)))
                          (:instance glcp-generic-eval-context-equiv-chain-iff
                           (x (glcp-generic-eval-context-equiv*-witness
                               '(iff) a b))))
             :in-theory (disable glcp-generic-eval-context-equiv*-suff)
             :expand ((glcp-generic-eval-context-equiv* '(iff) a b)
                      (glcp-generic-eval-context-equiv* '(iff) a nil)
                      (glcp-generic-eval-context-equiv* '(iff) nil b))))))

(defthm glcp-generic-eval-context-equiv-of-rewrites
  (implies (and (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term rule))
                (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                (glcp-generic-geval-ev (conjoin (acl2::rewrite-rule->hyps
                                                 rule))
                                       a)
                (proper-contextsp contexts)
                (symbolp (acl2::rewrite-rule->equiv rule))
                (not (eq (acl2::rewrite-rule->equiv rule) 'quote))
                (member (acl2::rewrite-rule->equiv rule) contexts)
                (equal lhs (glcp-generic-geval-ev
                            (acl2::rewrite-rule->lhs rule) a)))
           (glcp-generic-eval-context-equiv
            contexts
            (glcp-generic-geval-ev
             (acl2::rewrite-rule->rhs rule) a)
            lhs))
  :hints (("goal" :induct (len contexts)
           :in-theory (disable acl2::rewrite-rule-term)
           :expand ((:free (a b) (glcp-generic-eval-context-equiv contexts a
                                                                  b))))
          (and stable-under-simplificationp
               '(:use ((:instance glcp-generic-geval-ev-falsify
                        (x (acl2::rewrite-rule-term rule))))
             :in-theory (e/d ( ;; acl2::rewrite-rule->rhs
                                ;; acl2::rewrite-rule->lhs
                                ;; acl2::rewrite-rule->hyps
                                ;; acl2::rewrite-rule->equiv
                                ;; acl2::rewrite-rule->subclass
                                rewrite-rule-term-alt-def
                                glcp-generic-geval-ev-of-fncall-args)
                             (acl2::rewrite-rule-term))))))

(defsection glcp-generic-eval-context-equiv*-of-rewrites
  (defthmd glcp-generic-eval-context-equiv*-when-equiv
    (implies (glcp-generic-eval-context-equiv contexts x y)
             (glcp-generic-eval-context-equiv* contexts x y))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (list x y))))
             :in-theory (disable glcp-generic-eval-context-equiv*-suff))))

  (local (in-theory (enable glcp-generic-eval-context-equiv*-when-equiv)))

  (defthm glcp-generic-eval-context-equiv*-of-rewrites
    (implies (and (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term rule))
                  (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                  (glcp-generic-geval-ev (conjoin (acl2::rewrite-rule->hyps
                                                   rule))
                                         a)
                  (proper-contextsp contexts)
                  (symbolp (acl2::rewrite-rule->equiv rule))
                  (not (eq (acl2::rewrite-rule->equiv rule) 'quote))
                  (member (acl2::rewrite-rule->equiv rule) contexts)
                  (equal lhs (glcp-generic-geval-ev
                              (acl2::rewrite-rule->lhs rule) a)))
             (glcp-generic-eval-context-equiv*
              contexts
              (glcp-generic-geval-ev
               (acl2::rewrite-rule->rhs rule) a)
              lhs))))


(defsection bvar-db-depends-on
  (defund-nx bvar-db-depends-on (k p n bvar-db)
    (declare (xargs :measure (nfix n)))
    (if (<= (nfix n) (base-bvar bvar-db))
        nil
      (or (gobj-depends-on k p (get-bvar->term (1- (nfix n)) bvar-db))
          (bvar-db-depends-on k p (1- (nfix n)) bvar-db))))

  (local (in-theory (enable bvar-db-depends-on)))
  (local (include-book "std/basic/arith-equivs" :dir :system))

  (defthm gobj-depends-on-of-get-bvar->term
    (implies (and (<= (base-bvar bvar-db) (nfix m))
                  (not (bvar-db-depends-on k p n bvar-db))
                  (< (nfix m) (next-bvar bvar-db))
                  (< (nfix m) (nfix n)))
             (not (gobj-depends-on k p (get-bvar->term$a m bvar-db))))))

(defsection check-equiv-replacement

  (local (in-theory (enable check-equiv-replacement)))

  (local (defthmd context-equiv-term-when-member-equivs
           (implies (and (glcp-generic-geval-ev (list equiv (kwote x) (kwote y)) a)
                         (symbolp equiv)
                         (not (eq equiv 'quote))
                         (member equiv contexts))
                    (glcp-generic-eval-context-equiv contexts x y))
           :hints(("Goal" :in-theory (enable member
                                             glcp-generic-eval-context-equiv
                                             glcp-generic-geval-ev-of-fncall-args)))))

  (local (Defthm equal-of-len
           (implies (syntaxp (quotep y))
                    (equal (equal (len x) y)
                           (if (zp y)
                               (and (equal y 0)
                                    (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- y))))))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))


  (local (defthm check-equiv-replacement-correct1
           (b* (((mv ok replacement negp)
                 (check-equiv-replacement x equiv-term contexts state)))
             (implies (and (proper-contextsp contexts)
                           ok
                           (xor negp (glcp-generic-geval equiv-term env)))
                      (glcp-generic-eval-context-equiv
                       contexts
                       (glcp-generic-geval replacement env)
                       (glcp-generic-geval x env))))
           :hints (("goal" :expand ((:with glcp-generic-geval
                                     (glcp-generic-geval equiv-term env)))
                    :in-theory (enable glcp-generic-geval-list
                                       glcp-generic-eval-context-equiv-commute)
                    :use ((:instance context-equiv-term-when-member-equivs
                           (equiv (g-apply->fn equiv-term))
                           (x (glcp-generic-geval (car (g-apply->args equiv-term)) env))
                           (y (glcp-generic-geval (cadr (g-apply->args equiv-term)) env))
                           (a nil)))))))

  (defthmd glcp-generic-eval-context-equiv*-when-equiv
    (implies (glcp-generic-eval-context-equiv contexts x y)
             (glcp-generic-eval-context-equiv* contexts x y))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (list x y))))
             :in-theory (disable glcp-generic-eval-context-equiv*-suff))))

  (defthm check-equiv-replacement-correct
    (b* (((mv ok replacement negp) (check-equiv-replacement x equiv-term contexts state)))
      (implies (and (proper-contextsp contexts)
                    ok
                    (xor negp (glcp-generic-geval equiv-term env)))
               (glcp-generic-eval-context-equiv*
                contexts
                (glcp-generic-geval replacement env)
                (glcp-generic-geval x env))))
    :hints (("goal"
             :in-theory (e/d (glcp-generic-eval-context-equiv*-when-equiv)
                             (check-equiv-replacement)))))

  (defthm check-equiv-replacement-depends-on
    (b* (((mv ok replacement) (check-equiv-replacement x equiv-term contexts state)))
      (implies (and ok
                    (not (gobj-depends-on k p equiv-term)))
               (not (gobj-depends-on k p replacement))))))



(defsection try-equivalences
  (local (in-theory (enable try-equivalences)))

  (defthm try-equivalences-correct
    (b* (((mv ok repl) (try-equivalences x bvars pathcond contexts p bvar-db state)))
      (implies (and (bfr-hyp-eval pathcond (car env))
                    (glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env)
                    ok
                    (bdd-mode-or-p-true p (car env))
                    (bvar-listp bvars bvar-db)
                    (proper-contextsp contexts))
               (glcp-generic-eval-context-equiv* contexts
                                                 (glcp-generic-geval repl env)
                                                 (glcp-generic-geval x env))))
    :hints (("goal" :induct (try-equivalences x bvars pathcond contexts p bvar-db state)
             :expand ((bvar-listp$a bvars bvar-db)))
            (and stable-under-simplificationp
                 '(:use ((:instance true-under-hyp-point
                          (x (hyp-fix
                              (bfr-to-param-space
                               p (bfr-var (car bvars)))
                              pathcond))
                          (hyp pathcond)
                          (v (car env)))
                         (:instance false-under-hyp-point
                          (x (hyp-fix
                              (bfr-to-param-space
                               p (bfr-var (car bvars)))
                              pathcond))
                          (hyp pathcond)
                          (v (car env))))))))

  (defthm try-equivalences-depends-on
    (b* (((mv ok repl) (try-equivalences x bvars pathcond contexts pp bvar-db state)))
      (implies (and ok
                    (bvar-listp bvars bvar-db)
                    (not (bvar-db-depends-on k p (next-bvar$a bvar-db) bvar-db)))
               (not (gobj-depends-on k p repl))))
    :hints (("goal" :induct (try-equivalences x bvars pathcond contexts pp bvar-db state)
             :expand ((bvar-listp bvars bvar-db))))))

(defsection try-equivalences-loop
  (local (in-theory (enable try-equivalences-loop)))

  (defthm try-equivalences-loop-correct
    (b* (((mv ?er repl)
          (try-equivalences-loop x pathcond contexts clk p bvar-db state)))
      (implies (and (bfr-hyp-eval pathcond (car env))
                    (glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env)
                    (bdd-mode-or-p-true p (car env))
                    (proper-contextsp contexts))
               (glcp-generic-eval-context-equiv* contexts
                                                 (glcp-generic-geval repl env)
                                                 (glcp-generic-geval x env))))
    :hints (("goal" :induct (try-equivalences-loop x pathcond contexts clk p bvar-db state))
            (and stable-under-simplificationp
                 '(:use ((:instance try-equivalences-correct
                          (bvars (get-term->equivs x bvar-db))))
                   :in-theory (disable try-equivalences-correct)))))

  (defthm try-equivalences-loop-depends-on
    (b* (((mv ?er repl) (try-equivalences-loop x pathcond contexts clk pp bvar-db state)))
      (implies (and (not (gobj-depends-on k p x))
                    (not (bvar-db-depends-on k p (next-bvar$a bvar-db) bvar-db)))
               (not (gobj-depends-on k p repl)))))

  (defthm try-equivalences-loop-special
    (b* (((mv ?er repl)
          (try-equivalences-loop x pathcond contexts clk p bvar-db state)))
      (implies (and (bfr-hyp-eval pathcond (car env))
                    (glcp-generic-bvar-db-env-ok bvar-db p (next-bvar$a bvar-db) env)
                    (proper-contextsp contexts)
                    (bdd-mode-or-p-true p (car env))
                    (glcp-generic-eval-context-equiv*
                     contexts (glcp-generic-geval x env) y))
               (glcp-generic-eval-context-equiv* contexts
                                                 (glcp-generic-geval repl env)
                                                 y)))
    :hints(("Goal" :in-theory (e/d (glcp-generic-eval-context-equiv*-trans)
                                   (try-equivalences-loop-correct))
            :use try-equivalences-loop-correct
            :do-not-induct t))))

(defsection glcp-or-test-contexts
  (defthmd glcp-context-equiv-of-glcp-or-test-contexts
    (equal (glcp-generic-eval-context-equiv*
            (glcp-or-test-contexts contexts) x y)
           (and (hide (glcp-generic-eval-context-equiv*
                       (glcp-or-test-contexts contexts) x y))
                (iff* x y)
                (glcp-generic-eval-context-equiv*
                 contexts x y)))
    :hints (("goal" :expand ((:free (x) (hide x))))))

  (defthm proper-contextsp-of-glcp-or-test-contexts
    (proper-contextsp (glcp-or-test-contexts contexts))
    :hints(("Goal" :in-theory (e/d (glcp-generic-equiv-relp)
                                   ((proper-contextsp))))))

  (defthm contextsp-of-glcp-or-test-contexts
    (contextsp (glcp-or-test-contexts contexts))))




(defun id-on-the-way-to (id dest-id)
  (and
   ;; same induction step
   (equal (car id) (car dest-id))
   ;; case splits
   (acl2::prefixp (cadr id) (cadr dest-id))))


(defsection glcp-interp-accs-ok

  (defund-nx glcp-interp-accs-ok (interp-st bvar-db config env)
    (and (glcp-generic-geval-ev-theoremp
          (conjoin-clauses
           (acl2::interp-defs-alist-clauses (is-obligs interp-st))))
         (glcp-generic-bvar-db-env-ok
          bvar-db (glcp-config->param-bfr config)
          (next-bvar bvar-db) env)))

  (local (in-theory (enable glcp-interp-accs-ok)))

  (def-glcp-interp-thm glcp-generic-interp-accs-ok
    :hyps (not (glcp-interp-accs-ok interp-st bvar-db config env))
    :body (not (glcp-interp-accs-ok interp-st1 bvar-db1 config env))
    ;; :hints(("Goal" :in-theory (enable* env-ok-special-rules)))
    :no-induction-hint t)

  (defthm glcp-interp-accs-ok-of-maybe-add-equiv-term
    (equal (glcp-interp-accs-ok
            interp-st
            (maybe-add-equiv-term test-obj bvar bvar-db state) config env)
           (glcp-interp-accs-ok interp-st bvar-db config env))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm glcp-interp-accs-ok-implies
    (implies (glcp-interp-accs-ok interp-st bvar-db config env)
             (and (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st))))
                  (glcp-generic-bvar-db-env-ok
                   bvar-db (glcp-config->param-bfr config)
                   (next-bvar$a bvar-db) env))))

  (defthm glcp-interp-accs-ok-of-add-term-bvar
    (implies (not (glcp-interp-accs-ok interp-st bvar-db config env))
             (not (glcp-interp-accs-ok interp-st (add-term-bvar$a x bvar-db)
                                       config env))))

  (defthm glcp-interp-accs-ok-env-ok-necc
    (implies (and (glcp-interp-accs-ok interp-st bvar-db config env)
                  (natp n)
                  (<= (base-bvar$a bvar-db) n)
                  (< n (next-bvar$a bvar-db)))
             (iff (bfr-lookup
                   n (bfr-unparam-env (glcp-config->param-bfr config) (car env)))
                  (glcp-generic-geval (get-bvar->term$a n bvar-db) env))))

  (defthm glcp-interp-accs-ok-interp-function-lookup
     (b* (((mv erp & & out-defs)
           (acl2::interp-function-lookup fn (nth *is-obligs* interp-st) overrides world)))
       (implies (and (not (glcp-interp-accs-ok interp-st bvar-db config env))
                     (not erp))
                (not (glcp-interp-accs-ok
                      (update-nth *is-obligs* out-defs interp-st)
                      bvar-db config env)))))

  (defthm glcp-interp-accs-ok-interp-function-lookup-correct
    (mv-let (erp body formals out-defs)
      (acl2::interp-function-lookup fn (nth *is-obligs* interp-st) overrides (w state))
      (implies (and (glcp-interp-accs-ok
                     (update-nth *is-obligs* out-defs interp-st)
                     bvar-db config env)
                    (not erp)
                    (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp overrides)
                    (equal (len formals) (len actuals))
                    (not (eq fn 'quote))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                    (equal (w state) (w state1)))
               (equal (glcp-generic-geval-ev body (pairlis$ formals actuals))
                      (glcp-generic-geval-ev (cons fn (kwote-lst actuals))
                                             nil)))))

  (def-glcp-interp-thm glcp-generic-interp-accs-ok-final-implies-start
    :hyps (glcp-interp-accs-ok interp-st1 bvar-db1 config env)
    :body (glcp-interp-accs-ok interp-st bvar-db config env)
    ;; :hints(("Goal" :in-theory (enable* env-ok-special-rules)))
    :no-induction-hint t
    :rule-classes :forward-chaining)

  ;; (defthm glcp-interp-accs-ok-final-implies-start
  ;;   (b* (((mv & & & interp-st1 bvar-db1 &)
  ;;         (glcp-generic-interp-term-equivs
  ;;          x alist contexts pathcond clk config
  ;;          interp-st bvar-db st)))
  ;;     (implies (glcp-interp-accs-ok interp-st1 bvar-db1 config env)
  ;;              (glcp-interp-accs-ok interp-st bvar-db config env)))
  ;;   :hints(("Goal" :in-theory (enable* env-ok-special-rules)))
  ;;   :rule-classes :forward-chaining)
  )

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "clause-processors/constant-prop" :dir :System))

(defsection bvar-in-range
  (defund bvar-in-range (k bvar-db)
    (declare (Xargs :stobjs bvar-db
                    :guard (bfr-varname-p k)))
    (b* ((k (bfr-varname-fix k)))
      (and (natp k)
           (<= (base-bvar bvar-db) k)
           (< k (next-bvar bvar-db)))))

  (defthm bvar-in-range-by-bvar-db-extension
    (implies (and (bind-bvar-db-extension new old)
                  (bvar-in-range k old))
             (bvar-in-range k new))
    :hints(("Goal" :in-theory (enable bvar-in-range))))


  (defthm maybe-add-equiv-term-bvar-in-range-preserved
    (equal (bvar-in-range k (maybe-add-equiv-term
                             term bvar bvar-db state))
           (bvar-in-range k bvar-db))
    :hints(("Goal" :in-theory (enable bvar-in-range))))

  ;; (defthm maybe-add-equiv-term-bvar-in-range-preserved-fwd
  ;;   (implies (not (bvar-in-range k (maybe-add-equiv-term
  ;;                                   term bvar bvar-db state)))
  ;;            (not (bvar-in-range k bvar-db)))
  ;;   :rule-classes :forward-chaining)

  ;; (defthm add-term-bvar-bvar-in-range-preserved
  ;;   (implies (bvar-in-range k bvar-db)
  ;;            (bvar-in-range k (add-term-bvar$a term bvar-db))))

  (defthm not-in-range-implies-not-equal-get-term->bvar
    (implies (not (bvar-in-range k bvar-db))
             (not (equal (bfr-varname-fix k) (get-term->bvar$a term bvar-db))))
    :hints (("goal" :cases ((get-term->bvar$a term bvar-db))
             :in-theory (enable bvar-in-range bfr-varname-fix))))

  (defun find-good-add-term-bvar$a-term (bvar-db calls)
    (if (atom calls)
        nil
      (b* ((bdb1 (caddr (car calls)))
           (add-term-call (or (acl2::find-call 'add-term-bvar$a bdb1)
                              (acl2::find-call 'add-term-bvar-unique bdb1))))
        (if (and add-term-call
                 (equal bvar-db (caddr add-term-call)))
            `((bvar-db1 . ,bdb1))
          (find-good-add-term-bvar$a-term bvar-db (cdr calls))))))

  (defun find-add-term-bvar$a-term (bvar-db mfc state)
    (declare (xargs :mode :program :stobjs state)
             (ignorable state))
    (b* ((calls (acl2::find-calls-lst 'bvar-in-range (mfc-clause mfc))))
      (find-good-add-term-bvar$a-term bvar-db calls)))

  (defthm not-in-range-implies-not-equal-next-bvar$a-bind-free
    (implies (and (bind-free (find-add-term-bvar$a-term bvar-db mfc state) (bvar-db1))
                  (not (bvar-in-range k bvar-db1))
                  (equal (base-bvar bvar-db) (base-bvar bvar-db1))
                  (< (next-bvar bvar-db) (next-bvar bvar-db1)))
             (not (equal (bfr-varname-fix k) (next-bvar$a bvar-db))))
    :hints (("goal" :cases ((get-term->bvar$a term bvar-db))
             :in-theory (enable bvar-in-range))))



  (local (in-theory (disable bvar-in-range)))

  (local (in-theory (disable pseudo-termp
                             pseudo-term-listp
                             len
                             fgetprop
                             last
                             no-duplicatesp-equal
                             symbol-listp
                             general-concrete-obj-list
                             member-equal
                             default-car default-cdr
                             hons-assoc-equal)))

  ;; (def-glcp-interp-thm bvar-in-range-preserved
  ;;   :body (implies (bvar-in-range k bvar-db)
  ;;                  (bvar-in-range k bvar-db1))
  ;;   :expand-calls t)
  )


(defsection dependencies-of-glcp-generic-interp

  (defthm pbfr-depends-on-of-bfr-var-t
    (equal (pbfr-depends-on k t (bfr-var n))
           (equal (bfr-varname-fix k) (bfr-varname-fix n)))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-from-param-space))
           (and stable-under-simplificationp
                (if (member-equal '(not (pbfr-semantic-depends-on k 't (bfr-var n))) clause)
                    '(:expand ((pbfr-semantic-depends-on k 't (bfr-var n)))
                      :in-theory (enable bfr-varname-fix))
                  '(:use ((:instance pbfr-semantic-depends-on-suff
                           (p t) (x (bfr-var n))
                           (env (bfr-set-var k t env))
                           (v nil)))
                    :in-theory (enable bfr-param-env acl2::param-env))))))

  (local (defthm gobj-alist-depends-on-nil
           (not (gobj-alist-depends-on k p nil))))

  (local (in-theory (disable pseudo-termp
                             pseudo-termp-symbolp-car-x
                             gbc-process-new-lit
                             gbc-db-emptyp-implies-no-dependencies
                             tag-when-atom
; glcp-generic-interp-term-ok-obligs
                             (:t hyp-fix) (:t hyp-fixedp)
                             hyp-fix-of-hyp-fixedp
                             acl2::nfix-when-not-natp
                             acl2::natp-when-integerp
                             acl2::natp-rw
                             default-cdr
                             acl2::natp-when-gte-0
                             default-<-1
                             default-<-2
                             not len
                             pbfr-depends-on-t
                             acl2::cancel_plus-lessp-correct
                             acl2::cancel_plus-equal-correct
                             rationalp-implies-acl2-numberp
                             gobj-depends-on
                             glcp-or-test-contexts
                             gobj-alist-depends-on
                             acl2::cancel_times-equal-correct
                             acl2::cancel_plus-equal-correct)))


  (local (defthm bvar-db-depends-on-of-add-term-bvar-preserved
           (implies (and (not (bvar-db-depends-on k p n bvar-db))
                         (<= (nfix n) (next-bvar$a bvar-db)))
                    (not (bvar-db-depends-on k p n (add-term-bvar$a gobj bvar-db))))
           :hints(("Goal" :in-theory (enable bvar-db-depends-on)))))

  (local (defthm bvar-db-depends-on-of-add-term-bvar-unique-preserved
           (implies (and (not (bvar-db-depends-on k p n bvar-db))
                         (<= (nfix n) (next-bvar$a bvar-db)))
                    (not (bvar-db-depends-on k p n (mv-nth 1 (add-term-bvar-unique gobj bvar-db)))))
           :hints(("Goal" :in-theory (enable bvar-db-depends-on add-term-bvar-unique)))))

  (local (defthm bvar-db-depends-on-of-add-term-bvar
           (implies (and (not (bvar-db-depends-on k p (next-bvar$a bvar-db)
                                                  bvar-db))
                         (not (gobj-depends-on k p gobj)))
                    (not (bvar-db-depends-on k p (+ 1 (next-bvar$a bvar-db))
                                             (add-term-bvar$a
                                              gobj bvar-db))))
           :hints(("Goal" :expand ((bvar-db-depends-on k p (+ 1 (next-bvar$a bvar-db))
                                                       (add-term-bvar$a
                                                        gobj bvar-db)))))))

  (local (defthm bvar-db-depends-on-of-add-term-bvar-unique
           (implies (and (not (bvar-db-depends-on k p (next-bvar$a bvar-db)
                                                  bvar-db))
                         (not (gobj-depends-on k p gobj)))
                    (b* ((new-bvar-db (mv-nth 1 (add-term-bvar-unique gobj bvar-db))))
                      (not (bvar-db-depends-on k p (next-bvar$a new-bvar-db)
                                               new-bvar-db))))
           :hints(("Goal" :expand ((:free (next) (bvar-db-depends-on k p next
                                                                     (add-term-bvar-unique
                                                                      gobj bvar-db)))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable add-term-bvar-unique))))))

  (defthm bvar-db-depends-on-of-add-term-equiv
    (equal (bvar-db-depends-on k p n (add-term-equiv x z bvar-db))
           (bvar-db-depends-on k p n bvar-db))
    :hints(("Goal" :in-theory (enable bvar-db-depends-on))))

  (defthm bvar-db-depends-on-of-maybe-add-equiv-term
    (equal (bvar-db-depends-on k p n (maybe-add-equiv-term test-obj bvar bvar-db state))
           (bvar-db-depends-on k p n bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (local (in-theory (disable* (:rules-of-class :type-prescription :here))))
  (local (in-theory (enable (:t type-of-get-term->bvar$a)
                            (:t type-of-next-bvar$a)
                            (:t natp-bvar-of-add-term-bvar-unique))))


  (local (defthm not-equal-add-term-bvar-unique-lookup-when-not-depends-on-bvar-db
           (b* (((mv look new-bvar-db) (add-term-bvar-unique x bvar-db)))
             (implies (not (bvar-in-range k new-bvar-db))
                      (not (equal (bfr-varname-fix k) look))))
           :hints(("Goal" :in-theory (e/d (bvar-in-range)
                                          (natp-bvar-of-add-term-bvar-unique))
                   :use ((:instance natp-bvar-of-add-term-bvar-unique))))))

  (set-case-split-limitations '(2 100000))
  (local (in-theory (disable gobj-list-depends-on
                             BFR-VARS-BOUNDED-NECC
                             gobj-vars-bounded-implies-not-depends-on
                             ;; glcp-generic-interp-get-term->bvar-preserved-rewrite
                             fgetprop
                             len hons-assoc-equal
                             bfr-eval-booleanp
                             no-duplicatesp-equal
                             general-concrete-obj-list
                             pbfr-vars-bounded-necc)))

  (def-glcp-interp-thm dependencies-of-glcp-generic-interp
    :hyps (and ;; (not erp)
           (not (bvar-in-range k bvar-db1))
           (not (bfr-depends-on k p))
           ;; (bfr-eval p env)
           (equal p (glcp-config->param-bfr config))
           (not (bvar-db-depends-on k p (next-bvar$a bvar-db) bvar-db))
           (not (gbc-db-depends-on k p (nth *is-constraint-db* interp-st))))
    :add-bindings ((nn (next-bvar$a bvar-db1)))
    :add-concls ((not (gbc-db-depends-on k p (nth *is-constraint-db* interp-st1)))
                 (implies (not (bfr-constr-depends-on k p (nth *is-constraint* interp-st)))
                          (not (bfr-constr-depends-on k p (nth *is-constraint*
                                                         interp-st1))))
                 (not (bvar-db-depends-on k p nn bvar-db1)))
    :special
    ((test :add-hyps (not (gobj-alist-depends-on k p alist))
           :body (not (pbfr-depends-on k p val)))
     (equivs :add-hyps (not (gobj-alist-depends-on k p alist))
             :body (not (gobj-depends-on k p val)))
     (term :add-hyps (not (gobj-alist-depends-on k p alist))
           :body (not (gobj-depends-on k p val)))
     (if/or :add-hyps (not (gobj-alist-depends-on k p alist))
            :body (not (gobj-depends-on k p val)))
     (maybe :add-hyps (not (gobj-alist-depends-on k p alist))
            :body (not (gobj-depends-on k p val)))
     (if :add-hyps (not (gobj-alist-depends-on k p alist))
       :body (not (gobj-depends-on k p val)))
     (or :add-hyps (not (gobj-alist-depends-on k p alist))
         :body (not (gobj-depends-on k p val)))
     (merge :add-hyps (and (not (pbfr-depends-on k p test-bfr))
                                (not (gobj-depends-on k p then))
                                (not (gobj-depends-on k p else)))
            :body (not (gobj-depends-on k p val)))
     (merge-sub :add-hyps (and (not (pbfr-depends-on k p test-bfr))
                                    (not (gobj-depends-on k p then))
                                    (not (gobj-depends-on k p else)))
                :body (not (gobj-depends-on k p val)))
     (merge-list :add-hyps (and (not (pbfr-depends-on k p test-bfr))
                                     (not (gobj-list-depends-on k p then))
                                     (not (gobj-list-depends-on k p else))
                                     (equal (len then) (len else)))
                 :body (not (gobj-list-depends-on k p val))
                 :hints ('(:in-theory (enable len))))
     (maybe-test-simp :add-hyps (not (gobj-depends-on k p test-obj))
                      :body (not (pbfr-depends-on k p val)))
     (test-simp :add-hyps (not (gobj-depends-on k p test-obj))
                :body (not (pbfr-depends-on k p val)))
     (constraints :add-hyps (not (gobj-depends-on k p lit)))
     (constraint-substs :add-hyps (not (gobj-alist-list-depends-on
                                        k p (alist-vals substs)))
                        :hints('(:in-theory (enable
                                             gobj-alist-list-depends-on
                                             alist-vals))))
     (test-simp-fncall :add-hyps (not (gobj-list-depends-on k p args))
                       :body (not (pbfr-depends-on k p val)))
     ;; (fncall-ifs :add-hyps (not (gobj-list-depends-on k p actuals))
     ;;             :body (not (gobj-depends-on k p val)))
     ;; (maybe-fncall-ifs :add-hyps (not (gobj-list-depends-on k p actuals))
     ;;                   :body (not (gobj-depends-on k p val)))
     (fncall :add-hyps (not (gobj-list-depends-on k p actuals))
             :body (not (gobj-depends-on k p val))
             :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
     (rewrite :add-hyps (not (gobj-list-depends-on k p actuals))
              :body (not (gobj-alist-depends-on k p bindings)))
     (rules :add-hyps (not (gobj-list-depends-on k p actuals))
            :body (not (gobj-alist-depends-on k p bindings)))
     (rule :add-hyps (not (gobj-list-depends-on k p actuals))
           :body (not (gobj-alist-depends-on k p bindings)))
     (hyps :add-hyps (not (gobj-alist-depends-on k p bindings)))
     (hyp :add-hyps (not (gobj-alist-depends-on k p bindings)))
     (list :add-hyps (not (gobj-alist-depends-on k p alist))
           :body (not (gobj-list-depends-on k p vals))))
    :expand-calls t
    :hints (;;'(:error t)
            ;; (case-match id
            ;;   (('(0 1) '(29) . &)
            ;;    (prog2$ (cw "empty~%")
            ;;    (let ((state (f-put-global 'goals nil state)))
            ;;      (value nil))))
            ;;   (('(0 1) ('29 &) . &)
            ;;    (prog2$ (cw "cons~%")
            ;;    (let ((state (f-put-global 'goals (cons clause (@ goals))
            ;;                               state)))
            ;;      (value nil))))
            ;;   (& (value nil)))
            (let ((lit (car clause)))
              (case-match lit
                (('not ('acl2::flag-is . &) . &)
                 '(:computed-hint-replacement
                   ('(:expand :lambdas))
                   :clause-processor acl2::constant-prop-cp))))
            (and stable-under-simplificationp
                 '(; :in-theory (enable acl2::expand-marked-meta)
                   :do-not-induct t
                   :do-not '(generalize)))
            )))

(defsection bvar-db-vars-bounded
  (defund-nx bvar-db-vars-bounded (k p n bvar-db)
    (declare (xargs :measure (nfix n)))
    (if (<= (nfix n) (base-bvar bvar-db))
        t
      (and (gobj-vars-bounded k p (get-bvar->term (1- (nfix n)) bvar-db))
           (bvar-db-vars-bounded k p (1- (nfix n)) bvar-db))))

  (local (in-theory (enable bvar-db-vars-bounded)))

  (defthm gobj-vars-bounded-of-get-bvar->term
    (implies (and (<= (base-bvar bvar-db) (nfix m))
                  (bvar-db-vars-bounded k p n bvar-db)
                  (< (nfix m) (next-bvar bvar-db))
                  (< (nfix m) (nfix n)))
             (gobj-vars-bounded k p (get-bvar->term$a m bvar-db))))

  (defund-nx bvar-db-vars-bounded-witness (k p n bvar-db)
    (declare (xargs :measure (nfix n)))
    (if (<= (nfix n) (base-bvar bvar-db))
        nil
      (or (gobj-vars-bounded-witness k p (get-bvar->term (1- (nfix n)) bvar-db))
          (bvar-db-vars-bounded-witness k p (1- (nfix n)) bvar-db))))

  (defthm bvar-db-vars-bounded-witness-under-iff
    (iff (bvar-db-vars-bounded-witness k p n bvar-db)
         (not (bvar-db-vars-bounded k p n bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded-witness))))

  (defthmd bvar-db-vars-bounded-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal
              `(bvar-db-vars-bounded ,k ,p ,n ,bvar-db))
             (equal (bvar-db-vars-bounded k p n bvar-db)
                    (let ((m (bfr-varname-fix (bvar-db-vars-bounded-witness k p n bvar-db))))
                      (implies (or (not (natp m))
                                   (<= (nfix k) m))
                               (not (bvar-db-depends-on m p n bvar-db))))))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded-witness
                                      bvar-db-depends-on
                                      gobj-vars-bounded-in-terms-of-witness))))

  (defthm bvar-db-depends-on-when-vars-bounded
    (implies (and (bvar-db-vars-bounded k p n bvar-db)
                  (b* ((m (bfr-varname-fix m)))
                    (or (not (natp m))
                        (<= (nfix k) m))))
             (not (bvar-db-depends-on m p n bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded
                                      bvar-db-depends-on))))

  (defthm bvar-db-vars-bounded-of-add-term-bvar-preserved
    (implies (and (bvar-db-vars-bounded k p n bvar-db)
                  (<= (nfix n) (next-bvar$a bvar-db)))
             (bvar-db-vars-bounded k p n (add-term-bvar$a gobj bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded))))

  (defthmd bvar-db-vars-bounded-incr
    (implies (and (bvar-db-vars-bounded k p n bvar-db)
                  (<= (nfix k) (nfix m)))
             (bvar-db-vars-bounded m p n bvar-db))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded-in-terms-of-witness))))

  (defthm bvar-db-vars-bounded-of-add-term-bvar
    (implies (and (bvar-db-vars-bounded k p (next-bvar$a bvar-db)
                                        bvar-db)
                  (gobj-vars-bounded j p gobj)
                  (<= (nfix k) (nfix m))
                  (<= (nfix j) (nfix m)))
             (bvar-db-vars-bounded m p (+ 1 (next-bvar$a bvar-db))
                                   (add-term-bvar$a
                                    gobj bvar-db)))
    :hints(("Goal" :expand ((bvar-db-vars-bounded k p (+ 1 (next-bvar$a bvar-db))
                                                  (add-term-bvar$a
                                                   gobj bvar-db)))
            :in-theory (enable bvar-db-vars-bounded-incr)))))

(defun-sk bfr-constr-vars-bounded (n p x)
    (forall m
            (implies (and (bfr-varname-p m)
                          (or (not (natp m))
                              (<= (nfix n) m)))
                     (not (bfr-constr-depends-on m p x))))
    :rewrite :direct)

(in-theory (disable bfr-constr-vars-bounded))

(defsection vars-bounded-of-glcp-generic-interp
  (local (in-theory (disable ;; glcp-generic-interp-term-ok-obligs
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
                             proper-contextsp
                             (proper-contextsp)
                             kwote-lst)))

  (defthm bvar-not-in-range-when-not-natp
    (implies (not (natp (bfr-varname-fix v)))
             (not (bvar-in-range v bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-in-range))))

  (defthm bvar-not-in-range-when-too-big-1
    (implies (<= (next-bvar bvar-db) (bfr-varname-fix v))
             (not (bvar-in-range v bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-in-range))))

  (defthm bvar-not-in-range-when-too-big-2
    (implies (and (<= (next-bvar bvar-db) k)
                  (<= k (bfr-varname-fix v)))
             (not (bvar-in-range v bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-in-range))))

  (defthm bvar-vars-bounded-implies-not-depends-on
    (implies (and (bfr-vars-bounded n x)
                  (b* ((k (bfr-varname-fix k)))
                    (or (not (natp k))
                        (<= (nfix n) k))))
             (not (bfr-depends-on k x)))
    :hints (("goal" :use ((:instance bfr-vars-bounded-necc
                           (m (bfr-varname-fix k)))))))

  ;; this isn't an induction, it's just based on the dependencies theorem
  (def-glcp-interp-thm vars-bounded-of-glcp-generic-interp
    :hyps (and ;; (not erp)
           (<= (next-bvar$a bvar-db1) (nfix k))
           (bfr-vars-bounded k p)
           ; (bfr-eval p env)
           (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
           (equal nn (next-bvar$a bvar-db1))
           (equal p (glcp-config->param-bfr config))
           (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
    :add-concls ((implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                          (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st1)))
                 (bvar-db-vars-bounded k p nn bvar-db1)
                 (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st1)))
    :special
    ((test :add-hyps (gobj-alist-vars-bounded k p alist)
           :body (pbfr-vars-bounded k p val))
     (equivs :add-hyps (gobj-alist-vars-bounded k p alist)
             :body (gobj-vars-bounded k p val))
     (term :add-hyps (gobj-alist-vars-bounded k p alist)
           :body (gobj-vars-bounded k p val))
     (if/or :add-hyps (gobj-alist-vars-bounded k p alist)
            :body (gobj-vars-bounded k p val))
     (maybe :add-hyps (gobj-alist-vars-bounded k p alist)
            :body (gobj-vars-bounded k p val))
     (if :add-hyps (gobj-alist-vars-bounded k p alist)
       :body (gobj-vars-bounded k p val))
     (or :add-hyps (gobj-alist-vars-bounded k p alist)
         :body (gobj-vars-bounded k p val))
     (merge :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                                (gobj-vars-bounded k p then)
                                (gobj-vars-bounded k p else))
            :body (gobj-vars-bounded k p val))
     (merge-sub :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                                (gobj-vars-bounded k p then)
                                (gobj-vars-bounded k p else))
                :body (gobj-vars-bounded k p val))
     (merge-list :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                                     (gobj-list-vars-bounded k p then)
                                     (gobj-list-vars-bounded k p else)
                                     (equal (len then) (len else)))
                 :body (gobj-list-vars-bounded k p val))
     (maybe-test-simp :add-hyps (gobj-vars-bounded k p test-obj)
                      :body (pbfr-vars-bounded k p val))
     (test-simp :add-hyps (gobj-vars-bounded k p test-obj)
                :body (pbfr-vars-bounded k p val))

     (test-simp-fncall :add-hyps (gobj-list-vars-bounded k p args)
                       :body (pbfr-vars-bounded k p val))
     (constraints :add-hyps (gobj-vars-bounded k p lit))
     (constraint-substs :add-hyps (gobj-alist-list-vars-bounded
                                   k p (alist-vals substs)))
     ;; (fncall-ifs :add-hyps (gobj-list-vars-bounded k p actuals)
     ;;             :body (gobj-vars-bounded k p val))

     ;; (maybe-fncall-ifs :add-hyps (gobj-list-vars-bounded k p actuals)
     ;;                   :body (gobj-vars-bounded k p val))

     (fncall :add-hyps (gobj-list-vars-bounded k p actuals)
             :body (gobj-vars-bounded k p val))
     (rewrite :add-hyps (gobj-list-vars-bounded k p actuals)
              :body (gobj-alist-vars-bounded k p bindings))
     (rules :add-hyps (gobj-list-vars-bounded k p actuals)
            :body (gobj-alist-vars-bounded k p bindings))
     (rule :add-hyps (gobj-list-vars-bounded k p actuals)
           :body (gobj-alist-vars-bounded k p bindings))
     (hyps :add-hyps (gobj-alist-vars-bounded k p bindings)
           :body (bvar-db-vars-bounded k p nn bvar-db1))
     (hyp :add-hyps (gobj-alist-vars-bounded k p bindings)
          :body (bvar-db-vars-bounded k p nn bvar-db1))
     (list :add-hyps (gobj-alist-vars-bounded k p alist)
           :body (gobj-list-vars-bounded k p vals)))
    :hints (("goal" :in-theory (enable bvar-db-vars-bounded-in-terms-of-witness
                                       gobj-vars-bounded-in-terms-of-witness
                                       gobj-list-vars-bounded-in-terms-of-witness
                                       gobj-alist-vars-bounded-in-terms-of-witness
                                       gbc-db-vars-bounded-in-terms-of-witness))
            (and stable-under-simplificationp
                 (member (caar (last clause)) '(pbfr-vars-bounded
                                                bfr-constr-vars-bounded))
                 `(:expand (,(car (last clause))))))
    :no-induction-hint t))

(defthm gobj-alist-vars-bounded-of-glcp-unify-term/gobj-list
  (implies (and (gobj-list-vars-bounded k p actuals)
                (gobj-alist-vars-bounded k p alist))
           (gobj-alist-vars-bounded
            k p (mv-nth 1 (glcp-unify-term/gobj-list pat actuals alist))))
  :hints (("goal" :in-theory (enable gobj-alist-vars-bounded-in-terms-of-witness))))

(defthm gobj-list-vars-bounded-of-gl-args-split-ite
  (b* (((mv ?has-if test then else)
        (gl-args-split-ite args)))
    (implies (gobj-list-vars-bounded k p args)
             (and (gobj-vars-bounded k p test)
                  (gobj-list-vars-bounded k p then)
                  (gobj-list-vars-bounded k p else))))
  :hints (("goal" :in-theory (enable gobj-vars-bounded-in-terms-of-witness
                                     gobj-list-vars-bounded-in-terms-of-witness
                                     gobj-alist-vars-bounded-in-terms-of-witness))))

(defsection bvar-db-ordered-of-glcp-generic-interp
  (local (in-theory (disable pseudo-termp
                             pseudo-termp-symbolp-car-x
                             ;;glcp-generic-interp-term-ok-obligs
                             (:t hyp-fix) (:t hyp-fixedp)
                             hyp-fix-of-hyp-fixedp
                             acl2::nfix-when-not-natp
                             pbfr-vars-bounded-t
                             gbc-process-new-lit
                             glcp-or-test-contexts
                             acl2::cancel_times-equal-correct
                             acl2::cancel_plus-equal-correct)))

  (defthm bvar-db-orderedp-implies-vars-bounded
    (implies (and (bvar-db-orderedp p bvar-db)
                  (<= (next-bvar$a bvar-db) (nfix n))
                  (<= (nfix m) (next-bvar$a bvar-db)))
             (bvar-db-vars-bounded n p m bvar-db))
    :hints(("Goal" :in-theory (enable bvar-db-vars-bounded))))

  (defthm pbfr-vars-bounded-of-bfr-not
    (implies (pbfr-vars-bounded k p x)
             (pbfr-vars-bounded k p (bfr-not x)))
    :hints (("goal" :expand ((pbfr-vars-bounded k p (bfr-not x))))))

  (local (defthmd gobj-vars-bounded-when-gobject-hierarchy-lite
           (implies (gobject-hierarchy-lite x)
                    (gobj-vars-bounded k p x))
           :hints(("Goal" :in-theory (enable gobject-hierarchy-lite
                                             gobj-vars-bounded)))))

  (local (in-theory (disable len default-car default-cdr bfr-eval-booleanp
                             fgetprop hons-assoc-equal)))

  (defthm gobj-vars-bounded-of-general-consp-car
    (implies (and (gobj-vars-bounded k p x)
                  (general-consp x))
             (gobj-vars-bounded k p (general-consp-car x)))
    :hints(("Goal" :in-theory (enable general-consp general-consp-car
                                      mk-g-concrete
                                      concrete-gobjectp
                                      gobj-vars-bounded-when-gobject-hierarchy-lite))))

  (defthm gobj-vars-bounded-of-general-consp-cdr
    (implies (and (gobj-vars-bounded k p x)
                  (general-consp x))
             (gobj-vars-bounded k p (general-consp-cdr x)))
    :hints(("Goal" :in-theory (enable general-consp general-consp-cdr
                                      mk-g-concrete
                                      concrete-gobjectp
                                      gobj-vars-bounded-when-gobject-hierarchy-lite))))

  (defthm bvar-db-orderedp-of-maybe-add-equiv-term
    (implies (bvar-db-orderedp p bvar-db)
             (bvar-db-orderedp p (maybe-add-equiv-term x n bvar-db state)))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term
                                      add-term-equiv))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defthm bvar-db-orderedp-of-add-term->bvar
    (implies (and (bvar-db-orderedp p bvar-db)
                  (gobj-vars-bounded (next-bvar$a bvar-db) p gobj))
             (bvar-db-orderedp p (add-term-bvar$a gobj bvar-db)))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defthm bvar-db-orderedp-of-add-term->bvar-unique
    (implies (and (bvar-db-orderedp p bvar-db)
                  (gobj-vars-bounded (next-bvar$a bvar-db) p gobj))
             (bvar-db-orderedp p (mv-nth 1 (add-term-bvar-unique gobj bvar-db))))
    :hints(("Goal" :in-theory (enable add-term-bvar-unique))))


  (def-glcp-interp-thm bvar-db-ordered-of-glcp-generic-interp
    :body (implies (and ;; (not erp)
                    (bfr-vars-bounded k p)
                    ;; (bfr-eval p env)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p (glcp-config->param-bfr config))
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
                   (bvar-db-orderedp p bvar-db1))
    :add-bindings ((k (next-bvar$a bvar-db)))
    :special
    ((test :add-hyps (gobj-alist-vars-bounded k p alist))
     (equivs :add-hyps (gobj-alist-vars-bounded k p alist))
     (term :add-hyps (gobj-alist-vars-bounded k p alist))
     (if/or :add-hyps (gobj-alist-vars-bounded k p alist))
     (maybe :add-hyps (gobj-alist-vars-bounded k p alist))
     (if :add-hyps (gobj-alist-vars-bounded k p alist))
     (or :add-hyps (gobj-alist-vars-bounded k p alist))
     (merge :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                           (gobj-vars-bounded k p then)
                           (gobj-vars-bounded k p else)))
     (merge-sub :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                           (gobj-vars-bounded k p then)
                           (gobj-vars-bounded k p else)))
     (merge-list :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                                (gobj-list-vars-bounded k p then)
                                (gobj-list-vars-bounded k p else)
                                (equal (len then) (len else)))
                 :hints ('(:in-theory (enable len))))
     (finish-if :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                               (gobj-alist-vars-bounded k p alist)))

     (finish-or :add-hyps (and (pbfr-vars-bounded k p test-bfr)
                               (gobj-vars-bounded k p then-obj)
                               (gobj-alist-vars-bounded k p alist)))
     (maybe-test-simp :add-hyps (gobj-vars-bounded k p test-obj)
                      :hints ((and stable-under-simplificationp
                                   '(:use ((:instance gobj-vars-bounded-when-g-var
                                            (x test-obj) (k 0)
                                            (p (glcp-config->param-bfr config))))
                                     :in-theory (disable
                                                 gobj-vars-bounded-when-g-var)))))

     (test-simp :add-hyps (gobj-vars-bounded k p test-obj)
                :hints ((and stable-under-simplificationp
                             '(:use ((:instance gobj-vars-bounded-when-g-var
                                      (x test-obj) (k 0)
                                      (p (glcp-config->param-bfr config))))
                               :in-theory (disable
                                           gobj-vars-bounded-when-g-var)))))
     (test-simp-fncall :add-hyps (gobj-list-vars-bounded k p args))
     (constraints :add-hyps (gobj-vars-bounded k p lit))
     (constraint-substs :add-hyps (gobj-alist-list-vars-bounded
                                   k p (alist-vals substs))
                        :hints ((and stable-under-simplificationp
                                     '(:expand ((alist-vals substs))
                                       :in-theory (enable gobj-alist-list-vars-bounded)))))
     ;; (fncall-ifs :add-hyps (gobj-list-vars-bounded k p actuals))
     ;; (maybe-fncall-ifs :add-hyps (gobj-list-vars-bounded k p actuals))

     (fncall :add-hyps (gobj-list-vars-bounded k p actuals)
             :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
     (rewrite :add-hyps (gobj-list-vars-bounded k p actuals))
     (rules :add-hyps (gobj-list-vars-bounded k p actuals))
     (rule :add-hyps (gobj-list-vars-bounded k p actuals))
     (hyps :add-hyps (gobj-alist-vars-bounded k p bindings))
     (hyp :add-hyps (gobj-alist-vars-bounded k p bindings))
     (list :add-hyps (gobj-alist-vars-bounded k p alist)))
    :expand-calls t
    :hints (;; (let ((lit (car clause)))
            ;;   (case-match lit
            ;;     (('not ('acl2::flag-is . &) . &)
            ;;      '(;; :computed-hint-replacement
            ;;        ;; ('(:expand :lambdas))
            ;;        :clause-processor acl2::constant-prop-cp))))
            (and stable-under-simplificationp
                 `(,@(and (eq (caar (last clause)) 'bvar-db-orderedp)
                          `(:expand (,(car (last clause)))))
                     :in-theory (enable bvar-db-vars-bounded-incr)
                     :do-not-induct t)))))


(defsection glcp-generic-interp-correct
  (local (in-theory (disable ;;glcp-generic-interp-term-ok-obligs
                             (:type-prescription hyp-fix)
                             hyp-fix-of-hyp-fixedp
                             pseudo-termp
                             bfr-hyp-fix-when-hyp$ap
                             gbc-process-new-lit
                             glcp-generic-interp-term
                             glcp-or-test-contexts
                             glcp-generic-geval-general-concrete-obj-correct
                             pseudo-term-listp
                             acl2::interp-defs-alist-clauses
                             general-concrete-listp
                             general-concrete-obj-list
                             acl2::weak-rewrite-rule-p
                             acl2::eval-bdd
                             hons-assoc-equal
                             proper-contextsp
                             (bfr-hyp-init$a)
                             (proper-contextsp)
                             kwote-lst
                             symbol-listp)))

  (local (defthm proper-contextsp-of-iff
           (proper-contextsp '(iff))
           :hints(("Goal" :in-theory (enable proper-contextsp
                                             glcp-generic-equiv-relp)))))
  (local (defthm proper-contextsp-nil
           (proper-contextsp nil)
           :hints(("Goal" :in-theory (enable proper-contextsp
                                             glcp-generic-equiv-relp)))))

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

  (local (in-theory (enable (:t type-of-next-bvar$a)
                            (:t type-of-base-bvar$a)
                            (:t type-of-get-term->bvar$a)
                            (:t natp-bvar-of-add-term-bvar-unique))))

  (local (defthm len-general-concrete-obj-list
           (equal (len (general-concrete-obj-list x))
                  (len x))
           :hints(("Goal" :in-theory (enable general-concrete-obj-list len)))))

  (local (defthmd glcp-generic-geval-of-consp
           (implies (and (NOT (EQUAL (TAG X) :G-BOOLEAN))
                         (NOT (EQUAL (TAG X) :G-NUMBER))
                         (NOT (EQUAL (TAG X) :G-CONCRETE))
                         (NOT (EQUAL (TAG X) :G-VAR))
                         (NOT (EQUAL (TAG X) :G-ITE))
                         (NOT (EQUAL (TAG X) :G-APPLY))
                         (consp x))
                    (equal (glcp-generic-geval x env)
                           (cons (glcp-generic-geval (car x) env)
                                 (glcp-generic-geval (cdr x) env))))
           :hints(("Goal" :in-theory (enable g-keyword-symbolp)))))


  (local (defthmd glcp-generic-geval-g-ite-p
           (implies (equal (tag x) :g-ite)
                    (equal (glcp-generic-geval x env)
                           (if (glcp-generic-geval (g-ite->test x) env)
                               (glcp-generic-geval (g-ite->then x) env)
                             (glcp-generic-geval (g-ite->else x) env))))
           :hints(("Goal" :in-theory (enable glcp-generic-geval)))))

  (local (defthmd glcp-generic-geval-g-var
           (implies (equal (tag x) :g-var)
                    (equal (glcp-generic-geval x env)
                           (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
           :hints(("Goal" :in-theory (enable glcp-generic-geval)))))

  (local (defthmd bfr-eval-test-when-false
           (implies (and (not (hyp-fix x pathcond))
                         (bfr-hyp-eval pathcond (car env)))
                    (not (bfr-eval x (car env))))
           :hints ((bfr-reasoning))))

  (local (defthmd bfr-eval-test-when-true
           (implies (and (not (hyp-fix (bfr-not x) pathcond))
                         (bfr-hyp-eval pathcond (car env)))
                    (bfr-eval x (car env)))
           :hints ((bfr-reasoning))))

  (local (defthmd bfr-eval-when-not-bfr-not
           (implies (not (bfr-not x))
                    (bfr-eval x (car env)))
           :hints ((bfr-reasoning))))

  (local (defthmd hyp-fix-bfr-not
           (implies (and (not (hyp-fix x pathcond))
                         (bfr-hyp-eval pathcond (car env)))
                    (hyp-fix (bfr-not x) pathcond))
           :hints (("goal" :use (bfr-eval-test-when-true
                                 bfr-eval-test-when-false)))))

  (local (Defthmd car-kwote-lst
           (implies (>= (len x) 1)
                    (equal (car (kwote-lst x))
                           (list 'quote (car x))))
           :hints(("Goal" :in-theory (enable kwote-lst len)))))

  (local (Defthmd cadr-kwote-lst
           (implies (>= (len x) 2)
                    (equal (cadr (kwote-lst x))
                           (list 'quote (cadr x))))
           :hints(("Goal" :in-theory (enable kwote-lst len)))))

  (local (Defthmd car-glcp-generic-geval-list
           (implies (>= (len x) 1)
                    (equal (car (glcp-generic-geval-list x env))
                           (glcp-generic-geval (car x) env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-list len)))))

  (local (Defthmd cadr-glcp-generic-geval-list
           (implies (>= (len x) 2)
                    (equal (cadr (glcp-generic-geval-list x env))
                           (glcp-generic-geval (cadr x) env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-list len)))))

  (local (defthmd glcp-generic-geval-of-g-boolean
           (equal (glcp-generic-geval (g-boolean x) env)
                  (bfr-eval x (car env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval)))))

  (local (defthm len-0
           (equal (equal (len x) 0)
                  (not (consp x)))
           :hints(("Goal" :in-theory (enable len)))))

  (local (defthm if-test-fncall-when-quote
           (mv-nth 1 (glcp-generic-simplify-if-test-fncall
                      'quote args pathcond clk config interp-st
                      bvar-db st))
           :hints (("goal" :expand
                    ((glcp-generic-simplify-if-test-fncall
                      'quote args pathcond clk config interp-st
                      bvar-db st))))))

  (local (defthm glcp-interp-accs-ok-of-update-add-bvars-allowed
           (equal (glcp-interp-accs-ok (update-nth *is-add-bvars-allowed* val interp-st) bvar-db config env)
                  (glcp-interp-accs-ok interp-st bvar-db config env))
           :hints(("Goal" :in-theory (enable glcp-interp-accs-ok)))))

  (local (in-theory (disable
                     GLCP-GENERIC-INTERP-FUNCTION-LOOKUP-THEOREMP-DEFS-HISTORY
                     glcp-generic-geval-ev-conjoin-clauses-atom
                     acl2::cancel_times-equal-correct
                     acl2::cancel_plus-equal-correct
                     contextsp not iff tag-when-atom proper-contextsp
                     mv-nth-cons-meta
                     bfr-eval-booleanp
                     glcp-if-or-condition
                     acl2::rewrite-rule-term
                     rewrite-rule-term-alt-def
                     len hons-assoc-equal
                     ;; acl2::alistp-when-hons-duplicity-alist-p
                     acl2::alistp-when-esc-alist-p
                     glcp-generic-eval-context-equiv*-suff
;glcp-if-test-contexts
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-term
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-maybe
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-equivs
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-merge
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-test-simp
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-test-simp-fncall
; glcp-generic-interp-bvar-db-env-ok-preserved-fncall-ifs
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-rewrite
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-if/or
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-if
                     ;; glcp-generic-interp-bvar-db-env-ok-preserved-or
                     glcp-generic-bvar-db-env-ok-bound-decr
                     glcp-or-test-contexts)))

  ;; (local (in-theory (enable* env-ok-special-rules)))


  (local (in-theory (disable iff)))

  (defthm if*-cases
    (and (implies x
                  (equal (if* x y z) y))
         (implies (not x)
                  (equal (if* x y z) z))))

  (local (in-theory (disable if*)))

  (defthm glcp-interp-accs-ok-of-update-constraint
    (equal (glcp-interp-accs-ok (update-nth *is-constraint* c interp-st)
                                bvar-db config env)
           (glcp-interp-accs-ok interp-st bvar-db config env))
    :hints(("Goal" :in-theory (enable glcp-interp-accs-ok))))

  (defthm glcp-interp-accs-ok-of-update-constraint-db
    (equal (glcp-interp-accs-ok (update-nth *is-constraint-db* cdb interp-st)
                                bvar-db config env)
           (glcp-interp-accs-ok interp-st bvar-db config env))
    :hints(("Goal" :in-theory (enable glcp-interp-accs-ok))))

  (defthm glcp-generic-geval-ev-quote
    (equal (glcp-generic-geval-ev (cons 'quote x) env)
           (car x))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-ev-of-quote))))

  (local (defthm bfr-force-check-pathcond-unsat-bind-free
           (b* (((mv pc-sat ?xx) (bfr-force-check x pathcond dir)))
             (implies (and (bind-free '((env . (car env))) (env))
                           (bfr-eval pathcond env))
                      pc-sat))))


  (def-glcp-interp-thm glcp-generic-interp-correct
    :hyps (and (bfr-hyp-eval (nth *is-constraint* interp-st) (car env))
               (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
               (acl2::interp-defs-alistp (glcp-config->overrides config))
               ;; (glcp-generic-geval-ev-theoremp
               ;;  (conjoin-clauses
               ;;   (acl2::interp-defs-alist-clauses
               ;;    (nth *is-obligs* interp-st1))))
               ;; (glcp-generic-geval-ev-meta-extract-global-facts)
               (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
               ;; (glcp-generic-bvar-db-env-ok
               ;;  bvar-db1 (glcp-config->param-bfr config)
               ;;  (next-bvar$a bvar-db1) env)
               (bdd-mode-or-p-true (glcp-config->param-bfr config) (car env))
               (glcp-interp-accs-ok interp-st1 bvar-db1 config env)
               (equal (w state0) (w st)))
    :add-concls ((bfr-hyp-eval (nth *is-constraint* interp-st1) (car env))
                 (implies (equal erp :unreachable)
                          (not (bfr-hyp-eval pathcond (car env)))))
    :special
    ((test :add-hyps (and (pseudo-termp x)
                          (alistp alist))
           :body (implies (and (not erp)
                               (bfr-hyp-eval pathcond (car env)))
                          (iff* (bfr-eval val (car env))
                               (glcp-generic-geval-ev x (glcp-generic-geval-alist
                                                         alist env)))))

     (equivs :add-hyps (and (pseudo-termp x)
                            (alistp alist)
                            (proper-contextsp contexts)
                            (contextsp contexts))
             :body (implies (and (not erp)
                                 (bfr-hyp-eval pathcond (car env)))
                            (glcp-generic-eval-context-equiv*
                             contexts
                             (glcp-generic-geval val env)
                             (glcp-generic-geval-ev x (glcp-generic-geval-alist
                                                       alist env)))))
     (term :add-hyps (and (pseudo-termp x)
                          (alistp alist)
                          (proper-contextsp contexts)
                          (contextsp contexts))
           :body (implies (and (not erp)
                               (bfr-hyp-eval pathcond (car env)))
                          (glcp-generic-eval-context-equiv*
                           contexts
                           (glcp-generic-geval val env)
                           (glcp-generic-geval-ev x (glcp-generic-geval-alist
                                                     alist env))))
           :hints ((and stable-under-simplificationp
                        '(:in-theory (enable
                                      glcp-generic-geval-ev-of-fncall-args
                                      glcp-generic-geval-ev-of-return-last-call
                                      glcp-generic-geval-ev-of-if-call
                                      glcp-generic-geval-ev-of-gl-ignore-call
                                      glcp-generic-geval-ev-of-gl-aside-call
                                      glcp-generic-geval-ev-of-lambda
                                      glcp-generic-geval-ev-of-variable
                                      glcp-generic-geval-ev-of-quote
                                      equal-len
                                      acl2::expand-marked-meta)))))
     (if/or :add-hyps                     (and (pseudo-termp tbr)
                                               (pseudo-termp fbr)
                                               (pseudo-termp test)
                                               (alistp alist)
                                               (proper-contextsp contexts)
                                               (contextsp contexts))
            :body (implies (and (not erp)
                                (bfr-hyp-eval pathcond (car env)))
                           (glcp-generic-eval-context-equiv*
                            contexts
                            (glcp-generic-geval val env)
                            (if (glcp-generic-geval-ev test (glcp-generic-geval-alist
                                                             alist env))
                                (glcp-generic-geval-ev tbr (glcp-generic-geval-alist
                                                            alist env))
                              (glcp-generic-geval-ev fbr (glcp-generic-geval-alist
                                                          alist env))))))


     (maybe :add-hyps (and (pseudo-termp x)
                           (alistp alist)
                           (proper-contextsp contexts)
                           (contextsp contexts))
            :body (and (implies (and (and (not erp)
                                          (not unreachp)
                                          (bfr-hyp-eval pathcond (car env)))
                                     (bfr-eval branchcond (car env)))
                                (glcp-generic-eval-context-equiv*
                                 contexts
                                 (glcp-generic-geval val env)
                                 (glcp-generic-geval-ev x (glcp-generic-geval-alist
                                                           alist env))))
                       (implies (and unreachp
                                     (bfr-hyp-eval pathcond (car env)))
                                (not (bfr-eval branchcond (car env)))))

            :hints((and stable-under-simplificationp
                        '(:in-theory (enable bfr-eval-test-when-false)))))

     (if :add-hyps                  (and (pseudo-termp tbr)
                                         (pseudo-termp fbr)
                                         (pseudo-termp test)
                                         (alistp alist)
                                         (proper-contextsp contexts)
                                         (contextsp contexts))
       :body (implies (and (not erp)
                           (bfr-hyp-eval pathcond (car env)))
                      (glcp-generic-eval-context-equiv*
                       contexts
                       (glcp-generic-geval val env)
                       (if* (glcp-generic-geval-ev test (glcp-generic-geval-alist
                                                        alist env))
                           (glcp-generic-geval-ev tbr (glcp-generic-geval-alist
                                                       alist env))
                         (glcp-generic-geval-ev fbr (glcp-generic-geval-alist
                                                     alist env)))))
       :hints ((prog2$ (cw "IF case~%")
                       '(:no-op t))))

     (or :add-hyps (and (pseudo-termp fbr)
                        (pseudo-termp test)
                        (alistp alist)
                        (proper-contextsp contexts)
                        (contextsp contexts))
         :body (implies (and (not erp)
                             (bfr-hyp-eval pathcond (car env)))
                        (glcp-generic-eval-context-equiv*
                         contexts
                         (glcp-generic-geval val env)
                         (if* (glcp-generic-geval-ev test (glcp-generic-geval-alist
                                                          alist env))
                              (glcp-generic-geval-ev test (glcp-generic-geval-alist
                                                          alist env))
                             (glcp-generic-geval-ev fbr (glcp-generic-geval-alist
                                                         alist env)))))
         :hints ('(:in-theory (enable glcp-context-equiv-of-glcp-or-test-contexts))))

     (merge :add-hyps (and (proper-contextsp contexts)
                           (contextsp contexts))
            :body (implies (and (not erp)
                                (bfr-hyp-eval pathcond (car env)))
                           (glcp-generic-eval-context-equiv*
                            contexts
                            (glcp-generic-geval val env)
                            (if (bfr-eval test-bfr (car env))
                                (glcp-generic-geval then env)
                              (glcp-generic-geval else env))))
            :hints ((and stable-under-simplificationp
                         '(:in-theory (enable glcp-generic-geval-ev-of-if-call
                                              glcp-generic-geval-of-g-boolean
                                              glcp-generic-geval-ev-of-quote
                                              kwote-lst)))))

     (merge-sub :add-hyps (and (proper-contextsp contexts)
                               (contextsp contexts))
                :body (implies (and (not erp)
                                    (bfr-hyp-eval pathcond (car env)))
                               (glcp-generic-eval-context-equiv*
                                contexts
                                (glcp-generic-geval val env)
                                (if (bfr-eval test-bfr (car env))
                                    (glcp-generic-geval then env)
                                  (glcp-generic-geval else env)))
                               ;; (equal (glcp-generic-geval val env)
                               ;;        (if (bfr-eval test-bfr (car env))
                               ;;            (glcp-generic-geval then env)
                               ;;          (glcp-generic-geval else env)))
                               )
                :hints ((and stable-under-simplificationp
                             '(:in-theory (enable glcp-generic-geval-g-apply-p)))))

     (merge-list :add-hyps (equal (len then) (len else))
                 :body (implies (and (not erp)
                                     (bfr-hyp-eval pathcond (car env)))
                                (equal (glcp-generic-geval-list val env)
                                       (if (bfr-eval test-bfr (car env))
                                           (glcp-generic-geval-list then env)
                                         (glcp-generic-geval-list else env))))
                 :hints('(:in-theory (enable len))))

     (maybe-test-simp :body (and (implies (and (not erp)
                                               (not unreachp)
                                               (bfr-hyp-eval pathcond (car env))
                                               (bfr-eval branchcond (car env)))
                                          (iff* (bfr-eval val (car env))
                                                (glcp-generic-geval test-obj env)))
                                 (implies (and unreachp
                                               (bfr-hyp-eval pathcond (car env)))
                                          (not (bfr-eval branchcond (car env)))))
                      :hints ((and stable-under-simplificationp
                                   '(:expand ((:with glcp-generic-geval (glcp-generic-geval test-obj env)))
                                     :in-theory (enable ;; glcp-generic-geval-of-consp
                                                 ;; glcp-generic-geval-g-apply-p
                                                 ;; glcp-generic-geval-g-ite-p
                                                 bfr-eval-test-when-true
                                                 bfr-eval-when-not-bfr-not
                                                 bfr-eval-test-when-false
                                                 glcp-generic-geval-ev-of-gl-force-check-fn-call
                                                 glcp-generic-geval-ev-of-equal-call
                                                 glcp-generic-geval-ev-of-not-call
                                                 ;; glcp-generic-geval-g-var
                                                 car-glcp-generic-geval-list
                                                 cadr-glcp-generic-geval-list
                                                 car-kwote-lst
                                                 cadr-kwote-lst
                                                 glcp-generic-geval-ev-of-quote
                                                 hyp-fix-bfr-not
                                                 acl2::expand-marked-meta)))))

     (test-simp :body (implies (and (not erp)
                                    (bfr-hyp-eval pathcond (car env)))
                               (iff* (bfr-eval val (car env))
                                    (glcp-generic-geval test-obj env)))
                :hints ((and stable-under-simplificationp
                             '(:expand ((:with glcp-generic-geval (glcp-generic-geval test-obj env)))
                               :in-theory (enable ;; glcp-generic-geval-of-consp
                                           ;; glcp-generic-geval-g-apply-p
                                           ;; glcp-generic-geval-g-ite-p
                                           bfr-eval-test-when-true
                                           bfr-eval-when-not-bfr-not
                                           bfr-eval-test-when-false
                                           glcp-generic-geval-ev-of-gl-force-check-fn-call
                                           glcp-generic-geval-ev-of-equal-call
                                           glcp-generic-geval-ev-of-not-call
                                           car-glcp-generic-geval-list
                                           cadr-glcp-generic-geval-list
                                           car-kwote-lst
                                           cadr-kwote-lst
                                           glcp-generic-geval-ev-of-quote
                                           hyp-fix-bfr-not
                                           acl2::expand-marked-meta)))))

     (test-simp-fncall
      :body (implies (and (not erp)
                          (bfr-hyp-eval pathcond (car env)))
                     (iff* (bfr-eval val (car env))
                          (glcp-generic-geval-ev
                           (cons fn
                                 (kwote-lst (glcp-generic-geval-list args env)))
                           nil)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:with glcp-generic-geval (glcp-generic-geval test-obj env)))
                     :in-theory (enable ;; glcp-generic-geval-of-consp
                                 ;; glcp-generic-geval-g-apply-p
                                 ;; glcp-generic-geval-g-ite-p
                                 bfr-eval-test-when-true
                                 bfr-eval-when-not-bfr-not
                                 bfr-eval-test-when-false
                                 glcp-generic-geval-ev-of-gl-force-check-fn-call
                                 glcp-generic-geval-ev-of-equal-call
                                 glcp-generic-geval-ev-of-not-call
                                 car-glcp-generic-geval-list
                                 cadr-glcp-generic-geval-list
                                 car-kwote-lst
                                 cadr-kwote-lst
                                 glcp-generic-geval-ev-of-quote
                                 hyp-fix-bfr-not
                                 acl2::expand-marked-meta)))))
     (constraints)
     (constraint-substs)

     ;; (fncall-ifs :add-hyps (and (symbolp fn)
     ;;                            (not (eq fn 'quote))
     ;;                            (proper-contextsp contexts)
     ;;                            (contextsp contexts))
     ;;             :body (implies (and (not erp)
     ;;                                 (bfr-hyp-eval pathcond (car env)))
     ;;                            (glcp-generic-eval-context-equiv*
     ;;                             contexts
     ;;                             (glcp-generic-geval val env)
     ;;                             (glcp-generic-geval-ev
     ;;                              (cons fn (kwote-lst (glcp-generic-geval-list actuals env)))
     ;;                              nil))))
     ;; (maybe-fncall-ifs :add-hyps (and (symbolp fn)
     ;;                                  (not (eq fn 'quote))
     ;;                                  (proper-contextsp contexts)
     ;;                                  (contextsp contexts))
     ;;                   :body (and (implies (and (bfr-eval branchcond (car env))
     ;;                                            (not erp)
     ;;                                            (not unreachp)
     ;;                                            (bfr-hyp-eval pathcond (car env)))
     ;;                                       (glcp-generic-eval-context-equiv*
     ;;                                        contexts
     ;;                                        (glcp-generic-geval val env)
     ;;                                        (glcp-generic-geval-ev
     ;;                                         (cons fn (kwote-lst (glcp-generic-geval-list actuals env)))
     ;;                                         nil)))
     ;;                              (implies (and unreachp
     ;;                                            (bfr-hyp-eval pathcond (car env)))
     ;;                                       (not (bfr-eval branchcond (car env)))))
     ;;                   :hints('(:in-theory (enable bfr-eval-test-when-false))))

     (fncall :add-hyps (and (symbolp fn)
                            (not (eq fn 'quote))
                            (proper-contextsp contexts)
                            (contextsp contexts))
             :body (implies (and (not erp)
                                 (bfr-hyp-eval pathcond (car env)))
                            (glcp-generic-eval-context-equiv*
                             contexts
                             (glcp-generic-geval val env)
                             (glcp-generic-geval-ev
                              (cons fn (kwote-lst (glcp-generic-geval-list actuals env)))
                              nil)))
             :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
     (rewrite :add-hyps (and (symbolp fn)
                             (not (eq fn 'quote))
                             (contextsp contexts)
                             (proper-contextsp contexts))
              :body (implies (and (not erp)
                                  (bfr-hyp-eval pathcond (car env)))
                             (implies successp
                                      (glcp-generic-eval-context-equiv*
                                       contexts
                                       (glcp-generic-geval-ev term
                                                              (glcp-generic-geval-alist
                                                               bindings env))
                                       (glcp-generic-geval-ev
                                        (cons fn (kwote-lst (glcp-generic-geval-list
                                                             actuals env)))
                                        nil)))))
     (rules :add-hyps (and (symbolp fn)
                           (not (eq fn 'quote))
                           (good-rewrite-rulesp fn-rewrites)
                           (contextsp contexts)
                           (proper-contextsp contexts))
            :body (implies (and (not erp)
                                (bfr-hyp-eval pathcond (car env)))
                           (implies successp
                                    (glcp-generic-eval-context-equiv*
                                     contexts
                                     (glcp-generic-geval-ev term
                                                            (glcp-generic-geval-alist
                                                             bindings env))
                                     (glcp-generic-geval-ev
                                      (cons fn (kwote-lst (glcp-generic-geval-list
                                                           actuals env)))
                                      nil)))))
     (rule :add-hyps (and (symbolp fn)
                          (not (eq fn 'quote))
                          (glcp-generic-geval-ev-theoremp
                           (acl2::rewrite-rule-term rule))
                          (contextsp contexts)
                          (proper-contextsp contexts))
           :body (implies (and (not erp)
                               (bfr-hyp-eval pathcond (car env)))
                          (implies successp
                                   (glcp-generic-eval-context-equiv*
                                    contexts
                                    (glcp-generic-geval-ev term
                                                           (glcp-generic-geval-alist
                                                            bindings env))
                                    (glcp-generic-geval-ev
                                     (cons fn (kwote-lst (glcp-generic-geval-list
                                                          actuals env)))
                                     nil))))
           :hints((and stable-under-simplificationp
                       '(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                           acl2::expand-marked-meta))))))
     (hyps :add-hyps (and (pseudo-term-listp hyps)
                          (alistp bindings))
           :body (implies (and (not erp)
                               (bfr-hyp-eval pathcond (car env)))
                          (implies successp
                                   (glcp-generic-geval-ev
                                    (conjoin hyps)
                                    (glcp-generic-geval-alist bindings env)))))
     (hyp :add-hyps (and (pseudo-termp hyp)
                         (alistp bindings))
          :body (implies (and (not erp)
                              (bfr-hyp-eval pathcond (car env)))
                         (implies successp
                                  (glcp-generic-geval-ev
                                   hyp (glcp-generic-geval-alist bindings env))))
          :hints ((and stable-under-simplificationp
                       '(:in-theory (e/d* (gtests-known-and-true))))))
     (list :add-hyps (and (pseudo-term-listp x)
                          (alistp alist))
           :body (implies (and (not erp)
                               (bfr-hyp-eval pathcond (car env)))
                          (equal (glcp-generic-geval-list vals env)
                                 (glcp-generic-geval-ev-lst
                                  x (glcp-generic-geval-alist alist
                                                              env))))
           :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-lst-of-cons
                                       glcp-generic-geval-ev-lst-of-atom))))))
    :expand-calls t
    :hints (;; '(:error t)
            (let ((lit (car clause)))
              (case-match lit
                (('not ('acl2::flag-is . &) . &)
                 '(;; :computed-hint-replacement
                   ;; ('(:expand :lambdas))
                   :clause-processor acl2::constant-prop-cp))))
            (and stable-under-simplificationp
                 '(; :in-theory (enable acl2::expand-marked-meta)
                   :do-not-induct t
                   :do-not '(generalize)))
            ;; (and (equal id '((0 1) (49) . 0))
            ;;      (prog2$ (accumulated-persistence t)
            ;;              nil))
            ;; (and (equal id '((0 1) (48) . 0))
            ;;      (prog2$ (show-accumulated-persistence)
            ;;              nil))
            ;; (and (id-on-the-way-to id '((0 1) (64 2) . 0))
            ;;      '(:error t)
            ;;      ;; (cw "~x0~%" (acl2::prettyify-clause clause nil (w state)))
            ;;      )
            )))



(defun bvar-db-fix-env (n min bvar-db p bfr-env var-env)
  ;; For bfr-env in the param-space for p, assign each bfr variable from n-1
  ;; down to min to the value of the term bound to that variable.  This has to
  ;; work up from min so that the lower-numbered Boolean variables are
  ;; corrected, because the higher-numbered ones may depend on them.
  (declare (xargs :stobjs bvar-db
                  :measure (nfix n)
                  :guard (and (integerp n)
                              (integerp min)
                              (<= (base-bvar bvar-db) min)
                              (<= min n)
                              (<= n (next-bvar bvar-db)))))
  (b* ((n (lnfix n))
       (min (lnfix min))
       ((when (mbe :logic (or (<= n (base-bvar bvar-db))
                              (<= n min))
                   :exec (int= n min))) bfr-env)
       (n (1- n))
       (bfr-env (bvar-db-fix-env n min bvar-db p bfr-env var-env))
       (term (get-bvar->term n bvar-db))
       (val (glcp-generic-geval term (cons bfr-env var-env))))
    (bfr-param-env p
                   (bfr-set-var n val (bfr-unparam-env p bfr-env)))))

(defthm bvar-db-fix-env-eval-p-lemma
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
                (bfr-vars-bounded min p)
                (<= (nfix n) (next-bvar$a bvar-db)))
           (bfr-eval p (bfr-unparam-env p (bvar-db-fix-env n min bvar-db p
                                                           (bfr-param-env p env)
                                                           var-env)))))

(defthm bvar-db-fix-env-bdd-mode-or-p-true-unparam
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bdd-mode-or-p-true p env)
            (bfr-vars-bounded min p)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (bdd-mode-or-p-true p (bfr-unparam-env p (bvar-db-fix-env n min bvar-db p
                                                                         (bfr-param-env p env)
                                                                         var-env))))
  :hints(("Goal" :in-theory (enable bdd-mode-or-p-true))))

(defthm bvar-db-fix-env-bdd-mode-or-p-true
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bdd-mode-or-p-true p env)
            (bfr-vars-bounded min p)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (bdd-mode-or-p-true p (bvar-db-fix-env n min bvar-db p
                                                  (bfr-param-env p env)
                                                  var-env)))
  :hints(("Goal" :in-theory (e/d (bdd-mode-or-p-true bfr-unparam-env)
                                 (bvar-db-fix-env-bdd-mode-or-p-true-unparam))
          :use ((:instance bvar-db-fix-env-bdd-mode-or-p-true-unparam)))))

(defthm bfr-env-equiv-of-param-unparam-fix-param-env
  (implies (and (bfr-eval p env)
                (bfr-vars-bounded min p)
                (<= (nfix n) (next-bvar$a bvar-db)))
           (bfr-env-equiv (bfr-param-env p (bfr-unparam-env p (bvar-db-fix-env n min bvar-db p
                                                                               (bfr-param-env p env)
                                                                               var-env)))
                          (bvar-db-fix-env n min bvar-db p
                                           (bfr-param-env p env)
                                           var-env)))
  :hints (("goal" :expand ((bvar-db-fix-env n min bvar-db p
                                            (bfr-param-env p env)
                                            var-env)))))
  


;; (defthm bfr-list->s-of-set-non-dep-bounded
;;   (implies (and (pbfr-list-vars-bounded n p x)
;;                 (<= (nfix n) (nfix k))
;;                 (bfr-eval p env)
;;                 (bfr-eval p (bfr-set-var k v env)))
;;            (equal (bfr-list->s x (bfr-param-env p (bfr-set-var k v env)))
;;                   (bfr-list->s x (bfr-param-env p env)))))
;;   :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))




;; (defthm bfr-list->s-of-param-unparam-param-env
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->s x (bfr-param-env
;;                                   p (bfr-unparam-env
;;                                      p (bfr-param-env p env))))
;;                   (bfr-list->s x (bfr-param-env p env))))
;;   :hints(("Goal" :in-theory (enable bfr-list->s))))

;; (defthm bfr-list->u-of-param-unparam-param-env
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->u x (bfr-param-env
;;                                   p (bfr-unparam-env
;;                                      p (bfr-param-env p env))))
;;                   (bfr-list->u x (bfr-param-env p env))))
;;   :hints(("Goal" :in-theory (enable bfr-list->u))))
(defthm-gobj-flag
  (defthm glcp-generic-geval-bfr-env-equiv-congruence
    (implies (bfr-env-equiv a b)
             (equal (glcp-generic-geval x (cons a venv))
                    (glcp-generic-geval x (cons b venv))))
    :rule-classes :congruence
    :hints ('(:expand ((:free (env) (:with glcp-generic-geval (glcp-generic-geval x env))))))
    :flag gobj)
  (defthm glcp-generic-geval-list-bfr-env-equiv-congruence
    (implies (bfr-env-equiv a b)
             (equal (glcp-generic-geval-list x (cons a venv))
                    (glcp-generic-geval-list x (cons b venv))))
    :rule-classes :congruence
    :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env)))))
    :flag list))

;; (defthm-gobj-flag
;;   (defthm glcp-generic-geval-of-param-unparam-param-env
;;     (implies (bfr-eval p env)
;;              (equal (glcp-generic-geval x (cons (bfr-param-env
;;                                                  p (bfr-unparam-env
;;                                                     p (bfr-param-env p env)))
;;                                                 var-env))
;;                     (glcp-generic-geval x (cons (bfr-param-env p env)
;;                                                 var-env))))
;;     :hints ('(:expand ((:free (env) (:with glcp-generic-geval (glcp-generic-geval x env))))))
;;     :flag gobj)
;;   (defthm glcp-generic-geval-list-of-param-unparam-param-env
;;     (implies (bfr-eval p env)
;;              (equal (glcp-generic-geval-list x (cons (bfr-param-env
;;                                                       p (bfr-unparam-env
;;                                                          p (bfr-param-env p env)))
;;                                                      var-env))
;;                     (glcp-generic-geval-list x (cons (bfr-param-env p env)
;;                                                      var-env))))
;;     :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env)))))
;;     :flag list))


;; (defthm bfr-list->s-of-unparam-param-env
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->s x (bfr-unparam-env
;;                                   p (bfr-param-env p env)))
;;                   (bfr-list->s x env)))
;;   :hints(("Goal" :in-theory (enable bfr-list->s))))

;; (defthm bfr-list->u-of-unparam-param-env
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->u x (bfr-unparam-env
;;                                   p (bfr-param-env p env)))
;;                   (bfr-list->u x env)))
;;   :hints(("Goal" :in-theory (enable bfr-list->u))))


;; (defthm-gobj-flag
;;   (defthm glcp-generic-geval-of-unparam-param-env
;;     (implies (bfr-eval p env)
;;              (equal (glcp-generic-geval x (cons (bfr-unparam-env
;;                                                  p (bfr-param-env p env))
;;                                                 var-env))
;;                     (glcp-generic-geval x (cons env var-env))))
;;     :hints ('(:expand ((:free (env) (:with glcp-generic-geval (glcp-generic-geval x env))))))
;;     :flag gobj)
;;   (defthm glcp-generic-geval-list-of-unparam-param-env
;;     (implies (bfr-eval p env)
;;              (equal (glcp-generic-geval-list x (cons (bfr-unparam-env
;;                                                       p (bfr-param-env p env))
;;                                                      var-env))
;;                     (glcp-generic-geval-list x (cons env var-env))))
;;     :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env)))))
;;     :flag list))

;; (defthm glcp-generic-geval-param-unparam-fix-env
;;   (implies (and (bfr-eval p env)
;;                 (bfr-vars-bounded min p)
;;                 (<= (nfix n) (next-bvar$a bvar-db)))
;;            (equal (glcp-generic-geval x (cons (bfr-param-env
;;                                                p (bfr-unparam-env
;;                                                   p (bvar-db-fix-env
;;                                                      n min bvar-db p (bfr-param-env p env)
;;                                                      var-env)))
;;                                               var-env2))
;;                   (glcp-generic-geval x (cons (bvar-db-fix-env
;;                                                n min bvar-db p (bfr-param-env p env)
;;                                                var-env)
;;                                               var-env2))))
;;   :hints (("goal" :expand ((bvar-db-fix-env
;;                             n min bvar-db p (bfr-param-env p env)
;;                             var-env))
;;            :do-not-induct t)))

;; (defthm bfr-eval-param-unparam-fix-env
;;   (implies (and (bfr-eval p env)
;;                 (bfr-vars-bounded min p)
;;                 (<= (nfix n) (next-bvar$a bvar-db)))
;;            (equal (bfr-eval x (bfr-param-env
;;                                p (bfr-unparam-env
;;                                   p (bvar-db-fix-env
;;                                      n min bvar-db p (bfr-param-env p env)
;;                                      var-env))))
;;                   (bfr-eval x (bvar-db-fix-env
;;                                n min bvar-db p (bfr-param-env p env)
;;                                var-env))))
;;   :hints (("goal" :expand ((bvar-db-fix-env
;;                             n min bvar-db p (bfr-param-env p env)
;;                             var-env))
;;            :do-not-induct t)))


(acl2::def-functional-instance
 glcp-generic-geval-of-set-var-when-gobj-vars-bounded
 generic-geval-of-set-var-when-gobj-vars-bounded
 ((generic-geval-ev glcp-generic-geval-ev)
  (generic-geval-ev-lst glcp-generic-geval-ev-lst)
  (generic-geval glcp-generic-geval)
  (generic-geval-list glcp-generic-geval-list))
 :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                             glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                            (glcp-generic-geval-apply))
           :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

(acl2::def-functional-instance
 glcp-generic-geval-list-of-set-var-when-gobj-vars-bounded
 generic-geval-list-of-set-var-when-gobj-vars-bounded
 ((generic-geval-ev glcp-generic-geval-ev)
  (generic-geval-ev-lst glcp-generic-geval-ev-lst)
  (generic-geval glcp-generic-geval)
  (generic-geval-list glcp-generic-geval-list))
 :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                             glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                            (glcp-generic-geval-apply))
           :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))




(defthm bvar-db-fix-env-eval-gobj-vars-bounded-lemma
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (gobj-vars-bounded m p gobj)
            (< (nfix m) (nfix n))
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env))
                  (env-m (bvar-db-fix-env m min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval gobj (cons env-n var-env))
                    (glcp-generic-geval gobj (cons env-m var-env)))))
  :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                           var-env))
          (and stable-under-simplificationp
               '(:in-theory (enable bdd-mode-or-p-true)))
          (and stable-under-simplificationp
               '(:expand ((bvar-db-fix-env m min bvar-db p (bfr-param-env p env) var-env))))))


(defthm bvar-db-fix-env-eval-bfr-vars-bounded-lemma
  (implies (and ; (bvar-db-orderedp p bvar-db)
                (bfr-eval p env)
                (bfr-vars-bounded min p)
                (pbfr-vars-bounded m p x)
                (< (nfix m) (nfix n))
                (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env))
                  (env-m (bvar-db-fix-env m min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (bfr-eval x env-n)
                    (bfr-eval x env-m))))
  :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                           var-env))
          (and stable-under-simplificationp
               '(:expand ((bvar-db-fix-env m min bvar-db p (bfr-param-env p env) var-env))))))

(defthm bvar-db-fix-env-eval-bfr-vars-bounded-lemma-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
                (bfr-eval p env)
                (bfr-vars-bounded min p)
                (pbfr-vars-bounded min p x)
                (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (bfr-eval x env-n)
                    (bfr-eval x (bfr-param-env p env)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-bfr-vars-bounded-lemma
                         (m min)))
           :in-theory (disable bvar-db-fix-env-eval-bfr-vars-bounded-lemma)
           :expand ((bvar-db-fix-env min min bvar-db p (bfr-param-env p env)
                                     var-env)))))





;; (defthm bvar-db-env-ok-of-bvar-db-fix-env-lemma
;;   (implies (and (bvar-db-orderedp p bvar-db)
;;                 (bfr-eval p bfr-env)
;;                 (bfr-vars-bounded min p)
;;                 (<= (nfix min) (nfix m))
;;                 (<= (base-bvar$a bvar-db) (nfix m))
;;                 (< (nfix m) (nfix n))
;;                 (<= (nfix n) (next-bvar$a bvar-db)))
;;            (let* ((bfr-env (bvar-db-fix-env n min bvar-db p
;;                                             (bfr-param-env p bfr-env)
;;                                             var-env)))
;;              (iff (bfr-lookup m (bfr-unparam-env p bfr-env))
;;                   (glcp-generic-geval (get-bvar->term m bvar-db)
;;                                       (cons bfr-env var-env)))))
;;   :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p
;;                                            (bfr-param-env p bfr-env)
;;                                            var-env))
;;           (and stable-under-simplificationp
;;                '(:use ((:instance bvar-db-orderedp-necc
;;                         (n (nfix m)))
;;                        (:instance bvar-db-orderedp-necc
;;                         (n m)))
;;                  :in-theory (disable bvar-db-orderedp-necc)))))

(defthm bvar-db-env-ok-of-bvar-db-fix-env-lemma
  (implies (and (bvar-db-orderedp p bvar-db)
                (bfr-eval p bfr-env)
                (bfr-vars-bounded min p)
                (natp (bfr-varname-fix m))
                (<= (base-bvar$a bvar-db) (bfr-varname-fix m))
                (< (bfr-varname-fix m) (nfix n))
                (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((bfr-env1 (bvar-db-fix-env n min bvar-db p
                                             (bfr-param-env p bfr-env)
                                             var-env)))
             (iff (bfr-lookup m (bfr-unparam-env p bfr-env1))
                  (if (<= (nfix min) (bfr-varname-fix m))
                      (glcp-generic-geval (get-bvar->term m bvar-db)
                                          (cons bfr-env1 var-env))
                    (bfr-lookup m bfr-env)))))
  :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p
                                           (bfr-param-env p bfr-env)
                                           var-env))
          (and stable-under-simplificationp
               '(:use ((:instance bvar-db-orderedp-necc
                        (n (bfr-varname-fix m)))
                       (:instance bvar-db-orderedp-necc
                        (n m)))
                 :in-theory (disable bvar-db-orderedp-necc
                                     gobj-vars-bounded-of-get-bvar->term-when-bvar-db-orderedp)))))


(defthm bvar-db-env-ok-of-bvar-db-fix-env
  (implies (and (bvar-db-orderedp p bvar-db)
                (bfr-eval p bfr-env)
                (bfr-vars-bounded (base-bvar$a bvar-db) p)
                (<= (nfix n) (next-bvar$a bvar-db))
                (<= nn (nfix n))
                (equal b (base-bvar$a bvar-db)))
           (let ((bfr-env (bvar-db-fix-env n b
                                           bvar-db p
                                           (bfr-param-env p bfr-env) var-env)))
             (glcp-generic-bvar-db-env-ok bvar-db p nn (cons bfr-env var-env))))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))






(defthm bvar-db-env-ok-of-bvar-db-fix-env2
  (implies (and (bvar-db-orderedp p bvar-db)
                (bfr-eval p bfr-env)
                (bfr-vars-bounded min p)
                (<= (nfix n) (next-bvar$a bvar-db))
                (<= nn (nfix n))
                (<= (base-bvar$a bvar-db) (nfix n))
                (glcp-generic-bvar-db-env-ok bvar-db p min
                                             (cons (bfr-param-env p bfr-env)
                                                   var-env)))
           (let ((bfr-env (bvar-db-fix-env n min
                                           bvar-db p
                                           (bfr-param-env p bfr-env) var-env)))
             (glcp-generic-bvar-db-env-ok bvar-db p nn (cons bfr-env var-env))))
  :hints ((and stable-under-simplificationp
               (let* ((lit (car (last clause)))
                      (witness (cons 'glcp-generic-bvar-db-env-ok-witness (cdr lit))))
                 (prog2$ (cw "witness: ~x0~%" witness)
                 `(:computed-hint-replacement
                   ('(:use ((:instance glcp-generic-bvar-db-env-ok-necc
                             (n ,witness)
                             (env (cons (bfr-param-env p bfr-env) var-env))
                             (bound min))
                            (:instance bvar-db-fix-env-eval-gobj-vars-bounded-lemma
                             (gobj (GET-BVAR->TERM$A ,witness BVAR-DB))
                             (m min) (env bfr-env)))
                      :expand ((BVAR-DB-FIX-ENV MIN
                                                MIN BVAR-DB P (BFR-PARAM-ENV P BFR-ENV)
                                                VAR-ENV))
                      :in-theory (disable glcp-generic-bvar-db-env-ok-necc
                                          bvar-db-fix-env-eval-gobj-vars-bounded-lemma)))
                   :expand (,lit)
                   :do-not-induct t))))))



(defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (pbfr-vars-bounded m t x)
            (< (nfix m) (nfix n))
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env))
                  (env-m (bvar-db-fix-env m min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (bfr-eval x (bfr-unparam-env p env-n))
                    (bfr-eval x (bfr-unparam-env p env-m)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-bfr-vars-bounded-lemma
                         (x (bfr-to-param-space p x))))
           :in-theory (e/d ()
                           (bvar-db-fix-env-eval-bfr-vars-bounded-lemma))
           :do-not-induct t)))


(defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (pbfr-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (bfr-eval x (bfr-unparam-env p env-n))
                    (bfr-eval x env))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-bfr-vars-bounded-unparam
                         (m min)))
           :in-theory (disable bvar-db-fix-env-eval-bfr-vars-bounded-unparam)
           :expand ((BVAR-DB-FIX-ENV MIN MIN BVAR-DB P (BFR-PARAM-ENV P ENV)
                                     VAR-ENV))
           :do-not-induct t)))

(defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw-aig-mode
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-mode)
            (bfr-vars-bounded min p)
            (pbfr-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (bfr-eval x env-n)
                    (bfr-eval x env))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw))
           :in-theory (e/d (bfr-unparam-env) (bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw)))))


(defthm bfr-unparam-env-t
  (equal (bfr-unparam-env t env) env)
  :hints(("Goal" :in-theory (enable bfr-unparam-env))))

(defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam-with-no-param
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (pbfr-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db t env var-env)))
             (equal (bfr-eval x env-n)
                    (bfr-eval x env))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw
                         (p t)))
           :expand ((bfr-vars-bounded min t))
           :in-theory (disable bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw)
           :do-not-induct t)))

(encapsulate nil
  (local (defthm bfr-hyp-eval-to-bfr-eval-of-bfr
           (equal (bfr-hyp-eval x env)
                  (bfr-eval (bfr-constr->bfr x) env))))

  (local (in-theory (disable bfr-eval-of-bfr-constr->bfr)))


  (defthm pbfr-vars-bounded-of-bfr-constr->bfr
    (implies (bfr-constr-vars-bounded k p x)
             (pbfr-vars-bounded k p (bfr-constr->bfr x)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm bvar-db-fix-env-eval-bfr-vars-bounded-lemma-bfr-hyp-eval
    (implies (and ; (bvar-db-orderedp p bvar-db)
              (bfr-eval p env)
              (bfr-vars-bounded min p)
              (bfr-constr-vars-bounded min p x)
              (<= (nfix n) (next-bvar$a bvar-db)))
             (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                            var-env)))
               (equal (bfr-hyp-eval x env-n)
                      (bfr-hyp-eval x (bfr-param-env p env))))))

  (defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam-with-no-param-bfr-hyp-eval
    (implies (and ; (bvar-db-orderedp p bvar-db)
              (bfr-constr-vars-bounded min t x)
              (<= (nfix n) (next-bvar$a bvar-db)))
             (let* ((env-n (bvar-db-fix-env n min bvar-db t env var-env)))
               (equal (bfr-hyp-eval x env-n)
                      (bfr-hyp-eval x env)))))

  (defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam-rw-bfr-hyp-eval
    (implies (and ; (bvar-db-orderedp p bvar-db)
              (bfr-eval p env)
              (bfr-vars-bounded min p)
              (bfr-constr-vars-bounded min t x)
              (<= (nfix n) (next-bvar$a bvar-db)))
             (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                            var-env)))
               (equal (bfr-hyp-eval x (bfr-unparam-env p env-n))
                      (bfr-hyp-eval x env)))))

  (defthm bvar-db-fix-env-eval-bfr-vars-bounded-unparam1-rw-bfr-hyp-eval
    (implies (and ; (bvar-db-orderedp p bvar-db)
              (bfr-eval p env)
              (bfr-vars-bounded min p)
              (bfr-constr-vars-bounded min t x)
              (<= (nfix n) (next-bvar$a bvar-db)))
             (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                            var-env)))
               (equal (bfr-hyp-eval x (bfr-unparam-env p env-n))
                      (bfr-hyp-eval x env)))))

    (defthm bfr-hyp-eval-of-bfr-unparam-of-param
      (implies (bfr-eval p env)
               (equal (bfr-hyp-eval x (bfr-unparam-env p (bfr-param-env p env)))
                      (bfr-hyp-eval x env)))))



(acl2::def-functional-instance
  glcp-generic-geval-gobj-to-param-space-correct-with-unparam-env
  gobj-to-param-space-correct-with-unparam-env
  ((generic-geval-ev glcp-generic-geval-ev)
   (generic-geval-ev-lst glcp-generic-geval-ev-lst)
   (generic-geval glcp-generic-geval)
  (generic-geval-list glcp-generic-geval-list))
  :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                              glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                            (glcp-generic-geval-apply))
            :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

(acl2::def-functional-instance
 glcp-generic-geval-gobj-list-to-param-space-correct-with-unparam-env
 gobj-list-to-param-space-correct-with-unparam-env
 ((generic-geval-ev glcp-generic-geval-ev)
  (generic-geval-ev-lst glcp-generic-geval-ev-lst)
  (generic-geval glcp-generic-geval)
  (generic-geval-list glcp-generic-geval-list))
 :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                             glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                            (glcp-generic-geval-apply))
           :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))







(defthm bvar-db-fix-env-eval-gobj-vars-bounded-unparam
  (implies (and ; (bvar-db-orderedp p bvar-db)
                (bfr-eval p env)
                (bfr-vars-bounded min p)
                (gobj-vars-bounded m t gobj)
                (< (nfix m) (nfix n))
                (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env))
                  (env-m (bvar-db-fix-env m min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval gobj (cons (bfr-unparam-env p env-n) var-env))
                    (glcp-generic-geval gobj (cons (bfr-unparam-env p env-m) var-env)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-gobj-vars-bounded-lemma
                         (gobj (gobj-to-param-space gobj p))))
           :in-theory (e/d (genv-unparam)
                           (bvar-db-fix-env-eval-gobj-vars-bounded-lemma))
           :do-not-induct t)))

(defthm bvar-db-fix-env-eval-gobj-vars-bounded-unparam-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (gobj-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval x (cons (bfr-unparam-env p env-n) var-env))
                    (glcp-generic-geval x (cons env var-env)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-gobj-vars-bounded-unparam
                         (gobj x) (m min)))
           :in-theory (disable bvar-db-fix-env-eval-gobj-vars-bounded-unparam)
           :expand ((BVAR-DB-FIX-ENV MIN MIN BVAR-DB P (BFR-PARAM-ENV P ENV)
                                     VAR-ENV))
           :do-not-induct t)))

(defthm bvar-db-fix-env-eval-gobj-vars-bounded-unparam-with-no-param
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (gobj-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db t env var-env)))
             (equal (glcp-generic-geval x (cons env-n var-env))
                    (glcp-generic-geval x (cons env var-env)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-gobj-vars-bounded-unparam-rw
                         (p t)))
           :expand ((bfr-vars-bounded min t))
           :in-theory (disable bvar-db-fix-env-eval-gobj-vars-bounded-unparam-rw)
           :do-not-induct t)))




(defthm bvar-db-env-ok-of-bvar-db-fix-env2-no-param
  (implies (and (bvar-db-orderedp t bvar-db)
                (<= (nfix n) (next-bvar$a bvar-db))
                (<= nn (nfix n))
                (<= (base-bvar$a bvar-db) (nfix n))
                (glcp-generic-bvar-db-env-ok bvar-db t min
                                             (cons bfr-env var-env)))
           (let ((bfr-env (bvar-db-fix-env n min
                                           bvar-db t bfr-env var-env)))
             (glcp-generic-bvar-db-env-ok bvar-db t nn (cons bfr-env var-env))))
  :hints (("Goal" :use ((:instance bvar-db-env-ok-of-bvar-db-fix-env2
                         (p t)))
           :in-theory (disable bvar-db-env-ok-of-bvar-db-fix-env2))))






;; What's really going to happen?

;; We're going to simulate the hyps under P=t.  This may add some variables to
;; the bvar-db.  We get some expression H for the hyps.  We translate the
;; bvar-db to the param space of H.  Then we simulate the conclusion in the
;; param space of H.  We get some expression C for the conclusion.  We try to
;; prove C.  If we prove it, we have shown there is no env that is consistent
;; with the bvar-db, satisfies (the self-parameterization of) H, and does not satisfy C.

;; Now assume we have a counterexample to the original hyp => concl.  We want
;; to construct an env from this that contradicts our proof.




;; (defund glcp-generic-interp-top-level-term
;;   (term alist pathcond clk config interp-st bvar-db state)
;;   (declare (xargs :guard (and (pseudo-termp term)
;;                               (natp clk)
;;                               (acl2::interp-defs-alistp obligs)
;;                               (glcp-config-p config)
;;                               (acl2::interp-defs-alistp (glcp-config->overrides config)))
;;                   :stobjs (bvar-db state)
;;                   :verify-guards nil))
;;   (b* (((glcp-er res-obj)
;;         (glcp-generic-interp-term
;;          term alist pathcond '(iff) clk config interp-st bvar-db state)))
;;     (glcp-generic-simplify-if-test res-obj pathcond clk config interp-st bvar-db
;;                                    state)))

(defthm glcp-generic-equiv-relp-of-iff
  (glcp-generic-equiv-relp 'iff)
  :hints (("goal" :expand ((glcp-generic-equiv-relp 'iff)))))






(defsection glcp-generic-interp-top-level-term
  (local (in-theory (enable glcp-generic-interp-top-level-term)))

  (defthm glcp-generic-interp-top-level-term-correct
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (bind-free
                     (if (and (consp bfr-env)
                              (eq (car bfr-env) 'bvar-db-fix-env))
                         `((env . (cons ,bfr-env ,(nth 6 bfr-env))))
                       `((free-var . free-var))))
                    (bfr-eval pathcond bfr-env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (not erp)
                    (acl2::interp-defs-alistp (is-obligs interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (is-obligs interp-st1))))
                    ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal p (glcp-config->param-bfr config))
                    (glcp-generic-bvar-db-env-ok
                     bvar-db1 p (next-bvar$a bvar-db1) env)
                    (equal bfr-env (car env))
                    (equal (w state0) (w state))
                    (pseudo-termp term)
                    (alistp alist)
                    (bdd-mode-or-p-true p (car env)))
               (iff (bfr-eval val bfr-env)
                    (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                 alist env)))))
    :hints(("Goal" :in-theory (e/d (glcp-interp-accs-ok)
                                   (glcp-generic-interp-correct-term
                                    (bfr-hyp-init$a)
                                    eval-of-bfr-hyp-init$a))
            :use ((:instance glcp-generic-interp-correct-term
                   (x term) (contexts '(iff)) (st state)
                   (config (glcp-config-update-term term config)))
                  (:instance eval-of-bfr-hyp-init$a
                   (hyp$a nil) (env (car env)))))))

  (defthm glcp-generic-interp-top-level-term-preserves-constraint
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (bind-free
                     (if (and (consp bfr-env)
                              (eq (car bfr-env) 'bvar-db-fix-env))
                         `((env . (cons ,bfr-env ,(nth 6 bfr-env))))
                       `((free-var . free-var))))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (acl2::interp-defs-alistp (is-obligs interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (is-obligs interp-st1))))
                    ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal p (glcp-config->param-bfr config))
                    (glcp-generic-bvar-db-env-ok
                     bvar-db1 p (next-bvar$a bvar-db1) env)
                    (equal bfr-env (car env))
                    (equal (w state0) (w state))
                    (pseudo-termp term)
                    (alistp alist)
                    (bdd-mode-or-p-true p (car env)))
               (bfr-hyp-eval (nth *is-constraint* interp-st1) bfr-env)))
    :hints(("Goal" :in-theory (e/d (glcp-interp-accs-ok)
                                   (glcp-generic-interp-correct-term))
            :use ((:instance glcp-generic-interp-correct-term
                   (x term) (contexts '(iff)) (st state)
                   (config (glcp-config-update-term term config)))))))


  (defthm w-state-preserved-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (equal (w state1) (w state))))

  (defthm interp-defs-alistp-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (acl2::interp-defs-alistp (is-obligs interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (pseudo-termp term)
                    (not erp))
               (acl2::interp-defs-alistp (nth *is-obligs*  interp-st1)))))

  (defthm state-p1-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (state-p1 state)
               (state-p1 state1))))

  (defthm bad-obligs-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (not (glcp-generic-geval-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses
                            (is-obligs interp-st)))))
                    (not erp))
               (not (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (nth *is-obligs* interp-st1))))))))

  (defthm forward-obligs-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (nth *is-obligs* interp-st1))))
                    (not erp))
               (glcp-generic-geval-ev-theoremp
                (conjoin-clauses
                 (acl2::interp-defs-alist-clauses
                  (nth *is-obligs* interp-st))))))
    :rule-classes :forward-chaining)

  (defthm bvar-db-extension-p-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (bvar-db-extension-p bvar-db1 bvar-db)))
  ;; (defthm bvar-db-env-ok-preserved-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (implies (and (<= bound (next-bvar$a bvar-db))
  ;;                   (equal p (glcp-config->param-bfr config)))
  ;;              (equal (glcp-generic-bvar-db-env-ok bvar-db1 p bound env)
  ;;                     (glcp-generic-bvar-db-env-ok bvar-db p bound env))))
  ;;   ;; :hints(("Goal" :in-theory (enable glcp-generic-interp-bvar-db-env-ok-preserved-test)))
  ;;   )

  ;; (defthm bvar-db-env-ok-next-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (implies (and (not (glcp-generic-bvar-db-env-ok
  ;;                         bvar-db p (next-bvar$a bvar-db) env))
  ;;                   (equal p (glcp-config->param-bfr config)))
  ;;              (not (glcp-generic-bvar-db-env-ok
  ;;                    bvar-db1 p (next-bvar$a bvar-db1) env))))
  ;;   ;; :hints(("Goal" :in-theory (enable glcp-generic-interp-bvar-db-preserved-special-test)))
  ;;   )

  ;; (defthm base-bvar-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (equal (base-bvar$a bvar-db1) (base-bvar$a bvar-db))))

  ;; (defthm next-bvar-incr-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (>= (next-bvar$a bvar-db1) (next-bvar$a bvar-db)))
  ;;   :rule-classes :linear)

  ;; (defthm get-bvar->term-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (implies (and (<= (base-bvar$a bvar-db) (nfix n))
  ;;                   (< (nfix n) (next-bvar$a bvar-db)))
  ;;              (equal (get-bvar->term$a n bvar-db1)
  ;;                     (get-bvar->term$a n bvar-db)))))

  ;; (defthm get-term->bvar-of-glcp-generic-interp-top-level
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
  ;;         (glcp-generic-interp-top-level-term
  ;;          term alist pathcond clk config interp-st bvar-db state)))
  ;;     (implies (get-term->bvar$a x bvar-db)
  ;;              (equal (get-term->bvar$a x bvar-db1)
  ;;                     (get-term->bvar$a x bvar-db)))))


  (defthm vars-bounded-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (<= (next-bvar$a bvar-db1) (nfix k))
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (equal p (glcp-config->param-bfr config))
                    (gobj-alist-vars-bounded k p alist))
               (and (pbfr-vars-bounded k p val)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st1))))))

  (defthm constraint-vars-bounded-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (<= (next-bvar$a bvar-db1) (nfix k))
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (equal p (glcp-config->param-bfr config))
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st)))
               (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st1)))))

  (defthm bfr-vars-bounded-of-glcp-generic-interp-top-level-no-param
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state)))
      (implies (and (<= (next-bvar$a bvar-db1) (nfix k))
                    (equal t (glcp-config->param-bfr config))
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (bvar-db-orderedp t bvar-db)
                    (gobj-alist-vars-bounded k t alist))
               (bfr-vars-bounded k val)))
    :hints (("Goal" :use ((:instance vars-bounded-of-glcp-generic-interp-top-level
                           (p t)))
             :in-theory (disable vars-bounded-of-glcp-generic-interp-top-level))))

  (defthm bvar-db-ordered-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state))
         (k (next-bvar$a bvar-db)))
      (implies (and (equal p (glcp-config->param-bfr config))
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded k p alist))
               (bvar-db-orderedp p bvar-db1))))


  (defthm fix-env-correct-of-glcp-generic-interp-top-level-no-param
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state))
         (bfr-env1 (bvar-db-fix-env (next-bvar$a bvar-db1)
                                    next-of-bvar-db
                                    bvar-db1 t bfr-env var-env)))
      (implies (and (equal t (glcp-config->param-bfr config))
                    (equal next-of-bvar-db (next-bvar$a bvar-db))
                    (gbc-db-vars-bounded
                     (next-bvar$a bvar-db) t (nth *is-constraint-db* interp-st))
                    (bvar-db-orderedp t bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) t alist)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db t (next-bvar$a bvar-db) (cons bfr-env var-env)))
               (glcp-generic-bvar-db-env-ok
                bvar-db1 t (next-bvar$a bvar-db1) (cons bfr-env1 var-env))))
    :hints(("Goal" :in-theory (disable glcp-generic-interp-top-level-term
                                       bfr-eval-consts bfr-eval-booleanp)
            :use ((:theorem (bfr-eval t env))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-eval-consts)))))

  (defthm fix-env-correct-of-glcp-generic-interp-top-level
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
          (glcp-generic-interp-top-level-term
           term alist pathcond clk config interp-st bvar-db state))
         (bfr-env1 (bvar-db-fix-env (next-bvar$a bvar-db1)
                                    next-of-bvar-db
                                    bvar-db1 p
                                    (bfr-param-env p bfr-env)
                                    var-env)))
      (implies (and (equal p (glcp-config->param-bfr config))
                    (equal next-of-bvar-db (next-bvar$a bvar-db))
                    (bfr-vars-bounded (next-bvar$a bvar-db) p)
                    (bfr-eval p bfr-env)
                    (bvar-db-orderedp p bvar-db)
                    (gbc-db-vars-bounded
                     (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db p (next-bvar$a bvar-db)
                     (cons (bfr-param-env p bfr-env) var-env)))
               (glcp-generic-bvar-db-env-ok
                bvar-db1 p (next-bvar$a bvar-db1) (cons bfr-env1 var-env))))
    :hints(("Goal" :in-theory (disable glcp-generic-interp-top-level-term)))))


(defthm glcp-generic-geval-alist-of-gobj-alist-to-param-space
  (implies (bdd-mode-or-p-true pathcond (car env))
           (equal (glcp-generic-geval-alist (gobj-alist-to-param-space alist pathcond) env)
                  (glcp-generic-geval-alist
                   alist (genv-unparam pathcond env))))
  :hints (("goal" :induct (gobj-alist-to-param-space alist pathcond)
           :in-theory (enable glcp-generic-geval-alist))))

(defthm glcp-generic-geval-alist-of-unparam-param-env
  (implies (bfr-eval p env)
           (equal (glcp-generic-geval-alist x (cons (bfr-unparam-env
                                                     p (bfr-param-env p env))
                                                    var-env))
                  (glcp-generic-geval-alist x (cons env var-env))))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))





(encapsulate nil
  (local (defthm bfr-lookup-to-param-space-with-unparam-env-rev
           (implies (and (syntaxp (not (and (consp env)
                                            (eq (car env) 'bfr-param-env))))
                         (bdd-mode-or-p-true p env))
                    (equal (bfr-lookup n (bfr-unparam-env p env))
                           (bfr-eval (bfr-to-param-space p (bfr-var n)) env)))))

  (local (defthm bfr-eval-to-param-space-with-unparam-env-rev
           (implies (and (syntaxp (not (and (consp env)
                                            (eq (car env) 'bfr-param-env))))
                         (bdd-mode-or-p-true p env))
                    (equal (bfr-eval x (bfr-unparam-env p env))
                           (bfr-eval (bfr-to-param-space p x) env)))))
  (local (in-theory (disable bfr-eval-to-param-space-with-unparam-env)))

  (defthm bvar-db-env-ok-of-unparam-param
    (implies (bfr-eval pathcond bfr-env)
             (equal (glcp-generic-bvar-db-env-ok
                     bvar-db p bound (cons (bfr-unparam-env pathcond (bfr-param-env pathcond bfr-env))
                                           var-env))
                    (glcp-generic-bvar-db-env-ok
                     bvar-db p bound (cons bfr-env var-env))))
    :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok
                             bvar-db p bound (cons bfr-env var-env))))
            (and stable-under-simplificationp
                 (if (eq (caar clause) 'not)
                     `(:expand (,(car (last clause)))
                     :use ((:instance glcp-generic-bvar-db-env-ok-necc
                            (env (cons bfr-env
                                       var-env))
                            (n (glcp-generic-bvar-db-env-ok-witness
                                bvar-db p bound (cons (bfr-unparam-env pathcond
                                                        (bfr-param-env pathcond bfr-env))
                                                      var-env)))))
                     :in-theory (disable glcp-generic-bvar-db-env-ok-necc))
                   `(:expand (,(car clause))
                     :use ((:instance glcp-generic-bvar-db-env-ok-necc
                            (env (cons (bfr-unparam-env pathcond
                                                        (bfr-param-env pathcond bfr-env))
                                       var-env))
                            (n (glcp-generic-bvar-db-env-ok-witness
                                bvar-db p bound (cons bfr-env var-env)))))
                     :in-theory (disable glcp-generic-bvar-db-env-ok-necc)))))))




(defsection parametrize-bvar-db
  (local (in-theory (enable parametrize-bvar-db parametrize-bvar-db-aux)))
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm get-bvar->term-of-parametrize-bvar-db-aux
    (implies (and (<= (base-bvar$a bvar-db1) (nfix m))
                  (< (nfix m) (+ (next-bvar$a bvar-db1)
                                 (- (next-bvar$a bvar-db) (nfix n)))))
             (equal (get-bvar->term$a m (parametrize-bvar-db-aux n p bvar-db bvar-db1))
                    (if (<= (next-bvar$a bvar-db1) (nfix m))
                        (gobj-to-param-space
                         (get-bvar->term$a (+ (- (nfix m) (next-bvar$a bvar-db1))
                                              (nfix n))
                                           bvar-db)
                         p)
                      (get-bvar->term$a m bvar-db1)))))

  (defthm base-bvar-of-parametrize-bvar-db-aux
    (equal (base-bvar$a (parametrize-bvar-db-aux n p bvar-db bvar-db1))
           (base-bvar$a bvar-db1)))

  (defthm next-bvar-of-parametrize-bvar-db-aux
    (equal (next-bvar$a (parametrize-bvar-db-aux n p bvar-db bvar-db1))
           (+ (nfix (- (next-bvar$a bvar-db) (nfix n))) (next-bvar$a bvar-db1))))


  (defthm normalize-parametrize-bvar-db
    (implies (syntaxp (not (equal bvar-db1 ''nil)))
             (equal (parametrize-bvar-db p bvar-db bvar-db1)
                    (parametrize-bvar-db p bvar-db nil))))

  (defthm base-bvar-of-parametrize-bvar-db
    (equal (base-bvar$a (parametrize-bvar-db p bvar-db bvar-db1))
           (base-bvar$a bvar-db)))

  (defthm next-bvar-of-parametrize-bvar-db
    (equal (next-bvar$a (parametrize-bvar-db p bvar-db bvar-db1))
           (next-bvar$a bvar-db)))

  (defthm get-bvar->term-of-parametrize-bvar-db
    (implies (and (<= (base-bvar$a bvar-db) (nfix n))
                  (< (nfix n) (next-bvar$a bvar-db)))
             (equal (get-bvar->term$a n (parametrize-bvar-db p bvar-db bvar-db1))
                    (gobj-to-param-space
                     (get-bvar->term$a n bvar-db) p))))

  (defthm bvar-db-orderedp-of-parametrize-bvar-db
    (implies (bvar-db-orderedp t bvar-db)
             (bvar-db-orderedp p (parametrize-bvar-db p bvar-db bvar-db1)))
    :hints (("goal" :expand ((bvar-db-orderedp p (parametrize-bvar-db p bvar-db nil)))
             :in-theory (disable parametrize-bvar-db))))

  (defthm glcp-generic-bvar-db-env-ok-of-parametrize-bvar-db
    (implies (bdd-mode-or-p-true p (car env))
             (equal (glcp-generic-bvar-db-env-ok
                     (parametrize-bvar-db p bvar-db bvar-db1)
                     p bound env)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db t bound
                     (cons (bfr-unparam-env p (car env)) (cdr env)))))
    :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok
                             bvar-db t bound
                             (cons (bfr-unparam-env p (car env)) (cdr env)))))
            (and stable-under-simplificationp
                 (let* ((lit (if (eq (caar clause) 'not)
                                 (car (last clause))
                               (car clause)))
                        (other (if (eq (caar clause) 'not)
                                   (cadar clause)
                                 (cadar (last clause))))
                        (witness (cons 'glcp-generic-bvar-db-env-ok-witness
                                       (cdr lit))))
                   `(:expand (,lit)
                     :in-theory (enable genv-unparam)
                     :use ((:instance glcp-generic-bvar-db-env-ok-necc
                            (n ,witness)
                            (p ,(third other))
                            (env ,(nth 4 other))))))))))



;; ;; bvar-db1 is the real bvar-db from the hyp, bvar-db is initially empty
;; (defund glcp-generic-interp-concl
;;   (term alist pathcond clk config interp-st bvar-db1 bvar-db state)
;;   (declare (xargs :guard (and (pseudo-termp term)
;;                               (natp clk)
;;                               (acl2::interp-defs-alistp obligs)
;;                               (glcp-config-p config)
;;                               (acl2::interp-defs-alistp (glcp-config->overrides config)))
;;                   :stobjs (bvar-db bvar-db1 state)
;;                   :verify-guards nil))
;;   (b* ((al (gobj-alist-to-param-space alist pathcond))
;;        (bvar-db (init-bvar-db (base-bvar bvar-db1) bvar-db))
;;        (bvar-db (parametrize-bvar-db pathcond bvar-db1 bvar-db))
;;        (config (glcp-config-update-param pathcond config))
;;        (pathcond1 (bfr-to-param-space pathcond pathcond)))
;;     (glcp-generic-interp-top-level-term
;;      term al pathcond1 clk config interp-st bvar-db state)))


(defsection glcp-generic-interp-concl
  (local (in-theory (enable glcp-generic-interp-concl)))
  (local (set-default-hints '('(:do-not-induct t))))

  (defthm glcp-generic-interp-concl-norm
    (implies (syntaxp (not (equal bvar-db ''nil)))
             (equal (glcp-generic-interp-concl
                     term alist pathcond clk config interp-st bvar-db1 bvar-db state)
                    (glcp-generic-interp-concl
                     term alist pathcond clk config interp-st bvar-db1 nil state))))


  (defthm glcp-generic-interp-concl-correct
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist path-cond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (bind-free
                     (if (and (consp bfr-env)
                              (eq (car bfr-env) 'bvar-db-fix-env))
                         `((env . (cons ,bfr-env ,(nth 6 bfr-env))))
                       `((free-var . free-var))))
                    (bfr-eval path-cond (bfr-unparam-env path-cond bfr-env))
                    (bfr-hyp-eval (is-constraint interp-st) (bfr-unparam-env path-cond bfr-env))
                    (not erp)
                    (acl2::interp-defs-alistp (is-obligs interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (is-obligs interp-st1))))
                    ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db2 path-cond (next-bvar$a bvar-db2)
                     env)
                    (consp env)
                    (equal (car env) bfr-env)
                    (equal (w state0) (w state))
                    (pseudo-termp term)
                    (alistp alist)
                    (bdd-mode-or-p-true path-cond (car env)))
               (iff (bfr-eval val bfr-env)
                    (glcp-generic-geval-ev
                     term (glcp-generic-geval-alist
                           alist
                           (cons (bfr-unparam-env path-cond (car env))
                                 (cdr env)))))))
    :hints(("Goal" :in-theory (e/d (genv-unparam)
                                   (eval-of-bfr-constr-init))
            :use ((:instance eval-of-bfr-constr-init
                   (env (car env))))
            :do-not-induct t))
    :otf-flg t)

  (defthm glcp-generic-interp-concl-constraint-preserved
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (bind-free
                     (if (and (consp bfr-env)
                              (eq (car bfr-env) 'bvar-db-fix-env))
                         `((env . (cons ,bfr-env ,(nth 6 bfr-env))))
                       `((free-var . free-var))))
                    (bfr-hyp-eval (is-constraint interp-st) (bfr-unparam-env pathcond bfr-env))
                    (acl2::interp-defs-alistp (is-obligs interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (is-obligs interp-st1))))
                    ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db2 pathcond (next-bvar$a bvar-db2)
                     env)
                    (consp env)
                    (equal (car env) bfr-env)
                    (equal (w state0) (w state))
                    (pseudo-termp term)
                    (alistp alist)
                    (bdd-mode-or-p-true pathcond (car env)))
               (bfr-hyp-eval (nth *is-constraint* interp-st1) bfr-env)))
    :hints(("Goal" :in-theory (e/d (genv-unparam)
                                   (eval-of-bfr-constr-init))
            :use ((:instance eval-of-bfr-constr-init
                   (env (car env))))
            :do-not-induct t))
    :otf-flg t)

  (defthm w-state-preserved-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (equal (w state1) (w state))))

  (defthm interp-defs-alistp-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (pseudo-termp term)
                    (not erp))
               (acl2::interp-defs-alistp (nth *is-obligs* interp-st1)))))

  (defthm state-p1-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (state-p1 state)
               (state-p1 state1))))

  (defthm bad-obligs-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (not (glcp-generic-geval-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st)))))
                    (not erp))
               (not (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st1))))))))

  (defthm forward-obligs-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st1))))
                    (not erp))
               (glcp-generic-geval-ev-theoremp
                (conjoin-clauses
                 (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st))))))
    :rule-classes :forward-chaining)

  (defthm bvar-db-env-ok-preserved-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (<= bound (next-bvar$a bvar-db1))
                    (bdd-mode-or-p-true pathcond (car env))
                    ;; (bfr-hyp-eval pathcond (car env))
                    (glcp-generic-bvar-db-env-ok bvar-db1 t bound
                                                 (cons (bfr-unparam-env pathcond (car env))
                                                       (cdr env))))
               (glcp-generic-bvar-db-env-ok bvar-db2 pathcond bound env))))

  (defthm bvar-db-env-ok-next-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (not (glcp-generic-bvar-db-env-ok
                          (parametrize-bvar-db pathcond bvar-db1 nil)
                          pathcond (next-bvar$a bvar-db1)
                          env))
                    (bdd-mode-or-p-true pathcond (car env)))
               (not (glcp-generic-bvar-db-env-ok
                     bvar-db2 pathcond (next-bvar$a bvar-db2) env)))))

  (defthm bvar-db-env-ok-next-of-glcp-generic-interp-concl-forward
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (glcp-generic-bvar-db-env-ok
                     bvar-db2 pathcond (next-bvar$a bvar-db2) env)
                    (bdd-mode-or-p-true pathcond (car env)))
               (glcp-generic-bvar-db-env-ok
                bvar-db1
                t (next-bvar$a bvar-db1)
                (cons (bfr-unparam-env pathcond (car env))
                      (cdr env)))))
    :rule-classes :forward-chaining)

  (defthm base-bvar-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (equal (base-bvar$a bvar-db2) (base-bvar$a bvar-db1))))

  (defthm next-bvar-incr-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (>= (next-bvar$a bvar-db2) (next-bvar$a bvar-db1)))
    :rule-classes :linear)

  (defthm get-bvar->term-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (<= (base-bvar$a bvar-db1) (nfix n))
                    (< (nfix n) (next-bvar$a bvar-db1)))
               (equal (get-bvar->term$a n bvar-db2)
                      (gobj-to-param-space (get-bvar->term$a n bvar-db1)
                                           pathcond)))))

  ;; (defthm get-term->bvar-of-glcp-generic-interp-concl
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
  ;;         (glcp-generic-interp-concl
  ;;          term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
  ;;     (implies (get-term->bvar$a x bvar-db)
  ;;              (equal (get-term->bvar$a x bvar-db1)
  ;;                     (get-term->bvar$a x bvar-db)))))


  (defthm vars-bounded-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (<= (next-bvar$a bvar-db2) (nfix k))
                    (bfr-vars-bounded k pathcond)
                    (bvar-db-orderedp t bvar-db1)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k t alist))
               (and (pbfr-vars-bounded k pathcond val)
                    (gbc-db-vars-bounded k pathcond (nth *is-constraint-db*
                                                         interp-st1)))))
    )

  (defthm bfr-constr-vars-bounded-of-bfr-constr-init
    (bfr-constr-vars-bounded k p (bfr-constr-init))
    :hints(("Goal" :in-theory (enable bfr-constr-vars-bounded))))

  (defthm bfr-constr-vars-bounded-of-bfr-constr-assume
    (implies (and (bfr-constr-vars-bounded k p x)
                  (pbfr-vars-bounded k p a))
             (bfr-constr-vars-bounded k p (mv-nth 1 (bfr-constr-assume a x))))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))


  (defthm constraint-vars-bounded-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state)))
      (implies (and (<= (next-bvar$a bvar-db2) (nfix k))
                    (bfr-vars-bounded k pathcond)
                    (bvar-db-orderedp t bvar-db1)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k t alist)
                    (bfr-constr-vars-bounded k t (nth *is-constraint* interp-st)))
               (bfr-constr-vars-bounded k pathcond (nth *is-constraint*
                                                        interp-st1)))))

  (defthm bvar-db-ordered-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist pathcond clk config interp-st bvar-db1 bvar-db state))
         (k (next-bvar$a bvar-db1)))
      (implies (and (bfr-vars-bounded k pathcond)
                    (bvar-db-orderedp t bvar-db1)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k t alist))
               (bvar-db-orderedp pathcond bvar-db2))))


  ;; (defthm fix-env-correct-of-glcp-generic-interp-concl-no-param
  ;;   (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
  ;;         (glcp-generic-interp-concl
  ;;          term alist pathcond clk config interp-st bvar-db1 bvar-db state))
  ;;        (bfr-env1 (bvar-db-fix-env (next-bvar$a bvar-db1)
  ;;                                   (next-bvar$a bvar-db)
  ;;                                   bvar-db1 t bfr-env var-env)))
  ;;     (implies (and (equal t (glcp-config->param-bfr config))
  ;;                   (bvar-db-orderedp t bvar-db)
  ;;                   (gobj-alist-vars-bounded (next-bvar$a bvar-db) t alist)
  ;;                   (glcp-generic-bvar-db-env-ok
  ;;                    bvar-db t (next-bvar$a bvar-db) (cons bfr-env var-env)))
  ;;              (glcp-generic-bvar-db-env-ok
  ;;               bvar-db1 t (next-bvar$a bvar-db1) (cons bfr-env1 var-env))))
  ;;   :hints(("Goal" :in-theory (disable glcp-generic-interp-concl
  ;;                                      bfr-eval-consts bfr-eval-booleanp)
  ;;           :use ((:theorem (bfr-eval t env))))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable bfr-eval-consts)))))

  (local (defthm bdd-mode-or-p-true-of-bfr-param-env
           (implies (bdd-mode-or-p-true p env)
                    (bdd-mode-or-p-true p (bfr-param-env q env)))
           :hints(("Goal" :in-theory (enable bdd-mode-or-p-true bfr-param-env)))))


  (defthm fix-env-correct-of-glcp-generic-interp-concl
    (b* (((mv ?val ?erp ?interp-st1 ?bvar-db2 ?state1)
          (glcp-generic-interp-concl
           term alist path-cond clk config interp-st bvar-db1 bvar-db state))
         (bfr-env1 (bvar-db-fix-env (next-bvar$a bvar-db2)
                                    (next-bvar$a bvar-db1)
                                    bvar-db2 path-cond
                                    (bfr-param-env path-cond bfr-env)
                                    var-env)))
      (implies (and (bfr-vars-bounded (next-bvar$a bvar-db1) path-cond)
                    (bfr-eval path-cond bfr-env)
                    (bfr-hyp-eval (nth *is-constraint* interp-st) bfr-env)
                    ;; (bfr-unparam-env path-cond bfr-env))
                    (bvar-db-orderedp t bvar-db1)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db1) t alist)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db1 t (next-bvar$a bvar-db1)
                     (cons bfr-env var-env))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db1) t (nth *is-constraint-db* interp-st)))
               (glcp-generic-bvar-db-env-ok
                bvar-db2 path-cond (next-bvar$a bvar-db2) (cons bfr-env1
                                                               var-env))))
    :otf-flg t
    :hints (("goal" :do-not-induct t
             :in-theory (disable ;;eval-of-bfr-constr-init
                                 bfr-constr-assume-correct)
             :use (;; (:instance eval-of-bfr-constr-init
                   ;;  (env bfr-env))
                   (:instance bfr-constr-assume-correct
                    (hyp (bfr-constr-init))
                    (x (bfr-to-param-space
                        path-cond (bfr-constr->bfr (is-constraint interp-st))))
                    (env (bfr-param-env path-cond bfr-env))))))
    ))











(defthm bvar-db-fix-env-eval-gobj-alist-vars-bounded-no-param
  (implies (and (gobj-alist-vars-bounded min t x)
                (<= (nfix n) (next-bvar$a bvar-db)))
           (let ((env-n (bvar-db-fix-env
                         n min bvar-db t env var-env)))
             (equal (glcp-generic-geval-alist x (cons env-n var-env))
                    (glcp-generic-geval-alist x (cons env var-env)))))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))


(defthm bvar-db-fix-env-eval-gobj-alist-vars-bounded-unparam-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (gobj-alist-vars-bounded min t x)
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval-alist x (cons (bfr-unparam-env p env-n) var-env))
                    (glcp-generic-geval-alist x (cons env var-env)))))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))


(defthm bvar-db-fix-env-eval-gobj-vars-bounded-param-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (gobj-vars-bounded min p gobj)
            (<= (nfix min) (nfix n))
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval gobj (cons env-n var-env))
                    (glcp-generic-geval gobj (cons (bfr-param-env p env) var-env)))))
  :hints (("goal" :use ((:instance bvar-db-fix-env-eval-gobj-vars-bounded-lemma
                         (m min)))
           :expand ((bvar-db-fix-env min min bvar-db p (bfr-param-env p env)
                                     var-env))
           :in-theory (disable bvar-db-fix-env-eval-gobj-vars-bounded-lemma))))

(defthm bvar-db-fix-env-eval-gobj-alist-vars-bounded-param-rw
  (implies (and ; (bvar-db-orderedp p bvar-db)
            (bfr-eval p env)
            (bfr-vars-bounded min p)
            (gobj-alist-vars-bounded min p x)
            (<= (nfix min) (nfix n))
            (<= (nfix n) (next-bvar$a bvar-db)))
           (let* ((env-n (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                          var-env)))
             (equal (glcp-generic-geval-alist x (cons env-n var-env))
                    (glcp-generic-geval-alist x (cons (bfr-param-env p env) var-env)))))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))



(defthm bvar-db-env-ok-of-init-bvar-db
  (glcp-generic-bvar-db-env-ok (init-bvar-db$a base bvar-db) p bound env)
  :hints(("Goal" :in-theory (enable glcp-generic-bvar-db-env-ok))))



;; (defund glcp-generic-interp-hyp/concl
;;   (hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)
;;   (declare (xargs :guard (and (pseudo-termp hyp)
;;                               (pseudo-termp concl)
;;                               (natp clk)
;;                               (acl2::interp-defs-alistp obligs)
;;                               (glcp-config-p config)
;;                               (acl2::interp-defs-alistp (glcp-config->overrides config)))
;;                   :stobjs (bvar-db bvar-db1 state)
;;                   :verify-guards nil))
;;   (b* ((bvar-db (init-bvar-db next-bvar bvar-db))
;;        (bvar-db1 (init-bvar-db next-bvar bvar-db1))
;;        (config (glcp-config-update-param t config))
;;        ((mv er obligs hyp-bfr bvar-db state)
;;         (glcp-generic-interp-top-level-term
;;          hyp alist t clk config interp-st bvar-db state))
;;        ((when er)
;;         (mv er obligs hyp-bfr nil bvar-db bvar-db1 state))
;;        ((when (not hyp-bfr))
;;         (mv "Hypothesis is not satisfiable"
;;             obligs hyp-bfr nil bvar-db bvar-db1 state))
;;        ((mv er obligs concl-bfr bvar-db1 state)
;;         (glcp-generic-interp-concl
;;          concl alist hyp-bfr clk config interp-st bvar-db bvar-db1 state)))
;;     (mv er obligs hyp-bfr concl-bfr bvar-db bvar-db1 state)))

(defund-nx glcp-generic-interp-hyp/concl-env
  (env hyp concl alist clk config interp-st next-bvar state)
  (b* ((bvar-db (init-bvar-db next-bvar nil))
       (bvar-db1 (init-bvar-db next-bvar nil))
       (config (glcp-config-update-param t config))
       ((mv  hyp-bfr ?er ?interp-st bvar-db1 state)
        (glcp-generic-interp-top-level-term
         hyp alist t clk config interp-st bvar-db1 state))
       (bfr-env1 (bvar-db-fix-env (next-bvar bvar-db1)
                                  next-bvar bvar-db1 t
                                  (car env) (cdr env)))
       ((unless (glcp-generic-geval-ev
                 hyp (glcp-generic-geval-alist alist env)))
        bfr-env1)
       ((mv ?concl-bfr ?er ?obligs bvar-db state)
        (glcp-generic-interp-concl
         concl alist hyp-bfr clk config interp-st bvar-db1 nil state)))
    (bvar-db-fix-env (next-bvar bvar-db)
                     (next-bvar bvar-db1)
                     bvar-db hyp-bfr
                     (bfr-param-env hyp-bfr bfr-env1)
                     (cdr env))))



(defsection glcp-generic-interp-hyp/concl
  (local (in-theory (enable glcp-generic-interp-hyp/concl
                            glcp-generic-interp-hyp/concl-env)))

  (defthm glcp-generic-interp-hyp/concl-norm
    (implies (syntaxp (not (and (equal bvar-db ''nil)
                                (equal bvar-db1 ''nil))))
             (equal (glcp-generic-interp-hyp/concl
                     hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)
                    (glcp-generic-interp-hyp/concl
                     hyp concl alist clk config interp-st next-bvar nil nil state))))

  (defthm glcp-generic-interp-hyp/concl-hyp
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (not erp)
               (Equal (bfr-eval hyp-bfr env)
                      (bfr-eval (mv-nth 0 (glcp-generic-interp-top-level-term
                                           hyp alist t clk (glcp-config-update-param t config)
                                           interp-st (init-bvar-db next-bvar bvar-db1) state))
                                env))))
    :hints(("Goal" :in-theory (enable glcp-vacuity-check-unsat-implies))))
    

  (local (defthm bdd-mode-or-p-true-of-bfr-unparam-env-rev-special
           (implies (bfr-eval p (bfr-unparam-env p env))
                    (bdd-mode-or-p-true p env))
           :hints(("Goal" :in-theory (enable bdd-mode-or-p-true bfr-unparam-env)))))

  (local (defthm bdd-mode-or-p-true-of-bfr-unparam-env-rev
           (implies (bfr-eval p (bfr-unparam-env q env))
                    (bdd-mode-or-p-true p env))
           :hints(("Goal" :in-theory (enable bdd-mode-or-p-true bfr-unparam-env)))))

  (local (defthm bdd-mode-or-p-true-of-bfr-unparam-env
           (implies (bdd-mode-or-p-true p env)
                    (bdd-mode-or-p-true p (bfr-unparam-env q env)))
           :hints(("Goal" :in-theory (enable bdd-mode-or-p-true bfr-unparam-env)))))


  (local (defmacro hq (arg) `(acl2::hq ,arg)))

  (defthm glcp-generic-interp-hyp/concl-correct
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (not erp)
                    (bfr-hyp-eval (nth *is-constraint* interp-st)
                                  (bfr-unparam-env hyp-bfr bfr-env))
                    (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (nth *is-obligs* interp-st1))))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (glcp-generic-bvar-db-env-ok
                     concl-bvar-db hyp-bfr (next-bvar$a concl-bvar-db) env)
                    (consp env)
                    (equal bfr-env (car env))
                    (equal (w state0) (w state))
                    (pseudo-termp hyp)
                    (pseudo-termp concl)
                    (alistp alist))
               ;; (and (iff (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
               ;;           (glcp-generic-geval-ev
               ;;            hyp
               ;;            (glcp-generic-geval-alist
               ;;             alist (cons (bfr-unparam-env hyp-bfr (car env))
               ;;                         (cdr env)))))
               (implies (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
                        (iff (bfr-eval concl-bfr bfr-env)
                             (glcp-generic-geval-ev
                              concl
                              (glcp-generic-geval-alist
                               alist (cons (bfr-unparam-env hyp-bfr (car env))
                                           (cdr env))))))))
    :hints(("Goal" :in-theory (e/d (genv-unparam))
            :do-not-induct t)
           (acl2::use-termhint
            ;; sync with definition of interp-hyp/concl in glcp-templates
            (b* ((bvar-db (init-bvar-db next-bvar bvar-db))
                 (bvar-db1 (init-bvar-db next-bvar bvar-db1))
                 (config (glcp-config-update-param t config))
                 ((mv hyp-bfr ?er interp-st bvar-db state)
                  (glcp-generic-interp-top-level-term
                   hyp alist t clk config interp-st bvar-db state))
                 ((mv er unsat)
                  (glcp-vacuity-check hyp-bfr config))
                 (concl (if unsat ''t concl))
                 (env (bfr-unparam-env hyp-bfr (car env))))
              `'(:use ((:instance bvar-db-env-ok-next-of-glcp-generic-interp-concl-forward
                        (term ,(hq CONCL)) (alist ,(hq ALIST))
                        (pathcond ,(hq hyp-bfr))
                        (clk ,(hq clk))
                        (config ,(hq config))
                        (interp-st ,(hq interp-st))
                        (bvar-db1 ,(hq bvar-db))
                        (bvar-db nil)
                        (state ,(hq state)))
                       (:instance glcp-vacuity-check-unsat-implies
                        (hyp-bfr ,(hq hyp-bfr))
                        (config ,(hq config))
                        (env ,(hq env)))))))))

  (defthm w-state-preserved-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (equal (w state1) (w state))))

  (defthm interp-defs-alistp-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (pseudo-termp hyp)
                    (pseudo-termp concl)
                    (not erp))
               (acl2::interp-defs-alistp (nth *is-obligs* interp-st1)))))

  (defthm state-p1-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (state-p1 state)
               (state-p1 state1))))

  (defthm bad-obligs-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (not (glcp-generic-geval-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st)))))
                    (not erp))
               (not (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st1))))))))

  (defthm forward-obligs-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st1))))
                    (not erp))
               (glcp-generic-geval-ev-theoremp
                (conjoin-clauses
                 (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st))))))
    :rule-classes :forward-chaining)

  ;; (defthm bvar-db-env-ok-preserved-of-glcp-generic-interp-hyp/concl
  ;;   (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
  ;;         (glcp-generic-interp-hyp/concl
  ;;          hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
  ;;     (implies (and (<= bound (next-bvar$a bvar-db))
  ;;                   (equal p (glcp-config->param-bfr config)))
  ;;              (equal (glcp-generic-bvar-db-env-ok bvar-db1 p bound env)
  ;;                     (glcp-generic-bvar-db-env-ok bvar-db p bound env)))))

  ;; (defthm bvar-db-env-ok-next-of-glcp-generic-interp-hyp/concl
  ;;   (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
  ;;         (glcp-generic-interp-hyp/concl
  ;;          hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
  ;;     (implies (and (not (glcp-generic-bvar-db-env-ok
  ;;                         bvar-db p (next-bvar$a bvar-db) env))
  ;;                   (equal p (glcp-config->param-bfr config)))
  ;;              (not (glcp-generic-bvar-db-env-ok
  ;;                    bvar-db1 p (next-bvar$a bvar-db1) env)))))

  (defthm base-bvar-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (and (equal (base-bvar$a hyp-bvar-db) (nfix next-bvar))
           (equal (base-bvar$a concl-bvar-db) (nfix next-bvar)))))

  (defthm next-bvar-incr-of-glcp-generic-interp-hyp/concl-hyp
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (>= (next-bvar$a hyp-bvar-db) (nfix next-bvar)))
    :rule-classes :linear)

  (defthm next-bvar-incr-of-glcp-generic-interp-hyp/concl-concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (>= (next-bvar$a concl-bvar-db) (nfix next-bvar)))
    :rule-classes :linear)

  (defthm get-bvar->term-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (<= (base-bvar$a hyp-bvar-db) (nfix n))
                    (< (nfix n) (next-bvar$a hyp-bvar-db))
                    (not erp))
               (equal (get-bvar->term$a n concl-bvar-db)
                      (gobj-to-param-space (get-bvar->term$a n hyp-bvar-db)
                                           hyp-bfr)))))

  ;; (defthm get-term->bvar-of-glcp-generic-interp-hyp/concl
  ;;   (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
  ;;         (glcp-generic-interp-hyp/concl
  ;;          hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
  ;;     (implies (get-term->bvar$a x bvar-db)
  ;;              (equal (get-term->bvar$a x bvar-db1)
  ;;                     (get-term->bvar$a x bvar-db)))))


  (defthm vars-bounded-of-glcp-generic-interp-hyp/concl-hyp
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (<= (next-bvar$a hyp-bvar-db) (nfix k))
                    (gobj-alist-vars-bounded k t alist)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (pbfr-vars-bounded k t hyp-bfr)))
    :hints (("goal" :use ((:instance bfr-eval-consts))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp))))

  (defthm vars-bounded-of-glcp-generic-interp-hyp/concl-concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (<= (next-bvar$a concl-bvar-db) (nfix k))
                    (gobj-alist-vars-bounded next-bvar t alist)
                    (gbc-db-vars-bounded next-bvar t (nth *is-constraint-db* interp-st)))
               (pbfr-vars-bounded k hyp-bfr concl-bfr)))
    :hints (("goal" :use ((:instance bfr-eval-consts))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp))))

  (defthm bfr-constr-vars-bounded-incr
    (implies (and (bfr-constr-vars-bounded k p x)
                  (<= (nfix k) (nfix m)))
             (bfr-constr-vars-bounded m p x))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm constraint-vars-bounded-of-glcp-generic-interp-hyp/concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (<= (next-bvar$a concl-bvar-db) (nfix k))
                    (not erp)
                    (gobj-alist-vars-bounded next-bvar t alist)
                    (bfr-constr-vars-bounded next-bvar t (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded next-bvar t (nth *is-constraint-db* interp-st)))
               (bfr-constr-vars-bounded k hyp-bfr (nth *is-constraint* interp-st1))))
    :hints (("goal" :use ((:instance bfr-eval-consts))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp))))

  (defthm bvar-db-ordered-of-glcp-generic-interp-hyp/concl-hyp
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (gobj-alist-vars-bounded next-bvar t alist)
                    (gbc-db-vars-bounded next-bvar t (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp t hyp-bvar-db)))
    :hints (("goal" :use ((:instance bfr-eval-consts))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp))))

  (defthm bvar-db-ordered-of-glcp-generic-interp-hyp/concl-concl
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state)))
      (implies (and (gobj-alist-vars-bounded next-bvar t alist)
                    (gbc-db-vars-bounded next-bvar t (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp hyp-bfr concl-bvar-db)))
    :hints (("goal" :use ((:instance bfr-eval-consts))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp))))

  (local (defthm glcp-generic-interp-top-level-term-correct-bind
           (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
                 (glcp-generic-interp-top-level-term
                  term alist pathcond clk config interp-st bvar-db state)))
             (implies (and (bind-free
                            `((env . (cons ,bfr-env (cdr env)))))
                           (bfr-eval pathcond bfr-env)
                           (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                           (not erp)
                           (acl2::interp-defs-alistp (is-obligs interp-st))
                           (acl2::interp-defs-alistp (glcp-config->overrides config))
                           (glcp-generic-geval-ev-theoremp
                            (conjoin-clauses
                             (acl2::interp-defs-alist-clauses
                              (is-obligs interp-st1))))
                           ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                           (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                           (equal p (glcp-config->param-bfr config))
                           (glcp-generic-bvar-db-env-ok
                            bvar-db1 p (next-bvar$a bvar-db1) env)
                           (equal bfr-env (car env))
                           (equal (w state0) (w state))
                           (pseudo-termp term)
                           (alistp alist)
                           (bdd-mode-or-p-true p (car env)))
                      (iff (bfr-eval val bfr-env)
                           (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                        alist env)))))
           :hints(("Goal" :in-theory (e/d ()
                                          (glcp-generic-interp-top-level-term))
                   :use ((:instance glcp-generic-interp-correct-term
                          (x term) (contexts '(iff))))))))

  (local (defthm glcp-generic-interp-top-level-term-preserves-constraint-bind
           (b* (((mv ?val ?erp ?interp-st1 ?bvar-db1 ?state1)
                 (glcp-generic-interp-top-level-term
                  term alist pathcond clk config interp-st bvar-db state)))
             (implies (and (bind-free
                            `((env . (cons ,bfr-env (cdr env)))))
                           (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                           (acl2::interp-defs-alistp (is-obligs interp-st))
                           (acl2::interp-defs-alistp (glcp-config->overrides config))
                           (glcp-generic-geval-ev-theoremp
                            (conjoin-clauses
                             (acl2::interp-defs-alist-clauses
                              (is-obligs interp-st1))))
                           ;; (glcp-generic-geval-ev-meta-extract-global-facts)
                           (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                           (equal p (glcp-config->param-bfr config))
                           (glcp-generic-bvar-db-env-ok
                            bvar-db1 p (next-bvar$a bvar-db1) env)
                           (equal bfr-env (car env))
                           (equal (w state0) (w state))
                           (pseudo-termp term)
                           (alistp alist)
                           (bdd-mode-or-p-true p (car env)))
                      (bfr-hyp-eval (nth *is-constraint* interp-st1) bfr-env)))
           :hints (("goal" :use
                    glcp-generic-interp-top-level-term-preserves-constraint
                    :in-theory (disable glcp-generic-interp-top-level-term-preserves-constraint)))))

  (defthm glcp-generic-interp-hyp/concl-env-correct
    (b* (((mv ?hyp-bfr ?concl-bfr ?concl-bvar-db ?erp ?interp-st1 ?hyp-bvar-db ?state1)
          (glcp-generic-interp-hyp/concl
           hyp concl alist clk config interp-st next-bvar bvar-db bvar-db1 state))
         (fixed-env
          (glcp-generic-interp-hyp/concl-env
           env hyp concl alist clk config interp-st next-bvar state)))
      (implies (and (not erp)
                    (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp (glcp-config->overrides config))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses
                      (acl2::interp-defs-alist-clauses
                       (nth *is-obligs* interp-st1))))
                    (bfr-hyp-eval (nth *is-constraint* interp-st) (car env))
                    (bfr-constr-vars-bounded next-bvar t (nth *is-constraint* interp-st))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (pseudo-termp hyp)
                    (pseudo-termp concl)
                    (alistp alist)
                    (consp env)
                    (natp next-bvar)
                    (gobj-alist-vars-bounded next-bvar t alist)
                    (gbc-db-vars-bounded next-bvar t (nth *is-constraint-db* interp-st))
                    (glcp-generic-geval-ev
                     hyp (glcp-generic-geval-alist alist env))
                    (not (glcp-generic-geval-ev
                          concl (glcp-generic-geval-alist alist env))))
               (and (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr fixed-env))
                    (not (bfr-eval concl-bfr fixed-env))
                    (bfr-hyp-eval (nth *is-constraint* interp-st1) fixed-env) )))
    :hints (("goal" :use ((:instance bfr-eval-consts)
                          (:instance bfr-eval-consts (env (car env))))
             :in-theory (disable bfr-eval-consts bfr-eval-booleanp)
             :do-not-induct t)
            (acl2::use-termhint
            ;; sync with definition of interp-hyp/concl in glcp-templates
            (b* ((bvar-db (init-bvar-db next-bvar bvar-db))
                 (bvar-db1 (init-bvar-db next-bvar bvar-db1))
                 (config (glcp-config-update-param t config))
                 ((mv hyp-bfr ?er interp-st bvar-db state)
                  (glcp-generic-interp-top-level-term
                   hyp alist t clk config interp-st bvar-db state))
                 ((mv er unsat)
                  (glcp-vacuity-check hyp-bfr config))
                 (concl (if unsat ''t concl))
                 ;; (fixed-env (glcp-generic-interp-hyp/concl-env
                 ;;             env hyp concl alist clk config interp-st next-bvar state))
                 ;; (?hyp-env (bfr-unparam-env hyp-bfr (car env)))
                 (hyp-env (bvar-db-fix-env (next-bvar bvar-db)
                                  next-bvar bvar-db t
                                  (car env) (cdr env)))
                 )
              `'(:use ((:instance glcp-vacuity-check-unsat-implies
                        (hyp-bfr ,(hq hyp-bfr))
                        (config ,(hq config))
                        (env ,(hq hyp-env))))))))))
