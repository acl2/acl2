; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "centaur/sv/svex/symbolic" :dir :system)
(include-book "arith-base")
(include-book "glcp-config")
(include-book "def-gl-rewrite")
(include-book "syntax-bind")
(include-book "gl-object")
(include-book "centaur/misc/starlogic" :dir :system)

#!sv
(fgl::def-gl-rewrite svexlist-eval-for-fgl
  (equal (svexlist-eval-for-symbolic x env symbolic-params)
         (b* ((orig-x x)
              (env (make-fast-alist (svex-env-fix env)))
              (svars (svexlist-vars-for-symbolic-eval x env symbolic-params))
              (x (svexlist-x-out-unused-vars x svars
                                             (symbolic-params-x-out-cond symbolic-params)))
              (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
              (boolmasks (make-fast-alist
                          (hons-copy
                           (ec-call
                            (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
              ((unless (svex-env-check-boolmasks boolmasks env))
               (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%")))
                 (fgl::abort-rewrite (svexlist-eval-for-symbolic orig-x env symbolic-params))))

              ;; (?ign (cw "Boolmasks: ~x0~%" boolmasks))
              ;; (?ign (bitops::sneaky-push 'boolmasks boolmasks))
              ;; (?ign (bitops::sneaky-push 'vars vars))
              ;; (?ign (bitops::sneaky-push 'x x))
              ((mv err a4vecs) (time$ (svexlist->a4vecs-for-varlist x svars boolmasks)
                                      :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
              ((when err)
               (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                 (fgl::abort-rewrite (svexlist-eval-for-symbolic orig-x env symbolic-params))))
              ((mv ?err aig-env)
               ;; ignore the error; it can't exist if the above doesn't
               (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env)
                      :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
              (?ign (fast-alist-free env))
              (aig-env (make-fast-alist aig-env))
              (ans (a4veclist-eval a4vecs aig-env)))
           (fast-alist-free aig-env)
           ans))
  :hints (("Goal" :use svexlist-eval-for-symbolic-redef
           :in-theory (e/d (svexlist-eval-gl)
                           (svexlist-eval-gl-is-svexlist-eval)))))

(add-gl-rewrite sv::a4veclist-eval-redef)
(add-gl-rewrite sv::svex-alist-eval-gl-rewrite)
(add-gl-rewrite sv::svex-eval-gl-rewrite)

#!sv
(fgl::def-gl-rewrite svexlist/env-list-eval-fgl
  (equal (svexlist/env-list-eval-gl x envs symbolic-params)
         (b* ((envs (take (len x) envs))
              (x (svexlistlist-fix x))
              (svexes (append-lists x))
              (svars (svexlist/env-list-vars-for-symbolic-eval svexes envs symbolic-params))
              (svexes (svexlist-x-out-unused-vars svexes svars
                                                  (symbolic-params-x-out-cond symbolic-params)))
              (svexes (maybe-svexlist-rewrite-fixpoint svexes (cdr (assoc :simplify symbolic-params))))
              (boolmasks (make-fast-alist
                          (hons-copy
                           (ec-call
                            (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
              ((unless (svex-envlist-check-boolmasks boolmasks envs))
               (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%")))
                 (fgl::abort-rewrite (svexlist/env-list-eval-gl x envs symbolic-params))))
              ((mv err a4vecs) (time$ (svexlist->a4vecs-for-varlist svexes svars boolmasks)
                                      :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
              ((when err)
               (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                 (fgl::abort-rewrite (svexlist/env-list-eval-gl x envs symbolic-params))))
              (a4veclist-list (extract-lists x a4vecs)))
           (a4veclist/svex-env-list-eval a4veclist-list
                                         envs
                                         svexes
                                         svars
                                         boolmasks)))
  :hints (("goal" :in-theory (e/d (svexlist/env-list-eval-gl)
                                  (svexlist/env-list-eval-gl-correct)))))

(add-gl-rewrite sv::svexlist/env-list-eval-for-symbolic-redef)




;; (defun svex-env-fix-debug (x)
;;   (IF (ATOM X)
;;       NIL
;;       (LET ((REST (SVEX-ENV-FIX-debug (CDR X))))
;;            (IF (AND (CONSP (CAR X))
;;                     (SV::SVAR-P (CAAR X)))
;;                (LET ((FTY::FIRST-KEY (CAAR X))
;;                      (FTY::FIRST-VAL (SV::4VEC-FIX (CDAR X))))
;;                     (CONS (CONS FTY::FIRST-KEY FTY::FIRST-VAL)
;;                           REST))
;;                REST))))




;; (def-gl-rewrite svex-env-fix-use-debug
;;   (equal (sv::svex-env-fix x)
;;          (b* ((res (svex-env-fix-debug x))
;;               (?ign (syntax-bind foo (cw "svex-env-fix res: ~x0~%" res))))
;;            res))
;;   :hints(("Goal" :in-theory (enable sv::svex-env-fix))))

;; (encapsulate nil
;;   (local (in-theory (disable (tau-system) member set::empty-set-unique)))
;;   (install-gl-primitives patched-primitives))
  

;; (defun 4vec-fix-debug (x)
;;   (IF (CONSP X)
;;       (SV::4VEC (IFIX (CAR X)) (IFIX (CDR X)))
;;       (IF (INTEGERP X) X (SV::4VEC-X))))

;; (def-gl-rewrite 4vec-fix-use-debug
;;   (equal (sv::4vec-fix x)
;;          (b* ((res (4vec-fix-debug x))
;;               (?ign (syntax-bind foo (cw "4vec-fix res: ~x0~%" res))))
;;            res))
;;   :hints(("Goal" :in-theory (enable sv::4vec-fix))))
           


(table gl-fn-modes 'sv::4vec-fix$inline
       (make-gl-function-mode :dont-expand-def t))

(table gl-fn-modes 'sv::4vec
       (make-gl-function-mode :dont-expand-def t))

(table gl-fn-modes 'sv::4vec-p
       (make-gl-function-mode :dont-expand-def t))

(table gl-fn-modes 'sv::4vec->upper$inline
       (make-gl-function-mode :dont-expand-def t))

(table gl-fn-modes 'sv::4vec->lower$inline
       (make-gl-function-mode :dont-expand-def t))

(def-gl-rewrite 4vec-p-when-integerp
  (implies (and (syntaxp (gl-object-case x :g-integer))
                (integerp x))
           (sv::4vec-p x))
  :hints(("Goal" :in-theory (enable sv::4vec-p))))

(def-gl-rewrite 4vec-fix-resolve
  #!sv
  (equal (4vec-fix x)
         (b* (((when (and (fgl::syntax-bind check-integerp (fgl::gl-object-case x '(:g-concrete :g-integer)))
                          (integerp x)))
               x)
              ((when (and (fgl::syntax-bind check-consp (fgl::gl-object-case x '(:g-concrete :g-cons)))
                          (consp x)))
               (4vec (fgl::int (car x)) (fgl::int (cdr x))))
              (4vecp (and (4vec-p x) t))
              ((when (and (fgl::syntax-bind 4vecpc (equal 4vecp t)) 4vecp))
               x))
           (4vec (4vec->upper x) (4vec->lower x))))
  :hints ((and stable-under-simplificationp '(:in-theory (enable sv::4vec-fix sv::4vec->upper sv::4vec->lower)))))

(add-gl-rewrite sv::4vec-p-of-4vec)

(def-gl-rewrite integerp-of-4vec->upper
  #!sv (integerp (sv::4vec->upper x)))
(add-gl-rewrite sv::4vec->upper-of-4vec-fix)
(add-gl-rewrite sv::4vec->upper-of-4vec)

(def-gl-rewrite integerp-of-4vec->lower
  #!sv (integerp (sv::4vec->lower x)))
(add-gl-rewrite sv::4vec->lower-of-4vec-fix)
(add-gl-rewrite sv::4vec->lower-of-4vec)

(def-gl-rewrite 4vec->upper-of-integer
  #!sv
  (implies (integerp x)

           (equal (4vec->upper x) x))
  :hints(("Goal" :in-theory (enable sv::4vec->upper))))

(def-gl-rewrite 4vec->lower-of-integer
  #!sv
  (implies (integerp x)
           (equal (4vec->lower x) x))
  :hints(("Goal" :in-theory (enable sv::4vec->lower))))

(def-gl-rewrite 4vec->upper-of-cons
  #!sv
  (implies (consp x)
           (equal (4vec->upper x) (fgl::int (car x))))
  :hints(("Goal" :in-theory (enable sv::4vec->upper))))

(def-gl-rewrite 4vec->lower-of-cons
  #!sv
  (implies (consp x)
           (equal (4vec->lower x) (fgl::int (cdr x))))
  :hints(("Goal" :in-theory (enable sv::4vec->lower))))

(def-gl-rewrite equal-of-4vec
  #!sv (equal (equal (4vec upper lower) x)
              (and (4vec-p x)
                   (equal (4vec->upper x) (fgl::int upper))
                   (equal (4vec->lower x) (fgl::int lower)))))

(def-gl-rewrite integerp-of-4vec
  (equal (integerp (sv::4vec x y))
         (equal (int x) (int y)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-gl-rewrite int-of-4vec
  (equal (int (sv::4vec x y))
         (b* ((x (int x)))
           (if (equal x (int y)) x 0)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-gl-rewrite intcar-of-4vec
  (equal (intcar (sv::4vec x y))
         (and (equal (int x) (int y)) (intcar x)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-gl-rewrite intcdr-of-4vec
  (equal (intcdr (sv::4vec x y))
         (if (equal (int x) (int y)) (intcdr x) 0))
  :hints(("Goal" :in-theory (enable sv::4vec))))



(defmacro svdecomp-hints (&key hyp
                               g-bindings
                               enable
                               rewrite-limit)
  (declare (ignorable hyp g-bindings))
  `'(:computed-hint-replacement
     ((if stable-under-simplificationp
          (let ((state ,(if rewrite-limit
                            `(f-put-global 'sv::svdecomp-rewrite-limit ,rewrite-limit state)
                          'state)))
            (value '(:in-theory (acl2::e/d**
                                 #!sv
                                 (svdecomp-equal-svex-alist-evals-meta
                                  svdecomp-equal-svexlist-evals-meta
                                  svdecomp-equal-svex-evals-meta)))))
        (value nil))
      (and stable-under-simplificationp
           '(:in-theory (acl2::e/d**
                         #!sv ((:ruleset svtv-execs)
                               (:ruleset svtv-autoins)
                               (:ruleset svtv-autohyps)
                               (:ruleset svtv-alist-autoins)
                               (:ruleset svtv-alist-autohyps)
                               ,@fgl::enable))))
      (if stable-under-simplificationp
          (value '(:clause-processor
                   (gl-interp-cp clause
                                 (default-glcp-config)
                                 interp-st state)))
        (value nil)))
     :in-theory (acl2::e/d**
                 #!sv 
                 (svtv-run
                  (:ruleset svtv-execs)
                  (:ruleset svtv-autoins)
                  (:ruleset svtv-autohyps)
                  (:ruleset svtv-alist-autoins)
                  (:ruleset svtv-alist-autohyps)
                  assoc-in-svex-alist-eval
                  hons-assoc-in-svex-alist-eval
                  alistp-of-svex-alist-eval
                  assoc-of-append
                  acl2::hons-assoc-equal-append
                  assoc-of-acons
                  hons-assoc-equal-of-acons
                  assoc-of-nil
                  hons-assoc-equal-of-nil
                  alistp-of-acons
                  car-cons
                  cdr-cons
                  return-type-of-svex-alist-eval-for-symbolic
                  svexlist-eval-for-symbolic
                  fal-extract-of-svex-alist-eval
                  ;; fal-extract-open-cons
                  ;; fal-extract-done
                  ;; cons-onto-svex-alist-eval
                  ;; cons-onto-svex-alist-eval-append
                  ;; cons-svex-evals-into-svex-alist-eval

                  ;; Note: Need all functions used in processing the svtv->outexprs
                  ;; into the evaluated svex alists here
                  (hons-assoc-equal)
                  (svex-alist-fix)
                  (car) (cdr)
                  (svar-p)
                  (svex-p)
                  (svtv->outexprs)
                  (svarlist-fix)
                  (mergesort)
                  (difference)
                  (alistp)
                  (svex-alist-keys)
                  (append)
                  (consp)
                  (assoc)
                  (acl2::fal-extract)
                  svex-alist-eval-svex-env-equiv-congruence-on-env
                  svexlist-eval-svex-env-equiv-congruence-on-env
                  svex-eval-svex-env-equiv-congruence-on-env
                  svex-env-fix-under-svex-env-equiv
                  ,@fgl::enable))))
