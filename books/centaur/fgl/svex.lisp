; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "config")
(include-book "def-fgl-rewrite")
(include-book "syntax-bind")
(include-book "fgl-object")
(include-book "checks")
(include-book "ctrex-utils")
(include-book "centaur/misc/starlogic" :dir :system)

#!sv
(fgl::def-fgl-rewrite svexlist-eval-for-fgl
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
               (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                    (?foo (break$)))
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
              (ans ;; (fgl::fgl-progn (fgl::syntax-interp
                   ;;                  (cw "Aig-env: ~x0~%" aig-env))
                   ;;                 (fgl::syntax-interp
                   ;;                  (fgl::interp-st-put-user-scratch
                   ;;                   :aig-envs
                   ;;                   (cons aig-env (cdr (hons-get :aig-envs
                   ;;                                                (fgl::interp-st->user-scratch 'interp-st))))
                   ;;                   'interp-st))
                                   (a4veclist-eval a4vecs aig-env)))
           (fast-alist-free aig-env)
           ans))
  :hints (("Goal" :use svexlist-eval-for-symbolic-redef
           :in-theory (e/d (svexlist-eval-gl)
                           (svexlist-eval-gl-is-svexlist-eval)))))

#!sv
(fgl::def-fgl-rewrite svex-env-check-boolmasks-fgl
  (equal (svex-env-check-boolmasks boolmasks env)
         (b* (((when (atom boolmasks)) t)
              ((unless (svar-p (caar boolmasks)))
               (svex-env-check-boolmasks (cdr boolmasks) env))
              ((cons var mask) (car boolmasks))
              (val (svex-env-lookup var env))
              (ok (4vec-boolmaskp val mask))
              (?ign (and (not ok)
                         (b* ((?ign2 (cw "not 4vec-boolmaskp: ~x0~%" var)))
                           (break$)))))
           (and (svex-env-check-boolmasks (cdr boolmasks) env)
                ok)))
  :hints(("Goal" :in-theory (enable svex-env-check-boolmasks))))

(add-fgl-rewrite sv::a4veclist-eval-redef)
(add-fgl-rewrite sv::svex-alist-eval-gl-rewrite)
(add-fgl-rewrite sv::svex-eval-gl-rewrite)

#!sv
(fgl::def-fgl-rewrite svexlist/env-list-eval-fgl
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

(add-fgl-rewrite sv::svexlist/env-list-eval-for-symbolic-redef)




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




;; (def-fgl-rewrite svex-env-fix-use-debug
;;   (equal (sv::svex-env-fix x)
;;          (b* ((res (svex-env-fix-debug x))
;;               (?ign (syntax-bind foo (cw "svex-env-fix res: ~x0~%" res))))
;;            res))
;;   :hints(("Goal" :in-theory (enable sv::svex-env-fix))))

;; (encapsulate nil
;;   (local (in-theory (disable (tau-system) member set::empty-set-unique)))
;;   (install-fgl-metafns patched-primitives))
  

;; (defun 4vec-fix-debug (x)
;;   (IF (CONSP X)
;;       (SV::4VEC (IFIX (CAR X)) (IFIX (CDR X)))
;;       (IF (INTEGERP X) X (SV::4VEC-X))))

;; (def-fgl-rewrite 4vec-fix-use-debug
;;   (equal (sv::4vec-fix x)
;;          (b* ((res (4vec-fix-debug x))
;;               (?ign (syntax-bind foo (cw "4vec-fix res: ~x0~%" res))))
;;            res))
;;   :hints(("Goal" :in-theory (enable sv::4vec-fix))))
           


(disable-definition sv::4vec-fix$inline)

(disable-definition sv::4vec)

(disable-definition sv::4vec-p)

(disable-definition sv::4vec->upper$inline)

(disable-definition sv::4vec->lower$inline)

(def-fgl-rewrite 4vec-p-when-integerp
  (implies (and (syntaxp (fgl-object-case x :g-integer))
                (integerp x))
           (sv::4vec-p x))
  :hints(("Goal" :in-theory (enable sv::4vec-p))))

(def-fgl-rewrite 4vec-fix-resolve
  #!sv
  (equal (4vec-fix x)
         (b* (((when (fgl::check-integerp xintp x))
               x)
              ((when (fgl::check-consp xconsp x))
               (4vec (fgl::int (car x)) (fgl::int (cdr x))))
              (4vecp (and (4vec-p x) t))
              ((when (and (fgl::syntax-bind 4vecpc (equal 4vecp t)) 4vecp))
               x))
           (4vec (4vec->upper x) (4vec->lower x))))
  :hints ((and stable-under-simplificationp '(:in-theory (enable sv::4vec-fix sv::4vec->upper sv::4vec->lower)))))

(add-fgl-rewrite sv::4vec-p-of-4vec)

(def-fgl-rewrite integerp-of-4vec->upper
  #!sv (integerp (sv::4vec->upper x)))
(add-fgl-rewrite sv::4vec->upper-of-4vec-fix)
(add-fgl-rewrite sv::4vec->upper-of-4vec)

(def-fgl-rewrite integerp-of-4vec->lower
  #!sv (integerp (sv::4vec->lower x)))
(add-fgl-rewrite sv::4vec->lower-of-4vec-fix)
(add-fgl-rewrite sv::4vec->lower-of-4vec)

(def-fgl-rewrite 4vec->upper-of-integer
  #!sv
  (implies (integerp x)

           (equal (4vec->upper x) x))
  :hints(("Goal" :in-theory (enable sv::4vec->upper))))

(def-fgl-rewrite 4vec->lower-of-integer
  #!sv
  (implies (integerp x)
           (equal (4vec->lower x) x))
  :hints(("Goal" :in-theory (enable sv::4vec->lower))))

(def-fgl-rewrite 4vec->upper-of-cons
  #!sv
  (implies (fgl::check-consp xconsp x)
           (equal (4vec->upper x) (fgl::int (car x))))
  :hints(("Goal" :in-theory (enable sv::4vec->upper))))

(def-fgl-rewrite 4vec->lower-of-cons
  #!sv
  (implies (fgl::check-consp xconsp x)
           (equal (4vec->lower x) (fgl::int (cdr x))))
  :hints(("Goal" :in-theory (enable sv::4vec->lower))))

(def-fgl-rewrite equal-of-4vec
  #!sv (equal (equal (4vec upper lower) x)
              (and (4vec-p x)
                   (equal (4vec->upper x) (fgl::int upper))
                   (equal (4vec->lower x) (fgl::int lower)))))

(def-fgl-rewrite integerp-of-4vec
  (equal (integerp (sv::4vec x y))
         (equal (int x) (int y)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-fgl-rewrite int-of-4vec
  (equal (int (sv::4vec x y))
         (b* ((x (int x)))
           (if (equal x (int y)) x 0)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-fgl-rewrite intcar-of-4vec
  (equal (intcar (sv::4vec x y))
         (and (equal (int x) (int y)) (intcar x)))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-fgl-rewrite intcdr-of-4vec
  (equal (intcdr (sv::4vec x y))
         (if (equal (int x) (int y)) (intcdr x) 0))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(def-fgl-branch-merge if-merge-4vec
  (implies (sv::4vec-p x)
           (equal (if test (sv::4vec upper lower) x)
                  (sv::4vec (if test upper (sv::4vec->upper x))
                            (if test lower (sv::4vec->lower x))))))


(enable-split-ifs sv::4vec->upper$inline)
(enable-split-ifs sv::4vec->lower$inline)

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
                   (fgl-interp-cp clause
                                 (default-fgl-config)
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



;; (fgl::def-fgl-rewrite 4vec-boolmaskp-redef
;;   (equal (sv::4vec-boolmaskp x mask)
;;          (b* (((sv::4vec x))
;;               (xor (logxor x.upper x.lower))
;;               (and (logand mask xor))
;;               (?ignore (fgl::syntax-bind check
;;                                     (if (equal and 0)
;;                                         'ok
;;                                       (let ((?x (cw "4vec-boolmaskp not const 0~%")))
;;                                         (break$))))))
;;            (eql 0 and)))
;;   :hints(("Goal" :in-theory (enable sv::4vec-boolmaskp))))

(fgl::def-fgl-rewrite <-of-4vec
  (equal (< (sv::4vec a b) y)
         (< (b* ((a (int a))
                 (b (int b))
                 ;; (c (break$))
                 )
              (if (equal a b) a 0))
            y))
  :hints(("Goal" :in-theory (enable sv::4vec))))

(fgl::def-fgl-rewrite >-of-4vec
  (equal (> (sv::4vec a b) y)
         (> (b* ((a (int a))
                 (b (int b))
                 ;; (c (break$))
                 )
              (if (equal a b) a 0))
            y))
  :hints(("Goal" :in-theory (enable sv::4vec))))


(fgl::def-ctrex-rule 4vec-elim
  :match ((upper (sv::4vec->upper x))
          (lower (sv::4vec->lower x)))
  :match-conds ((upper-match upper)
                (lower-match lower))
  :assign (let ((upper (if upper-match upper (sv::4vec->upper x)))
                (lower (if lower-match lower (sv::4vec->lower x))))
            (sv::4vec upper lower))
  :assigned-var x
  :ruletype :elim)


(fgl::def-ctrex-rule svex-env-lookup-ctrex-rule
  :match ((val (sv::svex-env-lookup k x)))
  :assign (hons-acons k val x)
  :assigned-var x
  :ruletype :property)
