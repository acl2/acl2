; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "argmasks")
(include-book "rewrite-rules")
(include-book "concat-rw")
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "lattice")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(defxdoc svex-rewrite.lisp :parents (svex-rewriting))
(local (xdoc::set-default-parents svex-rewrite.lisp))


(local (std::add-default-post-define-hook :fix))

;; BOZO Separate mask stuff into a different book that doesn't depend on
;; svex-rewrite-rules?

(define svexlist-quotesp ((x svexlist-p))
  :hooks ((:fix :hints (("goal" :expand ((svexlist-fix x))))))
  (if (atom x)
      t
    (and (eq (svex-kind (car x)) :quote)
         (svexlist-quotesp (cdr x)))))

(define svexlist-unquote ((x svexlist-p))
  :prepwork ((local (in-theory (enable svexlist-quotesp))))
  :guard (svexlist-quotesp x)
  :returns (objs 4veclist-p)
  :hooks ((:fix :hints (("goal" :expand ((svexlist-fix x))))))
  (if (atom x)
      nil
    (cons (svex-quote->val (car x))
          (svexlist-unquote (cdr x))))
  ///

  (defthm svexlist-unquote-correct
    (implies (svexlist-quotesp x)
             (equal (svexlist-eval x env)
                    (svexlist-unquote x)))
    :hints(("Goal" :in-theory (enable svexlist-eval svex-eval)))))

(define svex-norm-call ((fn fnsym-p) (args svexlist-p))
  :returns (call svex-p)
  (if (svexlist-quotesp args)
      (svex-quote (svex-apply fn (svexlist-unquote args)))
    (svex-call fn args))
  ///

  (defthm svex-norm-call-correct
    (equal (svex-eval (svex-norm-call fn args) env)
           (svex-apply fn (svexlist-eval args env)))
    :hints (("goal" :in-theory (enable svex-eval))))

  (defthm vars-of-svex-norm-call
    (implies (not (member v (svexlist-vars args)))
             (not (member v (svex-vars (svex-norm-call fn args)))))))


(define svex-locally-rewrite ((mask 4vmask-p) (x svex-p) (limit natp))
  :returns (newx svex-p)
  :measure (nfix limit)
  (b* (((when (zp limit)) (svex-fix x))
       ((unless (eq (svex-kind x) :call))
        (svex-fix x))
       ((svex-call x) x)
       ((mv successp pat subst)
        (svex-rewrite-fncall-once mask x.fn x.args t))
       ((unless successp) (svex-fix x)))
    ;; The pattern is small -- just the RHS of a rewrite rule, so svex-subst
    ;; (not -memo) is good
    (svex-locally-rewrite mask (svex-subst pat subst) (1- limit)))
  ///
  (defthm svex-locally-rewrite-correct
    (equal (4vec-mask mask (svex-eval (svex-locally-rewrite mask x limit) env))
           (4vec-mask mask (svex-eval x env))))

  (defthm vars-of-svex-locally-rewrite
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-locally-rewrite mask x limit)))))))


(define svex-args-rewrite-locally ((args svexlist-p) (masks 4vmasklist-p))
  :guard (eql (len masks) (len args))
  :returns (args1 svexlist-p)
  :hooks ((:fix :hints (("goal" :expand ((4vmasklist-fix masks))))))
  (if (atom args)
      nil
    (cons (b* (((when (eql 0 (mbe :logic (4vmask-fix (car masks)) :exec (car masks))))
                (svex-x)))
            (svex-locally-rewrite (car masks) (car args) 10))
          (svex-args-rewrite-locally (cdr args) (cdr masks))))
  ///

  (defthm len-svex-args-rewrite-locally
    (equal (len (svex-args-rewrite-locally x masks))
           (len x)))

  (local (in-theory (disable pick-a-point-subset-strategy)))

  (defthm svex-args-rewrite-locally-correct
    (equal (4veclist-mask masks (svexlist-eval (svex-args-rewrite-locally x masks) env))
           (4veclist-mask masks (svexlist-eval x env)))
    :hints(("Goal" :in-theory (enable svexlist-eval 4veclist-mask)
            :induct (svex-args-rewrite-locally x masks))
           (and stable-under-simplificationp
                '(:use ((:instance svex-locally-rewrite-correct
                         (mask -1) (x (car x)) (limit 10)))
                  :in-theory (disable svex-locally-rewrite-correct)))))


  (defthm svex-args-rewrite-locally-apply-correct
    (equal (4vec-mask mask (svex-apply fn (svexlist-eval
                                           (svex-args-rewrite-locally
                                            args
                                            (svex-argmasks mask fn args))
                                           env)))
           (4vec-mask mask (svex-apply fn (svexlist-eval args env))))
    :hints (("goal" :use ((:instance svex-argmasks-correct
                           (args args)
                           (args1 (svexlist-eval
                                   (svex-args-rewrite-locally
                                    args (svex-argmasks mask fn args))
                                   env))))
             :in-theory (disable svex-argmasks-correct
                                 svex-argmasks-correct2))))

  (defthm svex-args-rewrite-locally-apply-correct-from-neg-1-mask
    (equal (svex-apply fn (svexlist-eval
                           (svex-args-rewrite-locally
                            args
                            (svex-argmasks -1 fn args))
                           env))
           (svex-apply fn (svexlist-eval args env)))
    :hints (("goal" :use ((:instance svex-args-rewrite-locally-apply-correct
                           (mask -1)))
             :in-theory (disable svex-args-rewrite-locally-apply-correct))))

  (defthm vars-of-svex-args-rewrite-locally
    (implies (not (member v (svexlist-vars args)))
             (not (member v (svexlist-vars (svex-args-rewrite-locally args masks)))))))

(defines svex-rewrite-fncall
  :verify-guards nil
  (define svex-rewrite-fncall ((clk natp)
                               (mask 4vmask-p)
                               (fn fnsym-p)
                               (args svexlist-p))
    :returns (xx svex-p)
    :well-founded-relation acl2::nat-list-<
    :measure (list clk 0)
    (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
         ((when (eql mask 0)) (svex-x))
         (masks (svex-argmasks mask fn args))
         (args (svex-args-rewrite-locally args masks))
         ((mv okp rhs sigma) (svex-rewrite-fncall-once mask fn args nil))
         ((unless okp) (svex-norm-call fn args))
         ((when (zp clk))
          (cw "Clock ran out!~%")
          (break$)
          (svex-norm-call fn args)))
      (svex-rewrite-under-subst (1- clk) mask rhs sigma)))

  (define svex-rewrite-under-subst ((clk natp)
                                    (mask 4vmask-p)
                                    (x svex-p)
                                    (sigma svex-alist-p))
    :returns (xx svex-p)
    :guard (subsetp-equal (svex-vars x) (svex-alist-keys sigma))
    :measure (list clk (svex-count x))
    (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
         ((when (eql mask 0)) (svex-x)))
      (svex-case x
        :var (mbe :logic (svex-fix (svex-lookup x.name sigma))
                  :exec (svex-lookup x.name sigma))
        :quote (mbe :logic (svex-fix x) :exec x)
        :call (b* ((masks (svex-argmasks -1 x.fn x.args))
                   ;; Note: we could use mask instead of -1 above, but in cases
                   ;; where the rewrites of different terms have common
                   ;; subterms, it might cause them to diverge.
                   ;; There are still possible divergences, however.
                   (args (svexlist-rewrite-under-subst clk masks x.args sigma)))
                (svex-rewrite-fncall clk mask x.fn args)))))

  (define svexlist-rewrite-under-subst ((clk natp)
                                        (masks 4vmasklist-p)
                                        (x svexlist-p)
                                        (sigma svex-alist-p))
    :returns (xx svexlist-p)
    :measure (list clk (svexlist-count x))
    :guard (and (equal (len x) (len masks))
                (subsetp-equal (svexlist-vars x) (svex-alist-keys sigma)))
    (if (atom x)
        nil
      (cons (svex-rewrite-under-subst clk (car masks) (car x) sigma)
            (svexlist-rewrite-under-subst clk (cdr masks) (cdr x) sigma))))
  ///
  (local (defthm svarlist-p-implies-true-listp
           (implies (svarlist-p x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable svarlist-p)))))

  (verify-guards svex-rewrite-fncall
    :hints (("goal" :do-not-induct t
             :expand ((svex-vars x)
                      (svexlist-vars x)))))

  (fty::deffixequiv-mutual svex-rewrite-fncall
    :hints (("goal" :expand ((svexlist-fix x)))))


  ;; (defthm svex-apply-fn-svex-args-delete-empty
  ;;   (equal (4vec-mask
  ;;           mask (svex-apply fn (svexlist-eval (svex-args-delete-empty
  ;;                                               args (svex-argmasks mask fn args))
  ;;                           env)))
  ;;          (4vec-mask
  ;;           mask (svex-apply fn (svexlist-eval args env))))
  ;;   :hints (("goal" :use ((:instance svex-argmasks-correct
  ;;                          (args1 (svexlist-eval
  ;;                                  (svex-args-delete-empty
  ;;                                   args (svex-argmasks mask fn args))
  ;;                                  env))))
  ;;            :in-theory (disable svex-argmasks-correct
  ;;                                svex-argmasks-correct2))))

  (local
   (defthm svex-argmasks-correct-minus1
     (implies (and (equal (4veclist-mask (svex-argmasks -1 fn args)
                                         (svexlist-eval args env))
                          (4veclist-mask (svex-argmasks -1 fn args)
                                         args1))
                   (syntaxp (not (equal args1 `(svexlist-eval ,args ,env)))))
              (equal (svex-apply fn args1)
                     (svex-apply fn (svexlist-eval args env))))
     :hints (("goal" :use ((:instance svex-argmasks-correct (mask -1)))
              :in-theory (disable svex-argmasks-correct
                                  svex-argmasks-correct2)))))

  (defthm-svex-rewrite-fncall-flag
    (defthm svex-rewrite-fncall-rw
      (equal (4vec-mask mask (svex-eval (svex-rewrite-fncall clk mask fn args) env))
             (4vec-mask mask (svex-eval (svex-call fn args) env)))
      :hints ('(:expand ((svex-rewrite-fncall clk mask fn args))))
      :flag svex-rewrite-fncall)
    (defthm svex-rewrite-under-subst-rw
      (equal (4vec-mask mask (svex-eval (svex-rewrite-under-subst clk mask x sigma) env))
             (4vec-mask mask (svex-eval (svex-subst x sigma) env)))
      :hints ('(:expand ((svex-rewrite-under-subst clk mask x sigma)
                         (:free (env) (svex-eval x env)))))
      :flag svex-rewrite-under-subst)
    (defthm svexlist-rewrite-under-subst-rw
      (equal (4veclist-mask masks (svexlist-eval
                                   (svexlist-rewrite-under-subst clk masks x sigma)
                                   env))
             (4veclist-mask masks (svexlist-eval (svexlist-subst x sigma) env)))
      :hints ('(:expand ((svexlist-rewrite-under-subst clk masks x sigma))))
      :flag svexlist-rewrite-under-subst))


  (defthm-svex-rewrite-fncall-flag
    (defthm svex-rewrite-fncall-vars
      (implies (not (member v (svexlist-vars args)))
               (not (member v (svex-vars (svex-rewrite-fncall clk mask fn args)))))
      :hints ('(:expand ((svex-rewrite-fncall clk mask fn args))))
      :flag svex-rewrite-fncall)
    (defthm svex-rewrite-under-subst-vars
      (implies (not (member v (svex-alist-vars sigma)))
               (not (member v (svex-vars (svex-rewrite-under-subst clk mask x sigma)))))
      :hints ('(:expand ((svex-rewrite-under-subst clk mask x sigma)
                         (:free (env) (svex-eval x env)))))
      :flag svex-rewrite-under-subst)
    (defthm svexlist-rewrite-under-subst-vars
      (implies (not (member v (svex-alist-vars sigma)))
               (not (member v (svexlist-vars (svexlist-rewrite-under-subst clk masks x sigma)))))
      :hints ('(:expand ((svexlist-rewrite-under-subst clk masks x sigma))))
      :flag svexlist-rewrite-under-subst)))




(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))


(define svexlist-toposort-p ((x svexlist-p))
  :measure (svexlist-count x)
  (b* (((when (atom x)) t)
       (rest (mbe :logic (svexlist-fix (cdr x))
                  :exec (cdr x)))
       (first (car x)))
    (and (or (not (eq (svex-kind first) :call))
             (subsetp-equal (svex-call->args first) rest))
         (svexlist-toposort-p rest)))
  ///
  (fty::deffixequiv svexlist-toposort-p
    :hints (("goal" :expand ((svexlist-fix x))))))


(defines svex-toposort
  :verify-guards nil
  (define svex-toposort ((x svex-p)
                         (sort svexlist-p)
                         (contents))
    :returns (mv (sort svexlist-p)
                 contents)
    :measure (svex-count x)
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         ((when (hons-get x contents))
          (mv (mbe :logic (svexlist-fix sort) :exec sort)
              contents))
         ((when (not (eq (svex-kind x) :call)))
          (mv (cons x (mbe :logic (svexlist-fix sort) :exec sort))
              (hons-acons x t contents)))
         ((mv sort contents)
          (svexlist-toposort (svex-call->args x) sort contents)))
      (mv (cons x sort)
          (hons-acons x t contents))))

  (define svexlist-toposort ((x svexlist-p)
                             (sort svexlist-p)
                             (contents))
    :returns (mv (sort svexlist-p)
                 contents)
    :measure (svexlist-count x)
    (b* (((when (atom x)) (mv (mbe :logic (svexlist-fix sort) :exec sort)
                              contents))
         ((mv sort contents) (svex-toposort (car x) sort contents)))
      (svexlist-toposort (cdr x) sort contents)))
  ///
  (fty::deffixequiv-mutual svex-toposort
    :hints (("goal" :expand ((svexlist-fix x)))))

  (verify-guards svex-toposort)

  (defthm-svex-toposort-flag
    (defthm svex-toposort-contents-in-sync
      (b* (((mv sort1 contents1)
            (svex-toposort x sort contents)))
        (implies (equal (strip-cars contents) (svexlist-fix sort))
                 (equal (strip-cars contents1) sort1)))
      :flag svex-toposort)
    (defthm svexlist-toposort-contents-in-sync
      (b* (((mv sort1 contents1)
            (svexlist-toposort x sort contents)))
        (implies (equal (strip-cars contents) (svexlist-fix sort))
                 (equal (strip-cars contents1) sort1)))
      :flag svexlist-toposort))

  (defthm-svex-toposort-flag
    (defthm svex-toposort-preserves-membership
      (b* (((mv sort1 ?contents1)
            (svex-toposort x sort contents)))
        (implies (member y (svexlist-fix sort))
                 (member y sort1)))
      :flag svex-toposort)
    (defthm svexlist-toposort-preserves-membership
      (b* (((mv sort1 ?contents1)
            (svexlist-toposort x sort contents)))
        (implies (member y (svexlist-fix sort))
                 (member y sort1)))
      :flag svexlist-toposort))

  (defthm svex-toposort-adds-elt
    (implies (equal (strip-cars contents) (svexlist-fix sort))
             (member (svex-fix x) (mv-nth 0 (svex-toposort x sort contents))))
    :hints (("goal" :expand ((svex-toposort x sort contents)))))

  (defthm-svex-toposort-flag
    (defthm svexlist-toposort-adds-elts
      (implies (equal (strip-cars contents) (svexlist-fix sort))
               (subsetp-equal (svexlist-fix x)
                              (mv-nth 0 (svexlist-toposort x sort contents))))
      :flag svexlist-toposort
      :hints ('(:expand ((svexlist-fix x)))))
    :skip-others t)

  (defthm svexlist-toposort-adds-elts-unfixed
    (implies (and (equal (strip-cars contents) (svexlist-fix sort))
                  (svexlist-p x))
             (subsetp-equal x
                            (mv-nth 0 (svexlist-toposort x sort contents))))
    :hints (("goal" :use svexlist-toposort-adds-elts)))

  (defthm-svex-toposort-flag
    (defthm svex-toposort-correct
      (b* (((mv sort1 ?contents1)
            (svex-toposort x sort contents)))
        (implies (and (svexlist-toposort-p sort)
                      (equal (strip-cars contents) (svexlist-fix sort)))
                 (svexlist-toposort-p sort1)))
      :hints ('(:expand ((:free (a b) (svexlist-toposort-p (cons a b))))))
      :flag svex-toposort)
    (defthm svexlist-toposort-correct
      (b* (((mv sort1 ?contents1)
            (svexlist-toposort x sort contents)))
        (implies (and (svexlist-toposort-p sort)
                      (equal (strip-cars contents) (svexlist-fix sort)))
                 (svexlist-toposort-p sort1)))
      :flag svexlist-toposort)))

(defsection svex-argmasks-okp
  ;; (svex-argmasks-okp x mask argmasks) if
  ;; x is a call (x.fn x.args) implies:
  ;; for all env, vals
  ;;  if vals are eqivalent to (eval x.args env) under argmasks
  ;;  then (eval x env) is equivalent to (apply x.fn vals) under argmasks.

  (acl2::defquant svex-argmasks-okp (x mask argmasks)
    (forall (env vals)
            (implies (and (equal (svex-kind x) :call)
                          (equal (4veclist-mask argmasks
                                                (svexlist-eval (svex-call->args x) env))
                                 (4veclist-mask argmasks vals)))
                     (equal (equal (4vec-mask mask (svex-eval x env))
                                   (4vec-mask mask (svex-apply (svex-call->fn x) vals)))
                            t)))
    :rewrite :direct)

  (acl2::defexample svex-argmasks-okp-example
    :pattern (equal (4vec-mask mask (svex-eval x env))
                    (4vec-mask mask (svex-apply fn vals)))
    :templates (env vals)
    :instance-rulename svex-argmasks-okp-instancing)

  (fty::deffixequiv svex-argmasks-okp
    :args ((x svex-p)
           (mask 4vmask-p)
           (argmasks 4vmasklist-p))
    :hints (("goal" :cases ((svex-argmasks-okp x mask argmasks)))
            (acl2::witness)))



  (defthm svex-argmasks-okp-of-svex-argmasks
    (implies (equal (svex-kind x) :call)
             (svex-argmasks-okp x mask (svex-argmasks mask (svex-call->fn x) (svex-call->args x))))
    :hints ((acl2::witness) (acl2::witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (env) (svex-eval x env))
                            (:free (f a env) (svex-eval (svex-call f a) env)))))))


  (defthm svex-argmasks-okp-when-subsumed
    (implies (and (4vmasklist-subsumes argmasks1 argmasks)
                  (svex-argmasks-okp x mask argmasks))
             (svex-argmasks-okp x mask argmasks1))
    :hints ((acl2::witness :ruleset (svex-argmasks-okp-witnessing
                                     svex-argmasks-okp-instancing
                                     svex-argmasks-okp-example))))

  (defthm svex-argmasks-okp-when-subsumed-match2
    (implies (and (svex-argmasks-okp x mask argmasks)
                  (4vmasklist-subsumes argmasks1 argmasks))
             (svex-argmasks-okp x mask argmasks1))))



(fty::defalist svex-mask-alist :key-type svex :val-type 4vmask :true-listp t)

(define svex-mask-acons ((x svex-p) (m 4vmask-p) (al svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svex-mask-alist-p
                                       svex-mask-alist-fix))))
  :returns (aa svex-mask-alist-p)
  (mbe :logic (cons (cons (svex-fix x) (4vmask-fix m))
                    (svex-mask-alist-fix al))
       :exec (hons-acons x m al))
  ///
  (fty::deffixequiv svex-mask-acons))

(define svex-mask-lookup ((x svex-p) (al svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svex-mask-alist-p
                                       svex-mask-alist-fix))))
  :returns (mask 4vmask-p :rule-classes :type-prescription)
  (or (mbe :logic (cdr (assoc (svex-fix x) (svex-mask-alist-fix al)))
           :exec (cdr (hons-get x al)))
      0)
  ///
  (fty::deffixequiv svex-mask-lookup)
  (defthm svex-mask-lookup-of-svex-mask-acons
    (equal (svex-mask-lookup x (svex-mask-acons y m al))
           (if (equal (svex-fix x) (svex-fix y))
               (4vmask-fix m)
             (svex-mask-lookup x al)))
    :hints(("Goal" :in-theory (enable svex-mask-acons))))

  (defthm svex-mask-lookup-of-nil
    (equal (svex-mask-lookup k nil)
           0)))


(define svex-mask-alist-keys ((x svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svex-mask-alist-p))))
  :returns (keys svexlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svex-fix (caar x)) :exec (caar x))
              (svex-mask-alist-keys (cdr x)))
      (svex-mask-alist-keys (cdr x))))
  ///
  (fty::deffixequiv svex-mask-alist-keys
    :hints (("goal" :expand ((svex-mask-alist-fix x)))))

  (defthm member-svex-mask-alist-keys
    (implies (not (member (svex-fix k) (svex-mask-alist-keys x)))
             (equal (svex-mask-lookup k x) 0))
    :hints(("Goal" :in-theory (enable svex-mask-lookup svex-mask-alist-fix))))

  (defthm svex-mask-alist-keys-of-svex-mask-acons
    (equal (svex-mask-alist-keys (svex-mask-acons k v x))
           (cons (svex-fix k) (svex-mask-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-mask-acons)))))



(defthm equal-of-svex-fix-implies-svex-equiv
    (implies (equal (svex-fix x) (svex-fix y))
             (svex-equiv x y))
    :hints(("Goal" :in-theory (enable svex-equiv)))
    :rule-classes :forward-chaining)



(define svex-argmasks-lookup ((args svexlist-p) (mask-al svex-mask-alist-p))
  :returns (argmasks 4vmasklist-p)
  (if (atom args)
      nil
    (cons (svex-mask-lookup (car args) mask-al)
          (svex-argmasks-lookup (cdr args) mask-al)))
  ///
  (defthm len-of-svex-argmasks-lookup
    (equal (len (svex-argmasks-lookup args mask-al))
           (len args)))

  (fty::deffixequiv svex-argmasks-lookup
    :hints (("goal" :expand ((svexlist-fix args)))))

  (defthm svex-argmasks-lookup-of-nil
    (equal (svex-argmasks-lookup args nil)
           (replicate (len args) 0))
    :hints(("Goal" :in-theory (enable replicate)))))

(define svex-args-apply-masks ((args svexlist-p)
                               (masks 4vmasklist-p)
                               (mask-al svex-mask-alist-p))
  :verify-guards nil
  :returns (mask-al1 svex-mask-alist-p)
  :guard (equal (len args) (len masks))
  (b* (((when (atom args)) (mbe :logic (svex-mask-alist-fix mask-al)
                                :exec mask-al))
       (mask-al (svex-args-apply-masks (cdr args) (cdr masks) mask-al))
       (look (svex-mask-lookup (car args) mask-al))
       (mask (4vmask-union (car masks) look)))
    (svex-mask-acons (car args) mask mask-al))
  ///

  (verify-guards svex-args-apply-masks)

  (defthm svex-args-apply-masks-lookup-subsumes-prev-lookup
    (4vmask-subsumes (svex-mask-lookup x (svex-args-apply-masks args masks mask-al))
                     (svex-mask-lookup x mask-al)))

  (defthm svex-args-apply-masks-lookup-when-not-in-args
    (implies (not (member (svex-fix y) (svexlist-fix args)))
             (equal (svex-mask-lookup y (svex-args-apply-masks args masks mask-al))
                    (svex-mask-lookup y mask-al)))
    :hints(("Goal" :in-theory (enable svexlist-fix))))

  (local (defun ind (n args masks mask-al)
           (if (atom args)
               (list n masks mask-al)
             (ind (1- (nfix n)) (cdr args) (cdr masks) mask-al))))

  (local (Defthmd nth-when-zp
           (implies (zp n) (equal (nth n x) (car X)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm svex-args-apply-masks-lookup-subsumes-mask
    (implies (< (nfix n) (len args))
             (4vmask-subsumes
              (svex-mask-lookup (nth n args) (svex-args-apply-masks args masks mask-al))
              (nth n masks)))
    :hints (("goal" :induct (ind n args masks mask-al)
             :in-theory (enable nfix nth-when-zp))))

  (defthm svex-args-apply-masks-argmasks-lookup-subsumes-prev-lookup
    (4vmasklist-subsumes (svex-argmasks-lookup x (svex-args-apply-masks args masks mask-al))
                         (svex-argmasks-lookup x mask-al))
    :hints (("goal" :induct (len x)
             :in-theory (enable svex-argmasks-lookup
                                4vmasklist-subsumes))))

  (local (defthm 4vmask-union-all
           (equal (4vmask-union x -1)
                  -1)
           :hints (("goal" :expand ((4vmask-union x -1))))))

  (defthm svex-args-apply-masks-lookup-when-all
    (implies (equal (svex-mask-lookup x mask-al) -1)
             (equal (svex-mask-lookup x (svex-args-apply-masks args masks mask-al))
                    -1)))

  (local (defun ctup (n a)
           (declare (xargs :measure (nfix (- (len a) (nfix n)))))
           (if (zp (- (len a) (nfix n)))
               n
             (ctup (1+ (nfix n)) a))))

  (local (defthm consp-of-nthcdr
           (iff (consp (nthcdr n x))
                (< (nfix n) (len x)))
           :hints(("Goal" :in-theory (e/d (nthcdr) (nfix))
                   :induct (nthcdr n x)))))

  (local (defthm nthcdr-of-cdr
           (equal (nthcdr n (cdr x))
                  (cdr (nthcdr n x)))))

  (local (defthm car-of-nthcdr
           (equal (car (nthcdr n x))
                  (nth n x))))

  (local (defthmd svex-args-apply-masks-argmasks-lookups-subsume-masks-lemma
           (implies (equal (len args) (len masks))
                    (4vmasklist-subsumes
                     (svex-argmasks-lookup (nthcdr n args) (svex-args-apply-masks args masks mask-al))
                     (nthcdr n masks)))
           :hints(("Goal" :in-theory (enable svex-argmasks-lookup
                                             4vmasklist-subsumes)
                   :induct (ctup n args)))))

  (defthm svex-args-apply-masks-argmasks-lookups-subsume-masks
    (implies (equal (len args) (len masks))
             (4vmasklist-subsumes
              (svex-argmasks-lookup args (svex-args-apply-masks args masks mask-al))
              masks))
    :hints (("goal" :use ((:instance svex-args-apply-masks-argmasks-lookups-subsume-masks-lemma
                           (n 0))))))

  (deffixequiv svex-args-apply-masks))

(defsection svex-mask-alist-partly-complete
  (acl2::defquant svex-mask-alist-partly-complete (x mask-al)
    (forall (y)
            (implies
             (not (member (svex-fix y) (svexlist-fix x)))
             (svex-argmasks-okp
              y (svex-mask-lookup y mask-al) (svex-argmasks-lookup (svex-call->args y) mask-al))))
    :rewrite :direct)

  (in-theory (disable svex-mask-alist-partly-complete))

  (acl2::defexample svex-mask-alist-partly-complete-example
    :pattern (svex-argmasks-lookup (svex-call->args y) mask-al)
    :templates (y)
    :instance-rulename svex-mask-alist-partly-complete-instancing)


  (fty::deffixequiv svex-mask-alist-partly-complete
    :args ((x svexlist)
           (mask-al svex-mask-alist))
    :hints (("goal" :cases ((svex-mask-alist-partly-complete x mask-al)))
            (acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))))



  (local (defthm nonmember-of-superset
           (implies (and (not (member y x))
                         (subsetp args x))
                    (not (member y args)))))

  (defthm svex-mask-alist-partly-complete-preserved-by-svex-args-apply-masks
    (implies (and (subsetp-equal (svexlist-fix args) (svexlist-fix x))
                  (svex-mask-alist-partly-complete x mask-al))
             (svex-mask-alist-partly-complete
              x (svex-args-apply-masks args masks mask-al)))
    :hints ((acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))))

  (local (defthm svex-argmasks-okp-when-not-fncall
           (implies (not (equal (svex-kind x) :call))
                    (svex-argmasks-okp x mask argmasks))
           :hints ((acl2::witness))))

  (defthm svex-mask-alist-partly-complete-preserved-by-svex-args-apply-masks-better
    (implies (and (subsetp-equal (svex-call->args (car x)) (svexlist-fix (cdr x)))
                  (svex-mask-alist-partly-complete x mask-al))
             (svex-mask-alist-partly-complete
              (cdr x)
              (svex-args-apply-masks (svex-call->args (car x))
                                     (svex-argmasks (svex-mask-lookup (car x) mask-al)
                                                    (svex-call->fn (car x))
                                                    (svex-call->args (car x)))
                                     mask-al)))
    :hints (("goal" :expand ((svexlist-fix x)))
            (acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))
            (and stable-under-simplificationp
                 '(:use ((:instance svex-argmasks-okp-of-svex-argmasks
                          (x acl2::y0)
                          (mask (svex-mask-lookup acl2::y0 mask-al))))
                   :in-theory (disable svex-argmasks-okp-of-svex-argmasks)))))

  (defthm svex-mask-alist-partly-complete-non-consp-norm
    (implies (and (syntaxp (not (equal x ''nil)))
                  (not (consp x)))
             (equal (svex-mask-alist-partly-complete x mask-al)
                    (svex-mask-alist-partly-complete nil mask-al)))
    :hints (("goal" :cases ((svex-mask-alist-partly-complete x mask-al))
             :expand ((svexlist-fix x)))
            (acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))))

  (defthm svex-mask-alist-partly-complete-cdr-when-not-fncall
    (implies (and (svex-mask-alist-partly-complete x mask-al)
                  (not (equal (svex-kind (car x)) :call)))
             (svex-mask-alist-partly-complete (cdr x) mask-al))
    :hints (("goal" :expand ((svexlist-fix x)))
            (acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))))

  (defthm svex-mask-alist-partly-complete-cdr-when-0-mask
    (implies (and (svex-mask-alist-partly-complete x mask-al)
                  (equal (svex-mask-lookup (car x) mask-al) 0))
             (svex-mask-alist-partly-complete (cdr x) mask-al))
    :hints (("goal" :expand ((svexlist-fix x))
             :in-theory (enable svex-argmasks-okp))
            (acl2::witness :ruleset (svex-mask-alist-partly-complete-witnessing
                                     svex-mask-alist-partly-complete-instancing
                                     svex-mask-alist-partly-complete-example))))


  (defthm starting-mask-al-is-partly-complete
    (implies (subsetp (svex-mask-alist-keys mask-al) (svexlist-fix x))
             (svex-mask-alist-partly-complete x mask-al))
    :hints ((acl2::witness :ruleset svex-mask-alist-partly-complete-witnessing)
            (acl2::witness))))

(define svexlist-compute-masks ((x svexlist-p)
                                (mask-al svex-mask-alist-p))
  :returns (mask-al1 svex-mask-alist-p)
  (b* (((when (atom x))
        (mbe :logic (svex-mask-alist-fix mask-al)
             :exec mask-al))
       (first (car x))
       ((when (not (eq (svex-kind first) :call)))
        (svexlist-compute-masks (cdr x) mask-al))
       (mask (svex-mask-lookup first mask-al))
       ((when (eql mask 0))
        (svexlist-compute-masks (cdr x) mask-al))
       (args (svex-call->args first))
       (argmasks (svex-argmasks mask
                                (svex-call->fn first)
                                args))
       (mask-al (svex-args-apply-masks args argmasks mask-al)))
    (svexlist-compute-masks (cdr x) mask-al))
  ///
  (defthm svexlist-compute-masks-lookup-subsumes-prev-lookup
    (4vmask-subsumes (svex-mask-lookup y (svexlist-compute-masks x mask-al))
                     (svex-mask-lookup y mask-al)))

  (defthm svexlist-compute-masks-lookup-when-all
    (implies (equal (svex-mask-lookup y mask-al) -1)
             (equal (svex-mask-lookup y (svexlist-compute-masks x mask-al))
                    -1)))

  (defthm svexlist-compute-masks-lookups-subsume-prev-lookups
    (4vmasklist-subsumes (svex-argmasks-lookup y (svexlist-compute-masks x mask-al))
                         (svex-argmasks-lookup y mask-al))
    :hints (("goal" :induct (len y)
             :expand ((:free (m) (svex-argmasks-lookup y m))
                      (:free (a b c d)
                       (4vmasklist-subsumes (cons a b) (cons c d)))))))

  (defthm svexlist-compute-masks-partly-complete
    (implies (and (svex-mask-alist-partly-complete x mask-al)
                  (svexlist-toposort-p x))
             (svex-mask-alist-partly-complete nil (svexlist-compute-masks x mask-al)))
    :hints (("goal" :expand ((svexlist-toposort-p x)))))

  (deffixequiv svexlist-compute-masks))

(defsection svex-mask-alist-complete
  ;; just like partly-complete but doesn't have a list of exceptions
  (acl2::defquant svex-mask-alist-complete (mask-al)
    (forall (y)
            (svex-argmasks-okp y (svex-mask-lookup y mask-al)
                               (svex-argmasks-lookup (svex-call->args y) mask-al)))
    :rewrite :direct)

  (in-theory (disable svex-mask-alist-complete))

  (acl2::defexample svex-mask-alist-complete-example
    :pattern (svex-argmasks-lookup (svex-call->args y) mask-al)
    :templates (y)
    :instance-rulename svex-mask-alist-complete-instancing)


  (fty::deffixequiv svex-mask-alist-complete
    :args ((mask-al svex-mask-alist))
    :hints (("goal" :cases ((svex-mask-alist-complete mask-al)))
            (acl2::witness :ruleset (svex-mask-alist-complete-witnessing
                                     svex-mask-alist-complete-instancing
                                     svex-mask-alist-complete-example))))

  (local (defthm nonmember-of-superset
           (implies (and (not (member y x))
                         (subsetp args x))
                    (not (member y args)))))

  (defthm svex-mask-alist-partly-complete-reduce-to-complete
    (equal (svex-mask-alist-partly-complete nil mask-al)
           (svex-mask-alist-complete mask-al))
    :hints (("goal" :cases ((svex-mask-alist-complete mask-al)))
            (acl2::witness)))

  (defthm svexlist-compute-masks-complete
    (implies (and (svexlist-toposort-p x)
                  (subsetp (svex-mask-alist-keys mask-al) (svexlist-fix x)))
             (svex-mask-alist-complete (svexlist-compute-masks x mask-al)))
    :hints (("goal" :use ((:instance svexlist-compute-masks-partly-complete))))))


(defines svex-rewrite
  :verify-guards nil
  (define svex-rewrite ((x svex-p)
                        (masks svex-mask-alist-p))
    :returns (xx svex-p)
    :measure (svex-count x)
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (kind (svex-kind x))
         ((when (eq kind :quote)) x)
         (mask (svex-mask-lookup x masks))
         ((when (eql mask 0)) (svex-x))
         ((when (eq kind :var)) x)
         ((svex-call x) x)
         (args (svexlist-rewrite x.args masks))
         ;; (argmasks (svex-argmasks mask x.fn args))
         ;; (args (svex-args-rewrite-under-masks args argmasks))
         )
      (svex-rewrite-fncall 1000 mask (svex-call->fn x) args)))

  (define svexlist-rewrite ((x svexlist-p)
                            (masks svex-mask-alist-p))
    :returns (xx svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (cons (svex-rewrite (car x) masks)
            (svexlist-rewrite (cdr x) masks))))
  ///
  (verify-guards svex-rewrite)

  (fty::deffixequiv-mutual svex-rewrite
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm len-of-svexlist-rewrite
    (equal (len (svexlist-rewrite x masks))
           (len x)))

  (local (acl2::defexample svex-argmasks-okp-example
           :pattern (4vec-mask mask (svex-apply fn (svexlist-eval args env)))
           :templates (env (svexlist-eval args env))
           :instance-rulename svex-argmasks-okp-instancing))

  (defthm-svex-rewrite-flag
    (defthm svex-rewrite-correct
      (implies (svex-mask-alist-complete masks)
               (equal (4vec-mask (svex-mask-lookup x masks)
                                 (svex-eval (svex-rewrite x masks) env))
                      (4vec-mask (svex-mask-lookup x masks)
                                 (svex-eval x env))))
      :hints ('(:expand ((:free (f a env) (svex-eval (svex-call f a) env))
                         (:free (env) (svex-eval x env)))
                :do-not-induct t)
              (acl2::witness)
              (acl2::witness))
      :flag svex-rewrite)
    (defthm svexlist-rewrite-correct
      (implies (svex-mask-alist-complete masks)
               (equal (4veclist-mask (svex-argmasks-lookup x masks)
                                     (svexlist-eval (svexlist-rewrite x masks) env))
                      (4veclist-mask (svex-argmasks-lookup x masks)
                                     (svexlist-eval x env))))
      :hints ('(:expand ((svex-argmasks-lookup x masks))))
      :flag svexlist-rewrite))

  (defthm-svex-rewrite-flag
    (defthm svex-rewrite-vars
      (implies (not (member v (svex-vars x)))
               (not (member v (svex-vars (svex-rewrite x masks)))))
      :hints ('(:expand ((svex-vars x)
                         (svex-rewrite x masks))
                :do-not-induct t)
              ;; (acl2::witness)
              ;; (acl2::witness)
              )
      :flag svex-rewrite)
    (defthm svexlist-rewrite-vars
      (implies (not (member v (svexlist-vars x)))
               (not (member v (svexlist-vars (svexlist-rewrite x masks)))))
      :hints ('(:expand ((svexlist-rewrite x masks))))
      :flag svexlist-rewrite masks))

  (memoize 'svex-rewrite
           :condition '(eq (svex-kind x) :call)))


(defines svex-maskfree-rewrite
  :verify-guards nil
  (define svex-maskfree-rewrite ((x svex-p))
    :returns (xx svex-p)
    :measure (svex-count x)
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (kind (svex-kind x))
         ((when (eq kind :quote)) x)
         ((when (eq kind :var)) x)
         ((svex-call x) x)
         (args (svexlist-maskfree-rewrite x.args))
         ;; (argmasks (svex-argmasks mask x.fn args))
         ;; (args (svex-args-rewrite-under-masks args argmasks))
         )
      (svex-rewrite-fncall 1000 -1 (svex-call->fn x) args)))

  (define svexlist-maskfree-rewrite ((x svexlist-p))
    :returns (xx svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (cons (svex-maskfree-rewrite (car x))
            (svexlist-maskfree-rewrite (cdr x)))))
  ///
  (verify-guards svex-maskfree-rewrite)

  (fty::deffixequiv-mutual svex-maskfree-rewrite
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm len-of-svexlist-maskfree-rewrite
    (equal (len (svexlist-maskfree-rewrite x))
           (len x)))

  (local (acl2::defexample svex-argmasks-okp-example
           :pattern (4vec-mask mask (svex-apply fn (svexlist-eval args env)))
           :templates (env (svexlist-eval args env))
           :instance-rulename svex-argmasks-okp-instancing))

  (defthm-svex-maskfree-rewrite-flag
    (defthm svex-maskfree-rewrite-correct
      (equal (svex-eval (svex-maskfree-rewrite x) env)
             (svex-eval x env))
      :hints ('(:expand ((:free (f a env) (svex-eval (svex-call f a) env))
                         (:free (env) (svex-eval x env))
                         (svex-maskfree-rewrite x))
                :use ((:instance svex-rewrite-fncall-rw
                       (clk 1000) (mask -1) (fn (svex-call->fn x))
                       (args (svexlist-maskfree-rewrite (svex-call->args x)))))
                :in-theory (e/d (4vec-mask) (svex-rewrite-fncall-rw))
                :do-not-induct t)
              ;; (acl2::witness)
              ;; (acl2::witness)
              )
      :flag svex-maskfree-rewrite)
    (defthm svexlist-maskfree-rewrite-correct
      (equal (svexlist-eval (svexlist-maskfree-rewrite x) env)
             (svexlist-eval x env))
      :hints ('(:expand ((svexlist-maskfree-rewrite x))))
      :flag svexlist-maskfree-rewrite))

  (defthm-svex-maskfree-rewrite-flag
    (defthm svex-maskfree-rewrite-vars
      (implies (not (member v (svex-vars x)))
               (not (member v (svex-vars (svex-maskfree-rewrite x)))))
      :hints ('(:expand ((svex-vars x)
                         (svex-maskfree-rewrite x))
                :do-not-induct t)
              ;; (acl2::witness)
              ;; (acl2::witness)
              )
      :flag svex-maskfree-rewrite)
    (defthm svexlist-maskfree-rewrite-vars
      (implies (not (member v (svexlist-vars x)))
               (not (member v (svexlist-vars (svexlist-maskfree-rewrite x)))))
      :hints ('(:expand ((svexlist-maskfree-rewrite x))))
      :flag svexlist-maskfree-rewrite))


  (memoize 'svex-maskfree-rewrite
           :condition '(eq (svex-kind x) :call)))


(define svexlist-mask-acons ((x svexlist-p) (mask 4vmask-p) (al svex-mask-alist-p))
  :verify-guards nil
  :returns (al svex-mask-alist-p)
  (if (atom x)
      (mbe :logic (svex-mask-alist-fix al) :exec al)
    (svex-mask-acons (car x) mask (svexlist-mask-acons (cdr x) mask al)))
  ///
  (fty::deffixequiv svexlist-mask-acons
    :hints(("Goal" :expand ((svexlist-fix x)))))

  (verify-guards svexlist-mask-acons)

  (defthm lookup-in-svexlist-mask-acons
    (equal (svex-mask-lookup k (svexlist-mask-acons x mask al))
           (if (member (svex-fix k) (svexlist-fix x))
               (4vmask-fix mask)
             (svex-mask-lookup k al)))
    :hints(("Goal" :in-theory (enable svexlist-fix))))

  (defthm svex-mask-alist-keys-of-svexlist-mask-acons
    (equal (svex-mask-alist-keys (svexlist-mask-acons x mask al))
           (append (svexlist-fix x) (svex-mask-alist-keys al)))
    :hints(("Goal" :in-theory (enable svexlist-fix)))))

(define svexlist-mask-alist ((x svexlist-p))
  :returns (mask-al svex-mask-alist-p)
  (b* (((mv toposort al) (cwtime (svexlist-toposort x nil nil) :mintime 1))
       (- (fast-alist-free al)))
    (cwtime (svexlist-compute-masks toposort (svexlist-mask-acons x -1 nil)) :mintime 1))
  ///
  (fty::deffixequiv svexlist-mask-alist)

  (defthm svexlist-mask-alist-complete
    (svex-mask-alist-complete (svexlist-mask-alist x)))

  (defthm svexlist-mask-alist-lookup
    (implies (member-equal (svex-fix y) (svexlist-fix x))
             (equal (svex-mask-lookup y (svexlist-mask-alist x))
                    -1)))

  (defthm svex-argmasks-lookup-of-svexlist-mask-alist
    (implies (subsetp-equal (svexlist-fix y) (svexlist-fix x))
             (equal (svex-argmasks-lookup y (svexlist-mask-alist x))
                    (replicate (len y) -1)))
    :hints(("Goal" :induct (len y)
            :in-theory (e/d (replicate) (svexlist-mask-alist))
            :expand ((svexlist-fix y)
                     (:free (x) (svex-argmasks-lookup y x)))))))

;; (define svexlist-mask-alist-for-given-masks ((x svexlist-p) (masks svex-mask-alist-p))
;;   (b* (((mv toposort al


(define svex-rewrite-top ((x svex-p))
  :returns (xx svex-p)
  (svex-rewrite x (svexlist-mask-alist (list x)))
  ;; (b* (((mv toposort al) (svex-toposort x nil nil))
  ;;      (- (fast-alist-free al))
  ;;      (masks (svexlist-compute-masks toposort (svex-mask-acons x -1 nil))))
  ;;   (svex-rewrite x masks))
  ///
  (fty::deffixequiv svex-rewrite-top)

  (defthm svex-rewrite-top-correct
    (equal (svex-eval (svex-rewrite-top x) env)
           (svex-eval x env))
    :hints (("goal" :use ((:instance svex-rewrite-correct
                           (masks (svexlist-mask-alist (list x)))))
             :in-theory (disable svex-rewrite-correct))
            (acl2::witness)))

  (defthm vars-of-svex-rewrite-top
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-rewrite-top x)))))))





(define svexlist-rewrite-top ((x svexlist-p) &key (verbosep 'nil))
  :returns (xx svexlist-p)
  (b* ((- (and verbosep (cw "opcount before rewrite: ~x0~%" (svexlist-opcount x))))
       (masks (svexlist-mask-alist x))
       (x (cwtime (svexlist-rewrite x masks) :mintime 1))
       (- (clear-memoize-table 'svex-rewrite)
          (fast-alist-free masks)
          (and verbosep (cw "opcount after rewrite: ~x0~%" (time$ (svexlist-opcount x)
                                                                  :msg "; svexlist-opcount: ~st sec, ~sa bytes.~%"))))
       ;; (x (cwtime (svexlist-normalize-concats x)))
       )
    ;; (and verbosep (cw "opcount after norm-concats: ~x0~%" (svexlist-opcount x)))
    x)
  ///
  (fty::deffixequiv svexlist-rewrite-top)

  (defthm svexlist-rewrite-top-correct
    (equal (svexlist-eval (svexlist-rewrite-top x :verbosep verbosep) env)
           (svexlist-eval x env))
    :hints (("goal" :use ((:instance svexlist-rewrite-correct
                           (masks (svexlist-mask-alist x))))
             :in-theory (disable svexlist-rewrite-correct))
            (acl2::witness)))

  (defthm len-of-svexlist-rewrite-top
    (equal (len (svexlist-rewrite-top x :verbosep verbosep))
           (len x)))

  (defthm vars-of-svexlist-rewrite-top
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars (svexlist-rewrite-top x :verbosep verbosep)))))))


(define svex-alist-rewrite-top ((x svex-alist-p) &key (verbosep 'nil))
  :returns (xx svex-alist-p)
  (pairlis$ (svex-alist-keys x)
            (svexlist-rewrite-top (svex-alist-vals x) :verbosep verbosep))
  ///
  (fty::deffixequiv svex-alist-rewrite-top)

  (defthm svex-alist-keys-of-pairlis$
    (equal (svex-alist-keys (pairlis$ x y))
           (svarlist-fix x))
    :hints(("Goal" :in-theory (enable svarlist-fix pairlis$ svex-alist-keys))))

  (defthm svex-alist-vals-of-pairlis$
    (implies (equal (len x) (len y))
             (equal (svex-alist-vals (pairlis$ x y))
                    (svexlist-fix y)))
    :hints(("Goal" :in-theory (enable svexlist-fix pairlis$ svex-alist-vals))))

  (local (defthm svex-alist-eval-redef
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svexlist-eval
                                             svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval
                                             pairlis$)))))

  (defthm svex-alist-rewrite-top-correct
    (equal (svex-alist-eval (svex-alist-rewrite-top x :verbosep verbosep) env)
           (svex-alist-eval x env))
    :hints (("goal" :use ((:instance svexlist-rewrite-correct
                           (masks (svexlist-mask-alist x))))
             :in-theory (disable svexlist-rewrite-correct))
            (acl2::witness)))

  (local (defthm len-of-pairlis$
           (equal (len (pairlis$ x y))
                  (len x))))

  (local (defthm len-of-svex-alist-keys
           (Equal (len (svex-alist-keys x))
                  (len (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix
                                             svex-alist-keys)))))

  (defthm len-of-svex-alist-rewrite-top
    (equal (len (svex-alist-rewrite-top x :Verbosep verbosep))
           (len (svex-alist-fix x))))

  (local (defthm svex-alist-vars-in-terms-of-vals
           (equal (svex-alist-vars x)
                  (svexlist-vars (svex-alist-vals x)))
           :hints(("Goal" :in-theory (enable svex-alist-vars
                                             svexlist-vars
                                             svex-alist-vals)))))
  (defthm svex-lookup-in-pairlis$
    (implies (equal (len x) (len y))
             (iff (svex-lookup v (pairlis$ x y))
                  (member (svar-fix v) (svarlist-fix x))))
    :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix pairlis$))))

  (defthm vars-of-svex-alist-rewrite-top
    (implies (not (member v (svex-alist-vars x)))
             (not (member v (svex-alist-vars (svex-alist-rewrite-top x :verbosep verbosep))))))

  (defthm keys-of-svex-alist-rewrite-top
    (iff (svex-lookup v (svex-alist-rewrite-top x :verbosep verbosep))
         (svex-lookup v x))))


(define svexlist-rewrite-fixpoint ((x svexlist-p) &key ((count natp) '4) (verbosep 'nil))
  :returns (xx svexlist-p)
  :measure (nfix count)
  (b* ((x (mbe :logic (svexlist-fix x) :exec x))
       ((when (zp count)) x)
       (newx (svexlist-rewrite-top x :verbosep verbosep))
       ((when (hons-equal x newx)) x))
    (svexlist-rewrite-fixpoint newx :count (1- count) :verbosep verbosep))
  ///
  (fty::deffixequiv svexlist-rewrite-fixpoint)

  (defthm svexlist-rewrite-fixpoint-correct
    (equal (svexlist-eval (svexlist-rewrite-fixpoint x :count count :verbosep verbosep) env)
           (svexlist-eval x env)))

  (defthm len-of-svexlist-rewrite-fixpoint
    (equal (len (svexlist-rewrite-fixpoint x :count count :verbosep verbosep))
           (len x)))

  (defthm consp-of-svexlist-rewrite-fixpoint
    (equal (consp (svexlist-rewrite-fixpoint x :count count :verbosep verbosep))
           (consp x))
    :hints (("goal" :use len-of-svexlist-rewrite-fixpoint
             :in-theory (e/d (len) (len-of-svexlist-rewrite-fixpoint))
             :expand ((len (svexlist-rewrite-fixpoint x :count count :verbosep verbosep))))))

  (defthm vars-of-svexlist-rewrite-fixpoint
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars (svexlist-rewrite-fixpoint x :count count :verbosep verbosep)))))))


(define svex-alist-rewrite-fixpoint ((x svex-alist-p)
                                     &key
                                     ((count natp) '4)
                                     (verbosep 'nil))
  :returns (xx svex-alist-p)
  (pairlis$ (svex-alist-keys x)
            (svexlist-rewrite-fixpoint (svex-alist-vals x)
                                       :count count :verbosep verbosep))
  ///
  (fty::deffixequiv svex-alist-rewrite-fixpoint)

  (local (defthm svex-alist-eval-redef
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svexlist-eval
                                             svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval
                                             pairlis$)))))

  (defthm svex-alist-rewrite-fixpoint-correct
    (equal (svex-alist-eval (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep) env)
           (svex-alist-eval x env))
    :hints (("goal" :use ((:instance svexlist-rewrite-correct
                           (masks (svexlist-mask-alist x))))
             :in-theory (disable svexlist-rewrite-correct))
            (acl2::witness)))

  (local (defthm len-of-pairlis$
           (equal (len (pairlis$ x y))
                  (len x))))

  (local (defthm len-of-svex-alist-keys
           (Equal (len (svex-alist-keys x))
                  (len (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix
                                             svex-alist-keys)))))

  (defthm len-of-svex-alist-rewrite-fixpoint
    (equal (len (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep))
           (len (svex-alist-fix x))))

  (local (defthm svex-alist-vars-in-terms-of-vals
           (equal (svex-alist-vars x)
                  (svexlist-vars (svex-alist-vals x)))
           :hints(("Goal" :in-theory (enable svex-alist-vars
                                             svexlist-vars
                                             svex-alist-vals)))))

  (defthm vars-of-svex-alist-rewrite-fixpoint
    (implies (not (member v (svex-alist-vars x)))
             (not (member v (svex-alist-vars (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep))))))

  (defthm keys-of-svex-alist-rewrite-fixpoint
    (iff (svex-lookup v (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep))
         (svex-lookup v x))))
