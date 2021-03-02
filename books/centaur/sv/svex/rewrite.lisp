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
(include-book "centaur/nrev/pure" :dir :system)
(include-book "lattice")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (xdoc::set-default-parents rewriting))


(local (std::add-default-post-define-hook :fix))

;; BOZO Separate mask stuff into a different book that doesn't depend on
;; svex-rewrite-rules?


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



(defines svex-multirefs
  :verify-guards nil
  (define svex-multirefs ((x svex-p)
                          (seen svex-key-alist-p)
                          (multiref svex-key-alist-p))
    :returns (mv (seen-out svex-key-alist-p)
                 (multiref-out svex-key-alist-p))
    :measure (svex-count x)
    (b* ((seen (svex-key-alist-fix seen))
         (multiref (svex-key-alist-fix multiref))
         (x (svex-fix x)))
      (svex-case x
        :call
        (b* ((seenp (hons-get x seen))
             ((when seenp)
              (mv seen (svex-set-multiref x multiref)))
             (seen (hons-acons x t seen)))
          (svexlist-multirefs x.args seen multiref))
        :otherwise (mv seen multiref))))
  (define svexlist-multirefs ((x svexlist-p)
                              (seen svex-key-alist-p)
                              (multiref svex-key-alist-p))
    :returns (mv (seen-out svex-key-alist-p)
                 (multiref-out svex-key-alist-p))
    :measure (svexlist-count x)
    (b* ((seen (svex-key-alist-fix seen))
         (multiref (svex-key-alist-fix multiref)))
      (if (atom x)
          (mv seen multiref)
        (b* (((mv seen multiref) (svex-multirefs (car x) seen multiref)))
          (svexlist-multirefs (cdr x) seen multiref)))))
  ///
  (verify-guards svex-multirefs)
  (deffixequiv-mutual svex-multirefs))

(define svexlist-multirefs-top ((x svexlist-p))
  :returns (multirefs svex-key-alist-p)
  (b* (((mv seen multirefs) (svexlist-multirefs x nil nil)))
    (fast-alist-free seen)
    multirefs))


(defines svex-rewrite-fncall
  :verify-guards nil
  (define svex-rewrite-fncall ((clk natp)
                               (mask 4vmask-p)
                               (fn fnsym-p)
                               (args svexlist-p)
                               (in-multirefp)
                               (out-multirefs svex-key-alist-p))
    :returns (xx svex-p)
    :well-founded-relation acl2::nat-list-<
    :measure (list clk 0)
    (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
         (out-multirefs (svex-key-alist-fix out-multirefs))
         ((when (sparseint-equal mask 0)) 0)
         ((mv okp rhs sigma) (svex-rewrite-fncall-once mask fn args in-multirefp out-multirefs))
         ((unless okp) (svex-norm-call fn args)
          ;; (b* ((res (svex-norm-call fn args))
          ;;      (out-multirefs (if in-multirefp (hons-acons res t out-multirefs) out-multirefs)))
          ;;   (mv res out-multirefs))
          )
         ((when (zp clk))
          (cw "Clock ran out!~%")
          (break$)
          (svex-norm-call fn args)))
      (svex-rewrite-under-subst (1- clk) mask rhs sigma in-multirefp out-multirefs)))

  (define svex-rewrite-under-subst ((clk natp)
                                    (mask 4vmask-p)
                                    (x svex-p)
                                    (sigma svex-alist-p)
                                    (in-multirefp)
                                    (out-multirefs svex-key-alist-p))
    :returns (xx svex-p)
    :guard (subsetp-equal (svex-vars x) (svex-alist-keys sigma))
    :measure (list clk (svex-count x))
    (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
         (out-multirefs (svex-key-alist-fix out-multirefs))
         ((when (sparseint-equal mask 0)) 0))
      (svex-case x
        :var (mbe :logic (svex-fix (svex-lookup x.name sigma))
                      :exec (svex-lookup x.name sigma))
        :quote (svex-quote (4vec-mask-to-zero mask x.val))
        :call (b* ((masks (svex-argmasks -1 x.fn x.args))
                   ;; Note: we could use mask instead of -1 above, but in cases
                   ;; where the rewrites of different terms have common
                   ;; subterms, it might cause them to diverge.
                   ;; BOZO We should do experiments with this
                   (args (svexlist-rewrite-under-subst clk masks x.args sigma out-multirefs)))
                (svex-rewrite-fncall clk mask x.fn args in-multirefp out-multirefs)))))

  (define svexlist-rewrite-under-subst ((clk natp)
                                        (masks 4vmasklist-p)
                                        (x svexlist-p)
                                        (sigma svex-alist-p)
                                        (out-multirefs svex-key-alist-p))
    :returns (xx svexlist-p)
    :measure (list clk (svexlist-count x))
    :guard (and (equal (len x) (len masks))
                (subsetp-equal (svexlist-vars x) (svex-alist-keys sigma)))
    (b* ((out-multirefs (svex-key-alist-fix out-multirefs)))
      (if (atom x)
          nil
        (cons (svex-rewrite-under-subst clk (car masks) (car x) sigma nil out-multirefs)
              (svexlist-rewrite-under-subst clk (cdr masks) (cdr x) sigma out-multirefs)))))
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
      (equal (4vec-mask mask (svex-eval (svex-rewrite-fncall clk mask fn args in-multirefp out-multirefs) env))
             (4vec-mask mask (svex-eval (svex-call fn args) env)))
      :hints ('(:expand ((svex-rewrite-fncall clk mask fn args in-multirefp out-multirefs))))
      :flag svex-rewrite-fncall)
    (defthm svex-rewrite-under-subst-rw
      (equal (4vec-mask mask (svex-eval (svex-rewrite-under-subst clk mask x sigma in-multirefp out-multirefs) env))
             (4vec-mask mask (svex-eval (svex-subst x sigma) env)))
      :hints ('(:expand ((svex-rewrite-under-subst clk mask x sigma in-multirefp out-multirefs)
                         (:free (env) (svex-eval x env)))))
      :flag svex-rewrite-under-subst)
    (defthm svexlist-rewrite-under-subst-rw
      (equal (4veclist-mask masks (svexlist-eval
                                   (svexlist-rewrite-under-subst clk masks x sigma out-multirefs)
                                   env))
             (4veclist-mask masks (svexlist-eval (svexlist-subst x sigma) env)))
      :hints ('(:expand ((svexlist-rewrite-under-subst clk masks x sigma out-multirefs))))
      :flag svexlist-rewrite-under-subst))

  (defthm svex-rewrite-fncall-nomasks-correct
    (equal (svex-eval (svex-rewrite-fncall clk -1 fn args in-multirefp out-multirefs) env)
           (svex-eval (svex-call fn args) env))
    :hints (("goal" :use ((:instance svex-rewrite-fncall-rw (mask -1)))
             :in-theory (e/d (4vec-mask) (svex-rewrite-fncall-rw)))))


  (defthm-svex-rewrite-fncall-flag
    (defthm svex-rewrite-fncall-vars
      (implies (not (member v (svexlist-vars args)))
               (not (member v (svex-vars (svex-rewrite-fncall clk mask fn args in-multirefp out-multirefs)))))
      :hints ('(:expand ((svex-rewrite-fncall clk mask fn args in-multirefp out-multirefs))))
      :flag svex-rewrite-fncall)
    (defthm svex-rewrite-under-subst-vars
      (implies (not (member v (svex-alist-vars sigma)))
               (not (member v (svex-vars (svex-rewrite-under-subst clk mask x sigma in-multirefp out-multirefs)))))
      :hints ('(:expand ((svex-rewrite-under-subst clk mask x sigma in-multirefp out-multirefs)
                         (:free (env) (svex-eval x env)))))
      :flag svex-rewrite-under-subst)
    (defthm svexlist-rewrite-under-subst-vars
      (implies (not (member v (svex-alist-vars sigma)))
               (not (member v (svexlist-vars (svexlist-rewrite-under-subst clk masks x sigma out-multirefs)))))
      :hints ('(:expand ((svexlist-rewrite-under-subst clk masks x sigma out-multirefs))))
      :flag svexlist-rewrite-under-subst)))

(defsection svcall-rw
  :parents (svex)
  :short "Safely construct an @(see svex) for a function call, with rewriting."

  :long "<p>@('(call svcall-rw)') constructs an @(see svex) that is equivalent
to the application of @('fn') to the given @('args').  This macro is ``safe''
in that, at compile time, it ensures that @('fn') is one of the known @(see
functions) and that it is being given the right number of arguments.</p>

@(def svcall-rw)"

  (defun svcall-rw-fn (fn args)
    (declare (xargs :guard t))
    (b* ((look (assoc fn *svex-op-table*))
         ((unless look)
          (er hard? 'svcall "Svex function doesn't exist: ~x0" fn))
         (formals (third look))
         ((unless (eql (len formals) (len args)))
          (er hard? 'svcall "Wrong arity for call of ~x0" fn)))
      `(svex-rewrite-fncall 1000 -1 ',fn (list . ,args) t t)))

  (defmacro svcall-rw (fn &rest args)
    (svcall-rw-fn fn args)))





(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
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
      :flag svexlist-toposort))

  (define svexlist-count-calls-aux ((x svexlist-p) (acc natp))
    :returns (call-count natp :rule-classes :type-prescription)
    (if (atom x)
        (lnfix acc)
      (svexlist-count-calls-aux (cdr x)
                                (+ (let ((x1 (car x)))
                                     (svex-case x1 :call 1 :otherwise 0))
                                   (lnfix acc)))))

  (define svexlist-count-calls ((x svexlist-p))
    ;; Has nothing to do with svex-toposort, but you can use
    ;; svexlist-count-calls of svex-toposort instead of svex-opcount.
    ;; Tail recursive because it blew up on us before.
    :returns (call-count natp :rule-classes :type-prescription)
    :inline t
    (svexlist-count-calls-aux x 0))

  (defthm-svex-toposort-flag
    (defthm member-vars-of-svex-toposort
      (implies (and (not (member v (svex-vars x)))
                    (not (member v (svexlist-vars sort))))
               (not (member v (svexlist-vars (mv-nth 0 (svex-toposort x sort contents))))))
      :hints ('(:expand ((svex-vars x)
                         (svex-toposort x sort contents))))
      :flag svex-toposort)
    (defthm member-vars-of-svexlist-toposort
      (implies (and (not (member v (svexlist-vars x)))
                    (not (member v (svexlist-vars sort))))
               (not (member v (svexlist-vars (mv-nth 0 (svexlist-toposort x sort contents))))))
      :hints ('(:expand ((svexlist-vars x)
                         (svexlist-toposort x sort contents))))
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



(fty::defmap svex-mask-alist :key-type svex :val-type 4vmask :true-listp t)

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
  (b* ((look (hons-get (svex-fix x) al)))
    (if look
        (4vmask-fix (cdr look))
      0))
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
    (if (mbt (and (consp (car x)) (svex-p (caar x))))
        (cons (caar x)
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

  (defcong sparseint-equal equal (sparseint-val x) 1)

  (defun 4vmask-equal (x y)
    (sparseint-equal (4vmask-fix x) (4vmask-fix y)))

  (defequiv 4vmask-equal)

  (local (defthm 4vmask-union-all
           (implies (sparseint-equal (4vmask-fix y) -1)
                    (sparseint-equal (4vmask-union x y)
                                     -1))
           :hints (("goal" :expand ((4vmask-union x y))))))

  (local (defthm 4vmask-union-neg1
           (equal (4vmask-union x -1)
                  -1)
           :hints (("goal" :expand ((4vmask-union x -1)
                                    (sparseint-bitor (4vmask-fix x) -1)
                                    (:free (op) (sparseint-binary-bitop op (4vmask-fix x) -1))
                                    (:free (op) (bitops::sparseint$-binary-bitop op (4vmask-fix x) -1))
                                    (:free (op height) (bitops::sparseint$-binary-bitop-offset op (4vmask-fix x) height 0 -1 0))
                                    (:free (op height) (bitops::sparseint$-binary-bitop-int op 0 (4vmask-fix x) height -1))
                                    (:free (op x height) (bitops::sparseint$-unary-bitop op x height)))))))

  (local (defcong 4vmask-equal 4vmask-equal (4vmask-union x y) 1
           :hints(("Goal" :in-theory (enable 4vmask-union)))))
  (local (defcong 4vmask-equal 4vmask-equal (4vmask-union x y) 2
           :hints(("Goal" :in-theory (enable 4vmask-union)))))

  (defthm svex-args-apply-masks-lookup-when-all
    (implies (sparseint-equal (svex-mask-lookup x mask-al) -1)
             (sparseint-equal (svex-mask-lookup x (svex-args-apply-masks args masks mask-al))
                              -1)))

  (defthm svex-args-apply-masks-lookup-when-neg1
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
                  (equal (sparseint-val (svex-mask-lookup (car x) mask-al)) 0))
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
       ((when (sparseint-equal mask 0))
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
    (implies (sparseint-equal (svex-mask-lookup y mask-al) -1)
             (sparseint-equal (svex-mask-lookup y (svexlist-compute-masks x mask-al))
                              -1)))

  (defthm svexlist-compute-masks-lookup-when-neg1
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





(defalist svex-svex-memo :key-type svex :val-type svex)

(defthm svex-p-of-lookup-in-svex-svex-memo
  (implies (and (svex-svex-memo-p memo)
                (hons-assoc-equal k memo))
           (svex-p (cdr (hons-assoc-equal k memo)))))


(defsection svex-rewrite-memo-correct
  (defun-sk svex-rewrite-memo-correct1 (x masks env)
    (forall (key)
            (b* ((lookup (hons-assoc-equal key x))
                 (mask (svex-mask-lookup key masks))
                 (val (cdr lookup)))
              (implies lookup
                       (equal (4vec-mask mask (svex-eval val env))
                              (4vec-mask mask (svex-eval key env)))))))

  (in-theory (disable svex-rewrite-memo-correct1
                      svex-rewrite-memo-correct1-necc))


  (define svex-rewrite-memo-correct ((x svex-svex-memo-p)
                                     (masks svex-mask-alist-p)
                                     (env svex-env-p))
    (ec-call (svex-rewrite-memo-correct1 (svex-svex-memo-fix x)
                                         (svex-mask-alist-fix masks)
                                         (svex-env-fix env)))
    ///
    (defthm svex-rewrite-memo-correct-of-empty
      (implies (atom x)
               (svex-rewrite-memo-correct x masks env))
      :hints(("Goal" :in-theory (enable svex-rewrite-memo-correct
                                        svex-rewrite-memo-correct1)))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm svex-rewrite-memo-correct-implies
      (implies (svex-rewrite-memo-correct x masks env)
               (b* ((lookup (hons-assoc-equal key (svex-svex-memo-fix x)))
                    (mask (svex-mask-lookup key masks))
                    (val (cdr lookup)))
                 (implies lookup
                          (equal (4vec-mask mask (svex-eval val env))
                                 (4vec-mask mask (svex-eval key env))))))
      :hints(("Goal" :use ((:instance svex-rewrite-memo-correct1-necc
                            (x (svex-svex-memo-fix x))
                            (key key)
                            (masks (svex-mask-alist-fix masks))
                            (env (svex-env-fix env)))))))

    (defthm svex-rewrite-memo-correct-implies-fix
      (implies (svex-rewrite-memo-correct x masks env)
               (b* ((lookup (hons-assoc-equal (svex-fix key) (svex-svex-memo-fix x)))
                    (mask (svex-mask-lookup key masks))
                    (val (cdr lookup)))
                 (implies lookup
                          (equal (4vec-mask mask (svex-eval val env))
                                 (4vec-mask mask (svex-eval key env))))))
      :hints(("Goal" :use ((:instance svex-rewrite-memo-correct1-necc
                            (x (svex-svex-memo-fix x))
                            (key (svex-fix key))
                            (masks (svex-mask-alist-fix masks))
                            (env (svex-env-fix env)))))))

    (deffixequiv svex-rewrite-memo-correct)

    (defthm svex-rewrite-memo-correct-cons
      (implies (svex-rewrite-memo-correct x masks env)
               (iff (svex-rewrite-memo-correct
                     (cons (cons y y1) x) masks env)
                    (equal (4vec-mask (svex-mask-lookup y masks)
                                      (svex-eval y env))
                           (4vec-mask (svex-mask-lookup y masks)
                                      (svex-eval y1 env)))))
      :hints (("goal" :cases (svex-rewrite-memo-correct
                     (cons (cons y y1) x) masks env)
               :in-theory (disable svex-rewrite-memo-correct))
              (and stable-under-simplificationp
                   (let ((term (assoc 'svex-rewrite-memo-correct clause)))
                     (and term
                          `(:expand (,term)))))
              (and stable-under-simplificationp
                   (let ((term (assoc 'svex-rewrite-memo-correct1 clause)))
                     (and term
                          `(:expand (,term)))))
              (and stable-under-simplificationp
                   '(:use ((:instance svex-rewrite-memo-correct-implies
                            (x (cons (cons y y1) x))
                            (key (svex-fix y))))
                     :in-theory (disable svex-rewrite-memo-correct-implies
                                         svex-rewrite-memo-correct))))
      :otf-flg t)))

(defsection svex-rewrite-memo-vars-ok
  (defun-sk svex-rewrite-memo-vars-ok1 (x var)
    (forall (key)
            (b* ((lookup (hons-assoc-equal key x))
                 (val (cdr lookup)))
              (implies (and lookup
                            (not (member var (svex-vars key))))
                       (not (member var (svex-vars val))))))
    :rewrite :direct)

  (in-theory (disable svex-rewrite-memo-vars-ok1
                      svex-rewrite-memo-vars-ok1-necc))

  (define svex-rewrite-memo-vars-ok ((x svex-svex-memo-p)
                                     (var))
    (ec-call (svex-rewrite-memo-vars-ok1 (svex-svex-memo-fix x)
                                         var))
    ///
    (defthm svex-rewrite-memo-vars-ok-of-empty
      (implies (atom atom)
               (svex-rewrite-memo-vars-ok atom var))
      :hints(("Goal" :in-theory (enable svex-rewrite-memo-vars-ok
                                        svex-rewrite-memo-vars-ok1)))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm svex-rewrite-memo-vars-ok-implies
      (implies (svex-rewrite-memo-vars-ok x var)
               (b* ((x (svex-svex-memo-fix x))
                    (lookup (hons-assoc-equal key x))
                    (val (cdr lookup)))
                 (implies (and lookup
                               (not (member var (svex-vars key))))
                          (not (member var (svex-vars val))))))
      :hints(("Goal" :use ((:instance svex-rewrite-memo-vars-ok1-necc
                            (x (svex-svex-memo-fix x))
                            (var var))))))


    (deffixequiv svex-rewrite-memo-vars-ok)

    

    (defthm svex-rewrite-memo-vars-ok-cons-1
      (implies (and (svex-rewrite-memo-vars-ok x var)
                    (member var (svex-vars y)))
               (svex-rewrite-memo-vars-ok
                (cons (cons y y1) x) var))
      :hints (("goal" :expand ((:free (y y1 x var)
                                (svex-rewrite-memo-vars-ok1
                                 (cons (cons y y1) x) var))))))

    (defthm svex-rewrite-memo-vars-ok-cons-2
      (implies (and (svex-rewrite-memo-vars-ok x var)
                    (not (member var (svex-vars y1))))
               (svex-rewrite-memo-vars-ok
                (cons (cons y y1) x) var))
      :hints (("goal" :expand ((:free (y y1 x var)
                                (svex-rewrite-memo-vars-ok1
                                 (cons (cons y y1) x) var))))))))


(defines svex-rewrite
  :verify-guards nil
  :parents (rewriting)
  (define svex-rewrite ((x svex-p)
                        (masks svex-mask-alist-p)
                        (multirefs svex-key-alist-p)
                        (out-multirefs svex-key-alist-p)
                        (memo svex-svex-memo-p))
    :short "Recursively rewrite an @(see svex) expression."
    :returns (mv (xx svex-p)
                 (out-multirefs svex-key-alist-p)
                 (memo svex-svex-memo-p))
    :measure (svex-count x)
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (masks (svex-mask-alist-fix masks))
         (multirefs (svex-key-alist-fix multirefs))
         (out-multirefs (svex-key-alist-fix out-multirefs))
         (memo (svex-svex-memo-fix memo))

         (kind (svex-kind x))
         (mask (svex-mask-lookup x masks))
         ((when (eq kind :quote))
          ;; Normalizing constants under the global masks may help to make
          ;; terms like (logand x #xFFFF0000) and (logand x #xFFFFFFFF) turn
          ;; into the same logand, if it turns out that we never care about the
          ;; lower 16 bits.
          (mv (svex-quote (4vec-mask-to-zero mask (svex-quote->val x))) out-multirefs memo))
         ((when (eql mask 0)) (mv 0 out-multirefs memo))
         ((when (eq kind :var)) (mv x out-multirefs memo))
         (multirefp (svex-get-multiref x multirefs))
         (memo? (and multirefp (hons-get x memo)))
         ((when memo?)
          (mv (cdr memo?) out-multirefs memo))
         ((svex-call x) x)
         ((mv args out-multirefs memo)
          (svexlist-rewrite x.args masks multirefs out-multirefs memo))
         (res (svex-rewrite-fncall 10000 mask (svex-call->fn x) args multirefp out-multirefs))
         ((unless multirefp)
          (mv res out-multirefs memo)))
      (mv res
          (svex-set-multiref res out-multirefs)
          (hons-acons x res memo))))

  (define svexlist-rewrite ((x svexlist-p)
                            (masks svex-mask-alist-p)
                            (multirefs svex-key-alist-p)
                            (out-multirefs svex-key-alist-p)
                            (memo svex-svex-memo-p))
    :short "Recursively rewrite a list of @(see svex) expressions."
    :returns (mv (xx svexlist-p)
                 (out-multirefs svex-key-alist-p)
                 (memo svex-svex-memo-p))
    :measure (svexlist-count x)
    (b* ((out-multirefs (svex-key-alist-fix out-multirefs))
         (memo (svex-svex-memo-fix memo))
         ((When (atom x)) (mv nil out-multirefs memo))
         ((mv car out-multirefs memo)
          (svex-rewrite (car x) masks multirefs out-multirefs memo))
         ((mv cdr out-multirefs memo)
          (svexlist-rewrite (cdr x) masks multirefs out-multirefs memo)))
      (mv (cons car cdr) out-multirefs memo)))
  ///
  (verify-guards svex-rewrite)

  (fty::deffixequiv-mutual svex-rewrite
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm-svex-rewrite-flag len-of-svexlist-rewrite
    (defthm len-of-svexlist-rewrite
      (equal (len (mv-nth 0 (svexlist-rewrite x masks multirefs out-multirefs memo)))
             (len x))
      :flag svexlist-rewrite)
    :skip-others t)

  (local (acl2::defexample svex-argmasks-okp-example
           :pattern (4vec-mask mask (svex-apply fn (svexlist-eval args env)))
           :templates (env (svexlist-eval args env))
           :instance-rulename svex-argmasks-okp-instancing))

  (defthm-svex-rewrite-flag
    (defthm svex-rewrite-correct
      (b* (((mv res out-multirefs1 memo1) (svex-rewrite x masks multirefs out-multirefs memo))
           (mask (svex-mask-lookup x masks)))
        (implies (and (svex-rewrite-memo-correct memo masks env)
                      (svex-mask-alist-complete masks))
                 (and (svex-rewrite-memo-correct memo1 masks env)
                      (equal (4vec-mask mask (svex-eval res env))
                             (4vec-mask mask (svex-eval x env))))))
      :hints ('(:expand ((:free (f a env) (svex-eval (svex-call f a) env))
                         (:free (env) (svex-eval x env))
                         (svex-rewrite x masks multirefs out-multirefs memo))
                :do-not-induct t)
              (acl2::witness)
              (acl2::witness))
      :flag svex-rewrite)
    (defthm svexlist-rewrite-correct
      (b* (((mv res out-multirefs1 memo1) (svexlist-rewrite x masks multirefs out-multirefs memo))
           (argmasks (svex-argmasks-lookup x masks)))
        (implies (and (svex-rewrite-memo-correct memo masks env)
                      (svex-mask-alist-complete masks))
                 (and (svex-rewrite-memo-correct memo1 masks env)
                      (equal (4veclist-mask argmasks (svexlist-eval res env))
                             (4veclist-mask argmasks (svexlist-eval x env))))))
      :hints ('(:expand ((svex-argmasks-lookup x masks)
                         (svexlist-rewrite x masks multirefs out-multirefs memo))))
      :flag svexlist-rewrite))

  (defthm-svex-rewrite-flag
    (defthm svex-rewrite-vars
      (b* (((mv res out-multirefs1 memo1) (svex-rewrite x masks multirefs out-multirefs memo)))
        (implies (svex-rewrite-memo-vars-ok memo v)
                 (and (svex-rewrite-memo-vars-ok memo1 v)
                      (implies (not (member v (svex-vars x)))
                               (not (member v (svex-vars res)))))))
      :hints ('(:expand ((svex-vars x)
                         (svex-rewrite x masks multirefs out-multirefs memo))
                :do-not-induct t)
              ;; (acl2::witness)
              ;; (acl2::witness)
              )
      :flag svex-rewrite)
    (defthm svexlist-rewrite-vars
      (b* (((mv res out-multirefs1 memo1) (svexlist-rewrite x masks multirefs out-multirefs memo)))
        (implies (svex-rewrite-memo-vars-ok memo v)
                 (and (svex-rewrite-memo-vars-ok memo1 v)
                      (implies (not (member v (svexlist-vars x)))
                               (not (member v (svexlist-vars res)))))))
      :hints ('(:expand ((svexlist-rewrite x masks multirefs out-multirefs memo))))
      :flag svexlist-rewrite masks))

  (defthm-svex-rewrite-flag
    (defthm true-listp-of-svexlist-rewrite
      (true-listp (mv-nth 0 (svexlist-rewrite x masks multirefs out-multirefs memo)))
      :flag svexlist-rewrite)
    :skip-others t)
  (defthm-svex-rewrite-flag
    (defthm svexlist-rewrite-breakdown
      (equal (list (mv-nth 0 (svexlist-rewrite x masks multirefs out-multirefs memo))
                   (mv-nth 1 (svexlist-rewrite x masks multirefs out-multirefs memo))
                   (mv-nth 2 (svexlist-rewrite x masks multirefs out-multirefs memo)))
             (svexlist-rewrite x masks multirefs out-multirefs memo))
      :hints ('(:expand ((svexlist-rewrite x masks multirefs out-multirefs memo))))
      :flag svexlist-rewrite)
    :skip-others t))






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
         (args (svexlist-maskfree-rewrite x.args)))
         ;; (argmasks (svex-argmasks mask x.fn args))
         ;; (args (svex-args-rewrite-under-masks args argmasks))
      (svex-rewrite-fncall 1000 -1 (svex-call->fn x) args t t)))

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
                       (args (svexlist-maskfree-rewrite (svex-call->args x)))
                       (in-multirefp t) (out-multirefs t)))
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

(define svexlist-maskfree-rewrite-nrev ((x svexlist-p)
                                        acl2::nrev)
  :returns new-nrev
  (b* ((acl2::nrev (acl2::nrev-fix acl2::nrev))
       ((when (atom x)) acl2::nrev)
       (first (svex-maskfree-rewrite (car x)))
       (acl2::nrev (acl2::nrev-push first acl2::nrev)))
    (svexlist-maskfree-rewrite-nrev (cdr x) acl2::nrev))
  ///
  (defret svexlist-maskfree-rewrite-nrev-removal
    (b* ((out-spec (svexlist-maskfree-rewrite x)))
      (equal new-nrev
             (append acl2::nrev out-spec)))
    :hints(("Goal" :induct t
            :expand ((svexlist-maskfree-rewrite x))))))

(define svexlist-maskfree-rewrite-top ((x svexlist-p))
  :enabled t
  (mbe :logic (svexlist-maskfree-rewrite x)
       :exec (acl2::with-local-nrev (svexlist-maskfree-rewrite-nrev x acl2::nrev))))
       


(define svexlist-mask-acons-rev ((x svexlist-p) (mask 4vmask-p) (al svex-mask-alist-p))
  (if (atom x)
      (svex-mask-alist-fix al)
    (svexlist-mask-acons-rev (cdr x) mask (svex-mask-acons (car x) mask al))))


(define svexlist-mask-acons ((x svexlist-p) (mask 4vmask-p) (al svex-mask-alist-p))
  :verify-guards nil
  :returns (al svex-mask-alist-p)
  (mbe :logic (if (atom x)
                  (mbe :logic (svex-mask-alist-fix al) :exec al)
                (svex-mask-acons (car x) mask (svexlist-mask-acons (cdr x) mask al)))
       :exec (svexlist-mask-acons-rev (rev x) mask al))
  ///

  (local (defthm svexlist-mask-acons-rev-elim
           (equal (svexlist-mask-acons-rev x mask al)
                  (svexlist-mask-acons (rev x) mask al))
           :hints(("Goal" :in-theory (enable svexlist-mask-acons-rev)))))

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


(define svexlist-mask-alist/toposort ((x svexlist-p))
  :returns (mv (mask-al svex-mask-alist-p)
               (toposort (and (svexlist-p toposort)
                              (svexlist-toposort-p toposort))))
  (b* (((mv toposort al) (cwtime (svexlist-toposort x nil nil) :mintime 1))
       (- (fast-alist-free al))
       (mask-al
        (cwtime (svexlist-compute-masks toposort (svexlist-mask-acons x -1 nil)) :mintime 1)))
    (mv mask-al toposort))
  ///
  (fty::deffixequiv svexlist-mask-alist/toposort)

  (defret svexlist-mask-alist/toposort-complete
    (svex-mask-alist-complete mask-al))

  (defret svexlist-mask-alist/toposort-lookup
    (implies (member-equal (svex-fix y) (svexlist-fix x))
             (equal (svex-mask-lookup y mask-al)
                    -1)))

  (defret svex-argmasks-lookup-of-svexlist-mask-alist/toposort
    (implies (subsetp-equal (svexlist-fix y) (svexlist-fix x))
             (equal (svex-argmasks-lookup y mask-al)
                    (replicate (len y) -1)))
    :hints(("Goal" :induct (len y)
            :in-theory (e/d (replicate) (svexlist-mask-alist/toposort))
            :expand ((svexlist-fix y)
                     (:free (x) (svex-argmasks-lookup y x)))))))


(define svexlist-mask-alist ((x svexlist-p))
  :returns (mask-al svex-mask-alist-p)
  (b* (((mv mask-al ?toposort) (svexlist-mask-alist/toposort x)))
    mask-al)
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
                     (:free (x) (svex-argmasks-lookup y x))))))

  (defthm svexlist-mask-alist/toposort-to-mask-alist
    (equal (svexlist-mask-alist/toposort x)
           (mv (svexlist-mask-alist x)
               (mv-nth 0 (svexlist-toposort x nil nil))))
    :hints(("Goal" :in-theory (enable svexlist-mask-alist/toposort)))))

;; (define svexlist-mask-alist-for-given-masks ((x svexlist-p) (masks svex-mask-alist-p))
;;   (b* (((mv toposort al


(define svex-rewrite-top ((x svex-p))
  :returns (xx svex-p)
  (b* ((list (list x))
       (masks (svexlist-mask-alist list))
       (multirefs (svexlist-multirefs-top list))
       ((mv res out-multirefs memo)
        (svex-rewrite x masks multirefs nil nil)))
    (fast-alist-free out-multirefs)
    (fast-alist-free memo)
    (fast-alist-free masks)
    (fast-alist-free multirefs)
    res)
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
                           (masks (svexlist-mask-alist (list x)))
                           (memo nil)
                           (multirefs (svexlist-multirefs-top (list x)))
                           (out-multirefs nil)))
             :in-theory (disable svex-rewrite-correct))
            (acl2::witness)))

  (defthm vars-of-svex-rewrite-top
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-rewrite-top x)))))))





(define svexlist-rewrite-under-masks ((x svexlist-p) (masks svex-mask-alist-p)
                                      &key (verbosep 'nil))
  :short "Rewrite the list of expressions under the provided mask alist, which should already be complete."
  :returns (xx svexlist-p)
  (b* ((multirefs (svexlist-multirefs-top x))
       (- (and verbosep (cw "opcount before rewrite: ~x0 multiply-referenced: ~x1~%"
                            (cwtime (svexlist-opcount x))
                            (len multirefs))))
       ((mv new-x out-multirefs memo)
        (cwtime (svexlist-rewrite x masks multirefs nil nil) :mintime 1))
       (- (clear-memoize-table 'svex-rewrite)
          (fast-alist-free memo)
          (fast-alist-free out-multirefs)
          (fast-alist-free multirefs)
          (and verbosep (cw "opcount after rewrite: ~x0~%" (cwtime (svexlist-opcount new-x)))))
       ;; (x (cwtime (svexlist-normalize-concats x)))
       )
    ;; (and verbosep (cw "opcount after norm-concats: ~x0~%" (svexlist-opcount x)))
    new-x)
  ///
  (fty::deffixequiv svexlist-rewrite-under-masks)

  (defthm svexlist-rewrite-under-masks-correct
    (implies (svex-mask-alist-complete masks)
             (equal (4veclist-mask (svex-argmasks-lookup x masks)
                                   (svexlist-eval (svexlist-rewrite-under-masks x masks :verbosep verbosep) env))
                    (4veclist-mask (svex-argmasks-lookup x masks)
                                   (svexlist-eval x env))))
    :hints (("goal" :use ((:instance svexlist-rewrite-correct
                           (multirefs (svexlist-multirefs-top x))
                           (out-multirefs nil) (memo nil)))
             :in-theory (disable svexlist-rewrite-correct))
            (acl2::witness)))

  (defthm len-of-svexlist-rewrite-under-masks
    (equal (len (svexlist-rewrite-under-masks x masks :verbosep verbosep))
           (len x)))

  (defthm vars-of-svexlist-rewrite-under-masks
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars (svexlist-rewrite-under-masks x masks :verbosep verbosep)))))))

(define svexlist-rewrite-nrev ((x svexlist-p)
                               (masks svex-mask-alist-p)
                               (multirefs svex-key-alist-p)
                               (out-multirefs svex-key-alist-p)
                               (memo svex-svex-memo-p)
                               acl2::nrev)
  :returns (mv new-nrev
               (out-multirefs1 svex-key-alist-p)
               (memo1 svex-svex-memo-p))
  (if (atom x)
      (b* ((acl2::nrev (acl2::nrev-fix acl2::nrev)))
        (mv acl2::nrev
            (svex-key-alist-fix out-multirefs)
            (svex-svex-memo-fix memo)))
    (b* (((mv first out-multirefs memo) (svex-rewrite (car x) masks multirefs out-multirefs memo))
         (acl2::nrev (acl2::nrev-push first acl2::nrev)))
      (svexlist-rewrite-nrev (cdr x) masks multirefs out-multirefs memo acl2::nrev)))
  ///
  (defret svexlist-rewrite-nrev-removal
    (b* (((mv out-spec out-multirefs1-spec memo1-spec)
          (svexlist-rewrite x masks multirefs out-multirefs memo)))
      (and (equal new-nrev
                  (append acl2::nrev out-spec))
           (equal out-multirefs1 out-multirefs1-spec)
           (equal memo1 memo1-spec)))
    :hints(("Goal" :induct t
            :expand ((svexlist-rewrite x masks multirefs out-multirefs memo))))))
  


(define svexlist-rewrite-top ((x svexlist-p) &key (verbosep 'nil))
  :returns (xx svexlist-p)
  (b* (((mv masks toposort) (svexlist-mask-alist/toposort x))
       (multirefs (svexlist-multirefs-top x))
       (multiref-count (len multirefs))
       (- (and verbosep (cw "opcount before rewrite: ~x0 multiply-referenced: ~x1~%"
                            (svexlist-count-calls toposort)
                            multiref-count)))
       ((mv new-x out-multirefs memo)
        (mbe :logic (svexlist-rewrite x masks multirefs
                                      ;; fast alist sizes
                                      multiref-count multiref-count)
             :exec (with-local-stobj acl2::nrev
                     (mv-let (new-x out-multirefs memo acl2::nrev)
                       (b* (((mv acl2::nrev out-multirefs memo)
                             (cwtime (svexlist-rewrite-nrev
                                      x masks multirefs
                                      multiref-count ;; out-multirefs
                                      multiref-count ;; memo
                                      acl2::nrev)
                                     :mintime 1))
                            ((mv new-x acl2::nrev) (acl2::nrev-finish acl2::nrev)))
                         (mv new-x out-multirefs memo acl2::nrev))
                       (mv new-x out-multirefs memo)))))
       (- (clear-memoize-table 'svex-rewrite)
          (fast-alist-free masks)
          (fast-alist-free memo)
          (fast-alist-free out-multirefs)
          (fast-alist-free multirefs)
          (and verbosep (cw "opcount after rewrite: ~x0~%" (cwtime (svexlist-opcount new-x)))))
       ;; (x (cwtime (svexlist-normalize-concats x)))
       )
    ;; (and verbosep (cw "opcount after norm-concats: ~x0~%" (svexlist-opcount x)))
    new-x)
  ///
  (fty::deffixequiv svexlist-rewrite-top)

  

  (defthm svexlist-rewrite-top-correct
    (equal (svexlist-eval (svexlist-rewrite-top x :verbosep verbosep) env)
           (svexlist-eval x env))
    :hints (("goal" :use ((:instance svexlist-rewrite-correct
                           (masks (svexlist-mask-alist x))
                           (multirefs (svexlist-multirefs-top x))
                           (out-multirefs (len (svexlist-multirefs-top x)))
                           (memo (len (svexlist-multirefs-top x)))))
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

  ;; (defthm svex-alist-keys-of-pairlis$
  ;;   (equal (svex-alist-keys (pairlis$ x y))
  ;;          (svarlist-fix x))
  ;;   :hints(("Goal" :in-theory (enable svarlist-fix pairlis$ svex-alist-keys))))

  ;; (defthm svex-alist-vals-of-pairlis$
  ;;   (implies (equal (len x) (len y))
  ;;            (equal (svex-alist-vals (pairlis$ x y))
  ;;                   (svexlist-fix y)))
  ;;   :hints(("Goal" :in-theory (enable svexlist-fix pairlis$ svex-alist-vals))))

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
  ;; (defthm svex-lookup-in-pairlis$
  ;;   (implies (equal (len x) (len y))
  ;;            (iff (svex-lookup v (pairlis$ x y))
  ;;                 (member (svar-fix v) (svarlist-fix x))))
  ;;   :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix pairlis$))))

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

  (defret svexlist-rewrite-fixpoint-correct
    (equal (svexlist-eval xx env)
           (svexlist-eval x env)))

  (defret len-of-svexlist-rewrite-fixpoint
    (equal (len xx)
           (len x)))

  (defret consp-of-svexlist-rewrite-fixpoint
    (equal (consp xx)
           (consp x))
    :hints (("goal" :use len-of-svexlist-rewrite-fixpoint
             :in-theory (e/d (len) (len-of-svexlist-rewrite-fixpoint
                                    svexlist-rewrite-fixpoint))
             :expand ((len (svexlist-rewrite-fixpoint x :count count :verbosep verbosep))))))

  (defret vars-of-svexlist-rewrite-fixpoint
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars xx))))))


(define svexlist-maybe-rewrite-fixpoint ((x svexlist-p)
                                         (do-rewrite)
                                         &key ((count natp) '4) (verbosep 'nil))
  :returns (xx svexlist-p)
  (if do-rewrite
      (svexlist-rewrite-fixpoint x :count count :verbosep verbosep)
    (svexlist-fix x))
  ///
  (fty::deffixequiv svexlist-maybe-rewrite-fixpoint)

  (defret svexlist-maybe-rewrite-fixpoint-correct
    (equal (svexlist-eval xx env)
           (svexlist-eval x env)))

  (defret len-of-svexlist-maybe-rewrite-fixpoint
    (equal (len xx)
           (len x)))

  (defret consp-of-svexlist-maybe-rewrite-fixpoint
    (equal (consp xx)
           (consp x))
    :hints (("goal" :use len-of-svexlist-maybe-rewrite-fixpoint
             :in-theory (e/d (len) (len-of-svexlist-maybe-rewrite-fixpoint
                                    svexlist-maybe-rewrite-fixpoint))
             :expand ((len (svexlist-maybe-rewrite-fixpoint x do-rewrite :count count :verbosep verbosep))))))

  (defret vars-of-svexlist-maybe-rewrite-fixpoint
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars xx))))))



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


(define svex-alist-maybe-rewrite-fixpoint ((x svex-alist-p)
                                           (do-rewrite)
                                           &key
                                           ((count natp) '4)
                                           (verbosep 'nil))
  :short "Rewrites the alist, but only if do-rewrite is non-nil."
  :returns (xx svex-alist-p)
  (if do-rewrite
      (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)
    (svex-alist-fix x))
  ///
  (fty::deffixequiv svex-alist-maybe-rewrite-fixpoint)

  (defret svex-alist-maybe-rewrite-fixpoint-correct
    (equal (svex-alist-eval xx env)
           (svex-alist-eval x env)))


  (defret len-of-svex-alist-maybe-rewrite-fixpoint
    (equal (len xx)
           (len (svex-alist-fix x))))

  (defret vars-of-svex-alist-maybe-rewrite-fixpoint
    (implies (not (member v (svex-alist-vars x)))
             (not (member v (svex-alist-vars xx)))))

  (defret keys-of-svex-alist-maybe-rewrite-fixpoint
    (iff (svex-lookup v xx)
         (svex-lookup v x))))





(defines svex-compose-rw
  (define svex-compose-rw ((x svex-p) (a svex-alist-p))
    :returns (xx svex-p)
    :measure (+ 1 (* 2 (svex-count x)))
    :verify-guards nil
    (svex-case x
      :quote (svex-fix x)
      :var (b* ((look (hons-get x.name a)))
             (if look
                 (svex-fix (cdr look))
               (svex-fix x)))
      :call (svex-compose-rw-memo x a)))
  (define svex-compose-rw-memo ((x svex-p) (a svex-alist-p))
    :guard (svex-case x :call)
    :returns (xx svex-p)
    :measure (* 2 (svex-count x))
    (b* (((unless (mbt (svex-case x :call))) (svex-x))
         ((svex-call x))
         (args (svexlist-compose-rw x.args a)))
      (svex-rewrite-fncall 1000 -1 x.fn args t t)))
  (define svexlist-compose-rw ((x svexlist-p) (a svex-alist-p))
    :returns (xx svexlist-p)
    :measure (* 2 (svexlist-count x))
    (if (atom x)
        nil
      (cons (svex-compose-rw (car x) a)
            (svexlist-compose-rw (cdr x) a))))
  ///
  (verify-guards svex-compose-rw)
  (local (defthm svex-env-lookup-of-append-1
           (implies (and (hons-assoc-equal x a)
                         (svar-p x))
                    (equal (sv::svex-env-lookup x (append a b))
                           (sv::svex-env-lookup x a)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (local (defthm svex-env-lookup-of-append-2
           (implies (and (not (hons-assoc-equal x a))
                         (svar-p x))
                    (equal (sv::svex-env-lookup x (append a b))
                           (sv::svex-env-lookup x b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (local (defthm hons-assoc-equal-of-svex-alist-eval
           (implies (svar-p x)
                    (iff (hons-assoc-equal x (svex-alist-eval a env))
                         (hons-assoc-equal x a)))
           :hints(("Goal" :in-theory (enable svex-alist-eval)))))
  (local (in-theory (enable sv::svex-lookup)))

  (std::defret-mutual svex-compose-rw-correct
    (defret svex-compose-rw-correct
      (equal (svex-eval xx env)
             (svex-eval (svex-compose x a) env))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand ((:Free (env) (svex-eval x env))))))
      :fn svex-compose-rw)
    (defret svex-compose-rw-memo-correct
      (implies (svex-case x :call)
               (equal (svex-eval xx env)
                      (svex-eval (svex-compose x a) env)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand ((:Free (env) (svex-eval x env))))))
      :fn svex-compose-rw-memo)
    (defret svexlist-compose-rw-correct
      (equal (svexlist-eval xx env)
             (svexlist-eval (svexlist-compose x a) env))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-rw))

  (deffixequiv-mutual svex-compose-rw)

  (memoize 'svex-compose-rw-memo))

(define svex-alist-compose-rw ((x svex-alist-p) (a svex-alist-p))
  :returns (xx svex-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x) (svex-compose-rw (cdar x) a))
              (svex-alist-compose-rw (cdr x) a))
      (svex-alist-compose-rw (cdr x) a)))
  ///
  (defret svex-alist-compose-rw-correct
    (equal (svex-alist-eval xx env)
           (svex-alist-eval (svex-alist-compose x a) env))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-compose))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys xx)
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))


(defines svex-subst-rw
  (define svex-subst-rw ((x svex-p) (a svex-alist-p))
    :returns (xx svex-p)
    :measure (+ 1 (* 2 (svex-count x)))
    :verify-guards nil
    (svex-case x
      :quote (svex-fix x)
      :var (b* ((look (hons-get x.name a)))
             (if look
                 (svex-fix (cdr look))
               (svex-x)))
      :call (svex-subst-rw-memo x a)))
  (define svex-subst-rw-memo ((x svex-p) (a svex-alist-p))
    :guard (svex-case x :call)
    :returns (xx svex-p)
    :measure (* 2 (svex-count x))
    (b* (((unless (mbt (svex-case x :call))) (svex-x))
         ((svex-call x))
         (args (svexlist-subst-rw x.args a)))
      (svex-rewrite-fncall 1000 -1 x.fn args t t)))
  (define svexlist-subst-rw ((x svexlist-p) (a svex-alist-p))
    :returns (xx svexlist-p)
    :measure (* 2 (svexlist-count x))
    (if (atom x)
        nil
      (cons (svex-subst-rw (car x) a)
            (svexlist-subst-rw (cdr x) a))))
  ///
  (verify-guards svex-subst-rw)
  (local (defthm svex-env-lookup-of-append-1
           (implies (and (hons-assoc-equal x a)
                         (svar-p x))
                    (equal (sv::svex-env-lookup x (append a b))
                           (sv::svex-env-lookup x a)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (local (defthm svex-env-lookup-of-append-2
           (implies (and (not (hons-assoc-equal x a))
                         (svar-p x))
                    (equal (sv::svex-env-lookup x (append a b))
                           (sv::svex-env-lookup x b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (local (defthm hons-assoc-equal-of-svex-alist-eval
           (implies (svar-p x)
                    (iff (hons-assoc-equal x (svex-alist-eval a env))
                         (hons-assoc-equal x a)))
           :hints(("Goal" :in-theory (enable svex-alist-eval)))))
  (local (in-theory (enable sv::svex-lookup)))

  (std::defret-mutual svex-subst-rw-correct
    (defret svex-subst-rw-correct
      (equal (svex-eval xx env)
             (svex-eval (svex-subst x a) env))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand ((:Free (env) (svex-eval x env))))))
      :fn svex-subst-rw)
    (defret svex-subst-rw-memo-correct
      (implies (svex-case x :call)
               (equal (svex-eval xx env)
                      (svex-eval (svex-subst x a) env)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   `(:expand ((:Free (env) (svex-eval x env))))))
      :fn svex-subst-rw-memo)
    (defret svexlist-subst-rw-correct
      (equal (svexlist-eval xx env)
             (svexlist-eval (svexlist-subst x a) env))
      :hints ('(:expand (<call>)))
      :fn svexlist-subst-rw))

  (deffixequiv-mutual svex-subst-rw)

  (memoize 'svex-subst-rw-memo))

(define svex-alist-subst-rw ((x svex-alist-p) (a svex-alist-p))
  :returns (xx svex-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x) (svex-subst-rw (cdar x) a))
              (svex-alist-subst-rw (cdr x) a))
      (svex-alist-subst-rw (cdr x) a)))
  ///
  (defret svex-alist-subst-rw-correct
    (equal (svex-alist-eval xx env)
           (svex-alist-eval (svex-alist-subst x a) env))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-subst))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys xx)
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (in-theory (enable svex-alist-fix))))
