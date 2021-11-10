; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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
(include-book "dfs-compose")
(include-book "mask-compose")
(include-book "scc-compose")
(include-book "compose-theory-split")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "alist-thms"))
(local (std::add-default-post-define-hook :fix))
(defxdoc svex-composition
  :parents (svex)
  :short "The process of composing together a netlist of svex assignments into
full update functions."
  :long "
<p>Suppose we have a module with a lot of assignment statements. We want to
compose together the RHS expressions in order to get the update formula for
each wire, in terms of the PIs and registers.</p>

<p>One basic thing to do is DFS through each of the expressions, building full
update formulas.  Every time we get to a wire, either it is a PI/register or
another internal wire.  If it is a PI/register, we leave it; if it's an
internal wire, either we've seen it before and computed some formula for it,
or we descend into its update formula and compute that first.</p>

<p>Two kinds of problems arise when using this strategy. First, there might be
variable-level self-loops, e.g.:</p>
@({
 wire [5:0] a = b | (a[4:0] << 1);
 })

<p>Here, @('a') looks like a has a self-loop, but in fact each bit only
depends on previous bits, so the loop can be unrolled into a combinational
formula.  This represents a third possibility for when we encounter an
internal wire: we've encountered it before, but haven't finished computing a
formula for it.</p>

<p>Second, there might be bit-level self-loops. These are bad news but they
do sometimes come up, e.g. in latch-based (as opposed to flipflop-based) logic
as well as with clock gating where the clock gate signal depends on the output
of a register that it gates (depending on how the clock gate is represented in
the logic).</p>

<p>To deal with these two problems, we do two further steps after the initial
simple DFS composition step; step 2 effectively deals with variable-level
self-loops and step 3 deals with bit-level self-loops.  The full sequence of
steps:</p>

<ul>

<li>1. Simple depth-first search composition, stopping whenever we reach a
variable that is still in the stack.</li>

<li>2. Iterative self-composition of the remaining signals, using caremasks to
determine when a variable needs to be composed in.  This is implemented in as
@('svex-alist-maskcompose-iter') in \"mask-compose.lisp\".</li>

<li>3. Break up into bits any remaining internal signals that other signals
still depend on, then find strongly-connected components of the bit-level
dependency graph and try to self-compose those components enough times to
resolve further dependencies.  Then translate the decomposed signals back into
the original namespace.</li>

<li>4. Finally, replace any remaining internal signal dependencies with Xes.</li>
</ul>

<p>This is implemented @('svex-assigns-compose').</p>

")





(define svex-assigns-compose-phase1 ((x svex-alist-p)
                                                &key (rewrite 't))
  :returns (new-x svex-alist-p)
  (b* ((xvals (svex-alist-vals x))
       (- (cw "Initial count: ~x0~%" (svexlist-opcount xvals)))
       ;;; Rewriting here at first presumably won't disrupt decompositions
       ;;; because the expressions should be relatively small and independent,
       ;;; to first approximation.
       ;; (- (sneaky-save 'orig-assigns x))
       (xvals (if rewrite (cwtime (svexlist-rewrite-top xvals :verbosep t) :mintime 0) xvals))
       (x (pairlis$ (svex-alist-keys x) xvals))
       (- (cw "Count after initial rewrite: ~x0~%" (svexlist-opcount xvals)))
       (updates (cwtime (svex-compose-assigns x) :mintime 0))
       ;; (updates (cwtime (svex-alist-rewrite-top updates :verbosep t) :mintime 0))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount (svex-alist-vals updates)))))
    updates)
  ///
  (local (defthm pairlis-svex-keys-vals
           (equal (pairlis$ (svex-alist-keys x) (svex-alist-vals x))
                  (svex-alist-fix x))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-vals svex-alist-fix)))))

  (local (defthmd svex-alist-eval-of-pairlis$
           (equal (svex-alist-eval (pairlis$ keys vals) env)
                  (svex-env-fix (pairlis$ keys (svexlist-eval vals env))))
           :hints(("Goal" :in-theory (enable svex-alist-eval svexlist-eval)))))

  (local (defcong svexlist-eval-equiv svex-alist-eval-equiv (pairlis$ keys vals) 2
           :hints (("goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                              svex-alist-eval-of-pairlis$)))))

  (local (Defthm svexlist-rewrite-top-under-svexlist-eval-equiv
           (svexlist-eval-equiv (svexlist-rewrite-top x :verbosep verbosep) x)
           :hints(("Goal" :in-theory (enable svexlist-eval-equiv)))))

  (local (defret netcomp-p-of-svex-compose-assigns-trans-rw
           (implies (netcomp-p (double-rewrite assigns) orig)
                    (netcomp-p updates orig))
           :hints (("goal" :in-theory (enable netcomp-p-transitive2)))
           :fn svex-compose-assigns))

  (defret netcomp-p-of-<fn>
    (netcomp-p new-x x))

  (defret netcomp-p-of-<fn>-trans
    (implies (netcomp-p x y)
             (netcomp-p new-x y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (defret no-duplicate-keys-of-<fn>
    (no-duplicatesp-equal (svex-alist-keys new-x)))

  (defret svex-alist-keys-of-<fn>
    (set-equiv (svex-alist-keys new-x)
               (svex-alist-keys x))))


(define svex-alist-pair-initial-masks ((x svex-alist-p))
  :enabled t
  :guard-hints (("goal" :in-theory (enable svex-alist-keys
                                           svexlist-mask-acons
                                           svarlist->svexes
                                           svex-mask-acons
                                           svex-alist-pair-initial-masks)))
  (mbe :logic (svexlist-mask-acons (svarlist->svexes (svex-alist-keys x)) -1 nil)
       :exec (if (atom x)
                 nil
               (cons (cons (svex-var (caar x)) -1)
                     (svex-alist-pair-initial-masks (cdr x))))))

(define svex-assigns-compose-phase2 ((x svex-alist-p)
                                                &key (simpconf svex-simpconfig-p))
  :returns (mv (masks svex-mask-alist-p)
               (new-x svex-alist-p))
  (b* (;; (dep-vars (cwtime (svexlist-collect-vars (svex-alist-vals x))))
       ((acl2::with-fast x))
       ;; (reduced-updates (svex-alist-reduce dep-vars x))
       ;; (rest-updates (svex-alist-reduce (hons-set-diff (svex-alist-keys x) dep-vars) x))
       ;; (init-masks (svex-alist-pair-initial-masks reduced-updates))
       (init-masks (svex-alist-pair-initial-masks x))
       ((mv masks phase2-updates)
        (with-fast-alist init-masks
          (cwtime (svex-alist-maskcompose-iter init-masks x simpconf)))))
    (mv masks (fast-alist-free phase2-updates)))
  ///
  (defret netcomp-p-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (netcomp-p new-x x)))

  (defret netcomp-p-of-<fn>-trans
    (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                  (netcomp-p x y))
             (netcomp-p new-x y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (defret svex-alist-keys-of-<fn>
    (set-equiv (svex-alist-keys new-x)
               (svex-alist-keys x))))
  

;; Need to experiment to see if it's best to split variables directly into bits
;; or use bigger chunks (e.g. by looking at the structure of the current
;; updates, either how the variables are built from bits or else how they are
;; used).  For now we just go with bits because it's simpler and we hope that
;; performance will be OK.

(define svar-split-variable ((orig svar-p)
                             (base-idx natp)
                             (width acl2::maybe-natp))
  :returns (new svar-p)
  :hooks ((:fix :hints (("goal" :in-theory (enable acl2::maybe-natp-fix)))))
  (b* (((svar orig)))
    (change-svar orig :name (hons :splitrange
                                  (if width
                                      (hons orig.name (hons (lnfix base-idx) (lnfix width)))
                                    (hons orig.name (lnfix base-idx)))))))


(define svar-mask-to-split ((orig svar-p)
                            (position natp)
                            (mask 4vmask-p)
                            (masklen (equal masklen (sparseint-length mask))))
  :measure (nfix (- (sparseint-length (4vmask-fix mask)) (nfix position)))
  :returns (mv (split svar-split-p)
               (bitcount natp :rule-classes :type-prescription))
  :prepwork ((local (defthm trailing-0-count-nonzero
                      (implies (and (not (logbitp n x))
                                    (< (nfix n) (integer-length x)))
                               (not (equal (bitops::trailing-0-count (logtail n x)) 0)))
                      :hints(("Goal" :in-theory (enable* bitops::trailing-0-count
                                                         bitops::ihsext-inductions
                                                         bitops::logtail**
                                                         bitops::logbitp**
                                                         bitops::integer-length**))))))
  :verify-guards :after-returns
  (b* ((mask (4vmask-fix mask))
       (masklen (mbe :logic (sparseint-length mask) :exec masklen))
       ((when (<= (the unsigned-byte masklen) (lnfix position)))
        (mv (svar-split-remainder (svar-split-variable orig position nil)) 0))
       ((when (eql (sparseint-bit position mask) 1))
        (b* (((mv rest rest-count) (svar-mask-to-split orig (+ 1 (lnfix position)) mask masklen)))
          (mv (make-svar-split-segment
               :var (svar-split-variable orig position 1)
               :width 1
               :rest rest)
              (+ 1 rest-count))))
       (zeros (sparseint-trailing-0-count-from mask position))
       ((mv rest rest-count) (svar-mask-to-split orig (+ zeros (lnfix position)) mask masklen)))
    (mv (make-svar-split-segment
         :var (svar-split-variable orig position zeros)
         :width zeros
         :rest rest)
        rest-count)))

(define svex-compose-splittab ((x svex-alist-p)
                               (masks svex-mask-alist-p))
  :returns (mv (splittab svar-splittab-p)
               (bitcount natp :rule-classes :type-prescription))
  :hooks ((:fix :hints (("goal" :induct (svex-compose-splittab x masks)
                         :expand ((svex-compose-splittab x masks)))
                        (and stable-under-simplificationp
                             '(:expand ((svex-alist-fix x)
                                        (svex-compose-splittab (svex-alist-fix (cdr x)) masks)))))))
  (b* (((when (atom x)) (mv nil 0))
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svex-compose-splittab (cdr x) masks))
       (var (caar x))
       (mask (svex-mask-lookup (svex-var var) masks))
       ((when (sparseint-equal mask 0))
        (svex-compose-splittab (cdr x) masks))
       ((mv split count1) (svar-mask-to-split var 0 mask (sparseint-length mask)))
       ((mv rest count2) (svex-compose-splittab (cdr x) masks)))
    (mv (cons (cons var split)
              rest)
        (+ count1 count2)))
  ///
  (defret hons-assoc-equal-under-iff-of-<fn>
    (iff (hons-assoc-equal var splittab)
         (and (svar-p var)
              (svex-lookup var x)
              (not (sparseint-equal 0 (svex-mask-lookup (svex-var var) masks)))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret <fn>-splittab-keys-subset
    (subsetp-equal (alist-keys splittab)
                   (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      alist-keys))))

  (local (defthm member-alist-keys-iff-hons-assoc-equal
           (iff (member-equal key (alist-keys x))
                (hons-assoc-equal key x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret <fn>-splittab-keys-no-dups
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (no-duplicatesp-equal (alist-keys splittab)))
    :hints(("Goal" :in-theory (e/d (svex-alist-keys alist-keys))))))


       
(local
 (defthm svarlist-p-alist-keys-when-svar-splittab-p
   (implies (svar-splittab-p x)
            (svarlist-p (alist-keys x)))
   :hints(("Goal" :in-theory (enable svar-splittab-p alist-keys)))))

(local (in-theory (disable acl2::hons-dups-p)))

(local
 (defthm svex-alist-rewrite-top-under-svex-alist-eval-equiv
   (svex-alist-eval-equiv (svex-alist-rewrite-top x :verbosep verbosep) x)
   :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))


(local (defthm svex-alist-keys-of-svex-alist-compose
         (Equal (svex-alist-keys (svex-alist-compose x a))
                (svex-alist-keys x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))

(define svex-alist-to-split-split-part ((x svex-alist-p)
                                        (splittab svar-splittab-p))
  :returns (new-x svex-alist-p)
  (b* ((subst (svar-splittab->subst splittab))
       (inverse (svar-splittab->inverse splittab))
       (comp1 (with-fast-alist x (svex-alist-compose inverse x))))
    (with-fast-alist subst
      (svex-alist-compose comp1 subst)))
  ///
  (defret <fn>-in-terms-of-svex-alist-to-split
    (svex-alist-eval-equiv new-x
                           (svex-alist-reduce (svar-splittab-vars splittab)
                                              (svex-alist-to-split x splittab)))
    :hints(("Goal" :in-theory (enable svex-alist-to-split
                                      svex-alist-eval-equiv))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys new-x)
           (svar-splittab-vars splittab))))

(local
 (defthm svex-alist-keys-of-svex-alist-rewrite-top
   (equal (svex-alist-keys (svex-alist-rewrite-top x :verbosep verbosep))
          (svex-alist-keys x))
   :hints(("Goal" :in-theory (enable svex-alist-rewrite-top)))))

(define svex-assigns-compose-phase3 ((x svex-alist-p)
                                     (masks svex-mask-alist-p))
  :returns (mv err (new-x svex-alist-p) (splittab svar-splittab-p))
  (b* ((x-vals (svex-alist-vals x))
       (vars (append (svex-alist-keys x) (svexlist-collect-vars x-vals)))
       ((mv splittab bitcount) (cwtime (svex-compose-splittab x masks) :mintime 0))
       (- (cw "Care bits remaining: ~x0~%" bitcount))
       ((unless splittab)
        (mv nil (svex-alist-fix x) splittab))
       (splittab-vars (svar-splittab-vars splittab))
       (- (cw "Total split variables: ~x0~%" (len splittab-vars)))
       (bad-vars (acl2::hons-intersection vars splittab-vars))
       ((when bad-vars)
        (mv (msg "Splittab had variables that already existed: ~x0~%" bad-vars) nil splittab))
       (dupsp (hons-dups-p splittab-vars))
       ((when dupsp)
        (mv (msg "Splittab had duplicate variables such as ~x0~%" (car dupsp)) nil splittab))
       (dupsp (hons-dups-p (alist-keys splittab)))
       ((when dupsp)
        (mv (msg "Splittab had duplicate keys such as ~x0~%" (car dupsp)) nil splittab))
       ;; (x-split-part (svex-alist-reduce (alist-keys splittab) x))
       (split-updates1 (cwtime (svex-alist-to-split-split-part x splittab) :mintime 0))
       (split-updates (cwtime (svex-alist-rewrite-top split-updates1 :verbosep t) :mintime 0))
       (- (cw "Split update variables: ~x0~%" (len split-updates))))
    (mv nil split-updates splittab))
  ///

  (local (defthm svex-alist-splittab-split-keys-of-nil
           (equal (svex-alist-splittab-split-keys x nil)
                  (svex-alist-fix x))
           :hints(("Goal" :in-theory (enable svex-alist-compose)))))

  (local (defthm svex-alist-compose-of-nil
           (svex-alist-eval-equiv (svex-alist-compose x nil)
                                  (svex-alist-fix x))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                             svex-alist-eval)))))

  (local (defthm svex-alist-to-split-of-nil
           (svex-alist-eval-equiv (svex-alist-to-split x nil)
                                  (svex-alist-fix x))
           :hints(("Goal" :in-theory (enable svex-alist-to-split)))))

  (local (defthm svex-alist-keys-of-svex-alist-reduce
           (equal (svex-alist-keys (svex-alist-reduce keys x))
                  (intersection-equal (svarlist-fix keys)
                                      (Svex-alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-alist-reduce svex-alist-keys)))))

  (local (defthm consp-intersection-equal
           (iff (consp (intersection-equal x y))
                (intersection-equal x y))))

  (local (defthm intersection-equal-under-iff
           (iff (intersection-equal x y)
                (intersectp-equal x y))))

  (local (defthm intersectp-identity
           (implies (not (intersectp-equal a c))
                    (not (intersectp-equal a (intersection-equal b c))))))

  (local (defthm subsetp-of-intersection
           (iff (subsetp-equal x (intersection-equal x y))
                (subsetp-equal x y))
           :hints(("Goal" :in-theory (enable subsetp-equal intersection-equal)))))

  (defret netcomp-p-of-<fn>
    (netcomp-p new-x (svex-alist-to-split x splittab)))

  (defret netcomp-of-<fn>-trans
    (implies (netcomp-p (svex-alist-to-split x splittab) y)
             (netcomp-p new-x y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (defret netcomp-p-of-<fn>-no-split
    (implies (not splittab)
             (netcomp-p new-x x)))

  (defret netcomp-p-of-<fn>-no-split-trans
    (implies (and (not splittab)
                  (netcomp-p x y))
             (netcomp-p new-x y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (local (defthm svex-alist-vars-is-svexlist-vars
           (equal (svex-alist-vars x)
                  (svexlist-vars (svex-alist-vals x)))
           :hints(("Goal" :in-theory (enable svex-alist-vals svexlist-vars svex-alist-vars)))))

  (defret splittab-props-of-<fn>
    (implies (not err)
             (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-splittab-vars splittab)))
                  (not (intersectp-equal (svex-alist-vars x)
                                         (svar-splittab-vars splittab)))
                  (no-duplicatesp-equal (svar-splittab-vars splittab))
                  (no-duplicatesp-equal (alist-keys splittab))
                  (subsetp-equal (alist-keys splittab)
                                 (svex-alist-keys x)))))

  (defret svex-alist-keys-of-<fn>
    (implies (and (not err) splittab)
             (equal (svex-alist-keys new-x)
                    (svar-splittab-vars splittab))))

  (defret subsetp-splittab-keys-of-<fn>-trans
    (implies (subsetp-equal (svex-alist-keys x) y)
             (subsetp-equal (alist-keys splittab) y))))
             

(local (in-theory (disable fast-alist-clean)))

(local (defthm svex-mask-alist-p-of-hons-remove-assoc
         (implies (svex-mask-alist-p x)
                  (svex-mask-alist-p (acl2::hons-remove-assoc k x)))
         :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc)))))

(local (defthm cdr-last-when-svex-mask-alist-p
         (implies (svex-mask-alist-p x)
                  (not (cdr (last x))))
         :rule-classes :forward-chaining))
                  

(local (defthm svex-mask-alist-p-of-fast-alist-clean
         (implies (svex-mask-alist-p x)
                  (svex-mask-alist-p (fast-alist-clean x)))
         :hints(("Goal" :induct (fast-alist-clean x)
                 :expand ((fast-alist-clean x)
                          (svex-mask-alist-p x))))))


(define svex-compose-extract-loop-var-alist-from-final-masks ((x svex-mask-alist-p))
  :returns (loop-vars svar-key-alist-p)
  :hooks ((:fix :hints(("Goal" :in-theory (enable svex-mask-alist-fix)))))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svex-p (caar x)))))
        (svex-compose-extract-loop-var-alist-from-final-masks (cdr x)))
       ((cons key mask) (car x))
       ((unless (svex-case key :var))
        (svex-compose-extract-loop-var-alist-from-final-masks (cdr x)))
       ((when (sparseint-equal 0 (4vmask-fix mask)))
        (svex-compose-extract-loop-var-alist-from-final-masks (cdr x))))
    (cons (cons (svex-var->name key) (4vmask-fix mask))
          (svex-compose-extract-loop-var-alist-from-final-masks (cdr x)))))


(local
 (defthm svar-key-alist-p-of-hons-remove-assoc
   (implies (svar-key-alist-p x)
            (svar-key-alist-p (acl2::hons-remove-assoc key x)))
   :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc)))))

(local
 (defthm svar-key-alist-p-of-fast-alist-clean
   (implies (svar-key-alist-p x)
            (svar-key-alist-p (fast-alist-clean x)))
   :hints(("Goal" :in-theory (enable acl2::fast-alist-clean-by-remove-assoc)))))


(local (defthm svex-alist-compose*-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-compose* x a)
                                (svex-alist-compose x a))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))

(local (defthm svex-alist-keys-of-svex-alist-compose*
         (equal (svex-alist-keys (svex-alist-compose* x a))
                (svex-alist-keys x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose*)))))

(define svex-assigns-compose-phase4 ((x svex-alist-p))
  :returns (mv err (new-x svex-alist-p))
  (b* ((final-masks (fast-alist-clean (svexlist-mask-alist (svex-alist-vals x))))
       ;; (- (with-fast-alist x
       ;;      (svex-masks-summarize-loops vars final-masks x)))
       (loop-var-alist (fast-alist-clean (svex-compose-extract-loop-var-alist-from-final-masks final-masks)))
       ;; (next-updates (with-fast-alist new-updates
       ;;                 (svex-alist-compose* split-updates new-updates)))

       
       ;; (- (acl2::sneaky-save 'next-updates next-updates))

       (- (cw "~x0 loop vars~%" (len loop-var-alist))
          ;; (cw "rest: ~x0~%keys: ~x1~%"
          ;;     (len rest) (alist-keys (take (min 20 (len rest)) rest)))
          )
       ((mv err looped-updates)
        (with-fast-alist loop-var-alist
          (with-fast-alist x
            (with-fast-alist final-masks
              (cwtime
               (svex-mask-alist-compose-bit-sccs
                final-masks 0 nil nil nil
                (make-svex-scc-consts :final-masks final-masks
                                      :updates x
                                      :loop-vars loop-var-alist)))))))
       ;; (- (acl2::sneaky-save 'looped-updates looped-updates))
       (- (fast-alist-free loop-var-alist))
       (- (fast-alist-free final-masks))
       ((when err)
        (fast-alist-free looped-updates)
        (mv err nil)))
    (mv err (with-fast-alist looped-updates (svex-alist-compose* x looped-updates))))
  ///

  (defret netcomp-p-of-<fn>
    (netcomp-p new-x x))

  (defret netcomp-p-of-<fn>-trans
    (implies (netcomp-p x y)
             (netcomp-p new-x y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (defret svex-alist-keys-of-<fn>
    (implies (not err)
             (equal (svex-alist-keys new-x)
                    (svex-alist-keys x)))))





(local
 (defret svex-alist-keys-of-svex-alist-splittab-unsplit-keys
   (set-equiv (svex-alist-keys new-x)
              (append (alist-keys (svar-splittab-fix splittab))
                      (set-difference-equal (svex-alist-keys x) (svar-splittab-vars splittab))))
   :hints(("Goal" :in-theory (enable <fn>)))
   :fn svex-alist-splittab-unsplit-keys))

(local
 (defret svex-alist-keys-of-svex-alist-from-split
   (set-equiv (svex-alist-keys new-x)
              (append (alist-keys (svar-splittab-fix splittab))
                      (set-difference-equal (svex-alist-keys x) (svar-splittab-vars splittab))))
   :hints(("Goal" :in-theory (enable <fn>)))
   :fn svex-alist-from-split))


(local (defthm svex-lookup-of-fast-alist-fork
         (equal (svex-lookup v (fast-alist-fork x y))
                (svex-lookup v (append y x)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(local (defthm fast-alist-fork-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (fast-alist-fork a b)
                                (append b a))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

(define svex-assigns-compose-phase5 ((unsplit svex-alist-p)
                                     (split svex-alist-p)
                                     (splittab svar-splittab-p))
  :returns (new-x svex-alist-p)
  (b* ((re-unsplit (svex-alist-from-split split splittab)))
    (fast-alist-fork (svex-alist-fix unsplit) (make-fast-alist re-unsplit)))
  ///
  (defret netcomp-p-of-<fn>
    (implies (and (netcomp-p split (svex-alist-to-split unsplit splittab))
                  (not (intersectp-equal (svex-alist-keys unsplit)
                                         (svar-splittab-vars splittab)))
                  (not (intersectp-equal (svex-alist-vars unsplit)
                                         (svar-splittab-vars splittab)))
                  (no-duplicatesp-equal (svar-splittab-vars splittab))
                  (no-duplicatesp-equal (alist-keys (svar-splittab-fix splittab)))
                  (subsetp-equal (alist-keys (svar-splittab-fix splittab))
                                 (svex-alist-keys unsplit)))
             (netcomp-p new-x unsplit)))

  (defret netcomp-p-of-<fn>-trans
    (implies (and (netcomp-p unsplit x)
                  (netcomp-p split (svex-alist-to-split unsplit splittab))
                  (not (intersectp-equal (svex-alist-keys unsplit)
                                         (svar-splittab-vars splittab)))
                  (not (intersectp-equal (svex-alist-vars unsplit)
                                         (svar-splittab-vars splittab)))
                  (no-duplicatesp-equal (svar-splittab-vars splittab))
                  (no-duplicatesp-equal (alist-keys (svar-splittab-fix splittab)))
                  (subsetp-equal (alist-keys (svar-splittab-fix splittab))
                                 (svex-alist-keys unsplit)))
             (netcomp-p new-x x))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (defret svex-alist-keys-of-<fn>
    (set-equiv (svex-alist-keys new-x)
               (append (alist-keys (svar-splittab-fix splittab))
                       (set-difference-equal (svex-alist-keys split) (svar-splittab-vars splittab))
                       (svex-alist-keys unsplit)))))


(define svex-assigns-compose1 ((x svex-alist-p)
                              &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (mv err (xx svex-alist-p))
  (b* ((phase1 (svex-assigns-compose-phase1 x :rewrite rewrite))
       ((mv masks phase2) (svex-assigns-compose-phase2 phase1 :simpconf (mbe :logic (if* rewrite 20 t)
                                                                             :exec (if rewrite 20 t))))
       ((mv err phase3 splittab) (svex-assigns-compose-phase3 phase2 masks))
       ((when err) (mv err nil))
       ((unless splittab)
        (mv nil phase2))
       ((mv err phase4) (svex-assigns-compose-phase4 phase3))
       ((when err) (mv err nil)))
    (mv nil (svex-assigns-compose-phase5 phase2 phase4 splittab)))
  ///
  (defret netcomp-p-of-<fn>
    (netcomp-p xx x)
    :hints(("Goal" :in-theory (disable if*
                                       svex-alist-keys-of-svex-assigns-compose-phase2))))

  (defret netcomp-p-of-<fn>-trans
    (implies (netcomp-p x y)
             (netcomp-p xx y))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>)))))

  (local (defthm set-difference-subset
           (implies (subsetp-equal x y)
                    (equal (set-difference-equal x y) nil))))

  (defret svex-alist-keys-of-<fn>
    (implies (not err)
             (set-equiv (svex-alist-keys xx)
                        (svex-alist-keys x)))))

(local (defthm svex-alist-compose-rw-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-compose-rw x a)
                                (svex-alist-compose x (svex-substconfig->alist a)))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))

(define svex-assigns-compose ((x svex-alist-p)
                              &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (xx svex-alist-p)
  (b* (((mv err ans) (svex-assigns-compose1 x :rewrite rewrite))
       ;; hack to get a logically reasonable result when error
       (ans (if err
                (prog2$ (raise "~@0" err)
                        (svex-alist-fix x))
              ans))
       (final-ans (b* ((vars (svex-alist-keys x))
                       (xes-alist (svarlist-x-subst vars)))
                    (with-fast-alist xes-alist (svex-alist-compose-rw
                                                ans
                                                (make-svex-substconfig
                                                 :simp (if rewrite 20 t)
                                                 :alist xes-alist))))))
    final-ans)
  ///
  (defret netevalcomp-p-of-<fn>
    (netevalcomp-p xx x))

  (defret svex-alist-keys-of-<fn>
    (set-equiv (svex-alist-keys xx)
               (svex-alist-keys x))))
