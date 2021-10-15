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
(include-book "rewrite")
(include-book "misc/hons-help" :dir :system)
(include-book "std/strings/hexify" :dir :system)
(include-book "centaur/misc/fast-alist-pop" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system) ;; with-fast
(include-book "tools/symlet" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "compose-theory-split")
(local (include-book "centaur/misc/dfs-measure" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (in-theory (disable tau-system)))
(local (std::add-default-post-define-hook :fix))
;; Suppose we have a module with a lot of assignment statements. We want to
;; compose together the RHS expressions in order to get the update formula for
;; each wire, in terms of the PIs and registers.

;; One basic thing to do is DFS through each of the expressions, building full
;; update formulas.  Every time we get to a wire, either it is a PI/register or
;; another internal wire.  If it is a PI/register, we leave it; if it's an
;; internal wire, either we've seen it before and computed some formula for it,
;; or we descend into its update formula and compute that first.

;; ** Problem 1: there might be apparent combinational loops, e.g.
;; wire [5:0] a = b | (a[4:0] << 1);

;; Here, it looks like a has a self-loop, but in fact each bit of A only
;; depends on previous bits, so the loop can be unrolled into a combinational
;; formula.  This represents a third possibility for when we encounter an
;; internal wire: we've encountered it before, but haven't finished computing a
;; formula for it.

;; For now, we'll just leave these loop wires.  When we're done with the DFS,
;; we can use svmasks to show that (hopefully) the care masks for each of the
;; looped wires lose bits each time we compose the formula with itself, and
;; thus we only have to unroll finitely many times.

;; ** Problem 2: there might be real combinational loops.  Hopefully not.
;; We'll deal with this later, perhaps with a real fixpoint algorithm.

;; ** Problem 3: Left-hand sides of assignments can be a certain class of
;; expressions (involving concatenations, slices, etc).  So when we're
;; assigning to some such expression, it's not as simple to determine what each
;; wire has.  We need a way to map back to what a complex assignment actually
;; assigns to each of the component wires.  Then, some wires may have multiple
;; assignments, which need to be resolved together before we know the true
;; update formula for each wire.  This is perhaps best viewed as a
;; preprocessing step.

(defxdoc svex-composition
  :parents (svex)
  :short "The process of composing together a netlist of svex assignments into
full update functions.")

(defxdoc compose.lisp :parents (svex-composition))
(local (xdoc::set-default-parents compose.lisp))




;; Note: This isn't memoized to the extent that it might be: it's memoized at
;; the level of named wires, i.e. subexpressions of assignments may be
;; traversed multiple times.  That could be ok, if the assigns it is run on are
;; simply translations of the assignments written in SV sources.  However, if
;; they somehow become large, repetitive structures, we may need to revisit
;; this.

(defines svex-compose-dfs
  :parents (sv)
  :short "Compose together a network of svex assignments, stopping when a
variable depends on itself."
  :flag-local nil

  (define svex-compose-dfs ((x svex-p "svex we're traversing")
                            (assigns svex-alist-p "alist of assign stmts")
                            (updates svex-alist-p "alist of composed update fns")
                            (memo svex-svex-memo-p "memo table for internal nodes")
                            (stack "alist of seen vars"
                                   alistp))
    :guard (no-duplicatesp-equal (strip-cars stack))
    :verify-guards nil
    :well-founded-relation acl2::nat-list-<
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svex-count x))
    :returns (mv (x1 svex-p "composition of x with other internal wires")
                 (updates1 svex-alist-p "extended update functions")
                 (memo1 svex-svex-memo-p "extended memo table"))
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (memo (svex-svex-memo-fix memo))
         (updates (mbe :logic (svex-alist-fix updates) :exec updates)))
      (svex-case x
        :quote (mv x updates memo)
        :call (b* ((look (hons-get x memo))
                   ((when look) (mv (cdr look) updates memo))
                   ((mv args updates memo)
                    (svexlist-compose-dfs x.args assigns updates memo stack))
                   (res (svex-call* x.fn args))
                   (memo (hons-acons x res memo)))
                (mv res updates memo))
        :var (b* ((update-fn (svex-fastlookup x.name updates))
                  ((when update-fn) (mv update-fn updates memo))
                  (assign (svex-fastlookup x.name assigns))
                  ((unless (and assign (not (hons-get x.name stack))))
                   ;; if it has no assignment OR we're already traversing it, leave it
                   (mv x updates memo))
                  (stack (hons-acons x.name t stack))
                  ((mv composed-assign updates memo1)
                   (svex-compose-dfs assign assigns updates nil stack))
                  (- (fast-alist-free memo1))
                  (- (acl2::fast-alist-pop stack))
                  (updates (svex-fastacons x.name composed-assign updates)))
               (mv composed-assign updates memo)))))

  (define svexlist-compose-dfs ((x svexlist-p)
                                (assigns svex-alist-p)
                                (updates svex-alist-p)
                                (memo svex-svex-memo-p)
                                (stack alistp))
    :guard (no-duplicatesp-equal (strip-cars stack))
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svexlist-count x))
    :returns (mv (x1 svexlist-p)
                 (updates1 svex-alist-p)
                 (memo1 svex-svex-memo-p))
    (b* ((updates (mbe :logic (svex-alist-fix updates) :exec updates))
         (memo (svex-svex-memo-fix memo))
         ((when (atom x)) (mv nil updates memo))
         ((mv first updates memo)
          (svex-compose-dfs (car x) assigns updates memo stack))
         ((mv rest updates memo)
          (svexlist-compose-dfs (cdr x) assigns updates memo stack)))
      (mv (cons first rest) updates memo)))
  ///
  (verify-guards svex-compose-dfs)

  (fty::deffixequiv-mutual svex-compose-dfs
    :hints (("goal" :expand ((svexlist-fix x))))))


(define svex-compose-assigns-keys ((keys svarlist-p "List of remaining target variables")
                                   (assigns svex-alist-p "Original list of assignments")
                                   (updates svex-alist-p "Accumulator of composed update functions")
                                   (memo svex-svex-memo-p "accumulated memo table"))
  :parents (svex-composition)
  :short "Compose together svex assignments (using svex-compose-dfs) for the
listed keys."
  :guard-hints(("Goal" :in-theory (enable svarlist-p)))
  :returns (mv (updates1 svex-alist-p)
               (memo1 svex-svex-memo-p))
  (b* (((when (atom keys)) (mv (mbe :logic (svex-alist-fix updates) :exec updates)
                               (svex-svex-memo-fix memo)))
       ((mv & updates memo) (svex-compose-dfs (svex-var (car keys)) assigns updates memo nil)))
    (svex-compose-assigns-keys (cdr keys) assigns updates memo))
  ///
  (fty::deffixequiv svex-compose-assigns-keys
    :hints (("goal" :expand ((svarlist-fix keys))))))


(define svex-compose-assigns ((assigns svex-alist-p))
  :parents (svex-composition)
  :short "Compose together an alist of svex assignments, with no unrolling when
variables depend on themselves."
  :returns (updates svex-alist-p)
  (b* (((mv updates memo)
        (with-fast-alist assigns
          (svex-compose-assigns-keys (svex-alist-keys assigns) assigns nil nil))))
    (fast-alist-free memo)
    updates)
  ///
  (fty::deffixequiv svex-compose-assigns))



(defmacro 4vmask-bits-maxcount () '(expt 2 30))


(define 4vmask-bitcount ((x 4vmask-p))
  :returns (count natp :rule-classes :type-prescription)
  :guard-hints ((and stable-under-simplificationp
                     '(:use ((:instance logcount-lemma (n (expt 2 30)))))))
  (b* ((x (mbe :logic (4vmask-fix x) :exec x)))
    (sparseint-bitcount (sparseint-concatenate (4vmask-bits-maxcount) x 0)))
  ///
  (fty::deffixequiv 4vmask-bitcount))


(define svexlist-masks-measure ((x svarlist-p) (al svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (b* ((mask (svex-mask-lookup (svex-var (car x)) al))
            (res (4vmask-bitcount mask)))
         ;; (and (< 1000 res)
         ;;      (cw "var ~x0, mask ~s1, count was ~x2~%" (car x) (str::hexify mask) res))
         res)
       (svexlist-masks-measure (cdr x) al)))
  ///
  (fty::deffixequiv svexlist-masks-measure))

(define svarlist-pair-with-masks ((x svarlist-p) (al svex-mask-alist-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  (if (atom x)
      nil
    (b* ((mask (svex-mask-lookup (svex-var (car x)) al)))
      (if (eql 0 mask)
          (svarlist-pair-with-masks (cdr x) al)
        (cons (cons (svar-fix (car x)) (str::binify mask))
              (svarlist-pair-with-masks (cdr x) al))))))



#||

logic [3:0] a;
logic [3:0] b;

a = (a << 1) & (b << 1)
b = (a << 1) | (b << 1)




||#


(defines svex-collect-subexprs
  (define svex-collect-subexprs ((x svex-p) acc)
    :measure (svex-count x)
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         ((when (hons-get x acc)) acc)
         (acc (hons-acons x t acc))
         ((when (not (eq (svex-kind x) :call))) acc))
      (svexlist-collect-subexprs (svex-call->args x) acc)))
  (define svexlist-collect-subexprs ((x svexlist-p) acc)
    :measure (svexlist-count x)
    (if (atom x)
        acc
      (svex-collect-subexprs
       (car x)
       (svexlist-collect-subexprs (cdr x) acc))))
  ///
  (fty::deffixequiv-mutual svex-collect-subexprs
    :hints(("Goal" :in-theory (enable svexlist-fix)))))

(defthm svexlist-p-alist-keys-of-mask-alist
  (IMPLIES (SVEX-MASK-ALIST-P X)
           (SVEXLIST-P (ALIST-KEYS X)))
  :hints(("Goal" :in-theory (enable svex-mask-alist-p
                                    svexlist-p
                                    alist-keys))))

(define svexlist-filter ((x svexlist-p))
  :returns (new-x svexlist-p)
  :verify-guards nil
  :hooks nil
  (mbe :logic
       (if (atom x)
           nil
         (if (svex-p (car x))
             (cons (car x) (svexlist-filter (cdr x)))
           (svexlist-filter (cdr x))))
       :exec x)
  ///
  (defret svexlist-filter-of-svexlist
    (implies (svexlist-p x)
             (equal (svexlist-filter x) x)))

  (verify-guards svexlist-filter))

(defthm alist-keys-of-svex-mask-alist-fix
  (equal (alist-keys (svex-mask-alist-fix x))
         (svexlist-filter (alist-keys x)))
  :hints(("Goal" :in-theory (enable svex-mask-alist-fix
                                    svexlist-filter
                                    alist-keys))))

(define svex-mask-alist-expand ((x svex-mask-alist-p))
  :returns (mask-al svex-mask-alist-p)
  (b* (((mv toposort al) (cwtime (svexlist-toposort (svex-mask-alist-keys x) nil nil)))
       (- (fast-alist-free al)))
    (cwtime (svexlist-compute-masks toposort (make-fast-alist x))))
  ///

  (fty::deffixequiv svex-mask-alist-expand)

  (defthm svex-mask-alist-expand-complete
    (svex-mask-alist-complete (svex-mask-alist-expand x))))

;; this is the same as svex-alist-reduce
;; (define svars-extract-updates ((vars svarlist-p)
;;                                (updates svex-alist-p))
;;   :returns (upds svex-alist-p)
;;   :guard-hints (("goal" :in-theory (enable svarlist-p)))
;;   (b* (((when (atom vars)) nil)
;;        (upd (svex-fastlookup (car vars) updates))
;;        ((unless upd) (svars-extract-updates (cdr vars) updates)))
;;     (cons (cons (svar-fix (car vars)) upd)
;;           (svars-extract-updates (cdr vars) updates)))
;;   ///
;;   (deffixequiv svars-extract-updates
;;     :hints(("Goal" :in-theory (enable svarlist-fix)))))


(define svar-updates-pair-masks ((vars svarlist-p)
                                 (masks svex-mask-alist-p)
                                 (updates svex-alist-p))
  :returns (newmasks svex-mask-alist-p
                     :hints(("Goal" :in-theory (enable svex-mask-alist-p))))
  :guard-hints (("goal" :in-theory (enable svarlist-p)))
  (b* (((when (atom vars)) nil)
       (var (car vars))
       (svex (svex-var var))
       (update (svex-fastlookup var updates))
       ((unless update)
        (svar-updates-pair-masks (cdr vars) masks updates))
       (mask (svex-mask-lookup svex masks)))
    (cons (cons update mask)
          (svar-updates-pair-masks (cdr vars) masks updates)))
  ///
  (deffixequiv svar-updates-pair-masks
    :hints(("Goal" :in-theory (enable svarlist-fix)))))

(define svex-updates-pair-masks ((updates svex-alist-p)
                                 (masks svex-mask-alist-p))
  :returns (newmasks svex-mask-alist-p
                     :hints(("Goal" :in-theory (enable svex-mask-alist-p))))
  :guard-hints (("goal" :in-theory (enable svarlist-p)))
  :measure (len (svex-alist-fix updates))
  (b* ((updates (svex-alist-fix updates))
       ((when (atom updates)) nil)
       ((cons var svex) (car updates))
       (mask (svex-mask-lookup (svex-var var) masks)))
    (cons (cons svex mask)
          (svex-updates-pair-masks (cdr updates) masks)))
  ///
  (deffixequiv svex-updates-pair-masks
    :hints(("Goal" :in-theory (enable svarlist-fix)))))

;; (defalist svar-mask-alist :key-type svar :val-type 4vmask)
(define svex-vars-detect-loops ((vars svarlist-p)
                                (masks1 svex-mask-alist-p)
                                (masks2 svex-mask-alist-p))
  :short "Collect variables whose masks may still be decreased by further compositions,
          and warn about those that have loops."
  :returns (vars svarlist-p)
  (b* (((when (atom vars)) nil)
       (svar1 (svar-fix (car vars)))
       (var1 (svex-var svar1))
       (mask1 (svex-mask-lookup var1 masks1))
       (mask2 (svex-mask-lookup var1 masks2))
       ((when (sparseint-< mask2 0))
        (cw "Warning: Infinite mask on variable ~x0~%" svar1)
        (svex-vars-detect-loops (cdr vars) masks1 masks2))
       ((when (sparseint-equal mask2 0))
        ;; Mask is now empty; drop this variable
        (svex-vars-detect-loops (cdr vars) masks1 masks2))
       ((when (or (sparseint-< mask1 0)
                  (< (4vmask-bitcount mask2) (4vmask-bitcount mask1))))
        ;; Mask decreasing; good
        (cons svar1 (svex-vars-detect-loops (cdr vars) masks1 masks2))))
    (cw "Warning: Mask for variable ~x0 is not decreasing: was ~x1, now ~x2~%" svar1
        mask1 mask2)
    (svex-vars-detect-loops (cdr vars) masks1 masks2)))


(local (defthm svarlist-p-of-hons-int1
         (implies (svarlist-p x)
                  (svarlist-p (acl2::hons-int1 x y)))
         :hints(("Goal" :in-theory (enable acl2::hons-int1)))))

(define svex-compose-extract-nonstable-vars ((loop-updates svex-alist-p)
                                             (curr-masks svex-mask-alist-p)
                                             (final-masks svex-mask-alist-p))
  ;; Extracts from loop-updates the subset of variables whose masks decrease
  ;; from curr-masks to final-masks.
  :measure (len (svex-alist-fix loop-updates))
  :returns (nonstable-updates svex-alist-p)
  (b* ((loop-updates (svex-alist-fix loop-updates))
       ((when (atom loop-updates)) nil)
       (var (caar loop-updates))
       (svex-var (svex-var var))
       (mask1 (svex-mask-lookup svex-var curr-masks))
       (mask2 (svex-mask-lookup svex-var final-masks))
       ((when (sparseint-< mask2 0))
        (svex-compose-extract-nonstable-vars (cdr loop-updates) curr-masks final-masks))
       ((when (sparseint-< mask1 0))
        (cons (car loop-updates)
              (svex-compose-extract-nonstable-vars (cdr loop-updates) curr-masks final-masks))))
    (if (< (4vmask-bitcount mask2) (4vmask-bitcount mask1))
        (cons (car loop-updates)
              (svex-compose-extract-nonstable-vars (cdr loop-updates) curr-masks final-masks))
      (svex-compose-extract-nonstable-vars (cdr loop-updates) curr-masks final-masks))))
       

(define svex-compose-keep-nonzero-mask-updates ((loop-updates svex-alist-p)
                                                (masks svex-mask-alist-p))
  :returns (pruned-updates svex-alist-p)
  :measure (len (svex-alist-fix loop-updates))
  (b* ((loop-updates (svex-alist-fix loop-updates))
       ((When (atom loop-updates)) nil)
       (svar (caar loop-updates))
       (var (svex-var svar))
       (mask (svex-mask-lookup var masks))
       ((when (sparseint-equal 0 mask))
        (svex-compose-keep-nonzero-mask-updates (cdr loop-updates) masks)))
    (cons (car loop-updates)
          (svex-compose-keep-nonzero-mask-updates (cdr loop-updates) masks))))
          


(defines svex-compose*
  :flag-local nil
  :parents (svex-composition)
  :short "Compose an svex with a substitution alist.  Variables not in the
substitution are left in place."
  (define svex-compose* ((x svex-p) (a svex-alist-p))
    :verify-guards nil
    :measure (svex-count x)
    :returns (xa svex-p "x composed with a, unbound variables preserved")
    (svex-case x
      :var (or (svex-fastlookup x.name a)
               (mbe :logic (svex-fix x) :exec x))
      :quote (mbe :logic (svex-fix x) :exec x)
      :call (svex-call* x.fn
                        (svexlist-compose* x.args a))))
  (define svexlist-compose* ((x svexlist-p) (a svex-alist-p))
    :measure (svexlist-count x)
    :returns (xa svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose* (car x) a)
            (svexlist-compose* (cdr x) a))))
  ///
  (verify-guards svex-compose*)
  (fty::deffixequiv-mutual svex-compose*
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm len-of-svexlist-compose*
    (equal (len (svexlist-compose* x a))
           (len x)))

  (local (defthm svex-env-lookup-of-append-svex-alist-eval-not-present
           (equal (svex-env-lookup v (append (svex-alist-eval a e) env))
                  (if (svex-lookup v a)
                      (svex-eval (svex-lookup v a) e)
                    (svex-env-lookup v env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup
                                             svex-env-fix
                                             svex-alist-fix
                                             svex-lookup)))))

  (defthm-svex-compose*-flag
    (defthm svex-eval-of-svex-compose*
      (equal (svex-eval (svex-compose* x a) env)
             (svex-eval x (append (svex-alist-eval a env) env)))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :flag svex-compose*)
    (defthm svexlist-eval-of-svexlist-compose*
      (equal (svexlist-eval (svexlist-compose* x a) env)
             (svexlist-eval x (append (svex-alist-eval a env) env)))
      :flag svexlist-compose*))

  (defthm-svex-compose*-flag
    (defthm vars-of-svex-compose*
      (implies (and (not (member v (svex-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svex-vars (svex-compose* x a)))))
      :flag svex-compose*)
    (defthm vars-of-svexlist-compose*
      (implies (and (not (member v (svexlist-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svexlist-vars (svexlist-compose* x a)))))
      :hints('(:in-theory (enable svexlist-vars)))
      :flag svexlist-compose*))

  (defthm-svex-compose*-flag
    ;; Note: The order of the disjuncts is important because sometimes you can
    ;; prove one given not the other but not vice versa.
    (defthm vars-of-svex-compose*-strong
      (implies (and (not (member v (svex-alist-vars a)))
                    (or (member v (svex-alist-keys a))
                        (not (member v (svex-vars x)))))
               (not (member v (svex-vars (svex-compose* x a)))))
      :flag svex-compose*)
    (defthm vars-of-svexlist-compose*-strong
      (implies (and (not (member v (svex-alist-vars a)))
                    (or (member v (svex-alist-keys a))
                        (not (member v (svexlist-vars x)))))
               (not (member v (svexlist-vars (svexlist-compose* x a)))))
      :hints('(:in-theory (enable svexlist-vars)))
      :flag svexlist-compose*))

  (in-theory (disable vars-of-svex-compose*-strong
                      vars-of-svexlist-compose*-strong))

  (memoize 'svex-compose* :condition '(eq (svex-kind x) :call)))

(define svex-alist-compose*-nrev ((x svex-alist-p)
                                 (a svex-alist-p)
                                 (nrev))
  :hooks nil
  (if (atom x)
      (acl2::nrev-fix nrev)
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (b* ((nrev (acl2::nrev-push (cons (caar x) (svex-compose* (cdar x) a)) nrev)))
          (svex-alist-compose*-nrev (cdr x) a nrev))
      (svex-alist-compose*-nrev (cdr x) a nrev))))

(define svex-alist-compose* ((x svex-alist-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (xx svex-alist-p)
  :verify-guards nil
  (if (atom x)
      nil
    (mbe :logic
         (if (mbt (and (consp (car x)) (svar-p (caar x))))
             (svex-acons (caar x) (svex-compose* (cdar x) a)
                         (svex-alist-compose* (cdr x) a))
           (svex-alist-compose* (cdr x) a))
         :exec
         (acl2::with-local-nrev
           (svex-alist-compose*-nrev x a acl2::nrev))))
  ///
  (local (defthm svex-alist-compose*-nrev-elim
           (equal (svex-alist-compose*-nrev x a nrev)
                  (append nrev (svex-alist-compose* x a)))
           :hints(("Goal" :in-theory (enable svex-alist-compose*-nrev
                                             svex-acons)))))
  (verify-guards svex-alist-compose*)

  (fty::deffixequiv svex-alist-compose*
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (defthm svex-alist-eval-of-svex-compose*
    (equal (svex-alist-eval (svex-alist-compose* x subst) env)
           (svex-alist-eval x (append (svex-alist-eval subst env) env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-acons
                                      svex-alist-compose*
                                      svex-env-acons))))

  (defthm vars-of-svex-alist-compose*
      (implies (and (not (member v (svex-alist-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svex-alist-vars (svex-alist-compose* x a)))))
      :hints(("goal" :in-theory (enable svex-alist-vars))))

  (local (defthm svex-compose*-under-iff
           (svex-compose* x a)
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-COMPOSE*.XA
                    :in-theory (disable RETURN-TYPE-OF-SVEX-COMPOSE*.XA)))))

  (local (defthm svex-fix-under-iff
           (svex-fix x)
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-FIX.NEW-X
                    :in-theory (disable RETURN-TYPE-OF-SVEX-FIX.NEW-X)))))

  (defthm svex-lookup-of-svex-alist-compose*
    (iff (svex-lookup v (svex-alist-compose* x a))
         (svex-lookup v x))
    :hints(("Goal" :in-theory (e/d (svex-lookup svex-alist-fix svex-acons)
                                   (svex-alist-p))))))


(define svexlist-compose-to-fix-rec2
  ((masks svex-mask-alist-p "Masks -- initially those of the updates, then those
                             for successive iterations of applying
                             loop-updates.")
   (loop-updates svex-alist-p
                 "Subset of update including only the bindings of the variables
                  that also appear as inputs.") ;; original dfs-composed assignments
   (count (or (natp count) (not count)) "Current count of the masks"))
  :prepwork ((local (defthm svarlist-p-of-instersection
                      (implies (svarlist-p a)
                               (svarlist-p (intersection-equal a b)))
                      :hints(("Goal" :in-theory (enable svarlist-p)))))
             (local (include-book "std/lists/take" :dir :system))
             (local (defthm svarlist-p-of-take
                      (implies (and (svarlist-p x)
                                    (<= (nfix n) (len x)))
                               (svarlist-p (take n x)))
                      :hints(("Goal" :in-theory (enable svarlist-p))))))
  :ruler-extenders :lambdas
  :hints(("Goal" :in-theory (enable o<)))
  :verify-guards nil
  :measure (if count
               (nfix count)
             (make-ord 1 1 0))
  :returns (mv (final-masks svex-mask-alist-p)
               (xx svex-alist-p))
  :short "Recompose the update functions together as long as it will decrease the
          care mask of some input variables that are also output variables."
  :long "
<p>Consider the SystemVerilog fragment:</p>
@({
 logic [2:0] a;
 assign a = ~{a[1:0], 1'b0};
 })

<p>At first glance this looks like a combinational loop: @('a') is used in its
own update function.  But at the bit level, this unwinds in a way that avoids
the combinational looping:</p>
@({
 assign a[2] = ~a[1];
 assign a[1] = ~a[0];
 assign a[0] = ~1'b0;
 })

<p>In SV, we don't bitblast; instead we look at the care masks of the variables
involved.  We start with the update function above.  The representation of the
RHS in svex is something like:</p>

@({
 (bitnot (concat 1 0 (zerox 2 a)))
 })

<p>First we compute the care masks for this, starting from the full mask (-1) (we show the masks in binary):</p>

@({
 (bitnot (concat 1 0 (zerox 2 a)))   --> -1
 (concat 1 0 (zerox 2 a))            --> -1
 (zerox 2 a)                         --> -1
 a                                   --> 11
})

<p>This means that we only care about the lower two bits of the input variable
@('a') in the update function given.</p>

<p>If we compose the update function with itself once, to begin unwinding the
loop, we'll get a new set of masks; these start with the mask @('11') for
the outermost expression:</p>

@({
 (bitnot (concat 1 0 (zerox 2 a)))   --> 11
 (concat 1 0 (zerox 2 a))            --> 11
 (zerox 2 a)                         -->  1
 a                                   -->  1
})

<p>Therefore, once we've composed the update function with itself once (so that
we have two nestings of it), we then only care about the LSB of the input
variable @('a').</p>

<p>Composing it on once more repeats the process:</p>

@({
 (bitnot (concat 1 0 (zerox 2 a)))   -->  1
 (concat 1 0 (zerox 2 a))            -->  1
 (zerox 2 a)                         -->  0
 a                                   -->  0
})

<p>This means if we've layered three copies of the update function, then we no
longer care about the input variable @('a'), so we can stop composing them.</p>

<p>For a less nice example:</p>

@({
 logic [3:0] a;
 assign a = ~{a[2:1], 1'b0, a[0]};
 })

<p>This does contain a combinational loop, but it also has a component that is
a false combinational loop.  If we do the same exercise with the masks, we find
the mask for @('a') with one copy of the update function is @('111'), with two
copies is @('11'), and with three or more is @('1').  So we still want to
compose the update function three times; more than that doesn't gain us
anything.</p>

<p>It is a bit confusing what happens when in this function; we annotate with
comments following this last example.</p>

"
  (b* (
       (- (cw "Loop variable count: ~x0~%" (len loop-updates)))
       (- (cw "Mask bits count: ~x0~%" count))

       ;; Initially, the masks are those of updates, i.e. those induced by
       ;; saying all bits of the update functions of named wires are cares.
       ;;  In the last example in the documentation, the mask for a is initially
       ;; 111, on second iteration, 11, on third and beyond 1.

       ;; This makes an (incomplete) mask alist mapping the update functions
       ;; for each of the variables to the mask for that variable as bound in
       ;; masks.  So in the first iteration, if a variable is used in the
       ;; updates, then its update function gets mapped to the mask for that
       ;; variable's occurrence in updates, which is (hopefully) less than the
       ;; full mask.  This maps (bitnot (concat 1 a (concat 1 0 (zerox 2 a))))
       ;; to 111 on the first iteration, then 11, then 1.
       (masks-start (svex-updates-pair-masks loop-updates masks))
       ;; Now expand those masks.  In the first iteration, this gives us the
       ;; masks for variables after composing together two copies of the
       ;; updates.  I.e. the mask for a is 11 in the first iteration and 1 in
       ;; the second and beyond.
       (masks-exp1 (cwtime (svex-mask-alist-expand masks-start) :mintime 0))

       ;; Now rewrite the loop-updates under those masks
       (updates-rw
        (cwtime (svexlist-rewrite-under-masks (svex-alist-vals loop-updates) masks-exp1)))
       (- (cw "Masked updates count: ~x0~%" (cwtime (svexlist-opcount updates-rw))))
       (- (fast-alist-free masks-exp1))
       (masks-exp (cwtime (svex-mask-alist-expand
                           (svex-updates-pair-masks (pairlis$ (svex-alist-keys loop-updates)
                                                              updates-rw)
                                                    masks))))

       (loop-vars (svex-alist-keys loop-updates))
       (new-count (cwtime (svexlist-masks-measure
                           loop-vars masks-exp) :mintime 0))
       ;; note: final-masks is a fast alist b/c svex-mask-alist-expand returns
       ;; a fast alist
       ((mv final-masks rest-alist)
        (b* (((when (eql 0 new-count))
              (cw "mask count reached 0~%")
              (mv masks-exp nil))
             ((when (and count (>= new-count (lnfix count))))
              (cw "Mask bits count didn't decrease~%")
              (mv masks-exp nil))
             (next-loop-updates (svex-compose-keep-nonzero-mask-updates loop-updates masks-exp)))
          (svexlist-compose-to-fix-rec2 masks-exp next-loop-updates new-count)))

       (changed-var-updates (with-fast-alist masks
                              (svex-compose-extract-nonstable-vars loop-updates
                                                                   masks
                                                                   final-masks)))
       (res (if rest-alist
                (with-fast-alist rest-alist
                  (svex-alist-compose* changed-var-updates rest-alist))
              changed-var-updates)))
    (clear-memoize-table 'svex-compose*)
    (mv final-masks res))
  ///
  (verify-guards svexlist-compose-to-fix-rec2
    :guard-debug t)
  (fty::deffixequiv svexlist-compose-to-fix-rec2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(second (car (last clause)))
                            ,(third (car (last clause)))))))))





;; The next part is gross.  We are going to do a version of Tarjan's
;; strongly-connected components algorithm on the graph formed of the
;; individual bits of the remaining looping variables.  Since Tarjan's
;; algorithm produces the SCCs in reverse topological order, at each SCC
;; computed we finalize that SCC's variables' update functions by:
;; - self-composing the SCC's update functions |SCC| times
;; - composing that result with the previously computed SCCs' update functions.

;; This is somewhat conservative since a variable can have bits in different
;; SCCs; if one such SCC depends on the other, then we need to compose that
;; variable's previous update function in, but if not, we are going to
;; conservatively do so anyway.  Perhaps we can revisit this later.

;; A real node of the graph is a pair (variable . bit-index).  However, we also
;; treat two other kinds of elements as pseudo-nodes:
;;  - (:bit svex . bit-index) denoting that bit of the svex, and
;;  - (:full svex . shift) denoting the entire svex right-shifted.
;; Certain expressions (concats with constant width and right-shifts of constant shift amount)
;; are passed through rather than being treated as nodes in themselves.
;; 


(fty::defmap svar-key-alist :key-type svar)

;; Use this for an optimization: don't traverse subtrees containing no looping vars
(defines svex-has-key
  (define svex-has-key ((x svex-p)
                        (var-alist svar-key-alist-p))
    :measure (two-nats-measure (svex-count x) 1)
    :returns (has-key
              (iff has-key
                   (intersectp (svex-vars x) (alist-keys (svar-key-alist-fix var-alist))))
              :hints ('(:expand ((svex-vars x)))))
    (svex-case x
      :var (consp (hons-get x.name (svar-key-alist-fix var-alist)))
      :quote nil
      :call (mbe :logic (svexlist-has-key x.args var-alist)
                 :exec (svex-call-has-key x var-alist))))
  (define svex-call-has-key ((x svex-p)
                             (var-alist svar-key-alist-p))
    :enabled t
    :guard (svex-case x :call)
    :measure (two-nats-measure (svex-count x) 0)
    (mbe :logic (svex-case x
                  :call (svexlist-has-key (svex-call->args x) var-alist)
                  :otherwise nil)
         :exec (svexlist-has-key (svex-call->args x) var-alist)))
  (define svexlist-has-key ((x svexlist-p)
                            (var-alist svar-key-alist-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (has-key
              (iff has-key
                   (intersectp (svexlist-vars x) (alist-keys (svar-key-alist-fix var-alist))))
              :hints ('(:expand ((svexlist-vars x)))))
    (if (atom x)
        nil
      (or (svex-has-key (car x) var-alist)
          (svexlist-has-key (cdr x) var-alist))))
  :prepwork ((local (defthm member-alist-keys
                      (iff (member x (alist-keys y))
                           (hons-assoc-equal x y))
                      :hints(("Goal" :in-theory (enable alist-keys hons-assoc-equal)))))
             (local (defthm consp-hons-assoc-equal
                      (iff (consp (hons-assoc-equal x y))
                           (hons-assoc-equal x y)))))
  ///
  (memoize 'svex-call-has-key))

(fty::defprod svex/index
  ((expr svex-p)
   (idx integerp :rule-classes :type-prescription
        "If nonnegative, the index of the bit we're traversing.  If negative, the
         lognot of the tail we're traversing."))
  :layout :tree :hons t)

(fty::defmap svex/index-nat-alist :key-type svex/index :val-type natp)
(fty::defmap svex/index-maybenat-alist :key-type svex/index :val-type maybe-natp)
(fty::defmap svex/index-key-alist :key-type svex/index)

(defprod svex-scc-consts
  ((final-masks svex-mask-alist-p "masks for looping vars")
   (loop-vars svar-key-alist-p "set of looping vars")
   (updates svex-alist-p "updates prior to bit-level loop-resolution"))
  :layout :tree)



;; The following is pseudocode for Tarjan's algorithm copied from the Wikipedia page
;; "Tarjan's strongly connected components algorithm",
;; https://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm
;; (Creative Commons Attribution-Share-Alike License):

 ;; algorithm tarjan is
 ;;  input: graph G = (V, E)
 ;;  output: set of strongly connected components (sets of vertices)

 ;;  index := 0
 ;;  S := empty array
 ;;  for each v in V do
 ;;    if (v.index is undefined) then
 ;;      strongconnect(v)
 ;;    end if
 ;;  end for

 ;;  function strongconnect(v)
 ;;    // Set the depth index for v to the smallest unused index
 ;;    v.index := index
 ;;    v.lowlink := index
 ;;    index := index + 1
 ;;    S.push(v)
 ;;    v.onStack := true

 ;;    // Consider successors of v
 ;;    for each (v, w) in E do
 ;;      if (w.index is undefined) then
 ;;        // Successor w has not yet been visited; recurse on it
 ;;        strongconnect(w)
 ;;        v.lowlink  := min(v.lowlink, w.lowlink)
 ;;      else if (w.onStack) then
 ;;        // Successor w is in stack S and hence in the current SCC
 ;;        // Note: The next line may look odd - but is correct.
 ;;        // It says w.index not w.lowlink; that is deliberate and from the original paper
 ;;        v.lowlink  := min(v.lowlink, w.index)
 ;;      end if
 ;;    end for

 ;;    // If v is a root node, pop the stack and generate an SCC
 ;;    if (v.lowlink = v.index) then
 ;;      start a new strongly connected component
 ;;      repeat
 ;;        w := S.pop()
 ;;        w.onStack := false
 ;;        add w to current strongly connected component
 ;;      while (w != v)
 ;;      output the current strongly connected component
 ;;    end if
 ;;  end function

;; Observations.

;; The lowlink value of a node doesn't need to be randomly available -- the
;; only use of a different node's lowlink value is when returning from a
;; recursive call, so the lowlink can simply be returned as one of the values
;; and not stored.

;; The index of a node is only useful while it is on the stack.  A couple
;; possible implementations:

;; - single fast alist where the node is associated with its index when first
;; traversed and then associated to NIL when popped off the stack

;; - two fast alists, one for the seen list and one for the stack: each node
;; traversed gets put on the seen list and stack, but then fast-alist-popped
;; off the stack when done.  (Either or both could store the index.)

;; We were going to try and treat variable/bit-index pairs as the only true
;; nodes and all other expressions as pseudo-nodes, which were just
;; intermediate stops on the way to computing a node's edge set.  We thought we
;; could still avoid traversing such pseudo-nodes multiple times by storing the
;; min lowlink value for future traversals.  But different traversals need to
;; produce different such values, depending on whether destination nodes are
;; still on the stack or not.

(deflist svex/indexlist :elt-type svex/index)


(define svex-sccs-get-scc ((key svex/index-p)
                           (stack svex/index-nat-alist-p))
  :guard (hons-get key stack)
  :measure (len (svex/index-nat-alist-fix stack))
  :returns (scc svex/indexlist-p)
  ;; Return the svex/index pairs making up the SCC.
  (b* ((key (svex/index-fix key))
       (stack (svex/index-nat-alist-fix stack))
       ((unless (mbt (consp stack)))
        (raise "Impossible"))
       ((when (equal key (caar stack)))
        (b* (((svex/index key)))
          (svex-case key.expr
            :var (list key)
            :otherwise nil)))
       ((svex/index trav1) (caar stack)))
    (svex-case trav1.expr
      :var
      (cons trav1
            (svex-sccs-get-scc key (cdr stack)))
      :otherwise (svex-sccs-get-scc key (cdr stack))))
  ///
  ;; Note: An SCC might be empty (of variables) because it just consists of a single expression.
  ;; We'll just check for this case and ignore it.

  ;; (local (defthm hons-assoc-equal-implies-consp-of-fix
  ;;          (implies (and (hons-assoc-equal key x)
  ;;                        (svex/index-p key))
  ;;                   (consp (svex/index-nat-alist-fix x)))
  ;;          :hints(("Goal" :in-theory (enable svex/index-nat-alist-fix
  ;;                                            hons-assoc-equal)))))

  ;; (defret consp-of-svex-sccs-get-scc
  ;;   (implies (and (hons-assoc-equal (svex/index-fix key)
  ;;                                   (svex/index-nat-alist-fix stack))
  ;;                 (
  ;;            (consp scc))
  ;;   :hints(("Goal" :in-theory (enable hons-assoc-equal
  ;;                                     svex/index-nat-alist-fix)
  ;;           :induct (svex-sccs-get-scc key stack))))
  )

(define svex-sccs-pop-stack ((key svex/index-p)
                                    (stack svex/index-nat-alist-p))
  :returns (new-stack svex/index-nat-alist-p)
  :measure (len (svex/index-nat-alist-fix stack))
  :guard (and (hons-get key stack)
              (no-duplicatesp-equal (alist-keys stack)))
  :guard-hints (("goal" :in-theory (enable alist-keys)))
  (b* ((key (svex/index-fix key))
       (stack (svex/index-nat-alist-fix stack))
       ((unless (mbt (consp stack)))
        (raise "Impossible"))
       ((when (equal key (caar stack)))
        (acl2::fast-alist-pop stack)))
    (svex-sccs-pop-stack key (acl2::fast-alist-pop stack)))
  ///
  (defret no-duplicates-of-svex-sccs-pop-stack
    (implies (no-duplicatesp (alist-keys (svex/index-nat-alist-fix stack)))
             (no-duplicatesp (alist-keys new-stack)))
    :hints(("Goal" :in-theory (enable alist-keys svex/index-nat-alist-fix))))

  (defret subsetp-of-svex-sccs-pop-stack
    (implies (subsetp (alist-keys (svex/index-nat-alist-fix stack)) other)
             (subsetp (alist-keys new-stack) other))
    :hints(("Goal" :in-theory (enable alist-keys svex/index-nat-alist-fix)))))


(include-book "std/util/defprojection" :dir :system)

(std::defprojection svex/indexlist-exprs ((x svex/indexlist-p))
  :returns (exprs svexlist-p)
  (svex/index->expr x))

(define svex-varlist-p ((x svexlist-p))
  (if (atom x)
      t
    (and (svex-case (car x) :var)
         (svex-varlist-p (cdr x)))))

(define svex-varlist-vars ((x svexlist-p))
  :guard (svex-varlist-p x)
  :returns (vars svarlist-p)
  :guard-hints (("goal" :in-theory (enable svex-varlist-p)))
  (if (atom x)
      nil
    (cons (svex-var->name (car x))
          (svex-varlist-vars (cdr x))))
  ///
  (defret len-of-svex-varlist-vars
    (equal (len vars) (len x))))

(define svex-alist-extract-bound-keys ((vars svarlist-p)
                            (x svex-alist-p))
  :returns (new-x svex-alist-p)
  (if (atom vars)
      nil
    (b* ((look (svex-fastlookup (car vars) x)))
      (if look
          (cons (cons (svar-fix (car vars)) look) (svex-alist-extract-bound-keys (cdr vars) x))
        (svex-alist-extract-bound-keys (cdr vars) x)))))

(define svex-alist-selfcompose-n-times ((n natp) (x svex-alist-p))
  :returns (new-x svex-alist-p)
  :verify-guards nil
  (b* (((when (zp n)) (svex-alist-fix x))
       (rest (svex-alist-selfcompose-n-times (1- n) x))
       ((acl2::with-fast rest))
       (ans (svex-alist-compose x rest)))
    (clear-memoize-table 'svex-compose)
    ans)
  ///
  (verify-guards svex-alist-selfcompose-n-times))
       

(define svex-sccs-finalize-scc ((scc svex/indexlist-p)
                                (params svex-scc-consts-p)
                                (finalized-updates svex-alist-p))
  :returns (mv (err)
               (new-finalized-updates svex-alist-p))
  (b* (((unless (consp scc)) (mv nil (svex-alist-fix finalized-updates)))
       (- (and (< 1 (len scc))
               (cw "Finalizing SCC of ~x0 bits: ~x1~%"
                   (len scc)
                   (ec-call (take (min 10 (len scc)) scc)))))
       (exprs (svex/indexlist-exprs scc))
       ((unless (svex-varlist-p exprs))
        (mv "Programming error -- SCC to finalize had non-variable expressions" nil))
       (vars (svex-varlist-vars exprs))
       ((svex-scc-consts params))
       (var-updates (svex-alist-extract-bound-keys vars params.updates))
       ((unless (eql (len var-updates) (len vars)))
        (mv "Programming error -- SCC contained variables without updates" nil))
       (selfcomposed (svex-alist-selfcompose-n-times (1- (len vars)) var-updates))
       (final (acl2::with-fast-alist finalized-updates
                (svex-alist-compose selfcomposed finalized-updates)))
       ;; (xes (pairlis$ vars (repeat (len vars) (svex-x))))
       ;; (final (acl2::with-fast-alist xes (sv::svex-alist-compose pre-final xes)))
       )
    (mv nil (append-without-guard final (svex-alist-fix finalized-updates)))))

(define svex/indices-for-mask ((x svex-p)
                               (mask 4vmask-p)
                               (offset natp))
  :guard (and (not (sparseint-< mask 0))
              (<= offset (sparseint-length mask)))
  :measure (nfix (- (sparseint-length (4vmask-fix mask)) (nfix offset)))
  :returns (pairs svex/indexlist-p)
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (include-book "arithmetic/top-with-meta" :dir :system)))
  (b* (((when (mbe :logic (zp (- (sparseint-length (4vmask-fix mask)) (nfix offset)))
                   :exec (eql offset (sparseint-length mask))))
        nil)
       (mask (4vmask-fix mask))
       ((when (eql 1 (sparseint-bit offset mask)))
        (cons (make-svex/index :expr x :idx (lnfix offset))
              (svex/indices-for-mask x mask (1+ (lnfix offset))))))
    (svex/indices-for-mask x mask (1+ (lnfix offset))))
  ///


  ;; (local (defthm logbitp-when-zp
  ;;          (implies (and (syntaxp (not (equal n ''0)))
  ;;                        (zp n))
  ;;                   (equal (logbitp n x)
  ;;                          (logbitp 0 x)))
  ;;          :hints(("Goal" :in-theory (enable logbitp)))))

  (local (defthm logbitp-past-integer-length
           (implies (and (<= 0 (ifix x))
                         (<= (integer-length x) (nfix n)))
                    (not (logbitp n x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defret member-of-svex/indices-for-mask
    (implies (and (<= 0 (sparseint-val (4vmask-fix mask)))
                  (svex/index-p p))
             (iff (member p pairs)
                  (b* (((svex/index p)))
                    (and (equal p.expr (svex-fix x))
                         (<= (lnfix offset) p.idx)
                         (logbitp p.idx (sparseint-val (4vmask-fix mask)))))))))
       
                               
(define svex/indices-of-masks ((x svex-mask-alist-p))
  ;; :measure (len (svex-mask-alist-fix x))
  :returns (pairs svex/indexlist-p)
  :prepwork ((local (in-theory (disable logbitp))))
  ;; (b* ((x (svex-mask-alist-fix x))
  ;;      ((when (atom x)) nil)
  ;;      ((unless (svex-case (caar x) :var))
  ;;       (svex/indices-of-masks (cdr x)))
  ;;      ((unless (<= 0 (cdar x)))
  ;;       (svex/indices-of-masks (cdr x))))
  ;;   (append-without-guard
  ;;    (svex/indices-for-mask (caar x) (cdar x) 0)
  ;;    (svex/indices-of-masks (cdr x))))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svex-p (caar x)))))
        (svex/indices-of-masks (cdr x)))
       ((unless (svex-case (caar x) :var))
        (svex/indices-of-masks (cdr x)))
       ((when (sparseint-< (4vmask-fix (cdar x)) 0))
        (svex/indices-of-masks (cdr x))))
    (append-without-guard
     (svex/indices-for-mask (caar x) (cdar x) 0)
     (svex/indices-of-masks (cdr x))))
  ///
  (local (defthm logbitp-when-zip
           (implies (zip x)
                    (equal (logbitp n x) nil))
           :hints(("Goal" :in-theory (enable logbitp)))))
  
  

  (local (defthm svex-mask-lookup-alt-def
           (equal (svex-mask-lookup v x)
                  (if (consp x)
                      (if (and (consp (car x))
                               (equal (svex-fix v) (caar x)))
                          (4vmask-fix (cdar x))
                        (svex-mask-lookup v (cdr x)))
                    0))
           :hints(("Goal" :in-theory (enable svex-mask-lookup)))
           :rule-classes ((:definition :controller-alist ((svex-mask-lookup nil t))))))

  (fty::deffixequiv svex/indices-of-masks
    :hints (("goal" :in-theory (enable svex-mask-alist-fix))))

  (local (defthm member-of-svexlist-filter-alist-keys-when-logbitp-of-mask-lookup
           (implies (and (logbitp n (sparseint-val (svex-mask-lookup k x)))
                         (svex-p k))
                    (member k (svexlist-filter (alist-keys x))))
           :hints(("Goal" :in-theory (enable alist-keys svexlist-filter)))))

  (defret member-svex/indices-iff-lookup
    (implies (and (svex/index-p p)
                  (no-duplicatesp (alist-keys (svex-mask-alist-fix x))))
             (iff (member p pairs)
                  (b* (((svex/index p)))
                    (and (svex-case p.expr :var)
                         (<= 0 p.idx)
                         (<= 0 (sparseint-val (svex-mask-lookup p.expr x)))
                         (logbitp p.idx (sparseint-val (svex-mask-lookup p.expr x)))))))
    :hints(("Goal" :in-theory (e/d (alist-keys
                                    svex-mask-alist-fix
                                      svexlist-filter
                                      ;; 4vmask-fix
                                      4vmask-p)
                                   (svex-mask-lookup
                                    SVEX/INDEX-P-WHEN-MEMBER-EQUAL-OF-SVEX/INDEXLIST-P)
                                   ;; (ALIST-KEYS-OF-SVEX-MASK-ALIST-FIX)
                                   )
            :induct t
            :do-not-induct t
            :expand ((:free (p) (svex-mask-lookup p x)))))))


(define svex-scc-min-lowlink ((x maybe-natp)
                              (y maybe-natp))
  :returns (min maybe-natp)
  (b* ((x (acl2::maybe-natp-fix x))
       (y (acl2::maybe-natp-fix y)))
    (if x
        (if y
            (min x y)
          x)
      y)))


(local (include-book "centaur/bitops/ihsext-basics" :dir :system))


(local (defthmd member-of-svexlist-filter
         (implies (not (member k x))
                  (not (member k (svexlist-filter x))))
         :hints(("Goal" :in-theory (enable svexlist-filter)))))
(local (defthm no-duplicates-of-svexlist-filter
         (implies (no-duplicatesp x)
                  (no-duplicatesp (svexlist-filter x)))
         :hints(("Goal" :in-theory (enable svexlist-filter
                                           member-of-svexlist-filter)))))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (in-theory (disable fast-alist-clean)))
(local (defthm alist-keys-of-hons-remove-assoc
         (equal (alist-keys (acl2::hons-remove-assoc k x))
                (remove k (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys acl2::hons-remove-assoc)))))
(local (defthm no-duplicate-keys-of-fast-alist-clean
         (no-duplicatesp (alist-keys (fast-alist-clean x)))
         :hints(("Goal" :in-theory (enable acl2::fast-alist-clean-by-remove-assoc)))))

(local (defthm svex-mask-lookup-of-fast-alist-clean
         (equal (svex-mask-lookup k (fast-alist-clean x))
                (svex-mask-lookup k x))
         :hints(("Goal" :in-theory (enable svex-mask-lookup)))))


#||

#!sv
(trace$
 (svex-compose-bit-sccs :cond (svex-case (svex/index->expr x) :var)
                        :entry (list 'svex-compose-bit-sccs x trav-index)
                        :exit 
                        (b* (((list err min-lowlink new-trav-index stack) values))
                          (list 'svex-compose-bit-sccs err min-lowlink new-trav-index (len stack)))))


||#

(progn
  (with-output :off (event prove)
    (defines svex-compose-bit-sccs
      :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
                 (local (in-theory (disable set-difference-equal
                                            member-equal
                                            set::pick-a-point-subsetp-equal-strategy
                                            set::empty-set-unique
                                            acl2::logtail-identity)))
                 )
      (define svex-compose-bit-sccs
        :long "<p>Implementation notes.</p>

<p>A node is a variable/bit-index pair that is a looping bit from final-masks.
A pseudo-node is an svex/integer pair, representing either a bit of that svex
expression (if the index is nonnegative) or a tail of that expression (if
negative -- the lognot is the number of bits to shift).</p>"
        
        ((x svex/index-p "current expression/bit (pseudo-node) to be traversed")
         (trav-index natp "next unused traversal index")
         (stack svex/index-nat-alist-p
                "Stack of elements not yet assigned to an SCC.")
         (trav-indices svex/index-nat-alist-p
                       "Traversal indices of nodes that have been visited.")
         (finalized-updates svex-alist-p
                            "Accumulator of finalized update functions.")
         (params svex-scc-consts-p))
        :guard (and (no-duplicatesp-equal (alist-keys trav-indices))
                    (no-duplicatesp-equal (alist-keys stack))
                    (subsetp-equal (alist-keys stack) (alist-keys trav-indices)))

        :well-founded-relation acl2::nat-list-<
        :measure (list (len (set-difference$ (svex/indices-of-masks
                                              (fast-alist-clean (svex-scc-consts->final-masks params)))
                                             (alist-keys (svex/index-nat-alist-fix trav-indices))))
                       (svex-count (svex/index->expr x))
                       0
                       0)
        :measure-debug t
        :hints (("goal" :in-theory (enable alist-keys))
                (and stable-under-simplificationp
                     '(:in-theory (enable nfix))))
        :verify-guards nil

        :returns (mv (err)
                     (min-lowlink maybe-natp :rule-classes :type-prescription)
                     (new-trav-index natp :rule-classes :type-prescription)
                     (new-stack svex/index-nat-alist-p)
                     (new-trav-indices svex/index-nat-alist-p)
                     (new-finalized-updates svex-alist-p))

        (b* (((symlet
               (!return (mv err min-lowlink trav-index stack trav-indices finalized-updates))
               (!args   (trav-index stack trav-indices finalized-updates params))))

             ((svex/index x) (svex/index-fix x))
             (trav-index (lnfix trav-index))
             (trav-indices (svex/index-nat-alist-fix trav-indices))
             (stack (svex/index-nat-alist-fix stack))
             (finalized-updates (svex-alist-fix finalized-updates))
             ((svex-scc-consts params))

             (min-lowlink nil)
             (err nil)

             (index-look (hons-get x trav-indices))
             ((when index-look)
              (b* ((stack-look (hons-get x stack))
                   ((when stack-look)
                    ;; number to use is the traversal index, not the lowlink -- corresponds to
                    ;; the if (w.onStack) case in the Wikipedia pseudocode above.
                    (b* ((min-lowlink (cdr index-look)))
                      !return)))
                ;; Note: This corresponds to the case in the pseudocode where w has
                ;; already been visited but is not on the stack, meaning it is in a
                ;; different SCC, and it does not contribute to the lowlink of the
                ;; nodes above.  So we return NIL as the min-lowlin.
                !return))
             ((unless (svex-has-key x.expr params.loop-vars))
              !return))

          (svex-case x.expr
            :call (b* ((index trav-index)
                       (stack (hons-acons x index stack))
                       (trav-indices (hons-acons x index trav-indices))
                       (trav-index (1+ trav-index))
                       (mask (if (<= 0 x.idx)
                                 (sparseint-concatenate x.idx 0 1)
                               (sparseint-concatenate (lognot x.idx) 0 -1)))
                       (argmasks (svex-argmasks mask x.expr.fn x.expr.args))
                       (!return
                        (svex-args-compose-bit-sccs
                         x.expr.args argmasks . !args))
                       ((when err) !return))
                    !return)
            :var (b* (((unless (<= 0 x.idx))
                       (b* ((err (msg "Encountered a negative-mask variable ~x0. ~
                                   Debugging info saved in ~x1."
                                      x.expr.name :svex-scc-debug-info))
                            (- (sneaky-save :svex-scc-debug-info
                                            (list x . !args))))
                         !return))
                      ;; Before continuing, make sure we're in the final-masks.
                      (mask-look (svex-mask-lookup x.expr params.final-masks))
                      ((when (sparseint-< mask-look 0))
                       (b* ((err (msg "Encountered a variable ~x0 that had negative
                                   final-masks.  ~ Debugging info saved in
                                   ~x1."
                                      x.expr.name :svex-scc-debug-info))
                            (- (sneaky-save :svex-scc-debug-info
                                            (list x . !args))))
                         !return))
                      ((unless (eql 1 (sparseint-bit x.idx mask-look)))
                       ;; This bit isn't set in the masks so this isn't one of the looping bits.
                       !return)

                      (update (svex-fastlookup x.expr.name params.updates))
                      ((unless update)
                       ;; Combinational input... should we warn?
                       !return)
                      
                      (index trav-index)
                      (stack (hons-acons x index stack))
                      (trav-indices (hons-acons x index trav-indices))
                      (trav-index (1+ trav-index))

                      (!return
                       (svex-compose-bit-sccs
                        (make-svex/index :expr update :idx x.idx) . !args))
                      ((when err) !return)

                      (min-lowlink (svex-scc-min-lowlink min-lowlink index))

                      ((unless (eql min-lowlink index))
                       ;; SCC is not complete yet.
                       !return)

                      ;; SCC is complete.  Finalize it...
                      (scc (svex-sccs-get-scc x stack))
                      (stack (svex-sccs-pop-stack x stack))
                      ((mv err finalized-updates) (svex-sccs-finalize-scc scc params finalized-updates))
                      ((when err) !return))
                   !return)
            :otherwise 
            (prog2$ (raise "impossible")
                    !return))))
      
      
      (define svex-args-compose-bit-sccs ((x svexlist-p)
                                          (argmasks 4vmasklist-p)
                                          (trav-index natp)
                                          (stack svex/index-nat-alist-p)
                                          (trav-indices svex/index-nat-alist-p)
                                          (finalized-updates svex-alist-p)
                                          (params svex-scc-consts-p))
        :guard (and (no-duplicatesp-equal (alist-keys trav-indices))
                    (no-duplicatesp-equal (alist-keys stack))
                    (subsetp-equal (alist-keys stack) (alist-keys trav-indices))
                    (eql (len argmasks) (len x)))

        
        :measure (list (len (set-difference$ (svex/indices-of-masks
                                              (fast-alist-clean (svex-scc-consts->final-masks params)))
                                             (alist-keys (svex/index-nat-alist-fix trav-indices))))
                       (svexlist-count x)
                       (len x)
                       0)
        

        :returns (mv (err)
                     (min-lowlink maybe-natp :rule-classes :type-prescription)
                     (new-trav-index natp :rule-classes :type-prescription)
                     (new-stack svex/index-nat-alist-p)
                     (new-trav-indices svex/index-nat-alist-p)
                     (new-finalized-updates svex-alist-p))

        (b* (((symlet
               (!return (mv err min-lowlink trav-index stack trav-indices finalized-updates))
               (!args   (trav-index stack trav-indices finalized-updates params))))
             (trav-index (lnfix trav-index))
             (trav-indices (svex/index-nat-alist-fix trav-indices))
             (stack (svex/index-nat-alist-fix stack))
             (finalized-updates (svex-alist-fix finalized-updates))

             ((when (atom x))
              (b* ((min-lowlink nil)
                   (err nil))
                !return))

             (!return
              (b* ((old-trav-indices trav-indices)
                   (!return
                    (svex-mask-compose-bit-sccs
                     (car x) 0 (car argmasks) . !args))
                   (err (or err
                            (and (not (mbt (<= (len (set-difference$
                                                     (svex/indices-of-masks
                                                      (fast-alist-clean (svex-scc-consts->final-masks params)))
                                                     (alist-keys (svex/index-nat-alist-fix trav-indices))))
                                               (len (set-difference$
                                                     (svex/indices-of-masks
                                                      (fast-alist-clean (svex-scc-consts->final-masks params)))
                                                     (alist-keys (svex/index-nat-alist-fix old-trav-indices)))))))
                                 "Measure increased, impossibly"))))
                !return))
             
             ((when err) !return)
             (min-lowlink1 min-lowlink)

             (!return
              (svex-args-compose-bit-sccs
               (cdr x) (cdr argmasks) . !args))
             ((when err) !return)

             (min-lowlink (svex-scc-min-lowlink min-lowlink1 min-lowlink)))
          !return))

      (define svex-mask-compose-bit-sccs ((x svex-p)
                                          (offset natp)
                                          (mask 4vmask-p)
                                          (trav-index natp)
                                          (stack svex/index-nat-alist-p)
                                          (trav-indices svex/index-nat-alist-p)
                                          (finalized-updates svex-alist-p)
                                          (params svex-scc-consts-p))
        :guard (and (no-duplicatesp-equal (alist-keys trav-indices))
                    (no-duplicatesp-equal (alist-keys stack))
                    (subsetp-equal (alist-keys stack) (alist-keys trav-indices)))

        :measure (list (len (set-difference$ (svex/indices-of-masks
                                              (fast-alist-clean (svex-scc-consts->final-masks params)))
                                             (alist-keys (svex/index-nat-alist-fix trav-indices))))
                       (svex-count x)
                       0
                       (+ 1 (nfix (- (sparseint-length (4vmask-fix mask)) (nfix offset)))))
        

        :returns (mv (err)
                     (min-lowlink maybe-natp :rule-classes :type-prescription)
                     (new-trav-index natp :rule-classes :type-prescription)
                     (new-stack svex/index-nat-alist-p)
                     (new-trav-indices svex/index-nat-alist-p)
                     (new-finalized-updates svex-alist-p))

        (b* (((symlet
               (!return (mv err min-lowlink trav-index stack trav-indices finalized-updates))
               (!args   (trav-index stack trav-indices finalized-updates params))))
             (mask (4vmask-fix mask))
             (offset (lnfix offset))
             (trav-index (lnfix trav-index))
             (trav-indices (svex/index-nat-alist-fix trav-indices))
             (stack (svex/index-nat-alist-fix stack))
             (finalized-updates (svex-alist-fix finalized-updates))

             (min-lowlink nil)
             (err nil)

             ((when (<= (sparseint-length mask) offset))
              (b* ((tail (sparseint-rightshift offset mask)) ;; either 0 or -1.
                   ((when (sparseint-equal tail 0)) !return)
                   (pair (make-svex/index :expr x :idx (lognot offset))))
                (svex-compose-bit-sccs pair trav-index stack trav-indices finalized-updates params)))

             (next-idx (+ offset (sparseint-trailing-0-count-from mask offset)))
             ;; next-idx might just be offset itself, still need to increment it before recurring
             ;; (logbitp next-idx mask) is always true

             (pair (make-svex/index :expr x :idx next-idx))

             (!return
              (b* ((old-trav-indices trav-indices)
                   (!return
                    (svex-compose-bit-sccs pair . !args))
                   (err (or err
                            (and (not (mbt (<= (len (set-difference$
                                                     (svex/indices-of-masks
                                                      (fast-alist-clean (svex-scc-consts->final-masks params)))
                                                     (alist-keys (svex/index-nat-alist-fix trav-indices))))
                                               (len (set-difference$
                                                     (svex/indices-of-masks
                                                      (fast-alist-clean (svex-scc-consts->final-masks params)))
                                                     (alist-keys (svex/index-nat-alist-fix old-trav-indices)))))))
                                 "Measure increased, impossibly"))))
                !return))

             ((when err) !return)
             (min-lowlink1 min-lowlink)

             (!return
              (svex-mask-compose-bit-sccs
               x (1+ next-idx) mask . !args))
             ((when err) !return)

             (min-lowlink (svex-scc-min-lowlink min-lowlink1 min-lowlink)))
          !return))
      ///
      (local (set-default-hints nil))
      (local (in-theory (disable SET::PICK-A-POINT-SUBSETP-EQUAL-STRATEGY)))
      (local (in-theory (disable svex-compose-bit-sccs
                                 svex-mask-compose-bit-sccs
                                 svex-args-compose-bit-sccs)))

      (std::defret-mutual trav-indices-superset-of-svex-compose-bit-sccs
        (defret trav-indices-superset-of-svex-compose-bit-sccs
          (subsetp (alist-keys (svex/index-nat-alist-fix trav-indices))
                   (alist-keys new-trav-indices))
          :hints ('(:expand (<call>)
                    :in-theory (enable alist-keys)))
          :fn svex-compose-bit-sccs)
        (defret trav-indices-superset-of-svex-args-compose-bit-sccs
          (subsetp (alist-keys (svex/index-nat-alist-fix trav-indices))
                   (alist-keys new-trav-indices))
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret trav-indices-superset-of-svex-mask-compose-bit-sccs
          (subsetp (alist-keys (svex/index-nat-alist-fix trav-indices))
                   (alist-keys new-trav-indices))
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

      (defret trav-indices-superset-of-svex-compose-bit-sccs-no-fix
        (implies (svex/index-nat-alist-p trav-indices)
                 (subsetp (alist-keys trav-indices)
                          (alist-keys new-trav-indices)))
        :hints (("goal" :use ((:instance trav-indices-superset-of-svex-compose-bit-sccs))
                 :in-theory (disable trav-indices-superset-of-svex-compose-bit-sccs)))
        :fn svex-compose-bit-sccs)

      (defret trav-indices-superset-of-svex-mask-compose-bit-sccs-no-fix
        (implies (svex/index-nat-alist-p trav-indices)
                 (subsetp (alist-keys trav-indices)
                          (alist-keys new-trav-indices)))
        :hints (("goal" :use ((:instance trav-indices-superset-of-svex-mask-compose-bit-sccs))
                 :in-theory (disable trav-indices-superset-of-svex-mask-compose-bit-sccs)))
        :fn svex-mask-compose-bit-sccs)

      (local (defthm member-alist-keys
               (iff (member k (alist-keys x))
                    (hons-assoc-equal k x))
               :hints(("Goal" :in-theory (enable alist-keys)))))

      (std::defret-mutual trav-indices-no-duplicates-of-svex-compose-bit-sccs
        (defret trav-indices-no-duplicates-of-svex-compose-bit-sccs
          (implies (no-duplicatesp (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (no-duplicatesp (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)
                    :in-theory (enable alist-keys)))
          :fn svex-compose-bit-sccs)
        (defret trav-indices-no-duplicates-of-svex-args-compose-bit-sccs
          (implies (no-duplicatesp (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (no-duplicatesp (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret trav-indices-no-duplicates-of-svex-mask-compose-bit-sccs
          (implies (no-duplicatesp (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (no-duplicatesp (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

      (std::defret-mutual stack-subsetp-of-indices-svex-compose-bit-sccs
        (defret stack-subsetp-of-indices-svex-compose-bit-sccs
          (implies (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                            (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (subsetp (alist-keys new-stack) (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)
                    :in-theory (enable alist-keys)))
          :fn svex-compose-bit-sccs)
        (defret stack-subsetp-of-indices-svex-args-compose-bit-sccs
          (implies (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                            (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (subsetp (alist-keys new-stack) (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret stack-subsetp-of-indices-svex-mask-compose-bit-sccs
          (implies (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                            (alist-keys (svex/index-nat-alist-fix trav-indices)))
                   (subsetp (alist-keys new-stack) (alist-keys new-trav-indices)))
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

      (local (defthm suffixp-of-svex-sccs-pop-stack
               (implies (and (acl2::suffixp (cons (cons (svex/index-fix x) val) stack)
                                            stack1)
                             (svex/index-nat-alist-p stack1))
                        (acl2::suffixp stack (svex-sccs-pop-stack x stack1)))
               :hints(("Goal" :in-theory (enable svex-sccs-pop-stack acl2::suffixp)))))

      (std::defret-mutual stack-suffixp-of-svex-compose-bit-sccs
        (defret stack-suffixp-of-svex-compose-bit-sccs
          (acl2::suffixp (svex/index-nat-alist-fix stack)
                         new-stack)
          :hints ('(:expand (<call>)
                    :in-theory (enable alist-keys acl2::suffixp)))
          :fn svex-compose-bit-sccs)
        (defret stack-suffixp-of-svex-args-compose-bit-sccs
          (acl2::suffixp (svex/index-nat-alist-fix stack)
                         new-stack)
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret stack-suffixp-of-svex-mask-compose-bit-sccs
          (acl2::suffixp (svex/index-nat-alist-fix stack)
                         new-stack)
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

      (local (defthmd not-in-stack-when-not-in-trav-indices
               (implies (and (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                                      (alist-keys (svex/index-nat-alist-fix trav-indices)))
                             (svex/index-p x)
                             (not (hons-assoc-equal x trav-indices)))
                        (not (hons-assoc-equal x stack)))
               :hints(("Goal" :in-theory (enable svex/index-nat-alist-fix alist-keys)
                       :induct (svex/index-nat-alist-fix stack)))))
      

      (std::defret-mutual stack-subsetp-of-svex-compose-bit-sccs
        (defret stack-no-duplicatesp-of-svex-compose-bit-sccs
          (implies (and (no-duplicatesp (alist-keys (svex/index-nat-alist-fix stack)))
                        (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                                 (alist-keys (svex/index-nat-alist-fix trav-indices))))
                   (no-duplicatesp (alist-keys new-stack)))
          :hints ('(:expand (<call>)
                    :in-theory (enable alist-keys
                                       not-in-stack-when-not-in-trav-indices)))
          :fn svex-compose-bit-sccs)
        (defret stack-no-duplicates-of-svex-args-compose-bit-sccs
          (implies (and (no-duplicatesp (alist-keys (svex/index-nat-alist-fix stack)))
                        (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                                 (alist-keys (svex/index-nat-alist-fix trav-indices))))
                   (no-duplicatesp (alist-keys new-stack)))
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret stack-no-duplicates-of-svex-mask-compose-bit-sccs
          (implies (and (no-duplicatesp (alist-keys (svex/index-nat-alist-fix stack)))
                        (subsetp (alist-keys (svex/index-nat-alist-fix stack))
                                 (alist-keys (svex/index-nat-alist-fix trav-indices))))
                   (no-duplicatesp (alist-keys new-stack)))
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

      (local (defthm set-difference-when-subset
               (implies (subsetp a b)
                        (<= (len (set-difference$ x b))
                            (len (set-difference$ x a))))))

      (local (defthm len-equal-0
               (equal (equal (len x) 0)
                      (not (consp x)))
               :hints(("Goal" :in-theory (enable len)))))

      (local (defthmd not-in-stack-when-not-in-trav-indices-nofix
               (implies (and (subsetp (alist-keys stack)
                                      (alist-keys trav-indices))
                             (not (hons-assoc-equal x trav-indices)))
                        (not (hons-assoc-equal x stack)))
               :hints(("Goal" :in-theory (enable alist-keys)
                       :induct (hons-assoc-equal x stack)))))

      (local (defthmd hons-assoc-equal-when-suffixp
               (implies (and (hons-assoc-equal x a)
                             (acl2::suffixp a b))
                        (hons-assoc-equal x b))
               :hints(("Goal" :in-theory (enable acl2::suffixp)))))

      (local (defthmd hons-assoc-equal-when-suffixp-fix
               (implies (and (hons-assoc-equal x a)
                             (acl2::suffixp (svex/index-nat-alist-fix a) b)
                             (svex/index-p x))
                        (hons-assoc-equal x b))
               :hints(("Goal" :use ((:instance hons-assoc-equal-when-suffixp
                                     (a (svex/index-nat-alist-fix a))))
                       :in-theory (disable hons-assoc-equal-when-suffixp)))))

      (local (defret hons-assoc-equal-in-stack-of-svex-compose-bit-sccs
               (implies (hons-assoc-equal k (svex/index-nat-alist-fix stack))
                        (hons-assoc-equal k new-stack))
               :hints(("Goal" :in-theory (enable hons-assoc-equal-when-suffixp-fix)))
               :fn svex-compose-bit-sccs))

      (verify-guards svex-compose-bit-sccs
        :hints(("Goal" :in-theory (enable alist-keys
                                          not-in-stack-when-not-in-trav-indices-nofix)
                :do-not-induct t))
        :guard-debug t
        :otf-flg t)

      (fty::deffixequiv-mutual svex-compose-bit-sccs
        :hints((acl2::just-expand-mrec-default-hint 'svex-compose-bit-sccs
                                                    id nil world))))))




(define svex-mask-alist-compose-bit-sccs

  ((x svex-mask-alist-p)
   (trav-index natp "next unused traversal index")
   (stack svex/index-nat-alist-p
          "stack of elements not yet assigned to an SCC.")
   (trav-indices svex/index-nat-alist-p
                 "traversal indices of nodes that have been visited.")
   (finalized-updates svex-alist-p
                      "accumulator of finalized update functions.")
   (params svex-scc-consts-p))
  :guard (and (no-duplicatesp-equal (alist-keys trav-indices))
              (no-duplicatesp-equal (alist-keys stack))
              (subsetp-equal (alist-keys stack) (alist-keys trav-indices)))

  :returns (mv (err)
               (new-finalized-updates svex-alist-p))
  :hooks ((:fix :hints (("goal" :in-theory (enable svex-mask-alist-fix)))))
  :verbosep t
  (b* ((err nil)
       ((when (atom x)) (mv err (svex-alist-fix finalized-updates)))
       ((unless (mbt (and (consp (car x)) (svex-p (caar x)))))
        (svex-mask-alist-compose-bit-sccs (cdr x) trav-index stack trav-indices finalized-updates params))
       ((cons key mask) (car x))
       ((unless (and (svex-case key :var)
                     (not (sparseint-equal 0 (4vmask-fix mask)))
                     (svex-fastlookup (svex-var->name key)
                                      (svex-scc-consts->updates params))))
        (svex-mask-alist-compose-bit-sccs (cdr x) trav-index stack trav-indices finalized-updates params))
       ((mv err ?min-lowlink trav-index stack trav-indices finalized-updates)
        (prog2$ (cw "svex-mask-compose-bit-sccs, key: ~x0, mask: ~x1~%" key mask)
                (svex-mask-compose-bit-sccs key 0 mask trav-index stack trav-indices finalized-updates params)))
       ((when err) (mv err finalized-updates)))
    (svex-mask-alist-compose-bit-sccs (cdr x) trav-index stack trav-indices finalized-updates params)))




;; (trace$ #!sv (sv::svex-compose-loopdebug
;;          :entry (list 'svex-compose-loopdebug
;;                       x mask (cdr (hons-get x stack)))
;;          :evisc-tuple '(nil 5 10 nil)
;;          :hide nil))


(define svex-loopdebug-stack-search ((x svex-p)
                                     (mask 4vmask-p)
                                     (stack svex-mask-alist-p))
  :returns (loop-stack svex-mask-alist-p)
  :measure (len (svex-mask-alist-fix stack))
  (b* ((stack (svex-mask-alist-fix stack))
       ((when (atom stack)) nil)
       ((when (and (equal (svex-fix x) (caar stack))
                   ;; previously seen mask is a (non-strict) subset of the current mask
                   (not (sparseint-test-bitandc2 (cdar stack) (4vmask-fix mask)))))
        (list (car stack)))
       (rest (svex-loopdebug-stack-search x mask (cdr stack))))
    (and rest (cons (car stack) rest))))
    

(defines svex-compose-loopdebug
  :parents (sv)
  :short "Look for a combinational loop under the given masks."
  :long "<p>The stack maps each variable we're traversing to the care mask when
we encountered it.  We say we've found a loop when we encounter a variable that
we've seen before with a mask that overlaps with that one.</p>"

  :prepwork ((local (defthm lookup-in-svex-mask-alist
                      (implies (and (svex-mask-alist-p x)
                                    (hons-assoc-equal k x))
                               (and (4vmask-p (cdr (hons-assoc-equal k x)))))
                      :hints(("Goal" :in-theory (enable svex-mask-alist-p
                                                        hons-assoc-equal))))))
                               
  :guard-debug t

  (define svex-compose-loopdebug ((x svex-p "svex we're traversing")
                                  (mask 4vmask-p "current care mask")
                                  (assigns svex-alist-p "alist of assign stmts")
                                  (stack "alist of seen vars"
                                         svex-mask-alist-p)
                                  (depthlimit natp))
    :verify-guards nil
    :well-founded-relation acl2::nat-list-<
    :measure (list depthlimit (svex-count x))
    :returns (mv (var (iff (svar-p var) var) "indicates the endpoint of the loop, if found")
                 (loopstack svex-mask-alist-p "stack showing the combinational loop, if found"))
    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (stack (svex-mask-alist-fix stack))
         (mask (4vmask-fix mask))
         ((when (sparseint-equal mask 0)) (mv nil nil)))
      (svex-case x
        :quote (mv nil nil)
        :call (b* ((argmasks (svex-argmasks mask x.fn x.args)))
                (svexlist-compose-loopdebug x.args argmasks assigns stack depthlimit))
        :var (b* ((stack-look (hons-get x stack))
                  ;; reduce overhead of stack search to only variables that
                  ;; exist in the stack
                  (loopstack (and stack-look
                                  (svex-loopdebug-stack-search x mask stack)))
                  ((when loopstack)
                   (b* ((loopstack (cons (cons x mask) loopstack)))
                     (cw "Combinational loop for ~x0: ~x1~%" x.name loopstack)
                     (mv x.name loopstack)))
                  (assign (svex-fastlookup x.name assigns))
                  ((unless assign) (mv nil nil))
                  ((when (zp depthlimit)) (mv nil nil))
                  (stack (hons-acons x mask stack))
                  ((mv loopvar loopstack)
                   (svex-compose-loopdebug assign mask assigns stack (1- depthlimit)))
                  (- (acl2::fast-alist-pop* stack-look stack)))
               (mv loopvar loopstack)))))

  (define svexlist-compose-loopdebug ((x svexlist-p)
                                      (masks 4vmasklist-p)
                                      (assigns svex-alist-p)
                                      (stack svex-mask-alist-p)
                                      (depthlimit natp))
    :guard (eql (len masks) (len x))
    :measure (list depthlimit (svexlist-count x))
    :returns (mv (var (iff (svar-p var) var) "indicates the endpoint of the loop, if found")
                 (loopstack svex-mask-alist-p "stack showing the combinational loop, if found"))
    (b* (((when (atom x)) (mv nil nil))
         ((mv loopvar loopstack)
          (svex-compose-loopdebug (car x) (car masks) assigns stack depthlimit))
         ((when loopvar) (mv loopvar loopstack)))
      (svexlist-compose-loopdebug (cdr x) (cdr masks) assigns stack depthlimit)))
  ///
  (verify-guards svex-compose-loopdebug)

  (fty::deffixequiv-mutual svex-compose-loopdebug
    :hints (("goal" :expand ((svexlist-fix x))))))




(define svex-masks-summarize-loops ((loop-vars svarlist-p)
                                    (final-masks svex-mask-alist-p)
                                    (assigns svex-alist-p))
  (b* (((when (atom loop-vars)) nil)
       (svar1 (car loop-vars))
       (var1 (svex-var svar1))
       (mask1 (svex-mask-lookup var1 final-masks))
       ((when (sparseint-equal mask1 0))
        (svex-masks-summarize-loops (cdr loop-vars) final-masks assigns))
       ((mv & &)
        (svex-compose-loopdebug var1 mask1 assigns nil 100)))
    (svex-masks-summarize-loops (cdr loop-vars) final-masks assigns)))





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

(define svex-assigns-compose ((x svex-alist-p)
                              &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (xx svex-alist-p)
  (b* ((xvals (svex-alist-vals x))
       (- (cw "Initial count: ~x0~%" (svexlist-opcount xvals)))
       ;;; Rewriting here at first presumably won't disrupt decompositions
       ;;; because the expressions should be relatively small and independent,
       ;;; to first approximation.
       ;; (- (sneaky-save 'orig-assigns x))
       (xvals (if rewrite (cwtime (svexlist-rewrite-top xvals :verbosep t) :mintime 0) xvals))
       (x (pairlis$ (svex-alist-keys x) xvals))
       (- (cw "Count after initial rewrite: ~x0~%" (svexlist-opcount xvals)))
       (updates (cwtime (svex-compose-assigns x) :mintime 1))
       (updates-vals (svex-alist-vals updates))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount updates-vals)))
       (updates-vals
        ;; (if rewrite (cwtime (svexlist-rewrite-top updates-vals :verbosep t) :mintime 0) updates-vals)
        ;; Note: it seems quite important to rewrite here or else
        ;; svexlist-compose-to-fix-rec2 takes a very long time.
        (cwtime (svexlist-rewrite-top updates-vals :verbosep t) :mintime 0))
       (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       (masks (svexlist-mask-alist updates-vals))
       ;; (updates-vals (cwtime (svexlist-rewrite updates-vals masks) :mintime 1))
       ;; (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       ;; (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (vars (svexlist-collect-vars updates-vals))
       (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (upd-subset (with-fast-alist updates (svex-alist-reduce vars updates)))
       ;; (- (acl2::sneaky-save 'simple-updates updates))
       (- (cw "Looping subset count: ~x0~%" (cwtime (svexlist-opcount (svex-alist-vals upd-subset)))))
       (- (cw "Mask bits count (starting): ~x0~%" (svexlist-masks-measure vars masks)))
       ((acl2::with-fast updates))
       ((mv final-masks rest)
        (cwtime (svexlist-compose-to-fix-rec2 masks upd-subset nil) :mintime 1))
       ;; (- (sneaky-save 'assigns x)
       ;;    (sneaky-save 'updates updates)
       ;;    (sneaky-save 'final-masks final-masks)
       ;;    (sneaky-save 'loop-vars vars))
       (final-masks (make-fast-alist final-masks))
       ;; (- (with-fast-alist x
       ;;      (svex-masks-summarize-loops vars final-masks x)))
       (loop-var-alist (fast-alist-clean (svex-compose-extract-loop-var-alist-from-final-masks final-masks)))
       (next-updates (with-fast-alist rest
                       (svex-alist-compose* updates rest)))

       
       ;; (- (acl2::sneaky-save 'next-updates next-updates))

       (- (cw "~x0 loop vars~%" (len loop-var-alist))
          ;; (cw "rest: ~x0~%keys: ~x1~%"
          ;;     (len rest) (alist-keys (take (min 20 (len rest)) rest)))
          )
       ((mv err looped-updates)
        (with-fast-alist loop-var-alist
          (with-fast-alist next-updates
            (cwtime
             (svex-mask-alist-compose-bit-sccs
              final-masks 0 nil nil nil
              (make-svex-scc-consts :final-masks final-masks
                                    :updates next-updates
                                    :loop-vars loop-var-alist))))))
       ;; (- (acl2::sneaky-save 'looped-updates looped-updates))
       (- (fast-alist-free loop-var-alist))
       (- (fast-alist-free final-masks))
       (- (and err
               (raise "Error while composing bit-level loops: ~@0" err)))

       (res-updates1 (with-fast-alist looped-updates
                       (svex-alist-compose* next-updates looped-updates)))
       ;; (- (acl2::sneaky-save 'res-updates1 res-updates1))

       ;; (res1-updates (svex-compose-keep-nonzero-mask-updates res1 final-masks))
       ;; This attempts to resolve apparent combinational loops by adding
       ;; another iteration for variables that are still used in the masks.
       ;; This isn't necessarily sufficient but it might be for simple cases.
       (res-updates2 (b* ((vars (svex-alist-keys updates))
                          (xes-alist (pairlis$ vars (make-list (len vars) :initial-element (svex-x)))))
                       (with-fast-alist xes-alist (svex-alist-compose* res-updates1 xes-alist))))
       ;; (res2 (with-fast-alist res1-updates2 (svex-alist-compose* res1 res1-updates2)))
       )
    (clear-memoize-table 'svex-compose*)
    (clear-memoize-table 'svex-compose)
    res-updates2)
  ///
  (deffixequiv svex-assigns-compose))

(define svex-assigns-compose-keys ((keys svarlist-p)
                                   (x svex-alist-p)
                                   &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (xx svex-alist-p)
  (b* ((xvals (svex-alist-vals x))
       (- (cw "Initial count: ~x0~%" (svexlist-opcount xvals)))
       ;;; Rewriting here at first presumably won't disrupt decompositions
       ;;; because the expressions should be relatively small and independent,
       ;;; to first approximation.
       ;; (- (sneaky-save 'orig-assigns x))
       (xvals (if rewrite (cwtime (svexlist-rewrite-top xvals :verbosep t) :mintime 0) xvals))
       (x (pairlis$ (svex-alist-keys x) xvals))
       (- (cw "Count after initial rewrite: ~x0~%" (svexlist-opcount xvals)))
       ((mv updates memo) (cwtime (svex-compose-assigns-keys keys x nil nil) :mintime 1))
       (- (fast-alist-free memo))
       (updates-vals (svex-alist-vals updates))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount updates-vals)))
       (updates-vals
        (if rewrite (cwtime (svexlist-rewrite-top updates-vals :verbosep t) :mintime 0) updates-vals))
       (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       (masks (svexlist-mask-alist updates-vals))
       ;; (updates-vals (cwtime (svexlist-rewrite updates-vals masks) :mintime 1))
       ;; (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       ;; (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (vars (svexlist-collect-vars updates-vals))
       (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (upd-subset (with-fast-alist updates (svex-alist-reduce vars updates)))
       ;; (- (acl2::sneaky-save 'simple-updates updates))
       (- (cw "Looping subset count: ~x0~%" (cwtime (svexlist-opcount (svex-alist-vals upd-subset)))))
       (- (cw "Mask bits count (starting): ~x0~%" (svexlist-masks-measure vars masks)))
       ((acl2::with-fast updates))
       ((mv final-masks rest)
        (cwtime (svexlist-compose-to-fix-rec2 masks upd-subset nil) :mintime 1))
       ;; (- (sneaky-save 'assigns x)
       ;;    (sneaky-save 'updates updates)
       ;;    (sneaky-save 'final-masks final-masks)
       ;;    (sneaky-save 'loop-vars vars))
       (final-masks (make-fast-alist final-masks))
       ;; (- (with-fast-alist x
       ;;      (svex-masks-summarize-loops vars final-masks x)))
       (loop-var-alist (fast-alist-clean (svex-compose-extract-loop-var-alist-from-final-masks final-masks)))
       (next-updates (with-fast-alist rest
                       (svex-alist-compose* updates rest)))

       
       ;; (- (acl2::sneaky-save 'next-updates next-updates))

       (- (cw "~x0 loop vars~%" (len loop-var-alist))
          ;; (cw "rest: ~x0~%keys: ~x1~%"
          ;;     (len rest) (alist-keys (take (min 20 (len rest)) rest)))
          )
       ((mv err looped-updates)
        (with-fast-alist loop-var-alist
          (with-fast-alist next-updates
            (cwtime
             (svex-mask-alist-compose-bit-sccs
              final-masks 0 nil nil nil
              (make-svex-scc-consts :final-masks final-masks
                                    :updates next-updates
                                    :loop-vars loop-var-alist))))))
       ;; (- (acl2::sneaky-save 'looped-updates looped-updates))
       (- (fast-alist-free loop-var-alist))
       (- (fast-alist-free final-masks))
       (- (and err
               (raise "Error while composing bit-level loops: ~@0" err)))

       (res-updates1 (with-fast-alist looped-updates
                       (svex-alist-compose* next-updates looped-updates)))
       ;; (- (acl2::sneaky-save 'res-updates1 res-updates1))

       ;; (res1-updates (svex-compose-keep-nonzero-mask-updates res1 final-masks))
       ;; This attempts to resolve apparent combinational loops by adding
       ;; another iteration for variables that are still used in the masks.
       ;; This isn't necessarily sufficient but it might be for simple cases.
       (res-updates2 (b* ((vars (svex-alist-keys updates))
                          (xes-alist (pairlis$ vars (make-list (len vars) :initial-element (svex-x)))))
                       (with-fast-alist xes-alist (svex-alist-compose* res-updates1 xes-alist))))
       ;; (res2 (with-fast-alist res1-updates2 (svex-alist-compose* res1 res1-updates2)))
       )
    (clear-memoize-table 'svex-compose*)
    (clear-memoize-table 'svex-compose)
    res-updates2)
  ///
  (deffixequiv svex-assigns-compose))

(define svex-assigns-compose-with-split-phase1 ((x svex-alist-p)
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
       (updates (cwtime (svex-alist-rewrite-top updates :verbosep t) :mintime 0))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount (svex-alist-vals updates)))))
    updates))

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
       ((when (eql mask 0))
        (svex-compose-splittab (cdr x) masks))
       ((mv split count1) (svar-mask-to-split var 0 mask (sparseint-length mask)))
       ((mv rest count2) (svex-compose-splittab (cdr x) masks)))
    (mv (cons (cons var split)
              rest)
        (+ count1 count2))))


       
(local
 (defthm svarlist-p-alist-keys-when-svar-splittab-p
   (implies (svar-splittab-p x)
            (svarlist-p (alist-keys x)))
   :hints(("Goal" :in-theory (enable svar-splittab-p alist-keys)))))

(define svex-assigns-compose-with-split-phase2 ((x svex-alist-p))
  :returns (mv err (new-x svex-alist-p) (splittab svar-splittab-p))
  (b* ((x-vals (svex-alist-vals x))
       (masks (svexlist-mask-alist x-vals))
       (vars (svexlist-collect-vars x-vals))
       ((mv splittab bitcount) (cwtime (svex-compose-splittab x masks) :mintime 0))
       (- (cw "Care bits remaining: ~x0~%" bitcount))
       (splittab-vars (svar-splittab-vars splittab))
       (- (cw "Total split variables: ~x0~%" (len splittab-vars)))
       (bad-vars (acl2::hons-intersection vars splittab-vars))
       ((when bad-vars)
        (mv (msg "Splittab had variables that already existed: ~x0~%" bad-vars) nil splittab))
       (dupsp (hons-dups-p bad-vars))
       ((when dupsp)
        (mv (msg "Splittab had duplicate variables such as ~x0~%" (car dupsp)) nil splittab))
       (x-split-part (svex-alist-reduce (alist-keys splittab) x))
       (split-updates1 (with-fast-alist x (cwtime (svex-alist-to-split x-split-part splittab) :mintime 0)))
       (split-updates (cwtime (svex-alist-rewrite-top split-updates1 :verbosep t) :mintime 0))
       (compose-vars (acl2::hons-intersection (svexlist-collect-vars (svex-alist-vals split-updates))
                                              (svex-alist-keys split-updates)))
       (- (cw "Split update variables: ~x0~%" (len compose-vars)))
       (new-updates (cwtime (svex-compose-assigns split-updates) :mintime 0)))
    (mv nil new-updates splittab)))

(define svex-assigns-compose-with-split-phase3 ((x svex-alist-p))
  :returns (mv err (new-x svex-alist-p))
  (b* ((final-masks (svexlist-mask-alist (svex-alist-vals x)))
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
    (mv err (with-fast-alist looped-updates (svex-alist-compose* x looped-updates)))))

(define svex-assigns-compose-with-split-phase4 ((unsplit svex-alist-p)
                                                (split svex-alist-p)
                                                (splittab svar-splittab-p))
  :returns (new-x svex-alist-p)
  (b* ((re-unsplit (svex-alist-from-split split splittab)))
    (with-fast-alist re-unsplit
      (svex-alist-compose* unsplit re-unsplit))))


(define svex-assigns-compose-with-split ((x svex-alist-p)
                              &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (mv err (xx svex-alist-p))
  (b* ((phase1 (svex-assigns-compose-with-split-phase1 x :rewrite rewrite))
       ((mv err phase2 splittab) (svex-assigns-compose-with-split-phase2 phase1))
       ((when err) (mv err nil))
       ((mv err phase3) (svex-assigns-compose-with-split-phase3 phase2))
       ((when err) (mv err nil)))
    (mv nil (svex-assigns-compose-with-split-phase4 phase1 phase3 splittab))))

(define svex-assigns-compose-split ((x svex-alist-p)
                              &key (rewrite 't))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (xx svex-alist-p)
  (b* (((mv err ans) (svex-assigns-compose-with-split x :rewrite rewrite))
       (- (and err (raise "~@0" err))))
    ans))



#||

(defconsts (*assigns* *updates* *final-masks* *loop-vars* state)
  #!sv
  (b* (((mv assigns state) (sneaky-load 'assigns state))
       ((mv updates state) (sneaky-load 'updates state))
       ((mv final-masks state) (sneaky-load 'final-masks state))
       ((mv loop-vars state) (sneaky-load 'loop-vars state)))
    (mv assigns updates final-masks loop-vars state)))


||#



#||

(defconst *assigns*
  (make-fast-alist
   '((a . (bitor b (lsh 1 (zerox 5 a))))
     (d . (+ a c))
     (b . (res (concat 5 e 0) (lsh 5 (rsh 5 (zerox 10 f))))))))

(time$ (svex-assigns-compose *assigns*))

(len (svex-collect-subexprs
      (svex-lookup 'd (svex-assigns-compose *assigns*))
      nil))

(len (svexlist-collect-subexprs (svex-alist-vals *assigns*) nil))



||#



#||

(defconst *assigns*
  (make-fast-alist
   '((a . (bitor b (lsh 1 (zerox 5 a))))
     (d . (+ a c))
     (b . (res (concat 5 e 0) (lsh 5 (rsh 5 (zerox 10 f))))))))

(defconst *updates*
  (svex-compose-assigns
   *assigns*))

(include-book
 "svex-rewrite")

(defconst *updates-rw*
  (pairlis$ (svex-alist-keys *updates*)
            (svexlist-rewrite-top (svex-alist-vals *updates*))))

(defconst *masks*
  (b* ((upd-svex (svex-alist-vals *updates*))
       ((mv toposort al) (svexlist-toposort upd-svex nil nil))
       (- (fast-alist-free al)))
    (svexlist-compute-masks toposort (svexlist-mask-acons upd-svex :all nil))))


(defconst *updates2* (make-fast-alist
                      (svex-alist-compose *updates* *updates*)))

(defconst *updates2-rw*
  (pairlis$ (svex-alist-keys *updates2*)
            (svexlist-rewrite-top (svex-alist-vals *updates2*))))

(defconst *masks2*
  (b* ((upd-svex (svex-alist-vals *updates2*))
       ((mv toposort al) (svexlist-toposort upd-svex nil nil))
       (- (fast-alist-free al)))
    (svexlist-compute-masks toposort (svexlist-mask-acons upd-svex :all nil))))


(defconst *updates3* (make-fast-alist (svex-alist-compose *updates2* *updates*)))

(defconst *masks3*
  (b* ((upd-svex (svex-alist-vals *updates3*))
       ((mv toposort al) (svexlist-toposort upd-svex nil nil))
       (- (fast-alist-free al)))
    (svexlist-compute-masks toposort (svexlist-mask-acons upd-svex :all nil))))

(defconst *updates4* (make-fast-alist (svex-alist-compose *updates3* *updates*)))

(defconst *updates5* (make-fast-alist (svex-alist-compose *updates4* *updates*)))

(defconst *updates6* (make-fast-alist (svex-alist-compose *updates5* *updates*)))

(defconst *masks6*
  (b* ((upd-svex (svex-alist-vals *updates6*))
       ((mv toposort al) (svexlist-toposort upd-svex nil nil))
       (- (fast-alist-free al)))
    (svexlist-compute-masks toposort (svexlist-mask-acons upd-svex :all nil))))

(defconst *updates6-rw*
  (pairlis$ (svex-alist-keys *updates6*)
            (svexlist-rewrite-top (svex-alist-vals *updates6*))))


||#
