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
                  ((mv composed-assign updates memo)
                   (svex-compose-dfs assign assigns updates memo stack))
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
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (defthmd logcount-lemma
                      (equal (logcount (loghead n (lognot x)))
                             (- (nfix n) (logcount (loghead n x))))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))
             (local (defthm natp-of-expt-2-30
                      (natp (expt 2 30))
                      :rule-classes :type-prescription))
             (local (defthm loghead-by-integer-length-or-greater
                      (implies (and (< (integer-length x) (nfix n))
                                    (<= 0 (ifix x)))
                               (equal (loghead n x) (ifix x)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))
             (local (defthm integer-length-of-lognot
                      (equal (integer-length (lognot x))
                             (integer-length x))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                                         bitops::ihsext-inductions)))))
             (local (include-book "arithmetic/top-with-meta" :dir :system))
             (local (in-theory (disable (expt) (loghead)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:use ((:instance logcount-lemma (n (expt 2 30)))))))
  (b* ((x (mbe :logic (4vmask-fix x) :exec x)))
    (mbe :logic (non-exec (logcount (loghead (4vmask-bits-maxcount) x)))
         :exec (let ((nbits (min (4vmask-bits-maxcount) (+ 1 (integer-length x)))))
                 (if (<= 0 x)
                     (logcount (loghead nbits x))
                   (- (4vmask-bits-maxcount)
                      (logcount (loghead nbits (lognot x))))))))
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

(defthm alist-keys-of-svex-mask-alist-fix
  (equal (alist-keys (svex-mask-alist-fix x))
         (svexlist-fix (alist-keys x)))
  :hints(("Goal" :in-theory (enable svex-mask-alist-fix
                                    svexlist-fix
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

(define svars-extract-updates ((vars svarlist-p)
                               (updates svex-alist-p))
  :returns (upds svex-alist-p)
  :guard-hints (("goal" :in-theory (enable svarlist-p)))
  (b* (((when (atom vars)) nil)
       (upd (svex-fastlookup (car vars) updates))
       ((unless upd) (svars-extract-updates (cdr vars) updates)))
    (cons (cons (svar-fix (car vars)) upd)
          (svars-extract-updates (cdr vars) updates)))
  ///
  (deffixequiv svars-extract-updates
    :hints(("Goal" :in-theory (enable svarlist-fix)))))


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
       ((when (< mask2 0))
        (cw "Warning: Infinite mask on variable ~x0~%" svar1)
        (svex-vars-detect-loops (cdr vars) masks1 masks2))
       ((when (eql mask2 0))
        ;; Mask is now empty; drop this variable
        (svex-vars-detect-loops (cdr vars) masks1 masks2))
       ((when (or (< mask1 0)
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
       ((when (< mask2 0))
        (svex-compose-extract-nonstable-vars (cdr loop-updates) curr-masks final-masks))
       ((when (< mask1 0))
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
       ((when (eql 0 mask))
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


(define svex-alist-compose* ((x svex-alist-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (xx svex-alist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (svex-acons (caar x) (svex-compose* (cdar x) a)
                    (svex-alist-compose* (cdr x) a))
      (svex-alist-compose* (cdr x) a)))
  ///
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
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-FIX$INLINE.NEW-X
                    :in-theory (disable RETURN-TYPE-OF-SVEX-FIX$INLINE.NEW-X)))))

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
anything.</p

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






(defines svex-compose-loopdebug
  :parents (sv)
  :short "Look for a combinational loop under the given masks."
  :long "<p>The stack maps each variable we're traversing to the care mask when
we encountered it.  We say we've found a loop when we encounter a variable that
we've seen before with a mask that overlaps with that one.</p>"

  :prepwork ((local (defthm lookup-in-svex-mask-alist
                      (implies (and (svex-mask-alist-p x)
                                    (hons-assoc-equal k x))
                               (and (4vmask-p (cdr (hons-assoc-equal k x)))
                                    (integerp (cdr (hons-assoc-equal k x)))))
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
         ((when (eql mask 0)) (mv nil nil)))
      (svex-case x
        :quote (mv nil nil)
        :call (b* ((argmasks (svex-argmasks mask x.fn x.args)))
                (svexlist-compose-loopdebug x.args argmasks assigns stack depthlimit))
        :var (b* ((stack-look (hons-get x stack))
                  (stack-mask (if stack-look (4vmask-fix (cdr stack-look)) 0))
                  ((when (not (eql 0 (logand mask stack-mask))))
                   (cw "Combinational loop for ~x0: ~x1~%" x.name stack)
                   (mv x.name stack))
                  (assign (svex-fastlookup x.name assigns))
                  ((unless assign) (mv nil nil))
                  ((when (zp depthlimit)) (mv nil nil))
                  (full-mask (logior stack-mask mask))
                  (stack (hons-acons x full-mask stack))
                  ((mv loopvar loopstack)
                   (svex-compose-loopdebug assign full-mask assigns stack (1- depthlimit)))
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
       ((when (eql mask1 0))
        (svex-masks-summarize-loops (cdr loop-vars) final-masks assigns))
       ((mv & &)
        (svex-compose-loopdebug var1 mask1 assigns nil 100)))
    (svex-masks-summarize-loops (cdr loop-vars) final-masks assigns)))







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
        (if rewrite (cwtime (svexlist-rewrite-top updates-vals :verbosep t) :mintime 0) updates-vals))
       (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       (masks (svexlist-mask-alist updates-vals))
       ;; (updates-vals (cwtime (svexlist-rewrite updates-vals masks) :mintime 1))
       ;; (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       ;; (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (vars (svexlist-collect-vars updates-vals))
       (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (upd-subset (with-fast-alist updates (svars-extract-updates vars updates)))
       ;; (- (acl2::sneaky-save 'updates updates))
       (- (cw "Looping subset count: ~x0~%" (cwtime (svexlist-opcount (svex-alist-vals upd-subset)))))
       (- (cw "Mask bits count (starting): ~x0~%" (svexlist-masks-measure vars masks)))
       ((acl2::with-fast updates))
       ((mv final-masks rest)
        (cwtime (svexlist-compose-to-fix-rec2 masks upd-subset nil) :mintime 1))
       ;; (- (sneaky-save 'assigns x)
       ;;    (sneaky-save 'updates updates)
       ;;    (sneaky-save 'final-masks final-masks)
       ;;    (sneaky-save 'loop-vars vars))
       (- (with-fast-alist x
            (with-fast-alist final-masks
              (svex-masks-summarize-loops vars final-masks x))))
       (- (fast-alist-free final-masks))
       (res (with-fast-alist rest
              (svex-alist-compose updates rest))))
    (clear-memoize-table 'svex-compose)
    res)
  ///
  (deffixequiv svex-assigns-compose))







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
