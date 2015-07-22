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
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system) ;; with-fast
(local (include-book "centaur/misc/dfs-measure" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
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


(defalist svex-svex-memo :key-type svex :val-type svex)

(defthm svex-p-of-lookup-in-svex-svex-memo
  (implies (and (svex-svex-memo-p memo)
                (hons-assoc-equal k memo))
           (svex-p (cdr (hons-assoc-equal k memo)))))

;; Note: This isn't memoized to the extent that it might be: it's memoized at
;; the level of named wires, i.e. subexpressions of assignments may be
;; traversed multiple times.  That could be ok, if the assigns it is run on are
;; simply translations of the assignments written in SV sources.  However, if
;; they somehow become large, repetitive structures, we may need to revisit
;; this.

(defines svex-compose-dfs
  :parents (svex-composition)
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
                   (res (svex-call x.fn args))
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
         (and (< 100 res)
              (cw "var ~x0, mask ~s1, count was ~x2~%" (car x) (str::hexify mask) res))
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






(define svexlist-compose-to-fix-rec ((x svexlist-p)      ;; current settings of assigns
                                     (update svex-alist-p) ;; original dfs-composed assignments
                                     (count (or (natp count) (not count)))
                                     (rewritep))
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
  :hints(("Goal" :in-theory (enable o<)))
  :guard-debug t
  :measure (if count
               (+ (* 2 (nfix count)) (if rewritep 0 1))
             (make-ord 1 1 0))
  :returns (xx svexlist-p)
  (b* ((- (cw "Count: ~x0~%" (svexlist-opcount x)))
       (x (cwtime (svexlist-compose x update) :mintime 0))
       (x (if rewritep
              (b* ((x (cwtime (svexlist-rewrite-top x) :mintime 0)))
                (cw "Post-rewrite count: ~x0~%" (svexlist-opcount x))
                x)
            x))
       ;; (vars (cwtime (svexlist-collect-vars x) :mintime 0))
       (key-vars (svex-alist-keys update))
       ((when (atom key-vars))
        (cw "no more internal vars~%")
        (if rewritep
            ;; already rewrote
            x
          (b* ((x (cwtime (svexlist-rewrite-top x) :mintime 0)))
            (cw "Final count: ~x0~%" (svexlist-opcount x))
            x)))
       (- (cw "Apparent combinational loops: ~x0~%" (len key-vars)))
       (masks (cwtime (svexlist-mask-alist x) :mintime 0))
       (new-count (cwtime (svexlist-masks-measure key-vars masks) :mintime 0))
       ((when (eql 0 new-count))
        (cw "mask count reached 0~%")
        (if rewritep
            ;; already rewrote
            x
          (b* ((x (cwtime (svexlist-rewrite-top x) :mintime 0)))
            (cw "Final count: ~x0~%" (svexlist-opcount x))
            x)))
       (- (cw "Vars: ~x0~%" (svarlist-pair-with-masks
                             ; (take (min (len key-vars) 20) key-vars)
                             key-vars
                             masks)))
       (- (cw "mask bits count: ~x0~%" new-count))
       (count-same (and count (eql new-count (lnfix count))))
       ((when (and count (or (> new-count (lnfix count))
                             (and rewritep count-same))))
        (cw "count didn't decrease~%")
        (cw "some remaining vars: ~x0~%"
            (svarlist-pair-with-masks
             (take (min (len key-vars) 100) key-vars)
             masks))
        x))
    (svexlist-compose-to-fix-rec x update new-count count-same))
  ///
  (fty::deffixequiv svexlist-compose-to-fix-rec
    :hints ((and stable-under-simplificationp
                 `(:expand (,(second (car (last clause)))
                            ,(third (car (last clause))))))))

  (defthm len-of-svexlist-compose-to-fix-rec
    (equal (len (svexlist-compose-to-fix-rec x update count rewritep))
           (len x))))


(define svex-assigns-compose-old ((x svex-alist-p))
  :returns (xx svex-alist-p)
  (b* ((xvals (svex-alist-vals x))
       (- (cw "Initial count: ~x0~%" (svexlist-opcount xvals)))
       (xvals (cwtime (svexlist-rewrite-top xvals) :mintime 0))
       (x (pairlis$ (svex-alist-keys x) xvals))
       (- (cw "Count after initial rewrite: ~x0~%" (svexlist-opcount xvals)))
       (updates (cwtime (svex-compose-assigns x) :mintime 1))
       (updates-vals (svex-alist-vals updates))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount updates-vals)))
       (updates-vals (cwtime (svexlist-rewrite-top updates-vals) :mintime 1))
       (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       ;; (- (acl2::sneaky-save 'updates updates))
       ((acl2::with-fast updates))
       (fix-vals (cwtime (svexlist-compose-to-fix-rec updates-vals updates nil nil) :mintime 1)))
    (pairlis$ (svex-alist-keys updates) fix-vals)))


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
       (- (fast-alist-free al))
       ((with-fast x)))
    (cwtime (svexlist-compute-masks toposort x)))
  ///

  (fty::deffixequiv svex-mask-alist-expand)

  (defthm svex-mask-alist-expand-complete
    (svex-mask-alist-complete (svex-mask-alist-expand x)))

  )

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

(define svexlist-compose-to-fix-rec2 ((vars svarlist-p) ;; current mask alist
                                      (masks svex-mask-alist-p)
                                      (update svex-alist-p) ;; original dfs-composed assignments
                                      (count (or (natp count) (not count))))
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
  :hints(("Goal" :in-theory (enable o<)))
  :verify-guards nil
  :measure (if count
               (nfix count)
             (make-ord 1 1 0))
  :returns (xx svex-alist-p)
  (b* ((upd-subset (svars-extract-updates vars update))
       (masks-start (svex-updates-pair-masks upd-subset masks))
       (masks-exp (cwtime (svex-mask-alist-expand masks-start) :mintime 0))
       (upd-list (svex-alist-vals upd-subset))
        ;; (cwtime (svexlist-rewrite (svex-alist-vals upd-subset) masks-exp) :mintime 0))
       (newvars (cwtime (svexlist-collect-vars upd-list) :mintime 0))
       (new-count (cwtime (svexlist-masks-measure
                           (svex-alist-keys upd-subset)
                           masks-exp) :mintime 0))
       (alist (pairlis$ (svex-alist-keys upd-subset) upd-list))
       (- (cw "Vars: ~x0~%" (svarlist-pair-with-masks
                             ; (take (min (len key-vars) 20) key-vars)
                             (svex-alist-keys upd-subset)
                             masks-exp)))
       ((when (eql 0 new-count))
        (cw "mask count reached 0~%")
        alist)
       (- (cw "mask bits count: ~x0~%" new-count))
       ((when (and count (>= new-count (lnfix count))))
        (cw "count didn't decrease~%")
        ;; (cw "some remaining vars: ~x0~%"
        ;;     (svarlist-pair-with-masks
        ;;      (take (min (len newvars) 100) newvars)
        ;;      masks))
        alist)
       (rest (svexlist-compose-to-fix-rec2 newvars masks-exp update new-count))
       (res (with-fast-alist rest
              (svex-alist-compose alist rest))))
    (clear-memoize-table 'svex-compose)
    res)
  ///
  (verify-guards svexlist-compose-to-fix-rec2
    :guard-debug t)
  (fty::deffixequiv svexlist-compose-to-fix-rec2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(second (car (last clause)))
                            ,(third (car (last clause)))))))))


(define svex-assigns-compose ((x svex-alist-p))
  :parents (svex-composition)
  :short "Given an alist mapping variables to assigned expressions, compose them together into full update functions."
  :returns (xx svex-alist-p)
  (b* ((xvals (svex-alist-vals x))
       (- (cw "Initial count: ~x0~%" (svexlist-opcount xvals)))
       ;;; Rewriting here at first presumably won't disrupt decompositions
       ;;; because the expressions should be relatively small and independent,
       ;;; to first approximation.
       ;; (xvals (cwtime (svexlist-rewrite-top xvals) :mintime 0))
       (x (pairlis$ (svex-alist-keys x) xvals))
       (- (cw "Count after initial rewrite: ~x0~%" (svexlist-opcount xvals)))
       (updates (cwtime (svex-compose-assigns x) :mintime 1))
       (updates-vals (svex-alist-vals updates))
       (- (cw "Updates count: ~x0~%" (svexlist-opcount updates-vals)))
       (masks (svexlist-mask-alist updates-vals))
       ;; (updates-vals (cwtime (svexlist-rewrite updates-vals masks) :mintime 1))
       ;; (- (cw "Updates count after rewrite: ~x0~%" (svexlist-opcount updates-vals)))
       ;; (updates (pairlis$ (svex-alist-keys updates) updates-vals))
       (vars (svexlist-collect-vars updates-vals))
       ;; (- (acl2::sneaky-save 'updates updates))
       ((acl2::with-fast updates))
       (rest (cwtime (svexlist-compose-to-fix-rec2 vars masks updates nil) :mintime 1))
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
