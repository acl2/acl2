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
(include-book "argmasks")
(include-book "rewrite")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "misc/hons-help" :dir :system)
(include-book "centaur/misc/fast-alist-pop" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "tools/symlet" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "compose-theory-base")
(local (include-book "centaur/misc/dfs-measure" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (in-theory (disable tau-system)))
(local (std::add-default-post-define-hook :fix))








;; We are going to do a version of Tarjan's
;; strongly-connected components algorithm on the graph formed of the
;; individual bits of the remaining looping variables.  Since Tarjan's
;; algorithm produces the SCCs in reverse topological order, at each SCC
;; computed we finalize that SCC's variables' update functions by:
;; - self-composing the SCC's update functions |SCC| times
;; - composing that result with the previously computed SCCs' update functions.

;; This would be somewhat conservative since a variable can have bits in
;; different SCCs.  However, we now split variables before we do this so that
;; any looping bits have their own variable.

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
              :hints ('(:expand ((svex-vars x)
                                 <call>))))
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

;; (define svex-alist-extract-bound-keys ((vars svarlist-p)
;;                             (x svex-alist-p))
;;   :returns (new-x svex-alist-p)
;;   (if (atom vars)
;;       nil
;;     (b* ((look (svex-fastlookup (car vars) x)))
;;       (if look
;;           (cons (cons (svar-fix (car vars)) look) (svex-alist-extract-bound-keys (cdr vars) x))
;;         (svex-alist-extract-bound-keys (cdr vars) x)))))

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
  (verify-guards svex-alist-selfcompose-n-times)

  (defret netcomp-p-of-<fn>
    (netcomp-p new-x x))

  (defret netcomp-p-of-<fn>-trans
    (implies (netcomp-p x y)
             (netcomp-p new-x y))))
       

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
       (var-updates (svex-alist-reduce vars params.updates))
       ((unless (eql (len var-updates) (len vars)))
        (mv "Programming error -- SCC contained variables without updates" nil))
       (selfcomposed (svex-alist-selfcompose-n-times (1- (len vars)) var-updates))
       (final (acl2::with-fast-alist finalized-updates
                (svex-alist-compose selfcomposed finalized-updates)))
       ;; (xes (pairlis$ vars (repeat (len vars) (svex-x))))
       ;; (final (acl2::with-fast-alist xes (sv::svex-alist-compose pre-final xes)))
       )
    (mv nil (append-without-guard final (svex-alist-fix finalized-updates))))
  ///
  (defret netcomp-p-of-<fn>
    (b* ((updates (svex-scc-consts->updates params)))
      (implies (netcomp-p finalized-updates updates)
               (netcomp-p new-finalized-updates updates)))))

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

  ;; (local (defthmd svex-mask-lookup-when-not-member-alist-keys
  ;;          (implies (not (member-equal (svex-fix key) (alist-keys (svex-mask-alist-fix x))))
  ;;                   (equal (svex-mask-lookup key x) 0))
  ;;          :hints(("Goal" :in-theory (enable svex-mask-lookup-alt-def
  ;;                                            svex-mask-alist-fix
  ;;                                            alist-keys)))))

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
                                    SVEX/INDEX-P-WHEN-MEMBER-EQUAL-OF-SVEX/INDEXLIST-P
                                    member-svex-mask-alist-keys
                                    member-equal
                                    set::empty-set-unique
                                    svexlist-filter-of-svexlist) 
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
                      ((unless (eql 1 (sparseint-bit x.idx mask-look)))
                       ;; This bit isn't set in the masks so this isn't one of the looping bits.
                       !return)
                      (update (svex-fastlookup x.expr.name params.updates))

                      ((unless update)
                       ;; Combinational input... should we warn?
                       !return)
                      ((when (sparseint-< mask-look 0))
                       (b* ((err (msg "Encountered a variable ~x0 that had ~
                                       negative final-masks.  Debugging info ~
                                       saved in ~x1."
                                      x.expr.name :svex-scc-debug-info))
                            (- (sneaky-save :svex-scc-debug-info
                                            (list x . !args))))
                         !return))
                      
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

      


      (std::defret-mutual netcomp-p-of-svex-compose-bit-sccs
        (defret netcomp-p-of-<fn>
          (b* ((updates (svex-scc-consts->updates params)))
            (implies (netcomp-p finalized-updates updates)
                     (netcomp-p new-finalized-updates updates)))
          :hints ('(:expand (<call>)))
          :fn svex-compose-bit-sccs)
        (defret netcomp-p-of-<fn>
          (b* ((updates (svex-scc-consts->updates params)))
            (implies (netcomp-p finalized-updates updates)
                     (netcomp-p new-finalized-updates updates)))
          :hints ('(:expand (<call>)))
          :fn svex-args-compose-bit-sccs)
        (defret netcomp-p-of-<fn>
          (b* ((updates (svex-scc-consts->updates params)))
            (implies (netcomp-p finalized-updates updates)
                     (netcomp-p new-finalized-updates updates)))
          :hints ('(:expand (<call>)))
          :fn svex-mask-compose-bit-sccs))

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
    (svex-mask-alist-compose-bit-sccs (cdr x) trav-index stack trav-indices finalized-updates params))
  ///
  (defret netcomp-p-of-<fn>
    (b* ((updates (svex-scc-consts->updates params)))
      (implies (netcomp-p finalized-updates updates)
               (netcomp-p new-finalized-updates updates))))

  (defret netcomp-p-of-<fn>-trans
    (b* ((updates (svex-scc-consts->updates params)))
      (implies (and (netcomp-p finalized-updates updates)
                    (netcomp-p updates y))
               (netcomp-p new-finalized-updates y)))
    :hints(("Goal" :in-theory (e/d (netcomp-p-transitive2)
                                   (<fn>))))))



