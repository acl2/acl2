; AIGNET - And/Inverter Graph Library
; Copyright (C) 2024 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "AIGNET")

(include-book "transform-utils")
(include-book "transform-stub")
(include-book "count")
(include-book "centaur/misc/numlist" :dir :system)
(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
;; need this book mostly for count-branches-to, could separate that out
(include-book "centaur/aig/bddify" :dir :system)

(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))

(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           unsigned-byte-p
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents parametrize))

(defxdoc parametrize
  :parents (aignet-comb-transforms)
  :short "Transform the AIG so that some conditions assumed to be untrue don't
affect the logical equivalence of nodes, using BDDs to compute a
hopefully-efficient parametrization."
  :long "<p>This is intended to have a similar effect as the @(see
observability-fix) transform, but perhaps making fraiging more efficient by
making the substitution applied to the primary inputs more transparent to
random simulation vectors. Currently it only works in the context of
m-assumption, n-output transforms, i.e. it preserves full combinational
equivalence for the first m outputs, then combinational equivalence under the
assumption that the first m outputs are true for the next n outputs.</p>

<h2>Usage</h2>

<p>In the context of a sequence of <see topic='@(url
apply-m-assumption-n-output-transform)'>m-assumption-n-output</see> AIG
transforms, this transform is invoked by including a @(see parametrize-config)
object in the list of transforms.</p>

<h2>Concept</h2>

<p>Like the observability transform, this replaces the PIs involved in the
assumed condition with new expressions.  These expressions equal the PIs
themselves when the condition holds, and they evaluate to some values for which
the condition does hold otherwise.  That is, if the inputs are @('ins[i]') for
@('i=0 to n-1'), the parametrized inputs for a satisfiable condition @('C(ins)') satisfies
@('C(Param(C,ins))') and @('C(ins) => Param(C,ins) = ins').  The
parametrization by @('C') can be thought of as a fixing function: it maps the
set of all input vectors into the subset that satisfy @('C'), keeping those that already
satisfy @('C') fixed.</p>

<p>So far, this holds for both the parametrize and
observability transforms. The difference is in how inputs that do not satisfy
@('C') are mapped to ones that do.</p>

<p>The observability transform maps all inputs that don't satisfy @('C') to a
fixed value that does satisfy it, except that inputs @('C') doesn't depend on
keep their values.  This is simple, but has one big downside: it can make
random simulation nearly useless, because if most input vectors do not satisfy
@('C') and @('C') depends on most input variables, then most randomly-generated
vectors will uselessly map to the same value of those inputs. It also means
that the substituted value for every variable involved in the condition depends
on the whole condition, regardless of what the particular constraints on that
variable are -- this makes strategies for FRAIGing such as level limiting and
dependency limiting much less useful.</p>

<p>The parametrize transform uses a different scheme that can potentially
distribute randomly-generated input vectors much more evenly over the set of
inputs that satisfy @('C'). It works by using BDD parametrization. We fix an
ordering of the input variables (the BDD ordering) and translate the assumption
@('C') into a BDD. Traversing this BDD lets us generate a set of BDDs giving
parametrized values for each of the inputs. The parametrized input vector
resulting from a particular input vector can be found by traversing the input
vector according to the BDD variable order. We maintain a cube of variable
assignments starting with the empty (constant-true) cube, for which @('C &
cube') should always be satisfiable (using the assumption that @('C') is
satisfiable).  For each variable @('k') in the BDD order, let @('v') be the
value of @('k') in the input vector.  We check whether @('C & cube & (k=v)') is
still satisfiable.  If so, then we add @('k=v') to the cube; if not, we add
@('k=~v') to the cube; either way, @('C & cube') remains satisfiable, and we
continue on with the next variable in the order.  Once all variables have had
assignments added to the cube, the cube then gives the parametrized assignment
satisfying @('C'), and if the original input vector satisfied @('C'), then the
resulting one is the same since @('C & cube & (k=v)') was satisfiable
throughout the algorithm.</p>

")


(acl2::def-1d-arr ubdd-arr :slotname ubdd :pred acl2::ubddp :fix acl2::ubdd-fix :default-val nil)

(acl2::defstobj-clone in-ubdds ubdd-arr :prefix "IN-")
(acl2::defstobj-clone reg-ubdds ubdd-arr :prefix "REG-")


(local
 (encapsulate nil
   (defthm natp-of-count-bdd-branches
     (implies (natp n)
              (acl2::maybe-natp (mv-nth 0 (acl2::count-bdd-branches x n acc))))
     :rule-classes :type-prescription)

   (defthm count-bdd-branches-bound
     (implies (and (mv-nth 0 (acl2::count-bdd-branches x n acc))
                   (natp n))
              (<= (mv-nth 0 (acl2::count-bdd-branches x n acc)) n))
     :rule-classes :linear)

   (defthm natp-of-count-branches-to
     (acl2::maybe-natp (acl2::count-branches-to x n))
     :hints(("Goal" :in-theory (enable acl2::count-branches-to)))
     :rule-classes :type-prescription)

   (defthm count-branches-to-bound
     (implies (acl2::count-branches-to x n)
              (<= (acl2::count-branches-to x n) (nfix n)))
     :hints(("Goal" :in-theory (enable acl2::count-branches-to)))
     :rule-classes :linear)

   (fty::deffixequiv acl2::count-branches-to :args ((acl2::n natp))
     :hints(("Goal" :in-theory (enable acl2::count-branches-to))))))


#!acl2
(local
 (defsection ubdd-facts

   (defthm max-depth-of-to-param-space2-bound-by-x
     (<= (max-depth (to-param-space2 p x)) (max-depth x))
     :hints(("Goal" :in-theory (enable max-depth to-param-space2)))
     :rule-classes :linear)

   
  ))

(define lubdd-fix ((x acl2::ubddp))
  :enabled t
  (mbe :logic (acl2::ubdd-fix x)
       :exec x))

(define aignet-count-ubdd-branches ((ubdd acl2::ubddp) (limit natp))
  ;; Returns a count <= the limit.  If less, this is the actual count,
  ;; otherwise it is the limit or greater.
  :returns (count natp :rule-classes :type-prescription)
  (or (acl2::count-branches-to (lubdd-fix ubdd) limit) (lnfix limit))
  ///
  (defthm aignet-count-ubdd-branches-bound
    (<= (aignet-count-ubdd-branches ubdd limit) (nfix limit))
    :rule-classes :linear))

(define ubdd-negate-cond ((neg bitp) (x acl2::ubddp))
  :returns (new-x acl2::ubddp)
  (let ((x (lubdd-fix x)))
    (if (eql neg 1)
      (acl2::q-not x)
      x))
  ///
  (defret eval-of-<fn>
    (equal (acl2::eval-bdd new-x env)
           (bit->bool (b-xor (bool->bit (acl2::eval-bdd x env))
                             neg)))))

(define aignet-node-to-ubdd-short-circuit-cond (ok
                                                xor
                                                (neg bitp)
                                                (ubdd-abs acl2::ubddp))
  (and ok
       (not xor)
       (eq (lubdd-fix ubdd-abs) (bit->bool neg))))

(define aignet-node-to-ubdd-build-cond (ok0 ok1
                                            (f0-size natp)
                                            (f1-size natp)
                                            (limit natp))
  (and ok0 ok1
       ;; Size limiting: in order to build a new BDD,
       ;; either both inputs must be under the limit or
       ;; else one of them must be constant.
       (or (and (< (lnfix f0-size) (lnfix limit))
                (< (lnfix f1-size) (lnfix limit)))
           (zp f0-size)
           (zp f1-size)))
  ///
  (defthm aignet-node-to-build-cond-of-not-ok
    (and (not (aignet-node-to-ubdd-build-cond nil ok1 f0-size f1-size limit))
         (not (aignet-node-to-ubdd-build-cond ok0 nil f0-size f1-size limit))))

  (defthm aignet-node-to-build-cond-implies-ok
    (implies (aignet-node-to-ubdd-build-cond ok0 ok1 f0-size f1-size limit)
             (and ok0 ok1))
    :rule-classes :forward-chaining))

(define ubdd-apply-gate (xor
                         (f0-ubdd acl2::ubddp)
                         (f1-ubdd acl2::ubddp))
  :returns (gate acl2::ubddp)
  (if xor
      (acl2::q-xor (lubdd-fix f0-ubdd) (lubdd-fix f1-ubdd))
    (acl2::q-and (lubdd-fix f0-ubdd) (lubdd-fix f1-ubdd)))
  ///
  (defret eval-of-<fn>
    (equal (acl2::eval-bdd gate env)
           (bit->bool
            (let ((f0 (bool->bit (acl2::eval-bdd f0-ubdd env)))
                  (f1 (bool->bit (acl2::eval-bdd f1-ubdd env))))
              (b-ite (bool->bit xor)
                     (b-xor f0 f1)
                     (b-and f0 f1)))))))

(local (defthm unsigned-byte-p-of-typecode
         (unsigned-byte-p 2 (typecode x))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(define eval-ubddarr ((x ubdd-arr$ap) env)
  :returns (bits bit-listp)
  (if (atom x)
      nil
    (cons (bool->bit (acl2::eval-bdd (car x) env))
          (eval-ubddarr (cdr x) env)))
  ///
  (defret nth-of-<fn>
    (bit-equiv (nth n bits)
               (bool->bit (acl2::eval-bdd (nth n x) env)))
    :hints(("Goal" :in-theory (enable nth)))))


(define aignet-node-to-ubdd ((id natp)
                             (limit natp)
                             (mark) ;; memoization marker
                             (mark2) ;; failure marker
                             (ubdd-arr)
                             (in-ubdds)
                             (reg-ubdds)
                             (u32arr) ;; ubdd sizes
                             (aignet))
  :guard (and (< id (num-fanins aignet))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (bits-length mark2))
              (<= (num-fanins aignet) (ubdds-length ubdd-arr))
              (<= (num-fanins aignet) (u32-length u32arr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (num-regs aignet) (ubdds-length reg-ubdds)))
  :measure (nfix id)
  :returns (mv new-mark new-mark2 new-ubdd-arr new-u32arr)
  :verify-guards nil
  (b* ((id (lnfix id))
       ((when (eql 1 (get-bit id mark)))
        (mv mark mark2 ubdd-arr u32arr))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :const (b* ((mark (set-bit id 1 mark))
                  (ubdd-arr (set-ubdd id nil ubdd-arr))
                  (u32arr (set-u32 id 0 u32arr)))
               (mv mark mark2 ubdd-arr u32arr))
      :in (b* ((slot1 (id->slot id 1 aignet))
               (regp (eql 1 (snode->regp slot1)))
               (ionum (snode->ionum slot1))
               (mark (set-bit id 1 mark))
               (ubdd (if regp
                         (get-ubdd ionum reg-ubdds)
                       (get-ubdd ionum in-ubdds)))
               (ubdd-arr (set-ubdd id ubdd ubdd-arr))
               (u32arr (set-u32 id (aignet-count-ubdd-branches ubdd limit) u32arr)))
            (mv mark mark2 ubdd-arr u32arr))
      :gate (b* ((f0 (snode->fanin slot0))
                 (slot1 (id->slot id 1 aignet))
                 (f1 (snode->fanin slot1))
                 (xor (eql 1 (snode->regp slot1)))
                 ((when (aignet-node-to-ubdd-short-circuit-cond
                         (acl2::and* (eql 1 (get-bit (lit->var f1) mark))
                                     (eql 0 (get-bit (lit->var f1) mark2)))
                         xor (lit-neg f1) (get-ubdd (lit->var f1) ubdd-arr)))
                  ;; Lazy-eval by memoization case: if it's an AND and f1 is
                  ;; already built and equals NIL, then skip f0.
                  (b* ((ubdd-arr (set-ubdd id nil ubdd-arr))
                       (u32arr (set-u32 id 0 u32arr))
                       (mark (set-bit id 1 mark)))
                    (mv mark mark2 ubdd-arr u32arr)))
                  
                 ((mv mark mark2 ubdd-arr u32arr)
                  (aignet-node-to-ubdd (lit->var f0) limit mark mark2 ubdd-arr in-ubdds reg-ubdds u32arr aignet))
                 (ok0 (eql 0 (get-bit (lit->var f0) mark2)))
                 (f0-ubdd-abs (get-ubdd (lit->var f0) ubdd-arr))
                 
                 ((when (aignet-node-to-ubdd-short-circuit-cond ok0 xor (lit->neg f0) f0-ubdd-abs))
                  ;; lazy eval case
                  (b* ((ubdd-arr (set-ubdd id nil ubdd-arr))
                       (u32arr (set-u32 id 0 u32arr))
                       (mark (set-bit id 1 mark)))
                    (mv mark mark2 ubdd-arr u32arr)))
                 ((when (acl2::and* (not ok0) xor))
                  ;; no point in building the other one, even if it's nil we
                  ;; can't determine this node
                  (b* ((mark (set-bit id 1 mark))
                       (mark2 (set-bit id 1 mark2)))
                    (mv mark mark2 ubdd-arr u32arr)))
                 ((mv mark mark2 ubdd-arr u32arr)
                  (aignet-node-to-ubdd (lit->var f1) limit mark mark2 ubdd-arr in-ubdds reg-ubdds u32arr aignet))
                 (ok1 (eql 0 (get-bit (lit->var f1) mark2)))
                 (f1-ubdd-abs (get-ubdd (lit->var f1) ubdd-arr))

                 ((when (aignet-node-to-ubdd-short-circuit-cond ok1 xor (lit->neg f1) f1-ubdd-abs))
                  ;; lazy eval case
                  (b* ((ubdd-arr (set-ubdd id nil ubdd-arr))
                       (u32arr (set-u32 id 0 u32arr))
                       (mark (set-bit id 1 mark)))
                    (mv mark mark2 ubdd-arr u32arr)))

                 (build (aignet-node-to-ubdd-build-cond ok0 ok1
                                                        (get-u32 (lit->var f0) u32arr)
                                                        (get-u32 (lit->var f1) u32arr)
                                                        limit))
                 
                 ((unless build)
                  ;; failed
                  (b* ((mark (set-bit id 1 mark))
                       (mark2 (set-bit id 1 mark2)))
                    (mv mark mark2 ubdd-arr u32arr)))

                 (f0-ubdd (ubdd-negate-cond (lit->neg f0) f0-ubdd-abs))
                 (f1-ubdd (ubdd-negate-cond (lit->neg f1) f1-ubdd-abs))
                 (gate-ubdd (ubdd-apply-gate xor f0-ubdd f1-ubdd))

                 (mark (set-bit id 1 mark))
                 (ubdd-arr (set-ubdd id gate-ubdd ubdd-arr))
                 (u32arr (set-u32 id (aignet-count-ubdd-branches gate-ubdd limit) u32arr)))
              (mv mark mark2 ubdd-arr u32arr))))
  ///
  (local (in-theory (disable (:d aignet-node-to-ubdd))))

  (local (defthm max-when-second
           (implies (<= x y)
                    (equal (max x y) y))))
  (local (defthm max-when-first
           (implies (> x y)
                    (equal (max x y) x))))

  ;; (local (defthm max-when-first-gte
  ;;          (implies (and (>= x y)
  ;;                        (rationalp x) (rationalp y))
  ;;                   (equal (max x y) x))))

  (local (in-theory (disable max not len)))
  
  (defret mark-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark))
                  (< (nfix id) (num-fanins aignet)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark2))
                  (< (nfix id) (num-fanins aignet)))
             (equal (len new-mark2) (len mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret ubdd-arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len ubdd-arr))
                  (< (nfix id) (num-fanins aignet)))
             (equal (len new-ubdd-arr) (len ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret u32arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len u32arr))
                  (< (nfix id) (num-fanins aignet)))
             (equal (len new-u32arr) (len u32arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (verify-guards aignet-node-to-ubdd
    :hints(("Goal" :in-theory (enable aignet-idp))))
  
  (local (in-theory (enable* acl2::arith-equiv-forwarding)))

  (defret mark-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (bit-equiv (nth n new-mark2)
                        (nth n mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-marks-id
    (equal (nth id new-mark) 1)
    :hints (("goal" :expand (<call>))))

  (defret ubdd-arr-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-ubdd-arr)
                    (nth n ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defun-sk aignet-node-to-ubdd-invar (mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
    (forall (n env)
            (implies (and (bit->bool (nth n mark))
                          (not (bit->bool (nth n mark2)))
                          (< (nfix n) (num-fanins aignet)))
                     (equal (bool->bit (acl2::eval-bdd (nth n ubdd-arr) env))
                            (id-eval n
                                     (eval-ubddarr in-ubdds env)
                                     (eval-ubddarr reg-ubdds env)
                                     aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-node-to-ubdd-invar))


  (local
   (defthm aignet-node-to-ubdd-short-circuit-cond-implies-when-invar
     (implies (and (aignet-node-to-ubdd-short-circuit-cond ok
                                                           xor neg
                                                           (acl2::ubdd-fix (nth i ubdd-arr)))
                   (aignet-node-to-ubdd-invar mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
                   (equal 1 (nth i mark))
                   (iff ok (not (equal 1 (nth i mark2))))
                   (< i (num-fanins aignet)))
              (equal (id-eval i
                              (eval-ubddarr in-ubdds env)
                              (eval-ubddarr reg-ubdds env)
                              aignet)
                     (bfix neg)))
     :hints (("goal" :use ((:instance aignet-node-to-ubdd-invar-necc
                            (n i) (env env))
                           (:instance acl2::eval-bdd-ubdd-fix
                            (x (nth i ubdd-arr)) (env env)))
              :in-theory (e/d (aignet-node-to-ubdd-short-circuit-cond)
                              (aignet-node-to-ubdd-invar-necc
                               acl2::eval-bdd-ubdd-fix))))))

  (local (defthm aignet-node-to-ubdd-short-circuit-cond-when-xor
           (not (aignet-node-to-ubdd-short-circuit-cond ok t neg ubdd-abs))
           :hints(("Goal" :in-theory (enable aignet-node-to-ubdd-short-circuit-cond)))))

  (local (defthm aignet-node-to-ubdd-short-circuit-cond-when-not-ok
           (not (aignet-node-to-ubdd-short-circuit-cond nil xor neg ubdd-abs))
           :hints(("Goal" :in-theory (enable aignet-node-to-ubdd-short-circuit-cond)))))
  
  (defret invar-of-<fn>
    (implies (aignet-node-to-ubdd-invar mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
             (aignet-node-to-ubdd-invar
              new-mark new-mark2 new-ubdd-arr in-ubdds reg-ubdds aignet))
    :hints (("goal" :induct <call>
             :do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 `(:expand (<call>
                            (:free (ins regs) (id-eval id ins regs aignet))
                            (:free (lit ins regs) (lit-eval lit ins regs aignet)))
                   :in-theory (enable eval-xor-of-lits
                                      eval-and-of-lits)))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::and*)))
            (and stable-under-simplificationp
                 (b* ((witness-call (acl2::find-call-lst 'aignet-node-to-ubdd-invar-witness clause))
                      (alist `(((mv-nth '0 ,witness-call) . nnn)
                               ((mv-nth '1 ,witness-call) . env))))
                   `(:clause-processor (acl2::generalize-with-alist-cp
                                        clause ',alist))))))

  (defthm invar-of-empty-mark
    (aignet-node-to-ubdd-invar (resize-list nil k 0) mark2 ubdd-arr in-ubdds reg-ubdds aignet)
    :hints(("Goal" :in-theory (enable aignet-node-to-ubdd-invar)))))


(define aignet-output-range-to-ubdds ((start natp)
                                     (count natp)
                                     (limit natp)
                                     (mark) ;; memoization marker
                                     (mark2) ;; failure marker
                                     (ubdd-arr)
                                     (in-ubdds)
                                     (reg-ubdds)
                                     (u32arr) ;; ubdd sizes
                                     (aignet))
  :guard (and (<= (+ start count) (num-outs aignet))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (bits-length mark2))
              (<= (num-fanins aignet) (ubdds-length ubdd-arr))
              (<= (num-fanins aignet) (u32-length u32arr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (num-regs aignet) (ubdds-length reg-ubdds)))
  :returns (mv new-mark new-mark2 new-ubdd-arr new-u32arr)
  (b* (((when (zp count))
        (mv mark mark2 ubdd-arr u32arr))
       ((mv mark mark2 ubdd-arr u32arr)
        (aignet-node-to-ubdd (lit->var
                              (outnum->fanin start aignet))
                             limit mark mark2 ubdd-arr
                             in-ubdds reg-ubdds u32arr aignet)))
    (aignet-output-range-to-ubdds (1+ (lnfix start))
                                 (1- count)
                                 limit mark mark2 ubdd-arr
                                 in-ubdds reg-ubdds u32arr aignet))
  ///
  (local (in-theory (disable (:d aignet-output-range-to-ubdds))))
  (defret mark-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark2))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-mark2) (len mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret ubdd-arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len ubdd-arr))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-ubdd-arr) (len ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret u32arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len u32arr))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-u32arr) (len u32arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (bit-equiv (nth n new-mark2)
                        (nth n mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-marks-output-id
    (implies (and (<= (nfix start) (nfix outnum))
                  (< (nfix outnum) (+ (nfix start) (nfix count))))
             (equal (nth (LIT->VAR (FANIN 0 (LOOKUP-STYPE OUTNUM :PO AIGNET)))
                         new-mark) 1))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret ubdd-arr-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-ubdd-arr)
                    (nth n ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret invar-of-<fn>
    (implies (aignet-node-to-ubdd-invar mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
             (aignet-node-to-ubdd-invar
              new-mark new-mark2 new-ubdd-arr in-ubdds reg-ubdds aignet))
    :hints (("goal" :induct <call> :expand (<call>)
             :do-not-induct t))))


(define aignet-output-range-conjoin-ubdds ((start natp)
                                           (count natp)
                                           (limit natp)
                                           (full-limit natp)
                                           (ubdd-acc acl2::ubddp)
                                           (conjunct-count natp)
                                           (mark) ;; memoization marker
                                           (mark2) ;; failure marker
                                           (ubdd-arr)
                                           (in-ubdds)
                                           (reg-ubdds)
                                           (u32arr) ;; ubdd sizes
                                           (aignet))
  :guard (and (<= (+ start count) (num-outs aignet))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (bits-length mark2))
              (<= (num-fanins aignet) (ubdds-length ubdd-arr))
              (<= (num-fanins aignet) (u32-length u32arr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (num-regs aignet) (ubdds-length reg-ubdds)))
  :returns (mv (conj-ubdd acl2::ubddp)
               (conj-count natp :rule-classes :type-prescription)
               new-mark new-mark2 new-ubdd-arr new-u32arr)
  (b* (((when (zp count))
        (mv (lubdd-fix ubdd-acc)
            (lnfix conjunct-count)
            mark mark2 ubdd-arr u32arr))
       (out-lit  (outnum->fanin start aignet))
       (out-id  (lit->var out-lit))
       ((mv mark mark2 ubdd-arr u32arr)
        (aignet-node-to-ubdd out-id
                             limit mark mark2 ubdd-arr
                             in-ubdds reg-ubdds u32arr aignet))
       ((mv ubdd-acc conjunct-count)
        (b* (((when (or (eql 1 (get-bit out-id mark2))
                        ;; ?? skip if result was too big, or only if it wasn't computed?
                        ;; (eql (lnfix limit) (get-u32 out-id u32arr ))
                        ))
              (mv ubdd-acc conjunct-count))
             (and-ubdd (acl2::q-and (ubdd-negate-cond (lit->neg out-lit)
                                                      (get-ubdd out-id ubdd-arr))
                                    ubdd-acc))
             (size (aignet-count-ubdd-branches and-ubdd full-limit))
             ((when (eql size (lnfix full-limit)))
              ;; conjoining this makes it too big, skip
              (mv ubdd-acc conjunct-count)))
          (mv and-ubdd (1+ (lnfix conjunct-count))))))
    (aignet-output-range-conjoin-ubdds (1+ (lnfix start))
                                       (1- count)
                                       limit full-limit
                                       ubdd-acc conjunct-count
                                       mark mark2 ubdd-arr
                                       in-ubdds reg-ubdds u32arr aignet))
  ///
  (local (in-theory (disable (:d aignet-output-range-conjoin-ubdds))))
  (defret mark-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark2))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-mark2) (len mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret ubdd-arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len ubdd-arr))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-ubdd-arr) (len ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret u32arr-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len u32arr))
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (equal (len new-u32arr) (len u32arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret mark2-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (bit-equiv (nth n new-mark2)
                        (nth n mark2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-marks-output-id
    (implies (and (<= (nfix start) (nfix outnum))
                  (< (nfix outnum) (+ (nfix start) (nfix count))))
             (equal (nth (LIT->VAR (FANIN 0 (LOOKUP-STYPE OUTNUM :PO AIGNET)))
                         new-mark) 1))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret ubdd-arr-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-ubdd-arr)
                    (nth n ubdd-arr)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret invar-of-<fn>
    (implies (aignet-node-to-ubdd-invar mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
             (aignet-node-to-ubdd-invar
              new-mark new-mark2 new-ubdd-arr in-ubdds reg-ubdds aignet))
    :hints (("goal" :induct <call> :expand (<call>)
             :do-not-induct t)))

  (defret eval-conj-ubdd-of-<fn>
    (implies (and (aignet-node-to-ubdd-invar mark mark2 ubdd-arr in-ubdds reg-ubdds aignet)
                  (equal (conjoin-output-range start count
                                               (eval-ubddarr in-ubdds env)
                                               (eval-ubddarr reg-ubdds env)
                                               aignet)
                         1)
                  (acl2::eval-bdd ubdd-acc env))
             (acl2::eval-bdd conj-ubdd env))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (invals regvals)
                       (conjoin-output-range start count invals regvals aignet)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance invar-of-aignet-node-to-ubdd
                          (id (LIT->VAR (FANIN 0 (LOOKUP-STYPE START :PO AIGNET))))))
                   :in-theory (e/d (output-eval lit-eval)
                                   (invar-of-aignet-node-to-ubdd)))))))

(fty::deffixtype acl2::ubddp
  :pred acl2::ubddp
  :fix acl2::ubdd-fix
  :equiv acl2::ubdd-equiv :define t)

(fty::defprod ubdd/level
  ((ubdd acl2::ubddp)
   (level natp))
  :layout :fulltree
  :hons t)

(fty::defmap ubdd-to-aignet-memo :key-type ubdd/level :val-type litp :true-listp t
  ///
  (defthm lit-listp-alist-vals-when-ubdd-to-aignet-memo-p
    (implies (ubdd-to-aignet-memo-p memo)
             (lit-listp (alist-vals memo)))
    :hints(("Goal" :in-theory (enable alist-vals)))))

(local (defthm litarr$ap-is-lit-listp
         (equal (litarr$ap x) (lit-listp x))
         :hints(("Goal" :in-theory (enable litarr$ap lit-listp)))))


(define bits->bools ((x bit-listp))
  :returns (bools boolean-listp)
  (if (atom x)
      nil
    (cons (bit->bool (car X))
          (bits->bools (cdr x)))))

(fty::deffixequiv lit-eval-list :args ((aignet node-list-p)))

(encapsulate nil
  (local (defthm nth-of-atom
           (implies (atom x)
                    (equal (nth n x) nil))
           :hints(("Goal" :in-theory (enable nth)))))
  (local (defthm aignet-copies-in-bounds-of-atom
           (implies (atom copy)
                    (aignet-copies-in-bounds copy aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-in-bounds
                                             nth-lit)))))
  
  (local (defthm aignet-copies-in-bounds-of-cdr
           (implies (aignet-copies-in-bounds copy aignet)
                    (aignet-copies-in-bounds (cdr copy) aignet))
           :hints (("goal" :expand ((aignet-copies-in-bounds (cdr copy) aignet)
                                    (aignet-copies-in-bounds nil aignet)
                                    (:free (n) (nth (+ 1 (nfix n)) copy)))
                    :use ((:instance aignet-copies-in-bounds-necc
                           (n (+ 1 (nfix (aignet-copies-in-bounds-witness (cdr copy) aignet))))))
                    :in-theory (e/d (nth-lit)
                                    (aignet-copies-in-bounds-necc))))))
  (defthmd aignet-copies-in-bounds-iff-aignet-lit-listp
    (iff (aignet-copies-in-bounds copy aignet)
         (aignet-lit-listp copy aignet))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-copies-in-bounds clause)))
                   (if lit
                       `(:expand (,lit
                                  (nth (aignet-copies-in-bounds-witness
                                        copy aignet)
                                       copy))
                         :use ((:instance aignet-copies-in-bounds-necc
                                (copy (cdr copy))
                                (n (+ -1 (nfix (aignet-copies-in-bounds-witness
                                                copy aignet))))))
                         :in-theory (e/d (nth-lit nth)
                                         (aignet-copies-in-bounds-necc)))
                     '(:use ((:instance aignet-copies-in-bounds-necc
                              (n 0)))
                       :in-theory (e/d (nth-lit nth)
                                       (aignet-copies-in-bounds-necc)))))))))

(define ubdd-to-aignet-memo-ok ((memo ubdd-to-aignet-memo-p)
                                litarr
                                aignet
                                invals regvals)
  :returns (ok)
  :verify-guards nil
  (b* (((when (atom memo)) t)
       ((unless (mbt (and (consp (car memo))
                          (ubdd/level-p (caar memo)))))
        (ubdd-to-aignet-memo-ok (cdr memo) litarr aignet invals regvals))
       ((cons (ubdd/level key) lit) (car memo))
       (values (bits->bools (non-exec (lit-eval-list litarr invals regvals aignet)))))
    (and (equal (lit-eval lit invals regvals aignet)
                (bool->bit
                 (acl2::eval-bdd key.ubdd (nthcdr key.level values))))
         (ubdd-to-aignet-memo-ok (cdr memo) litarr aignet invals regvals)))
  ///
  (defretd <fn>-implies-rewrite
    (implies (and ok
                  (ubdd/level-p key)
                  (hons-assoc-equal key memo))
             (equal (lit-eval (cdr (hons-assoc-equal key memo))
                              invals regvals aignet)
                    (B* (((ubdd/level key))
                         (values (bits->bools (lit-eval-list litarr invals regvals aignet))))
                      (bool->bit
                       (acl2::eval-bdd key.ubdd
                                       (nthcdr key.level values)))))))

  (defthm ubdd-to-aignet-memo-ok-of-aignet-extension
    (implies (and (aignet-extension-binding )
                  (aignet-lit-listp
                   (alist-vals (ubdd-to-aignet-memo-fix memo)) orig)
                  (aignet-lit-listp litarr orig))
             (iff (ubdd-to-aignet-memo-ok memo litarr new invals regvals)
                  (ubdd-to-aignet-memo-ok memo litarr orig invals regvals)))
    :hints (("goal" :expand ((:free (aignet)
                              (ubdd-to-aignet-memo-ok memo litarr aignet invals regvals))
                             (ubdd-to-aignet-memo-fix memo))
             :in-theory (enable alist-vals)
             :induct (len memo))))

  (defthm ubdd-to-aignet-memo-ok-of-nil
    (ubdd-to-aignet-memo-ok nil litarr aignet invals regvals))
  
  (local (in-theory (enable ubdd-to-aignet-memo-fix))))


(define ubdd-to-aignet ((x acl2::ubddp)
                        (level natp)
                        (memo ubdd-to-aignet-memo-p)
                        (litarr) ;; maps bdd variable levels to AIG literals
                        (gatesimp gatesimp-p)
                        (strash)
                        (aignet))
  :returns (mv (val litp)
               (new-memo ubdd-to-aignet-memo-p)
               new-strash new-aignet)
  :guard (and (aignet-lit-listp (alist-vals memo) aignet)
              (aignet-copies-in-bounds litarr aignet)
              (<= (+ level (acl2::max-depth x)) (lits-length litarr)))
  :measure (Acl2-count (acl2::ubdd-fix x))
  :prepwork ((local (defthm ubdd-of-car/cdr
                      (implies (acl2::ubddp x)
                               (and (acl2::ubddp (car x))
                                    (Acl2::ubddp (cdr x))))
                      :hints(("Goal" :in-theory (enable acl2::ubddp))))))
  :verify-guards nil
  (b* ((memo (ubdd-to-aignet-memo-fix memo))
       (aignet (mbe :logic (non-exec (node-list-fix aignet))
                    :exec aignet))
       (x (lubdd-fix x))
       ((when (atom x))
        (mv (bool->bit x) memo strash aignet))
       (key (make-ubdd/level :ubdd x :level level))
       (look (hons-get key memo))
       ((when look)
        (mv (cdr look) memo strash aignet))
       ((mv then memo strash aignet)
        (ubdd-to-aignet (car x) (1+ (lnfix level)) memo litarr gatesimp strash aignet))
       ((mv else memo strash aignet)
        (ubdd-to-aignet (cdr x) (1+ (lnfix level)) memo litarr gatesimp strash aignet))
       (test (get-lit level litarr))
       ((mv ite strash aignet) (aignet-hash-mux test then else gatesimp strash aignet))
       (memo (hons-acons key ite memo)))
    (mv ite memo strash aignet))
  ///
  (local (in-theory (disable (:d ubdd-to-aignet))))
  
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet aignet)
    :hints (("Goal" :induct <call>
             :expand (<call>))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet))
    :hints (("Goal" :induct <call>
             :expand (<call>))))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet))
    :hints (("Goal" :induct <call>
             :expand (<call>))))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet))
    :hints (("Goal" :induct <call>
             :expand (<call>))))

  (local (defthm lit->var-of-bool->bit
           (equal (lit->var (bool->bit x)) 0)
           :hints(("Goal" :in-theory (enable bool->bit)))))

  (local (defthm aignet-idp-of-lookup-when-aignet-lit-listp-alist-vals
           (implies (and (aignet-lit-listp (alist-vals (ubdd-to-aignet-memo-fix x))
                                           aignet)
                         (ubdd/level-p k)
                         (hons-assoc-equal k x))
                    (aignet-litp (cdr (hons-assoc-equal k x)) aignet))
           :hints(("Goal" :in-theory (enable ubdd-to-aignet-memo-fix
                                             alist-vals
                                             hons-assoc-equal)
                   :induct (ubdd-to-aignet-memo-fix x)))))
  
  (defret result-lits-of-<fn>
    (implies (and (aignet-lit-listp (alist-vals (ubdd-to-aignet-memo-fix memo))
                                    aignet)
                  (aignet-copies-in-bounds litarr aignet))
             (and (aignet-litp val new-aignet)
                  (aignet-lit-listp (alist-vals new-memo)
                                    new-aignet)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b) (alist-vals (cons a b)))))))

  (local (defthm lit-eval-of-bool->bit
           (equal (lit-eval (bool->bit x) invals regvals aignet)
                  (bool->bit x))
           :hints(("Goal" :in-theory (enable bool->bit)))))

  (local (defthm eval-bdd-when-atom-fix
           (implies (not (consp (acl2::ubdd-fix x)))
                    (equal (acl2::eval-bdd x env)
                           (acl2::ubdd-fix x)))
           :hints(("Goal" :in-theory (enable acl2::ubdd-fix acl2::eval-bdd)))))

  (local (defthm aignet-lit-listp-when-aignet-copies-in-bounds
           (implies (aignet-copies-in-bounds copy aignet)
                    (aignet-lit-listp copy aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-in-bounds-iff-aignet-lit-listp)))))

  (local (defthm ubdd-fix-when-not-consp
           (implies (not (consp x))
                    (equal (acl2::ubdd-fix x)
                           (acl2::bool-fix x)))
           :hints(("Goal" :in-theory (enable acl2::ubdd-fix)))))

  (local (defthm eval-bdd-in-terms-of-ubdd-fix
           (equal (acl2::eval-bdd x env)
                  (b* ((x (acl2::ubdd-fix x)))
                    (cond ((atom x) x)
                          ((car env)
                           (acl2::eval-bdd (car x) (cdr env)))
                          (t (acl2::eval-bdd (cdr x) (cdr env))))))
           :hints (("goal" :use ((:instance acl2::eval-bdd-ubdd-fix
                                  (env env)))
                    :in-theory (disable acl2::eval-bdd-ubdd-fix)
                    :expand ((acl2::eval-bdd (acl2::ubdd-fix x) env))))
           :rule-classes ((:definition :controller-alist ((acl2::eval-bdd t nil))))))

  (local (defthm nth-of-lit-eval-list
           (equal (nth level (bits->bools (lit-eval-list x invals regvals aignet)))
                  (bit->bool (lit-eval (nth-lit level x) invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval-list bits->bools nth nth-lit)
                   :induct (nth level x)
                   :expand ((lit-eval nil invals regvals aignet))))))
  
  (defret <fn>-preserves-ubdd-to-aignet-memo-ok
    (b* ((values (bits->bools (lit-eval-list litarr invals regvals aignet))))
      (implies (and (ubdd-to-aignet-memo-ok memo
                                            litarr
                                            aignet invals regvals)
                    (aignet-copies-in-bounds litarr aignet)
                    (aignet-lit-listp
                     (alist-vals (ubdd-to-aignet-memo-fix memo)) aignet))
               (and (ubdd-to-aignet-memo-ok new-memo litarr new-aignet
                                            invals regvals)
                    (equal (lit-eval val invals regvals new-aignet)
                           (bool->bit
                            (acl2::eval-bdd x (nthcdr level values)))))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (enable ubdd-to-aignet-memo-ok-implies-rewrite)
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:expand ((:free (env)
                             (:with eval-bdd-in-terms-of-ubdd-fix
                              (acl2::eval-bdd x env)))
                            (:free (a b aignet)
                             (ubdd-to-aignet-memo-ok
                              (cons a b) litarr
                              aignet invals regvals)))))))

  (verify-guards ubdd-to-aignet
    :hints (("goal" :expand ((acl2::max-depth x))))))


(fty::deftagsum parametrize-output-type
  :parents (parametrize parametrize-config)
  :short "Indicator of how the @(see parametrize) transform should treat a range of outputs"
  :long "<p>The possibilities are:</p>

<ul>
<li>@('(parametrize-output-type-param)'), the default, which
indicates that the output range should be parametrized (except any part of it
in the initial range of assumptions, which cannot be parametrized)</li>

<li>@('(parametrize-output-type-ignore)'), indicating these outputs should be copied as-is without parametrization</li>

<li>@('(parametrize-output-type-bdd-order)'), indicating these outputs should
be used to compute the initial portion of the BDD variable order. This range of
outputs is traversed in order, with any combinational inputs in the fanin cone
of each output added to the BDD order unless it is already present.</li>

</ul>"
  (:param nil) ;; default
  (:ignore nil)
  (:bdd-order nil))

(fty::defalist parametrize-output-type-map :key-type symbolp :val-type parametrize-output-type-p
  :true-listp t)

(fty::defprod parametrize-config
  :parents (parametrize)
  :short "Config object for the @(see parametrize) AIG transform"
  :long "<p>Two of the fields configure BDD size limits. These limits put an
approximate upper bound on the size of BDDs, and are maintained by checking
after each BDD operation to see if the limit is violated. Size limit violations
are dealt with by using an overapproximation of the assumption, which is sound
but may not be useful.</p>"
  ((build-limit natp :rule-classes :type-prescription
                "BDD size limit when recursively building from AIGs.")
   (conjoin-limit natp :rule-classes :type-prescription
                  "Bdd size limit when conjoining hypotheses together. Should
                   be at least as big as build-limit.")
   (output-types parametrize-output-type-map-p
                 "Mapping from output range names (see @(see
aignet-output-ranges)) to @(see parametrize-output-type) objects, indicating
that the outputs are to be treated specially.  The default output type is
@('(parametrize-output-type-param)').))"))
  :tag :parametrize-config)


(define bitarr-range-count ((start natp)
                            (count natp)
                            bitarr)
  :guard (<= (+ start count) (bits-length bitarr))
  :returns (bitcount natp :rule-classes :type-prescription)
  (if (zp count)
      0
    (+ (get-bit start bitarr)
       (bitarr-range-count (1+ (lnfix start)) (1- count) bitarr)))
  ///
  (defthm bitarr-range-count-of-update
    (equal (bitarr-range-count start count (update-nth n b bitarr))
           (+ (bitarr-range-count start count bitarr)
              (cond ((< (nfix n) (nfix start)) 0)
                    ((<= (+ (nfix start) (nfix count)) (nfix n)) 0)
                    (t (- (bfix b) (bfix (nth n bitarr)))))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret bitarr-range-count-upper-bound
    (<= bitcount (nfix count))
    :rule-classes :linear)

  (defret bitarr-range-count-not-equal-when-nonzer
    (implies (and (not (equal 1 (nth n mark)))
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix count))))
             (not (equal count (bitarr-range-count start count mark))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret bitarr-range-count-less-when-nonzer
    (implies (and (not (equal 1 (nth n mark)))
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix count))))
             (< (bitarr-range-count start count mark) (nfix count)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defret bitarr-range-count-of-resize-nil
    (equal (bitarr-range-count start count (resize-list nil k 0)) 0)))


(define bitarr-range-1bit-indices ((start natp)
                                  (count natp)
                                  bitarr)
  :returns (indices nat-listp)
  :guard (<= (+ start count) (bits-length bitarr))
  (if (zp count)
      nil
    (mbe :logic
         (let ((rest (bitarr-range-1bit-indices (1+ (lnfix start))
                                               (1- count) bitarr)))
           (if (eql 1 (get-bit start bitarr))
               (cons (lnfix start) rest)
             rest))
         :exec
         (if (eql 1 (get-bit start bitarr))
             (cons (lnfix start)
                   (bitarr-range-1bit-indices (1+ (lnfix start))
                                                      (1- count) bitarr))
           (bitarr-range-1bit-indices (1+ (lnfix start))
                                     (1- count) bitarr))))
  ///
  (defret member-of-<fn>
    (iff (member n indices)
         (and (natp n)
              (<= (nfix start) (nfix n))
              (< (nfix n) (+ (nfix start) (nfix count)))
              (equal 1 (get-bit n bitarr)))))

  (defret no-duplicatesp-of-<fn>
    (no-duplicatesp-equal indices))
  
  (defret <fn>-of-update-under-set-equiv
    (acl2::set-equiv (bitarr-range-1bit-indices start count (update-nth n b bitarr))
                     (cond ((< (nfix n) (nfix start)) indices)
                           ((<= (+ (nfix start) (nfix count)) (nfix n)) indices)
                           ((eql 1 b) (cons (nfix n) indices))
                           (t (remove (nfix n) indices))))
    :hints (("goal" :in-theory (e/d (acl2::set-unequal-witness-rw)
                                    (<fn>))))))



(define ubdd-arr-max-depth (ubdd-arr)
  :verify-guards nil
  (non-exec
   (if (atom ubdd-arr)
       0
     (max (acl2::max-depth (acl2::ubdd-fix (car ubdd-arr)))
          (ubdd-arr-max-depth (cdr ubdd-arr)))))
  ///
  (defthm max-depth-nth-when-ubdd-arr-max-depth
    (<= (acl2::max-depth (acl2::ubdd-fix (nth n ubdd-arr))) (ubdd-arr-max-depth ubdd-arr))
    :hints(("Goal" :in-theory (enable nth)))
    :rule-classes :linear)

  (defthm ubdd-arr-max-depth-of-update-nth
    (<= (ubdd-arr-max-depth (update-nth n x arr))
        (max (acl2::max-depth (acl2::ubdd-fix x))
             (ubdd-arr-max-depth arr)))
    :hints(("Goal" :in-theory (enable update-nth)))
    :rule-classes
    ((:linear :trigger-terms ((ubdd-arr-max-depth (update-nth n x arr))))))

  (defthm ubdd-arr-max-depth-of-nil
    (equal (ubdd-arr-max-depth nil) 0))
  
  (defthm ubdd-arr-max-depth-of-update-nth-rw
    (implies (and (< (acl2::max-depth (acl2::ubdd-fix x)) d)
                  (< (ubdd-arr-max-depth arr) d))
             (< (ubdd-arr-max-depth (update-nth n x arr)) d))
    :hints(("Goal" :in-theory (enable update-nth))))

  (defthm ubdd-arr-max-depth-of-update-nth-rw2
    (implies (and (<= (acl2::max-depth (acl2::ubdd-fix x)) d)
                  (<= (ubdd-arr-max-depth arr) d))
             (<= (ubdd-arr-max-depth (update-nth n x arr)) d))
    :hints(("Goal" :in-theory (enable update-nth))))

  (defthm ubdd-arr-max-depth-of-resize
    (equal (ubdd-arr-max-depth (resize-list nil n nil))
           0)
    :hints(("Goal" :in-theory (enable resize-list)))))


(define aignet-output-range-collect-in/reg-ubdd-order ((start natp)
                                                  (count natp)
                                                  (index natp) ;; fill pointer in litarr
                                                  aignet
                                                  invals ;; 1 for inputs that are set
                                                  regvals ;; 1 for regs that are set
                                                  litarr  ;; input order
                                                  in-ubdds
                                                  reg-ubdds) ;; inverse
  :returns (mv (new-index natp :rule-classes :type-prescription)
               (new-invals)
               (new-regvals)
               (new-litarr)
               (new-in-ubdds)
               (new-reg-ubdds))
  :guard (and (<= (+ start count) (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (lits-length litarr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (num-regs aignet) (ubdds-length reg-ubdds))
              (eql index
                   (+ (bitarr-range-count 0 (num-ins aignet) invals)
                      (bitarr-range-count 0 (num-regs aignet) regvals))))
  :measure (nfix count)
  :verify-guards nil
  (b* (((when (zp count)) (mv (lnfix index)  invals regvals litarr in-ubdds reg-ubdds))
       (id (lit->var (outnum->fanin start aignet)))
       ((unless (eql (id->type id aignet) (in-type)))
        (aignet-output-range-collect-in/reg-ubdd-order
         (1+ (lnfix start)) (1- count) index aignet invals regvals litarr in-ubdds reg-ubdds))
       (innum (ci-id->ionum id aignet))
       (regp (eql (id->regp id aignet) 1))
       ((unless (eql 0 (if regp
                           (get-bit innum regvals)
                         (get-bit innum invals))))
        (aignet-output-range-collect-in/reg-ubdd-order
         (1+ (lnfix start)) (1- count) index aignet invals regvals litarr in-ubdds reg-ubdds))
       ((mv invals regvals in-ubdds reg-ubdds)
        (if regp
            (b* ((regvals (set-bit innum 1 regvals))
                 (reg-ubdds (set-ubdd innum (acl2::qv (lnfix index)) reg-ubdds)))
              (mv invals regvals in-ubdds reg-ubdds))
          (b* ((invals (set-bit innum 1 invals))
               (in-ubdds (set-ubdd innum (acl2::qv (lnfix index)) in-ubdds)))
            (mv invals regvals in-ubdds reg-ubdds))))
       (litarr (set-lit index (make-lit id 0) litarr)))
    (aignet-output-range-collect-in/reg-ubdd-order
     (1+ (lnfix start)) (1- count)
     (1+ (lnfix index))
     aignet invals regvals litarr in-ubdds reg-ubdds))
  ///
  (local (in-theory (disable (:d aignet-output-range-collect-in/reg-ubdd-order))))

  (defret len-invals-of-<fn>
    (implies (<= (num-ins aignet) (len invals))
             (equal (len new-invals) (len invals)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-regvals-of-<fn>
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len new-regvals) (len regvals)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-litarr-of-<fn>
    (implies (and (<= (+ (num-ins aignet) (num-regs aignet)) (len litarr))
                  (eql index (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                (bitarr-range-count 0 (num-regs aignet) regvals))))
             (equal (len new-litarr) (len litarr)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                '(:use ((:instance bitarr-range-count-not-equal-when-nonzer
                         (mark invals) (start 0) (count (stype-count :pi aignet))
                         (n (STYPE-COUNT
                             :PI
                             (CDR (LOOKUP-ID (LIT->VAR (FANIN 0 (LOOKUP-STYPE START :PO AIGNET)))
                                             AIGNET)))))
                        (:instance bitarr-range-count-not-equal-when-nonzer
                         (mark regvals) (start 0) (count (stype-count :reg aignet))
                         (n (STYPE-COUNT
                             :reg
                             (CDR (LOOKUP-ID (LIT->VAR (FANIN 0 (LOOKUP-STYPE START :PO AIGNET)))
                                             AIGNET))))))
                  :in-theory (disable bitarr-range-count-not-equal-when-nonzer)))))

  (defret len-in-ubdds-of-<fn>
    (implies (<= (num-ins aignet) (len in-ubdds))
             (equal (len new-in-ubdds) (len in-ubdds)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-reg-ubdds-of-<fn>
    (implies (<= (num-regs aignet) (len reg-ubdds))
             (equal (len new-reg-ubdds) (len reg-ubdds)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (verify-guards aignet-output-range-collect-in/reg-ubdd-order
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance bitarr-range-count-not-equal-when-nonzer
                          (mark invals) (start 0) (count (stype-count :pi aignet))
                          (n (STYPE-COUNT
                              :PI
                              (CDR (LOOKUP-ID (LIT->VAR (FANIN 0 (LOOKUP-STYPE START :PO AIGNET)))
                                              AIGNET)))))
                         (:instance bitarr-range-count-not-equal-when-nonzer
                          (mark regvals) (start 0) (count (stype-count :reg aignet))
                          (n (STYPE-COUNT
                              :reg
                              (CDR (LOOKUP-ID (LIT->VAR (FANIN 0 (LOOKUP-STYPE START :PO AIGNET)))
                                              AIGNET))))))
                   :in-theory (disable bitarr-range-count-not-equal-when-nonzer)))))


  (defun-sk aignet-ubdd-input-order-invar (index litarr invals regvals in-ubdds reg-ubdds aignet)
    (forall n
            (implies (< (nfix n) (nfix index))
                     (b* ((lit (nth-lit n litarr))
                          (neg (lit->neg lit))
                          (id (lit->var lit))
                          (tail (lookup-id id aignet))
                          (node (car tail))
                          (innum (stype-count (stype node) (cdr tail))))
                       (and (equal neg 0)
                            (equal (ctype (stype node)) :input)
                            (implies (equal (stype node) :pi)
                                     (and (equal (nth innum invals) 1)
                                          (equal (nth innum in-ubdds)
                                                 (acl2::qv n))))
                            (implies (equal (stype node) :reg)
                                     (and (equal (nth innum regvals) 1)
                                          (equal (nth innum reg-ubdds)
                                                 (acl2::qv n))))))))
    :rewrite :direct)

  (in-theory (disable aignet-ubdd-input-order-invar))

  (defthm aignet-ubdd-input-order-invar-necc-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (< (nfix n) (nfix index)))
             (b* ((lit (nth-lit n litarr))
                  (neg (lit->neg lit))
                  (id (lit->var lit))
                  (tail (lookup-id id aignet))
                  (node (car tail))
                  (innum (stype-count stype (cdr tail))))
               (and (equal neg 0)
                    (equal (ctype (stype node)) :input)
                    (implies (and (equal (stype node) :pi)
                                  (equal stype :pi))
                             (and (equal (nth innum invals) 1)
                                  (equal (nth innum in-ubdds)
                                         (acl2::qv n))))
                    (implies (and (equal (stype node) :reg)
                                  (equal stype :reg))
                             (and (equal (nth innum regvals) 1)
                                  (equal (nth innum reg-ubdds)
                                         (acl2::qv n)))))))
    :hints (("goal" :use aignet-ubdd-input-order-invar-necc
             :in-theory (disable aignet-ubdd-input-order-invar-necc))))
  
  (defret <fn>-input-order-invar-preserved
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (aignet-ubdd-input-order-invar new-index new-litarr new-invals new-regvals new-in-ubdds new-reg-ubdds aignet))
    :hints(("Goal" 
            :induct <call>
            :do-not-induct t
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-input-order-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-input-order-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defthm aignet-ubdd-input-order-invar-when-index-0
    (aignet-ubdd-input-order-invar 0 litarr invals regvals in-ubdds reg-ubdds aignet)
    :hints(("Goal" :in-theory (enable aignet-ubdd-input-order-invar))))

  (defund qv-inverse (x)
    (nfix (- (acl2::max-depth x) 1)))
  
  (local (defthm max-depth-of-qv
           (equal (acl2::max-depth (acl2::qv n))
                  (+ 1 (nfix n)))
           :hints(("Goal" :in-theory (enable acl2::max-depth acl2::qv)))))

  (defthm qv-inverse-of-qv
    (equal (qv-inverse (acl2::qv n))
           (nfix n))
    :hints(("Goal" :in-theory (enable qv-inverse))))

  (defun-sk aignet-ubdd-order-in-marked-invar (index litarr invals in-ubdds aignet)
    (forall n
            (implies (and ;; (<= (nfix n) (nfix bound))
                          (equal 1 (nth n invals)))
                     (let ((var-num (qv-inverse (nth n in-ubdds))))
                       (and (equal (acl2::qv var-num)
                                   (nth n in-ubdds))
                            (< var-num (nfix index))
                            (equal (nth-lit var-num litarr)
                                   (make-lit (innum->id n aignet) 0))))))
    :rewrite :direct)

  (in-theory (disable aignet-ubdd-order-in-marked-invar))
  
  (defthm aignet-ubdd-order-in-marked-invar-implies-linear
    (implies (and (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
                  ;; (<= (nfix n) (nfix bound))
                  (equal 1 (nth n invals)))
             (let ((var-num (qv-inverse (nth n in-ubdds))))
               (< var-num (nfix index))))
    :rule-classes :linear)

  (defret <fn>-order-in-marked-invar-preserved
    (implies (and (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (aignet-ubdd-order-in-marked-invar new-index new-litarr new-invals new-in-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-in-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-in-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-in-marked-invar-of-empty-mark
    (aignet-ubdd-order-in-marked-invar index litarr (resize-list nil k 0) in-ubdds aignet)
    :hints(("Goal" :in-theory (enable aignet-ubdd-order-in-marked-invar))))

  (defun-sk aignet-ubdd-order-reg-marked-invar (index litarr regvals reg-ubdds aignet)
    (forall n
            (implies (and ;; (<= (nfix n) (nfix bound))
                          (equal 1 (nth n regvals)))
                     (let ((var-num (qv-inverse (nth n reg-ubdds))))
                       (and (equal (acl2::qv var-num)
                                   (nth n reg-ubdds))
                            (< var-num (nfix index))
                            (equal (nth-lit var-num litarr)
                                   (make-lit (regnum->id n aignet) 0))))))
    :rewrite :direct)

  (in-theory (disable aignet-ubdd-order-reg-marked-invar))
  
  (defthm aignet-ubdd-order-reg-marked-invar-implies-linear
    (implies (and (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
                  ;; (<= (nfix n) (nfix bound))
                  (equal 1 (nth n regvals)))
             (let ((var-num (qv-inverse (nth n reg-ubdds))))
               (< var-num (nfix index))))
    :rule-classes :linear)

  (defret <fn>-order-reg-marked-invar-preserved
    (implies (and (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
                  (<= (+ (nfix start) (nfix count)) (num-outs aignet)))
             (aignet-ubdd-order-reg-marked-invar new-index new-litarr new-regvals new-reg-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-reg-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-reg-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-reg-marked-invar-of-empty-mark
    (aignet-ubdd-order-reg-marked-invar index litarr (resize-list nil k 0) reg-ubdds aignet)
    :hints(("Goal" :in-theory (enable aignet-ubdd-order-reg-marked-invar))))

  (defretd bitarr-range-count-of-<fn>
    (implies (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                    (bitarr-range-count 0 (num-regs aignet) regvals)))
             (equal new-index (+ (bitarr-range-count 0 (num-ins aignet) new-invals)
                                 (bitarr-range-count 0 (num-regs aignet) new-regvals))))
     :hints(("Goal" 
             :induct <call>
             :expand ((:free (count) <call>)))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet)
             (aignet-copies-in-bounds new-litarr aignet))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>)))))

  

  (defret in-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth in-ubdds)
                      (nfix index))
                  (equal (nfix index)
                         (+ (bitarr-range-count 0 (num-ins aignet) invals)
                            (bitarr-range-count 0 (num-regs aignet) regvals))))
             (<= (ubdd-arr-max-depth new-in-ubdds)
                 new-index))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-in-ubdds)
       new-index))))

  (defret reg-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth reg-ubdds)
                      (nfix index))
                  (equal (nfix index)
                         (+ (bitarr-range-count 0 (num-ins aignet) invals)
                            (bitarr-range-count 0 (num-regs aignet) regvals))))
             (<= (ubdd-arr-max-depth new-reg-ubdds)
                 new-index))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-reg-ubdds)
       new-index)))))

(define bitarr-range-set ((start natp)
                          (count natp)
                          (bitarr))
  :guard (<= (+ start count) (bits-length bitarr))
  :measure (nfix count)
  (if (zp count)
      t
    (and (eql 1 (get-bit start bitarr))
         (bitarr-range-set (1+ (lnfix start)) (1- count) bitarr)))
  ///
  (defthmd bitarr-range-set-implies-nth
    (implies (and (bitarr-range-set start count bitarr)
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix count))))
             (Equal (nth n bitarr) 1))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthmd bitarr-range-set-of-update-lemma
           (implies (and (bitarr-range-set start (1- count) bitarr)
                         (posp count))
                    (bitarr-range-set start count (update-nth (1- (+ (nfix start) count)) 1 bitarr)))
           :hints (("goal" :induct (bitarr-range-set start count bitarr)
                    :expand ((:free (bitarr) (bitarr-range-set start 1 bitarr)))
                    :do-not-induct t))))
  
  (defthm bitarr-range-set-of-update
    (implies (and (equal idx (+ -1 (nfix start) count))
                  (bitarr-range-set start (1- count) bitarr)
                  (posp count))
             (bitarr-range-set start count (update-nth idx 1 bitarr)))
    :hints (("goal" :use bitarr-range-set-of-update-lemma)))

  (defthm bitarr-range-count-when-bitarr-range-set
    (implies (bitarr-range-set start count bitarr)
             (equal (bitarr-range-count start count bitarr)
                    (nfix count)))
    :hints(("Goal" :in-theory (enable bitarr-range-count)))))


(define aignet-finish-in-ubdd-order ((start natp) ;; begin at 0
                                     (index natp) ;; fill pointer in litarr
                                     (invals) ;; inputs already included
                                     (litarr)
                                     (in-ubdds)
                                     aignet)
  :guard (and (<= start (num-ins aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (lits-length litarr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (>= index (bitarr-range-count 0 (num-ins aignet) invals))
              (<= index (+ (bitarr-range-count 0 (num-ins aignet) invals)
                           (num-regs aignet))))
  :returns (mv new-index new-invals new-litarr new-in-ubdds)
  :measure (nfix (- (num-ins aignet) (nfix start)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix start)))
                   :exec (eql start (num-ins aignet))))
        (mv (lnfix index) invals litarr in-ubdds))
       ((when (eql 1 (get-bit start invals)))
        (aignet-finish-in-ubdd-order
         (1+ (lnfix start))
         index invals litarr in-ubdds aignet))
       (invals (set-bit start 1 invals))
       (litarr (set-lit index (make-lit (innum->id start aignet) 0) litarr))
       (in-ubdds (set-ubdd start (acl2::qv (lnfix index)) in-ubdds)))
    (aignet-finish-in-ubdd-order
     (1+ (lnfix start))
     (1+ (lnfix index)) invals litarr in-ubdds aignet))
  ///
  (defret invals-len-of-<fn>
    (implies (<= (num-ins aignet) (len invals))
             (equal (len new-invals) (len invals))))

  (defret litarr-len-of-<fn>
    (implies (and (<= (+ (num-ins aignet) (num-regs aignet)) (len litarr))
                  (<= (nfix index)
                      (+ (bitarr-range-count 0 (num-ins aignet) invals)
                         (num-regs aignet))))
             (equal (len new-litarr) (len litarr)))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:use ((:instance bitarr-range-count-not-equal-when-nonzer
                          (mark invals)
                          (n start)
                          (start 0) (count (stype-count :pi aignet))))
                   :in-theory (disable bitarr-range-count-not-equal-when-nonzer)))))
  
  (defret in-ubdds-len-of-<fn>
    (implies (<= (num-ins aignet) (len in-ubdds))
             (equal (len new-in-ubdds) (len in-ubdds))))

  (verify-guards aignet-finish-in-ubdd-order)

  (defret <fn>-index-increases
    (<= (nfix index) new-index)
    :rule-classes :linear)
  
  (local (defun assoc-first (keys a)
           (if (atom a)
               nil
             (if (member (caar a) keys)
                 (car a)
               (assoc-first keys (cdr a))))))


  ;; (local (defthm ubdd-var-num-facts-when-both-invars
  ;;          (implies (and (aignet-ubdd-input-order-invar index litarr invals in-ubdds)
  ;;                        (aignet-ubdd-in-order-marked-invar index litarr invals in-ubdds)
  ;;                        (< (nfix ubdd-var-num) (nfix index)))
  ;;                   (b* ((innum (nth ubdd-var-num litarr))

  (local (in-theory (disable LOOKUP-STYPE-OF-STYPE-COUNT-MATCH)))

  

  
  (defret <fn>-ubdd-input-order-invar-preserved
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals))))
             (aignet-ubdd-input-order-invar new-index new-litarr new-invals regvals new-in-ubdds reg-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand (<call>
                     (:free (bound) (bitarr-range-count start bound invals)))
            :do-not-induct t)
           (and stable-under-simplificationp
                `(:expand (,(assoc 'aignet-ubdd-input-order-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-input-order-invar-witness clause))
                     (alist `((,witness-call . ubdd-var-num))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-input-order-invar-necc
                              (n (nfix ubdd-var-num))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-input-order-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-ubdd-input-order-invar-preserved-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals)))
                  (equal new-ind new-index))
             (aignet-ubdd-input-order-invar new-ind new-litarr new-invals regvals new-in-ubdds reg-ubdds aignet)))

  (defret <fn>-ubdd-input-order-invar-preserved-implies-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals)))
                  (equal new-ind new-index))
             (b* ((index new-ind)
                  (litarr new-litarr)
                  (invals new-invals)
                  (in-ubdds new-in-ubdds))
               (implies (< (nfix n) (nfix index))
                        (b* ((lit (nth-lit n litarr))
                             (neg (lit->neg lit))
                             (id (lit->var lit))
                             (tail (lookup-id id aignet))
                             (node (car tail))
                             (innum (stype-count stype (cdr tail))))
                          (and (equal neg 0)
                               (equal (ctype (stype node)) :input)
                               (implies (and (equal (stype node) :pi)
                                             (equal stype :pi))
                                        (and (equal (nth innum invals) 1)
                                             (equal (nth innum in-ubdds)
                                                    (acl2::qv n))))
                               (implies (and (equal (stype node) :reg)
                                             (equal stype :reg))
                                        (and (equal (nth innum regvals) 1)
                                             (equal (nth innum reg-ubdds)
                                                    (acl2::qv n)))))))))
    :hints (("goal" :use <fn>-ubdd-input-order-invar-preserved
             :in-theory (disable <fn>-ubdd-input-order-invar-preserved
                                 <fn>-ubdd-input-order-invar-preserved-rw))))

  (defret <fn>-order-reg-marked-invar-preserved
    (implies (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
             (aignet-ubdd-order-reg-marked-invar new-index new-litarr regvals reg-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-reg-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-reg-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-order-reg-marked-invar-necc
                              (n (nfix nnn))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-order-reg-marked-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-reg-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-reg-marked-invar new-ind new-litarr regvals reg-ubdds aignet)))

  (defret <fn>-order-in-marked-invar-preserved
    (implies (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
             (aignet-ubdd-order-in-marked-invar new-index new-litarr new-invals new-in-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-in-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-in-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-order-in-marked-invar-necc
                              (n (nfix nnn))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-order-in-marked-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-in-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-in-marked-invar new-ind new-litarr new-invals new-in-ubdds aignet)))

  (defret <fn>-preserves-invals
    (implies (equal (nth n invals) 1)
             (equal (nth n new-invals) 1))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (local (defretd bitarr-range-set-of-<fn>-lemma
           (bitarr-range-set start (- (num-ins aignet) (nfix start)) new-invals)
           :hints (("goal" :induct <call>
                    :expand (<call>
                             (:free (bound invals) (bitarr-range-set start bound invals)))))))
   
  (defret bitarr-range-set-of-<fn>
    (implies (equal bound (- (num-ins aignet) (nfix start)))
             (bitarr-range-set start bound new-invals))
    :hints (("goal" :use bitarr-range-set-of-<fn>-lemma)))

  (local (defthm equal-nfix-plus-1
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret new-index-of-<fn>
    (equal new-index
           (+ (nfix index)
              (- (nfix (- (num-ins aignet) (nfix start)))
                 (bitarr-range-count start (- (num-ins aignet) (nfix start)) invals))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (bound invals) (bitarr-range-count start bound invals))))
            (and stable-under-simplificationp
                 '(:cases ((<= (nfix start) (num-ins aignet)))))))

  (defret <fn>-ins-marked
    (equal (nth n new-invals)
           (if (and (<= (nfix start) (nfix n))
                    (< (nfix n) (num-ins aignet)))
               1
             (nth n invals)))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet)
             (aignet-copies-in-bounds new-litarr aignet)))

  (defret in-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth in-ubdds)
                      (nfix index))
                  (<= (nfix index)
                      (+ (bitarr-range-count 0 (num-ins aignet) invals)
                         (num-regs aignet))))
             (<= (ubdd-arr-max-depth new-in-ubdds)
                 new-index))
    :hints (("Goal"
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct <call>
             :expand ((:free (count) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((:free (count) (bitarr-range-count start count invals))))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-in-ubdds)
       new-index)))))


(define aignet-finish-reg-ubdd-order ((start natp) ;; begin at 0
                                     (index natp) ;; fill pointer in litarr
                                     (regvals) ;; inputs already included
                                     (litarr)
                                     (reg-ubdds)
                                     aignet)
  :guard (and (<= start (num-regs aignet))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (lits-length litarr))
              (<= (num-regs aignet) (ubdds-length reg-ubdds))
              (>= index (bitarr-range-count 0 (num-regs aignet) regvals))
              (<= index (+ (bitarr-range-count 0 (num-regs aignet) regvals)
                           (num-ins aignet))))
  :returns (mv new-index new-regvals new-litarr new-reg-ubdds)
  :measure (nfix (- (num-regs aignet) (nfix start)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix start)))
                   :exec (eql start (num-regs aignet))))
        (mv (lnfix index) regvals litarr reg-ubdds))
       ((when (eql 1 (get-bit start regvals)))
        (aignet-finish-reg-ubdd-order
         (1+ (lnfix start))
         index regvals litarr reg-ubdds aignet))
       (regvals (set-bit start 1 regvals))
       (litarr (set-lit index (make-lit (regnum->id start aignet) 0) litarr))
       (reg-ubdds (set-ubdd start (acl2::qv (lnfix index)) reg-ubdds)))
    (aignet-finish-reg-ubdd-order
     (1+ (lnfix start))
     (1+ (lnfix index)) regvals litarr reg-ubdds aignet))
  ///
  (defret regvals-len-of-<fn>
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len new-regvals) (len regvals))))

  (defret litarr-len-of-<fn>
    (implies (and (<= (+ (num-ins aignet) (num-regs aignet)) (len litarr))
                  (<= (nfix index)
                      (+ (bitarr-range-count 0 (num-regs aignet) regvals)
                         (num-ins aignet))))
             (equal (len new-litarr) (len litarr)))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:use ((:instance bitarr-range-count-not-equal-when-nonzer
                          (mark regvals)
                          (n start)
                          (start 0) (count (stype-count :reg aignet))))
                   :in-theory (disable bitarr-range-count-not-equal-when-nonzer)))))
  
  (defret reg-ubdds-len-of-<fn>
    (implies (<= (num-regs aignet) (len reg-ubdds))
             (equal (len new-reg-ubdds) (len reg-ubdds))))

  (verify-guards aignet-finish-reg-ubdd-order)

  (defret <fn>-index-increases
    (<= (nfix index) new-index)
    :rule-classes :linear)
  
  (local (defun assoc-first (keys a)
           (if (atom a)
               nil
             (if (member (caar a) keys)
                 (car a)
               (assoc-first keys (cdr a))))))


  ;; (local (defthm ubdd-var-num-facts-when-both-invars
  ;;          (implies (and (aignet-ubdd-input-order-invar index litarr regvals reg-ubdds)
  ;;                        (aignet-ubdd-in-order-marked-invar index litarr regvals reg-ubdds)
  ;;                        (< (nfix ubdd-var-num) (nfix index)))
  ;;                   (b* ((innum (nth ubdd-var-num litarr))

  (local (in-theory (disable LOOKUP-STYPE-OF-STYPE-COUNT-MATCH)))

  

  
  (defret <fn>-ubdd-input-order-invar-preserved
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals))))
             (aignet-ubdd-input-order-invar new-index new-litarr invals new-regvals in-ubdds new-reg-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand (<call>
                     (:free (bound) (bitarr-range-count start bound regvals)))
            :do-not-induct t)
           (and stable-under-simplificationp
                `(:expand (,(assoc 'aignet-ubdd-input-order-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-input-order-invar-witness clause))
                     (alist `((,witness-call . ubdd-var-num))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-input-order-invar-necc
                              (n (nfix ubdd-var-num))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-input-order-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-ubdd-input-order-invar-preserved-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals)))
                  (equal new-ind new-index))
             (aignet-ubdd-input-order-invar new-ind new-litarr invals new-regvals in-ubdds new-reg-ubdds aignet)))

  (defret <fn>-ubdd-input-order-invar-preserved-implies-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                         (bitarr-range-count 0 (num-regs aignet) regvals)))
                  (equal new-ind new-index))
             (b* ((index new-ind)
                  (litarr new-litarr)
                  (regvals new-regvals)
                  (reg-ubdds new-reg-ubdds))
               (implies (< (nfix n) (nfix index))
                        (b* ((lit (nth-lit n litarr))
                             (neg (lit->neg lit))
                             (id (lit->var lit))
                             (tail (lookup-id id aignet))
                             (node (car tail))
                             (innum (stype-count stype (cdr tail))))
                          (and (equal neg 0)
                               (equal (ctype (stype node)) :input)
                               (implies (and (equal (stype node) :pi)
                                             (equal stype :pi))
                                        (and (equal (nth innum invals) 1)
                                             (equal (nth innum in-ubdds)
                                                    (acl2::qv n))))
                               (implies (and (equal (stype node) :reg)
                                             (equal stype :reg))
                                        (and (equal (nth innum regvals) 1)
                                             (equal (nth innum reg-ubdds)
                                                    (acl2::qv n)))))))))
    :hints (("goal" :use <fn>-ubdd-input-order-invar-preserved
             :in-theory (disable <fn>-ubdd-input-order-invar-preserved
                                 <fn>-ubdd-input-order-invar-preserved-rw))))

  (defret <fn>-order-reg-marked-invar-preserved
    (implies (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
             (aignet-ubdd-order-reg-marked-invar new-index new-litarr new-regvals new-reg-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-reg-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-reg-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-order-reg-marked-invar-necc
                              (n (nfix nnn))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-order-reg-marked-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-reg-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-reg-marked-invar new-ind new-litarr new-regvals new-reg-ubdds aignet)))

  (defret <fn>-order-in-marked-invar-preserved
    (implies (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
             (aignet-ubdd-order-in-marked-invar new-index new-litarr invals in-ubdds aignet))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))
           (and stable-under-simplificationp
                `(:expand (,(assoc-eq 'aignet-ubdd-order-in-marked-invar clause))))
           (and stable-under-simplificationp
                (b* ((witness-call (acl2::find-call-lst 'aignet-ubdd-order-in-marked-invar-witness clause))
                     (alist `((,witness-call . nnn))))
                  `(:computed-hint-replacement
                    ('(:use ((:instance aignet-ubdd-order-in-marked-invar-necc
                              (n (nfix nnn))))
                       :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                        (aignet-ubdd-order-in-marked-invar-necc))))
                    :clause-processor (acl2::generalize-with-alist-cp
                                       clause ',alist))))))

  (defret <fn>-order-in-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-in-marked-invar new-ind new-litarr invals in-ubdds aignet)))

  (defret <fn>-preserves-regvals
    (implies (equal (nth n regvals) 1)
             (equal (nth n new-regvals) 1))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (local (defretd bitarr-range-set-of-<fn>-lemma
           (bitarr-range-set start (- (num-regs aignet) (nfix start)) new-regvals)
           :hints (("goal" :induct <call>
                    :expand (<call>
                             (:free (bound regvals) (bitarr-range-set start bound regvals)))))))
   
  (defret bitarr-range-set-of-<fn>
    (implies (equal bound (- (num-regs aignet) (nfix start)))
             (bitarr-range-set start bound new-regvals))
    :hints (("goal" :use bitarr-range-set-of-<fn>-lemma)))

  (local (defthm equal-nfix-plus-1
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret new-index-of-<fn>
    (equal new-index
           (+ (nfix index)
              (- (nfix (- (num-regs aignet) (nfix start)))
                 (bitarr-range-count start (- (num-regs aignet) (nfix start)) regvals))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (bound invals) (bitarr-range-count start bound regvals))))
            (and stable-under-simplificationp
                 '(:cases ((<= (nfix start) (num-regs aignet)))))))

  (defret <fn>-regs-marked
    (equal (nth n new-regvals)
           (if (and (<= (nfix start) (nfix n))
                    (< (nfix n) (num-regs aignet)))
               1
             (nth n regvals)))
    :hints(("Goal"
            :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet)
             (aignet-copies-in-bounds new-litarr aignet)))

  (defret reg-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth reg-ubdds)
                      (nfix index))
                  (<= (nfix index)
                      (+ (bitarr-range-count 0 (num-regs aignet) regvals)
                         (num-ins aignet))))
             (<= (ubdd-arr-max-depth new-reg-ubdds)
                 new-index))
    :hints (("Goal"
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct <call>
             :expand ((:free (count) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((:free (count) (bitarr-range-count start count invals))))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-reg-ubdds)
       new-index)))))




(define aignet-parametrize-collect-bdd-order-aux ((start natp)
                                                  (output-ranges aignet-output-range-map-p)
                                                  (outtypes parametrize-output-type-map-p)
                                                  (index natp)
                                                  invals ;; mark inputs already in the BDD order
                                                  regvals ;; mark regs already in the BDD order
                                                  litarr
                                                  in-ubdds
                                                  reg-ubdds
                                                  aignet)
  :returns (mv (new-index natp :rule-classes :type-prescription)
               (new-invals)
               (new-regvals)
               (new-litarr)
               (new-in-ubdds)
               (new-reg-ubdds))
  :guard (and (<= start (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (lits-length litarr))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (num-regs aignet) (ubdds-length reg-ubdds))
              (eql index
                   (+ (bitarr-range-count 0 (num-ins aignet) invals)
                      (bitarr-range-count 0 (num-regs aignet) regvals))))
  :measure (len output-ranges)
  :verify-guards nil
  (b* (((when (or (atom output-ranges)
                  (<= (num-outs aignet) (lnfix start))))
        (mv (lnfix index) invals regvals litarr in-ubdds reg-ubdds))
       ((unless (mbt (consp (car output-ranges))))
        (aignet-parametrize-collect-bdd-order-aux
         start (cdr output-ranges) outtypes index invals regvals litarr in-ubdds reg-ubdds aignet))
       (name (mbe :logic (acl2::symbol-fix (caar output-ranges))
                  :exec (caar output-ranges)))
       (count 
         (min (lnfix (cdar output-ranges))
              (- (num-outs aignet) (lnfix start))))
       (type (or (cdr (hons-assoc-equal name (parametrize-output-type-map-fix outtypes)))
                 (parametrize-output-type-param)))
       ((unless (parametrize-output-type-case type :bdd-order))
        (aignet-parametrize-collect-bdd-order-aux
         (+ (lnfix start) count)
         (cdr output-ranges)
         outtypes
         index invals regvals litarr in-ubdds reg-ubdds aignet))
       ((mv index invals regvals litarr in-ubdds reg-ubdds)
        (aignet-output-range-collect-in/reg-ubdd-order
         start count
         index aignet invals regvals litarr in-ubdds reg-ubdds)))
    (aignet-parametrize-collect-bdd-order-aux
     (+ (lnfix start) count)
     (cdr output-ranges)
     outtypes index invals regvals litarr in-ubdds reg-ubdds aignet))
  ///
  (local (in-theory (disable (:d aignet-parametrize-collect-bdd-order-aux))))

  (defret len-invals-of-<fn>
    (implies (<= (num-ins aignet) (len invals))
             (equal (len new-invals) (len invals)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-regvals-of-<fn>
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len new-regvals) (len regvals)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-litarr-of-<fn>
    (implies (and (<= (+ (num-ins aignet) (num-regs aignet)) (len litarr))
                  (eql index (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                (bitarr-range-count 0 (num-regs aignet) regvals))))
             (equal (len new-litarr) (len litarr)))
    :hints(("Goal" :in-theory (enable  bitarr-range-count-of-aignet-output-range-collect-in/reg-ubdd-order)
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-in-ubdds-of-<fn>
    (implies (<= (num-ins aignet) (len in-ubdds))
             (equal (len new-in-ubdds) (len in-ubdds)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret len-reg-ubdds-of-<fn>
    (implies (<= (num-regs aignet) (len reg-ubdds))
             (equal (len new-reg-ubdds) (len reg-ubdds)))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (count) <call>)))))

  (verify-guards aignet-parametrize-collect-bdd-order-aux
    :hints(("Goal" :in-theory (enable bitarr-range-count-of-aignet-output-range-collect-in/reg-ubdd-order)
            :do-not-induct t)))

  (fty::deffixcong nat-equiv iff
    (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet) index
    :hints (("goal" :cases ((aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-ubdd-input-order-invar clause)))
                   `(:expand (,lit))))))

  (fty::deffixcong nat-equiv iff
    (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet) index
    :hints (("goal" :cases ((aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-ubdd-order-in-marked-invar clause))
                      (other (if (eq (cadr lit) 'index) '(nfix index) 'index)))
                   `(:expand (,lit)
                     :use ((:instance aignet-ubdd-order-in-marked-invar-necc
                            (n (aignet-ubdd-order-in-marked-invar-witness . ,(cdr lit)))
                            (index ,other)))
                     :in-theory (disable aignet-ubdd-order-in-marked-invar-necc))))))

  (fty::deffixcong nat-equiv iff
    (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet) index
    :hints (("goal" :cases ((aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-ubdd-order-reg-marked-invar clause))
                      (other (if (eq (cadr lit) 'index) '(nfix index) 'index)))
                   `(:expand (,lit)
                     :use ((:instance aignet-ubdd-order-reg-marked-invar-necc
                            (n (aignet-ubdd-order-reg-marked-invar-witness . ,(cdr lit)))
                            (index ,other)))
                     :in-theory (disable aignet-ubdd-order-reg-marked-invar-necc))))))
             
                 

  
  (defret <fn>-input-order-invar-preserved
    (implies (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
             (aignet-ubdd-input-order-invar new-index new-litarr new-invals new-regvals new-in-ubdds new-reg-ubdds aignet))
    :hints(("Goal" 
            :induct <call>
            :do-not-induct t
            :expand ((:free (count) <call>)))))

  (defret <fn>-input-order-invar-preserved-rw
    (implies (and (aignet-ubdd-input-order-invar index litarr invals regvals in-ubdds reg-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-input-order-invar new-ind new-litarr new-invals new-regvals new-in-ubdds new-reg-ubdds aignet)))

  (defret <fn>-order-in-marked-invar-preserved
    (implies (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
             (aignet-ubdd-order-in-marked-invar new-index new-litarr new-invals new-in-ubdds aignet))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret <fn>-order-in-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-in-marked-invar index litarr invals in-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-in-marked-invar new-ind new-litarr new-invals new-in-ubdds aignet)))

  (defret <fn>-order-reg-marked-invar-preserved
    (implies (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
             (aignet-ubdd-order-reg-marked-invar new-index new-litarr new-regvals new-reg-ubdds aignet))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret <fn>-order-reg-marked-invar-preserved-rw
    (implies (and (aignet-ubdd-order-reg-marked-invar index litarr regvals reg-ubdds aignet)
                  (equal new-ind new-index))
             (aignet-ubdd-order-reg-marked-invar new-ind new-litarr new-regvals new-reg-ubdds aignet)))
  
  (defret bitarr-range-count-of-<fn>
    (implies (equal (nfix index) (+ (bitarr-range-count 0 (num-ins aignet) invals)
                                    (bitarr-range-count 0 (num-regs aignet) regvals)))
             (equal new-index (+ (bitarr-range-count 0 (num-ins aignet) new-invals)
                                 (bitarr-range-count 0 (num-regs aignet) new-regvals))))
    :hints(("Goal"
            :in-theory (enable bitarr-range-count-of-aignet-output-range-collect-in/reg-ubdd-order)
            :induct <call>
            :expand ((:free (count) <call>)))))

  
  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet)
             (aignet-copies-in-bounds new-litarr aignet))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (count) <call>)))))

  (defret in-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth in-ubdds)
                      (nfix index))
                  (equal (nfix index)
                       (+ (bitarr-range-count 0 (num-ins aignet) invals)
                          (bitarr-range-count 0 (num-regs aignet) regvals))))
             (<= (ubdd-arr-max-depth new-in-ubdds)
                 new-index))
    :hints(("Goal"
            :induct <call>
            :in-theory (enable bitarr-range-count-of-aignet-output-range-collect-in/reg-ubdd-order)
            :expand ((:free (count) <call>))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-in-ubdds)
       new-index))))

  (defret reg-ubdds-max-depth-of-<fn>
    (implies (and (<= (ubdd-arr-max-depth reg-ubdds)
                      (nfix index))
                  (equal (nfix index)
                       (+ (bitarr-range-count 0 (num-ins aignet) invals)
                          (bitarr-range-count 0 (num-regs aignet) regvals))))
             (<= (ubdd-arr-max-depth new-reg-ubdds)
                 new-index))
    :hints(("Goal"
            :induct <call>
            :in-theory (enable bitarr-range-count-of-aignet-output-range-collect-in/reg-ubdd-order)
            :expand ((:free (count) <call>))))
    :rule-classes
    ((:linear :trigger-terms
      ((ubdd-arr-max-depth new-reg-ubdds)
       new-index))))
  
  (local (in-theory (enable aignet-output-range-map-fix))))



(define copy-lits-compose ((start natp)
                           (count natp)
                           aignet
                           litarr
                           copy
                           copy2)
  ;; Litarr contains aignet literals.
  ;; Copy maps those literals to aignet2 literals (for some aignet2).
  ;; We create copy2 which maps the indices of litarr to the aignet2 literals, composing
  ;; (copy) o (litarr).
  ;; Note aignet is only used for guard :(
  :guard (and (<= (+ start count) (lits-length litarr))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (+ start count) (lits-length copy2))
              (aignet-copies-in-bounds litarr aignet))
  :prepwork ((local (defthm <=-fanin-count-when-aignet-idp
                      (implies (and (aignet-idp id aignet)
                                    (natp id))
                               (< id (+ 1 (fanin-count aignet))))
                      :hints(("Goal" :in-theory (enable aignet-idp))))))
  :returns (new-copy2)
  :measure (nfix count)
  (b* (((when (zp count)) copy2)
       (lit (get-lit start litarr))
       (copy2 (set-lit start (lit-copy lit copy) copy2)))
    (copy-lits-compose (1+ (lnfix start)) (1- count)
                       aignet litarr copy copy2))
  ///
  (defret len-of-<fn>
    (implies (<= (+ (nfix start) (nfix count)) (len copy2))
             (equal (len new-copy2) (len copy2))))

  (defret nth-of-<fn>
    (equal (nth-lit n new-copy2)
           (if (and (<= (nfix start) (nfix n))
                    (< (nfix n) (+ (nfix start) (nfix count))))
               (lit-copy (nth-lit n litarr) copy)
             (nth-lit n copy2)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret aignet-elim-<fn>
    (implies (syntaxp (not (equal aignet ''nil)))
             (equal new-copy2
                    (let ((aignet nil)) <call>))))


  (local (defthm aignet-lit-listp-of-update-nth-lit
           (implies (and (aignet-lit-listp x aignet)
                         (aignet-litp y aignet))
                    (aignet-lit-listp (update-nth-lit n y x) aignet))
           :hints(("Goal" :in-theory (enable aignet-lit-listp update-nth-lit
                                             update-nth)))))
  
  (defret aignet-lit-listp-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-lit-listp copy2 aignet2))
             (aignet-lit-listp new-copy2 aignet2))))

(define copy-lits-compose-in-place (aignet
                                    litarr
                                    copy)
  ;; same as copy-lits-compose but copies over the given range in litarr
  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds litarr aignet))
  :returns (new-litarr)
  (b* (((acl2::local-stobjs copy2)
        (mv litarr copy2))
       (len  (lits-length litarr))
       (copy2 (resize-lits len copy2))
       (copy2 (copy-lits-compose 0 len aignet litarr copy copy2))
       ((mv litarr copy2) (swap-stobjs litarr copy2)))
    (mv litarr copy2))
  ///
  (defret len-of-<fn>
    (equal (len new-litarr) (len litarr)))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit nth)))))
  
  (defret nth-of-<fn>
    (equal (nth-lit n new-litarr)
           (if (< (nfix n) (len litarr))
               (lit-copy (nth-lit n litarr) copy)
             0)))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-litarr aignet2))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret aignet-elim-<fn>
    (implies (syntaxp (not (equal aignet ''nil)))
             (equal new-litarr
                    (let ((aignet nil)) <call>))))

  (defthm aignet-lit-listp-of-resize
    (aignet-lit-listp (resize-list nil n 0) aignet)
    :hints(("Goal" :in-theory (enable aignet-lit-listp
                                      resize-list))))
  
  (defret aignet-lit-listp-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-lit-listp new-litarr aignet2))))
              
              

(include-book "std/util/termhints" :dir :System)


(define aignet-parametrize-collect-bdd-order ((output-ranges aignet-output-range-map-p)
                                              (outtypes parametrize-output-type-map-p)
                                              litarr
                                              in-ubdds
                                              reg-ubdds
                                              aignet)
  :returns (mv new-litarr new-in-ubdds new-reg-ubdds)
  :guard (and (non-exec (equal litarr (create-litarr)))
              (non-exec (equal in-ubdds (create-ubdd-arr)))
              (non-exec (equal reg-ubdds (create-ubdd-arr))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bitarr-range-count-of-aignet-parametrize-collect-bdd-order-aux
                                          new-index-of-aignet-finish-in-ubdd-order
                                          new-index-of-aignet-finish-reg-ubdd-order))))
  (b* (((acl2::local-stobjs invals regvals)
        (mv invals regvals litarr in-ubdds reg-ubdds))
       (litarr (mbe :logic (non-exec (create-litarr))
                    :exec litarr))
       (litarr (resize-lits (+ (num-ins aignet) (num-regs aignet)) litarr))
       (in-ubdds (mbe :logic (non-exec (create-ubdd-arr))
                      :exec in-ubdds))
       (in-ubdds (resize-ubdds (num-ins aignet) in-ubdds))
       (reg-ubdds (mbe :logic (non-exec (create-ubdd-arr))
                       :exec reg-ubdds))
       (reg-ubdds (resize-ubdds (num-regs aignet) reg-ubdds))
       (invals (resize-bits (num-ins aignet) invals))
       (regvals (resize-bits (num-regs aignet) regvals))

       ((mv index invals regvals litarr in-ubdds reg-ubdds)
        (aignet-parametrize-collect-bdd-order-aux
         0 output-ranges
         outtypes 0 invals regvals litarr in-ubdds reg-ubdds aignet))

       ((mv index invals litarr in-ubdds)
        (aignet-finish-in-ubdd-order 0 index invals litarr in-ubdds aignet))

       ((mv ?index regvals litarr reg-ubdds)
        (aignet-finish-reg-ubdd-order 0 index regvals litarr reg-ubdds aignet))
       ((acl2::hintcontext :end)))
    (mv invals regvals litarr in-ubdds reg-ubdds))
  ///
  (set-ignore-ok t)
  
  (defret litarr-lookup-of-<fn>
    (implies (< (nfix n) (+ (num-regs aignet)
                            (num-ins aignet)))
             (B* ((LIT (NTH-LIT N new-LITARR))
                  (NEG (LIT->NEG LIT))
                  (ID (LIT->VAR LIT))
                  (TAIL (LOOKUP-ID ID AIGNET))
                  (NODE (CAR TAIL))
                  (INNUM (STYPE-COUNT (STYPE NODE) (CDR TAIL))))
               (AND (EQUAL NEG 0)
                    (EQUAL (CTYPE (STYPE NODE)) :INPUT)
                    (IMPLIES (EQUAL (STYPE NODE) :PI)
                             (EQUAL (NTH INNUM new-IN-UBDDS)
                                    (ACL2::QV N)))
                    (IMPLIES (EQUAL (STYPE NODE) :REG)
                             (EQUAL (NTH INNUM new-REG-UBDDS)
                                    (ACL2::QV N))))))
    :hints (("goal" :in-theory (disable aignet-finish-reg-ubdd-order-ubdd-input-order-invar-preserved
                                        aignet-finish-reg-ubdd-order-ubdd-input-order-invar-preserved-rw))
            (acl2::function-termhint
              aignet-parametrize-collect-bdd-order
             (:end
              (if (aignet-ubdd-input-order-invar
                   index litarr invals regvals in-ubdds reg-ubdds aignet)
                  `(:use ((:instance acl2::mark-clause-is-true (x :invar-holds)))
                    :in-theory (disable aignet-finish-reg-ubdd-order-ubdd-input-order-invar-preserved
                                        aignet-finish-reg-ubdd-order-ubdd-input-order-invar-preserved-rw))
                '(:use ((:instance acl2::mark-clause-is-true (x :invar-does-not-hold)))
                  :in-theory (enable aignet-finish-reg-ubdd-order-ubdd-input-order-invar-preserved-rw)))))))

  (defret in-ubdds-lookup-of-<fn>
    (implies (< (nfix n) (num-ins aignet))
             (let ((var-num (qv-inverse (nth n new-in-ubdds))))
               (and (equal (acl2::qv var-num)
                           (nth n new-in-ubdds))
                    (< var-num (+ (num-ins aignet)
                                  (num-regs aignet)))
                    (equal (nth-lit var-num new-litarr)
                           (make-lit (innum->id n aignet) 0)))))
    :hints (("goal" :in-theory (disable aignet-finish-reg-ubdd-order-order-in-marked-invar-preserved
                                        aignet-finish-reg-ubdd-order-order-in-marked-invar-preserved-rw))
            (acl2::function-termhint
             aignet-parametrize-collect-bdd-order
             (:end
              (if (aignet-ubdd-order-in-marked-invar
                   index litarr invals in-ubdds aignet)
                  `(:use ((:instance acl2::mark-clause-is-true (x :invar-holds))))
                '(:use ((:instance acl2::mark-clause-is-true (x :invar-does-not-hold)))
                  :in-theory (enable aignet-finish-reg-ubdd-order-order-in-marked-invar-preserved-rw)))))))

  (defret in-ubdds-lookup-of-<fn>-linear
    (implies (< (nfix n) (num-ins aignet))
             (let ((var-num (qv-inverse (nth n new-in-ubdds))))
               (< var-num (+ (stype-count :pi aignet)
                             (stype-count :reg aignet)))))
    :hints (("goal" :use in-ubdds-lookup-of-<fn>
             :in-theory (disable <fn> in-ubdds-lookup-of-<fn>)))
    :rule-classes :linear)

  (local (defthmd eval-bdd-of-equal-qv
           (implies (equal x (acl2::qv n))
                    (iff (acl2::eval-bdd x env)
                         (nth n env)))))
  
  (defret in-ubdds-eval-of-<fn>
    (implies (< (nfix n) (num-ins aignet))
             (iff (acl2::eval-bdd (nth n new-in-ubdds) env)
                  (nth (qv-inverse (nth n new-in-ubdds)) env)))
    :hints (("goal" :use in-ubdds-lookup-of-<fn>
             :in-theory (e/d (eval-bdd-of-equal-qv)
                             (<fn> in-ubdds-lookup-of-<fn>)))))

  (defret reg-ubdds-lookup-of-<fn>
    (implies (< (nfix n) (num-regs aignet))
             (let ((var-num (qv-inverse (nth n new-reg-ubdds))))
                       (and (equal (acl2::qv var-num)
                                   (nth n new-reg-ubdds))
                            (< var-num (+ (num-ins aignet)
                                          (num-regs aignet)))
                            (equal (nth-lit var-num new-litarr)
                                   (make-lit (regnum->id n aignet) 0)))))
    :hints (("goal" :in-theory (disable aignet-finish-reg-ubdd-order-order-reg-marked-invar-preserved
                                        aignet-finish-reg-ubdd-order-order-reg-marked-invar-preserved-rw))
            (acl2::function-termhint
             aignet-parametrize-collect-bdd-order
             (:end
              (if (aignet-ubdd-order-reg-marked-invar
                   index litarr regvals reg-ubdds aignet)
                  `(:use ((:instance acl2::mark-clause-is-true (x :invar-holds))))
                '(:use ((:instance acl2::mark-clause-is-true (x :invar-does-not-hold)))
                  :in-theory (enable aignet-finish-reg-ubdd-order-order-reg-marked-invar-preserved-rw)))))))

  (defret reg-ubdds-lookup-of-<fn>-linear
    (implies (< (nfix n) (num-regs aignet))
             (let ((var-num (qv-inverse (nth n new-reg-ubdds))))
               (< var-num (+ (stype-count :pi aignet)
                             (stype-count :reg aignet)))))
    :hints (("goal" :use reg-ubdds-lookup-of-<fn>
             :in-theory (disable <fn> reg-ubdds-lookup-of-<fn>)))
    :rule-classes :linear)
    


  (defret reg-ubdds-eval-of-<fn>
    (implies (< (nfix n) (num-regs aignet))
             (iff (acl2::eval-bdd (nth n new-reg-ubdds) env)
                  (nth (qv-inverse (nth n new-reg-ubdds)) env)))
    :hints (("goal" :use reg-ubdds-lookup-of-<fn>
             :in-theory (e/d (eval-bdd-of-equal-qv)
                             (<fn> reg-ubdds-lookup-of-<fn>)))))

  (defret in-ubdds-length-of-<fn>
    (equal (len new-in-ubdds) (num-ins aignet)))

  (defret reg-ubdds-length-of-<fn>
    (equal (len new-reg-ubdds) (num-regs aignet)))

  (defret litarr-length-of-<fn>
    (equal (len new-litarr) (+ (num-ins aignet) (num-regs aignet))))


  (defret in-ubdds-max-depth-of-<fn>
    (<= (ubdd-arr-max-depth new-in-ubdds)
        (+ (stype-count :pi aignet)
           (stype-count :reg aignet)))
    :rule-classes :linear)

  (defret reg-ubdds-max-depth-of-<fn>
    (<= (ubdd-arr-max-depth new-reg-ubdds)
        (+ (stype-count :pi aignet)
           (stype-count :reg aignet)))
    :rule-classes :linear)
  
  (defret aignet-copies-in-bounds-of-<fn>
    (aignet-copies-in-bounds new-litarr aignet))

  

  (local (defthm nth-of-take-split
           (equal (nth n (take m x))
                  (and (< (nfix n) (nfix m))
                       (nth n x)))
           :hints(("Goal" :in-theory (enable nth take)))))

  (local (defthm nth-of-bits->bools
           (equal (nth n (bits->bools x))
                  (bit->bool (nth n x)))
           :hints(("Goal" :in-theory (enable bits->bools nth)))))


  (local (defthm lit-eval-of-nil
           (equal (lit-eval nil invals regvals aignet)
                  0)
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))
  
  (local (defthm nth-of-lit-eval-list
           (bit-equiv (nth n (lit-eval-list x invals regvals aignet))
                      (lit-eval (nth-lit n x) invals regvals aignet))
           :hints(("Goal" :in-theory (enable nth nth-lit lit-eval-list)))))
  
  (defret eval-ubddarr-of-<fn>-in-ubddar-compose
    (bits-equiv (take (stype-count :pi aignet)
                      (eval-ubddarr new-in-ubdds
                                    (bits->bools
                                     (lit-eval-list
                                      (copy-lits-compose-in-place
                                       aignet0
                                       new-litarr
                                       copy)
                                      invals regvals aignet2))))
                (input-copy-values 0 invals regvals aignet copy aignet2))
    :hints(("Goal" :in-theory (e/d (bits-equiv
                                    lit-copy)
                                   (<fn>)))))

  (defret eval-ubddarr-of-<fn>-reg-ubddar-compose
    (bits-equiv (take (stype-count :reg aignet)
                      (eval-ubddarr new-reg-ubdds
                                    (bits->bools
                                     (lit-eval-list
                                      (copy-lits-compose-in-place
                                       aignet0
                                       new-litarr
                                       copy)
                                      invals regvals aignet2))))
                (reg-copy-values 0 invals regvals aignet copy aignet2))
    :hints(("Goal" :in-theory (e/d (bits-equiv
                                    lit-copy)
                                   (<fn>)))))
)



(define ubdd-arr-to-param-space ((start natp)
                                 (count natp)
                                 (hyp acl2::ubddp)
                                 (ubdd-arr))
  :returns (new-ubdd-arr)
  :guard (<= (+ start count) (ubdds-length ubdd-arr))
  (b* (((when (zp count)) ubdd-arr)
       (param-ubdd (acl2::to-param-space2 (lubdd-fix hyp) (get-ubdd start ubdd-arr)))
       (ubdd-arr (set-ubdd start param-ubdd ubdd-arr)))
    (ubdd-arr-to-param-space (1+ (lnfix start)) (1- count) hyp ubdd-arr))
  ///
  (defret len-of-<fn>
    (implies (<= (+ (nfix start) (nfix count)) (len ubdd-arr))
             (equal (len new-ubdd-arr) (len ubdd-arr))))


  
  (defret nth-of-<fn>
    (equal (nth n new-ubdd-arr)
           (cond ((and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix count))))
                  (acl2::to-param-space2
                   (acl2::ubdd-fix hyp)
                   (acl2::ubdd-fix (nth n ubdd-arr))))
                 (t (nth n ubdd-arr))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret max-depth-of-<fn>
    (<= (ubdd-arr-max-depth new-ubdd-arr)
        (ubdd-arr-max-depth ubdd-arr))
    :hints(("Goal" :in-theory (enable ubdd-arr-max-depth)))
    :rule-classes :linear)
  
  (local (defthm x-equal-nfix-plus-1
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret eval-ubddarr-of-<fn>
    (implies (acl2::eval-bdd hyp env)
             (bits-equiv (eval-ubddarr new-ubdd-arr env)
                         (eval-ubddarr ubdd-arr env)))
    :hints(("Goal" :in-theory (enable bits-equiv)))))
                                 


(define aignet-copy-dfs-output-range ((start natp)
                                      (count natp)
                                      aignet
                                      mark
                                      copy
                                      strash
                                      (gatesimp gatesimp-p)
                                      aignet2)
  :guard (and (<= (+ start count) (num-outs aignet))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :returns (mv new-mark
               new-copy
               new-strash
               new-aignet2)
  :measure (nfix count)
  (b* (((when (zp count))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv mark copy strash aignet2)))
       (lit (outnum->fanin start aignet))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec (lit->var lit) aignet mark copy strash gatesimp aignet2))
       (aignet2 (aignet-add-out (lit-copy lit copy) aignet2)))
    (aignet-copy-dfs-output-range (1+ (lnfix start))
                                  (1- count)
                                  aignet mark copy strash gatesimp aignet2))
  ///
  (local (in-theory (disable (:d aignet-copy-dfs-output-range))))
  (local (acl2::use-trivial-ancestors-check))
  
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints(("Goal" :induct <call>
            :in-theory (enable aignet-extension-p-transitive)
            :expand ((:free (count) <call>)))))
  
  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (case (stype-fix stype)
                      (:po (+ (nfix count) (stype-count stype aignet2)))
                      (t (stype-count stype aignet2)))))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (defret input-copies-in-bounds-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints(("Goal" :induct <call>
            :expand (<call>))))
  
  (defret marked-copies-in-bounds-of-<fn>
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (defret copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints(("Goal" :induct <call>
            :expand ((:free (count) <call>)))))

  (defret mark-length-of-<fn>
    (implies (<= (num-fanins aignet) (len mark))
             (equal (len new-mark) (len mark)))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (defret copy-length-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (defret <fn>-preserves-marked
    (implies (equal 1 (nth n mark))
             (equal (nth n new-mark) 1))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (defret <fn>-preserves-ci-copies
    (implies (double-rewrite (equal (id->type i aignet) (in-type)))
             (equal (nth-lit i (mv-nth 1 (aignet-copy-dfs-rec
                                          id aignet mark copy
                                          strash gatesimp aignet2)))
                    (nth-lit i copy)))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (local (defthm dfs-copy-onto-invar-of-add-po
           (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                         (aignet-input-copies-in-bounds copy aignet aignet2)
                         (aignet-marked-copies-in-bounds copy mark aignet2))
                    (dfs-copy-onto-invar aignet mark copy
                                         (cons (po-node fanin) (node-list-fix aignet2))))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))
  
  (defret dfs-copy-onto-invar-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (dfs-copy-onto-invar aignet new-mark new-copy new-aignet2))
    :hints(("Goal" :induct <call>
            :expand (<call>))))

  (local (defthm plus-cancel
           (equal (+ n (- n) x)
                  (fix x))))

  (local (defthm output-eval-of-new-po
           (implies (and (equal (nfix n) (stype-count :po aignet))
                         (aignet-idp (lit->var fanin) aignet))
                    (equal (output-eval n invals regvals (cons (po-node fanin) aignet))
                           (lit-eval fanin invals regvals aignet)))
           :hints(("Goal" :in-theory (enable output-eval)
                   :expand ((lookup-stype n :po (cons (po-node fanin) aignet)))))))


  (defret output-eval-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (equal (output-eval n invals regvals new-aignet2)
                    (if (and (<= (num-outs aignet2) (nfix n))
                             (< (nfix n) (+ (num-outs aignet2) (nfix count))))
                        (output-eval (+ (nfix start) (- (nfix n) (num-outs aignet2)))
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet)
                      (output-eval n invals regvals aignet2))))
    :hints(("Goal" :induct <call>
            :expand (<call>)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((:free (invals regvals)
                            (output-eval start invals regvals aignet))))))
    :otf-flg t)

  (defret input-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (input-copy-values n invals regvals aignet new-copy new-aignet2)
                    (input-copy-values n invals regvals aignet copy aignet2)))
    :hints(("Goal" :induct <call>
            :expand ((:free (count) <call>)))))

  (defret reg-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (reg-copy-values n invals regvals aignet new-copy new-aignet2)
                    (reg-copy-values n invals regvals aignet copy aignet2)))
    :hints(("Goal" :induct <call>
            :expand ((:free (count) <call>))))))



;; (define aignet-parametrize-m-n-output-types/ranges ((m natp)
;;                                                     (num-outs natp)
;;                                                     (output-ranges aignet-output-range-map-p)
;;                                                     (outtypes parametrize-output-type-map-p))
;;   :guard (<= m num-outs)
;;   :returns (mv (new-outtypes parametrize-output-types-p)
;;                (new-outcounts nat-listp :hyp (nat-listp outcounts)))
;;   :prepwork ((local (defthm minus-minus
;;                       (equal (- (- x)) (fix x)))))
;;   ;; Normalize outtypes/outcounts so that there are (- num-outs n) total
;;   ;; outputs accounted for.
;;   (b* ((sum (aignet-output-range-map-length outcounts))
;;        (target-num-outs (lnfix (- (lnfix num-outs) (lnfix m))))
;;        (outcounts
;;         (if (<= target-num-outs sum)
;;             (outcounts-trim (- sum target-num-outs) outcounts)
;;           (cons (- target-num-outs sum) outcounts)))
;;        (outtypes (parametrize-output-types-fix outtypes))
;;        (outtypes (if (<= (len outcounts) (len outtypes))
;;                      (nthcdr (- (len outtypes) (len outcounts)) outtypes)
;;                    (append (acl2::repeat (- (len outcounts) (len outtypes)) :param)
;;                            outtypes))))
;;     (mv outtypes outcounts))
;;   ///
;;   (defret len-outtypes-of-<fn>
;;     (equal (len new-outtypes) (len new-outcounts)))

;;   (local (defthm plus-minus-cancel
;;              (equal (+ x (- x) y)
;;                     (fix y))))
  
;;   (defret sum-outcounts-of-<fn>
;;     (equal (sum-outcounts new-outcounts)
;;            (nfix (- (nfix num-outs) (nfix m))))
;;     :hints (("goal" :expand ((:free (a b) (sum-outcounts (cons a b))))))))






(define aignet-parametrize-copy-set-ins ((n natp)
                                         litarr ;; UBDD variable nums to aignet2 literals
                                         in-ubdds ;; pi nums to parametrized ubdds
                                         aignet
                                         (memo ubdd-to-aignet-memo-p)
                                         copy ;; output: aignet pi nodes to parametrized ubdd copies in aignet2
                                         strash
                                         (gatesimp gatesimp-p)
                                         aignet2)
  :returns (mv (new-memo ubdd-to-aignet-memo-p)
               new-copy new-strash new-aignet2)
  :guard (and (<= n (num-ins aignet))
              (aignet-lit-listp (alist-vals memo) aignet2)
              (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds litarr aignet2)
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (ec-call (ubdd-arr-max-depth in-ubdds)) (lits-length litarr)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv (ubdd-to-aignet-memo-fix memo) copy strash aignet2)))
       (ubdd (get-ubdd n in-ubdds))
       ((mv ubdd-lit memo strash aignet2)
        (ubdd-to-aignet ubdd 0 memo litarr gatesimp strash aignet2))
       (id (innum->id n aignet))
       (copy (set-lit id ubdd-lit copy)))
    (aignet-parametrize-copy-set-ins (1+ (lnfix n)) litarr in-ubdds aignet memo copy strash gatesimp aignet2))
  ///
  (local (in-theory (disable (:d aignet-parametrize-copy-set-ins))))
  
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet2))
    :hints (("Goal" :induct <call>
             :expand (<call>))))
  
  (defret copy-len-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret result-lits-of-<fn>
    (implies (and (aignet-lit-listp (alist-vals (ubdd-to-aignet-memo-fix memo))
                                    aignet2)
                  (aignet-copies-in-bounds litarr aignet2))
             (and (implies (aignet-copies-in-bounds copy aignet2)
                           (aignet-copies-in-bounds new-copy new-aignet2))
                  (aignet-lit-listp (alist-vals new-memo) new-aignet2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-preserves-ubdd-to-aignet-memo-ok
    (implies (and (ubdd-to-aignet-memo-ok memo litarr aignet2 invals regvals)
                  (aignet-copies-in-bounds litarr aignet2)
                  (aignet-lit-listp
                   (alist-vals (ubdd-to-aignet-memo-fix memo)) aignet2))
             (ubdd-to-aignet-memo-ok new-memo litarr new-aignet2 invals regvals))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret nth-lit-preserved-of-<fn>
    (b* ((suff (lookup-id id aignet))
         (node (car suff))
         (rest (cdr suff))
         (stype (stype node))
         (innum (stype-count :pi rest)))
      (implies (not (and (eq stype :pi)
                         (<= (nfix n) innum)))
               (equal (nth-lit id new-copy)
                      (nth-lit id copy))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthm aignet-lit-listp-when-aignet-copies-in-bounds
           (implies (aignet-copies-in-bounds copy aignet)
                    (aignet-lit-listp copy aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-in-bounds-iff-aignet-lit-listp)))))
  
  (defret eval-nth-lit-of-<fn>
    (b* ((suff (lookup-id id aignet))
         (node (car suff))
         (rest (cdr suff))
         (stype (stype node))
         (innum (stype-count :pi rest)))
      (implies (and (eq stype :pi)
                    (<= (nfix n) innum)
                    (ubdd-to-aignet-memo-ok memo litarr aignet2 invals regvals)
                    (aignet-copies-in-bounds litarr aignet2)
                    (aignet-lit-listp
                     (alist-vals (ubdd-to-aignet-memo-fix memo)) aignet2))
               (equal (lit-eval (nth-lit id new-copy) invals regvals new-aignet2)
                      (bool->bit (acl2::eval-bdd (nth innum in-ubdds)
                                                 (bits->bools
                                                  (lit-eval-list litarr invals regvals aignet2)))))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding)))))


(define aignet-parametrize-copy-set-regs ((n natp)
                                          litarr ;; UBDD variable nums to aignet2 literals
                                          reg-ubdds ;; reg nums to parametrized ubdds
                                          aignet
                                          (memo ubdd-to-aignet-memo-p)
                                          copy ;; output: aignet reg nodes to parametrized ubdd copies in aignet2
                                          strash
                                          (gatesimp gatesimp-p)
                                          aignet2)
  :returns (mv (new-memo ubdd-to-aignet-memo-p)
               new-copy new-strash new-aignet2)
  :guard (and (<= n (num-regs aignet))
              (aignet-lit-listp (alist-vals memo) aignet2)
              (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds litarr aignet2)
              (<= (num-regs aignet) (ubdds-length reg-ubdds))
              (<= (ec-call (ubdd-arr-max-depth reg-ubdds)) (lits-length litarr)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv (ubdd-to-aignet-memo-fix memo) copy strash aignet2)))
       (ubdd (get-ubdd n reg-ubdds))
       ((mv ubdd-lit memo strash aignet2)
        (ubdd-to-aignet ubdd 0 memo litarr gatesimp strash aignet2))
       (id (regnum->id n aignet))
       (copy (set-lit id ubdd-lit copy)))
    (aignet-parametrize-copy-set-regs (1+ (lnfix n)) litarr reg-ubdds aignet memo copy strash gatesimp aignet2))
  ///
  (local (in-theory (disable (:d aignet-parametrize-copy-set-regs))))
  
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet2))
    :hints (("Goal" :induct <call>
             :expand (<call>))))

  (defret copy-len-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret result-lits-of-<fn>
    (implies (and (aignet-lit-listp (alist-vals (ubdd-to-aignet-memo-fix memo))
                                    aignet2)
                  (aignet-copies-in-bounds litarr aignet2))
             (and (implies (aignet-copies-in-bounds copy aignet2)
                           (aignet-copies-in-bounds new-copy new-aignet2))
                  (aignet-lit-listp (alist-vals new-memo) new-aignet2)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-preserves-ubdd-to-aignet-memo-ok
    (implies (and (ubdd-to-aignet-memo-ok memo litarr aignet2 invals regvals)
                  (aignet-copies-in-bounds litarr aignet2)
                  (aignet-lit-listp
                   (alist-vals (ubdd-to-aignet-memo-fix memo)) aignet2))
             (ubdd-to-aignet-memo-ok new-memo litarr new-aignet2 invals regvals))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret nth-lit-preserved-of-<fn>
    (b* ((suff (lookup-id id aignet))
         (node (car suff))
         (rest (cdr suff))
         (stype (stype node))
         (regnum (stype-count :reg rest)))
      (implies (not (and (eq stype :reg)
                         (<= (nfix n) regnum)))
               (equal (nth-lit id new-copy)
                      (nth-lit id copy))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthm aignet-lit-listp-when-aignet-copies-in-bounds
           (implies (aignet-copies-in-bounds copy aignet)
                    (aignet-lit-listp copy aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-in-bounds-iff-aignet-lit-listp)))))
  
  (defret eval-nth-lit-of-<fn>
    (b* ((suff (lookup-id id aignet))
         (node (car suff))
         (rest (cdr suff))
         (stype (stype node))
         (regnum (stype-count :reg rest)))
      (implies (and (eq stype :reg)
                    (<= (nfix n) regnum)
                    (ubdd-to-aignet-memo-ok memo litarr aignet2 invals regvals)
                    (aignet-copies-in-bounds litarr aignet2)
                    (aignet-lit-listp
                     (alist-vals (ubdd-to-aignet-memo-fix memo)) aignet2))
               (equal (lit-eval (nth-lit id new-copy) invals regvals new-aignet2)
                      (bool->bit (acl2::eval-bdd (nth regnum reg-ubdds)
                                                 (bits->bools
                                                  (lit-eval-list litarr invals regvals aignet2)))))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding)))))

(define aignet-parametrize-copy-init (litarr ;; UBDD variable nums to aignet2 literals
                                      in-ubdds ;; pi nums to parametrized ubdds
                                      reg-ubdds ;; reg nums to parametrized ubdds
                                      aignet
                                      copy ;; output: aignet input nodes to parametrized ubdd copies in aignet2
                                      strash
                                      (gatesimp gatesimp-p)
                                      aignet2)
  :returns (mv new-copy new-strash new-aignet2)
  :guard (and (aignet-copies-in-bounds litarr aignet2)
              (<= (num-regs aignet) (ubdds-length reg-ubdds))
              (<= (num-ins aignet) (ubdds-length in-ubdds))
              (<= (ec-call (ubdd-arr-max-depth in-ubdds)) (lits-length litarr))
              (<= (ec-call (ubdd-arr-max-depth reg-ubdds)) (lits-length litarr))
              (non-exec (equal copy (create-litarr))))
  (b* ((memo nil)
       (copy (mbe :logic (non-exec (create-litarr)) :exec copy))
       (copy (resize-lits (num-fanins aignet) copy))

       ((mv memo copy strash aignet2)
        (aignet-parametrize-copy-set-ins 0 litarr in-ubdds aignet memo copy strash gatesimp aignet2))
       ((mv memo copy strash aignet2)
        (aignet-parametrize-copy-set-regs 0 litarr reg-ubdds aignet memo copy strash gatesimp aignet2))
       (- (fast-alist-free memo)))
    (mv copy strash aignet2))
  ///
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet2)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet2)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet2)))

  

  (defret copy-len-of-<fn>
    (equal (len new-copy) (num-fanins aignet)))
  
  (defret result-lits-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (local (defthm aignet-lit-listp-when-aignet-copies-in-bounds
           (implies (aignet-copies-in-bounds copy aignet)
                    (aignet-lit-listp copy aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-in-bounds-iff-aignet-lit-listp)))))

  (defret eval-nth-lit-of-<fn>
    (b* ((suff (lookup-id id aignet))
         (node (car suff))
         (rest (cdr suff))
         (stype (stype node))
         (regnum (stype-count :reg rest))
         (innum (stype-count :pi rest)))
      (implies
       (aignet-copies-in-bounds litarr aignet2)
       (and (implies (equal stype :reg)
                     (equal (lit-eval (nth-lit id new-copy) invals regvals new-aignet2)
                            (bool->bit (acl2::eval-bdd (nth regnum reg-ubdds)
                                                       (bits->bools
                                                        (lit-eval-list litarr invals regvals aignet2))))))
            (implies (equal stype :pi)
                     (equal (lit-eval (nth-lit id new-copy) invals regvals new-aignet2)
                            (bool->bit (acl2::eval-bdd (nth innum in-ubdds)
                                                       (bits->bools
                                                        (lit-eval-list litarr invals regvals aignet2)))))))))
    :hints (("goal" :do-not-induct t)))

  (local (defthm nth-of-take-split
           (equal (nth n (take m x))
                  (and (< (nfix n) (nfix m))
                       (nth n x)))
           :hints(("Goal" :in-theory (enable nth take)))))
                    
  
  (defret input-copy-values-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet2)
             (bits-equiv (input-copy-values 0 invals regvals aignet new-copy new-aignet2)
                         (take (stype-count :pi aignet)
                               (eval-ubddarr in-ubdds (bits->bools (lit-eval-list litarr invals regvals aignet2))))))
    :hints(("Goal" :in-theory (e/d (bits-equiv
                                    nth-of-input-copy-values-split)
                                   (<fn>))
            :do-not-induct t)))

  (defret reg-copy-values-of-<fn>
    (implies (aignet-copies-in-bounds litarr aignet2)
             (bits-equiv (reg-copy-values 0 invals regvals aignet new-copy new-aignet2)
                         (take (stype-count :reg aignet)
                               (eval-ubddarr reg-ubdds (bits->bools (lit-eval-list litarr invals regvals aignet2))))))
    :hints(("Goal" :in-theory (e/d (bits-equiv
                                    nth-of-reg-copy-values-split)
                                   (<fn>))
            :do-not-induct t))))

(local (defthm len-equal-0
         (equal (equal (len x) 0) (atom x))))




(local (defcong bits-equiv equal (output-eval n invals regvals aignet) 2
         :hints(("Goal" :in-theory (enable output-eval)))))
(local (defcong bits-equiv equal (output-eval n invals regvals aignet) 3
         :hints(("Goal" :in-theory (enable output-eval)))))

(define aignet-parametrize-output-ranges ((start natp)
                                          (output-ranges aignet-output-range-map-p)
                                          (outtypes parametrize-output-type-map-p)
                                          aignet
                                          mark copy ;; unparametrized copying
                                          mark2 copy2 ;; parametrized copying
                                          strash (gatesimp gatesimp-p) aignet2)
  :measure (len output-ranges)
  :guard (and ;; (<= (+ (nfix start) (aignet-output-range-map-length output-ranges))
              ;;     (num-outs aignet))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (bits-length mark2))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-fanins aignet) (lits-length copy2))
              (aignet-copies-in-bounds copy aignet2)
              (aignet-copies-in-bounds copy2 aignet2))
  :returns (mv new-mark new-copy new-mark2 new-copy2 new-strash new-aignet2)
  :guard-hints (("goal" :expand ((aignet-output-range-map-length output-ranges))
                 :do-not-induct t))
  :guard-debug t
  (b* (((when (<= (num-outs aignet) (lnfix start)))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv mark copy mark2 copy2 strash aignet2)))
       ((when (atom output-ranges))
        ;; default to param type
        (b* (((mv mark2 copy2 strash aignet2)
              (aignet-copy-dfs-output-range
               start (- (num-outs aignet) (lnfix start))
               aignet mark2 copy2 strash gatesimp aignet2)))
          (mv mark copy mark2 copy2 strash aignet2)))

       ((unless (mbt (consp (car output-ranges))))
        (aignet-parametrize-output-ranges
         start (cdr output-ranges) outtypes aignet mark copy mark2 copy2 strash gatesimp aignet2))
       (name (mbe :logic (acl2::symbol-fix (caar output-ranges))
                  :exec (caar output-ranges)))
       (count (min (lnfix (cdar output-ranges))
                   (- (num-outs aignet) (lnfix start))))
       (type (or (cdr (hons-assoc-equal name (parametrize-output-type-map-fix outtypes)))
                 (parametrize-output-type-param)))
       ((mv mark copy mark2 copy2 strash aignet2)
        (if (parametrize-output-type-case type :param)
            (b* (((mv mark2 copy2 strash aignet2)
                  (aignet-copy-dfs-output-range
                   start count aignet mark2 copy2 strash gatesimp aignet2)))
              (mv mark copy mark2 copy2 strash aignet2))
          (b* (((mv mark copy strash aignet2)
                (aignet-copy-dfs-output-range
                 start count aignet mark copy strash gatesimp aignet2)))
            (mv mark copy mark2 copy2 strash aignet2)))))
    (aignet-parametrize-output-ranges
     (+ (lnfix start) count) (cdr output-ranges) outtypes
     aignet mark copy mark2 copy2 strash gatesimp aignet2))
  ///
  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints(("Goal" :induct <call>
            :expand ((:free (count) <call>)))))
  
  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (case (stype-fix stype)
                      (:po (+ (nfix (- (stype-count :po aignet) (nfix start)))
                              (stype-count stype aignet2)))
                      (t (stype-count stype aignet2)))))
    :hints(("Goal" :induct <call>
            :expand (<call>
                     (aignet-output-range-map-length output-ranges)))
           (and stable-under-simplificationp
                '(:in-theory (enable nfix)))))

  (local
   (defthm dfs-copy-onto-invar-of-aignet-extension
     (implies (and (aignet-extension-binding)
                   (dfs-copy-onto-invar aignet mark copy orig)
                   (aignet-copies-in-bounds copy orig))
              (dfs-copy-onto-invar aignet mark copy new))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause))))))))
  
  (defret output-eval-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (dfs-copy-onto-invar aignet mark2 copy2 aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (aignet-copies-in-bounds copy2 aignet2)
                  (bits-equiv (input-copy-values 0 invals regvals aignet copy aignet2)
                              (input-copy-values 0 invals regvals aignet copy2 aignet2))
                  (bits-equiv (reg-copy-values 0 invals regvals aignet copy aignet2)
                              (reg-copy-values 0 invals regvals aignet copy2 aignet2)))
             (equal (output-eval n invals regvals new-aignet2)
                    (if (and (<= (num-outs aignet2) (nfix n))
                             (< (nfix n) (+ (num-outs aignet2)
                                            (nfix (- (stype-count :po aignet) (nfix start))))))
                        (output-eval (+ (nfix start)
                                        (- (nfix n) (num-outs aignet2)))
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet)
                      (output-eval n invals regvals aignet2)))))

  (local (in-theory (enable aignet-output-range-map-fix))))
              

(define split-output-ranges ((count natp)
                             (output-ranges aignet-output-range-map-p))
  :returns (mv (first-ranges aignet-output-range-map-p)
               (rest-ranges aignet-output-range-map-p))
  ;; :guard (<= count (aignet-output-range-map-length output-ranges))
  :guard-hints (("goal" :in-theory (enable aignet-output-range-map-length)))
  :measure (len output-ranges)
  (b* (((when (zp count))
        (mv nil (aignet-output-range-map-fix output-ranges)))
       ((unless (consp output-ranges))
        ;; Pad out the first ranges to count
        (mv (list (cons nil count)) nil))
       ;; ((unless (mbt (consp output-ranges)))
       ;;  (mv nil nil))
       ((unless (mbt (consp (car output-ranges))))
        (split-output-ranges count (cdr output-ranges)))
       (first (mbe :logic (cons (acl2::symbol-fix (caar output-ranges))
                                (nfix (cdar output-ranges)))
                   :exec (car output-ranges)))
       ((mv first2 rest) (split-output-ranges (max 0 (- (lnfix count) (lnfix (cdar output-ranges))))
                                              (cdr output-ranges))))
    (mv (cons first first2) rest))
  ///
  (defret append-of-<fn>
    (implies (<= (nfix count) (aignet-output-range-map-length output-ranges))
             (equal (append first-ranges rest-ranges)
                    (aignet-output-range-map-fix output-ranges)))
    :hints(("Goal" :in-theory (enable aignet-output-range-map-fix
                                      aignet-output-range-map-length))))

  (defret length-of-<fn>
    (<= (nfix count) (aignet-output-range-map-length first-ranges))
    :hints(("Goal" :in-theory (enable aignet-output-range-map-length)))
    :rule-classes :linear)

  (defret length-of-<fn>-first-upper-bound
    (implies (<= (nfix count) (aignet-output-range-map-length output-ranges))
             (<= (aignet-output-range-map-length first-ranges)
                 (aignet-output-range-map-length output-ranges)))
    :hints(("Goal" :in-theory (enable aignet-output-range-map-length)))
    :rule-classes :linear)

  (local (defthm plus-minus
           (equal (+ x (- x) y)
                  (fix y))))
  
  (defret length-of-<fn>-adds-up
    (implies (<= (nfix count) (aignet-output-range-map-length output-ranges))
             (equal (aignet-output-range-map-length rest-ranges)
                    (- (aignet-output-range-map-length output-ranges)
                       (aignet-output-range-map-length first-ranges))))
    :hints(("Goal" :in-theory (enable aignet-output-range-map-length))))

  (defret true-listp-of-<fn>
    (true-listp first-ranges)
    :rule-classes :type-prescription)

  ;; (defret <fn>-when-split-count-greater
  ;;   (implies (< (aignet-output-range-map-length output-ranges)
  ;;               (nfix count))
  ;;            (and (equal first-ranges
  ;;                        (aignet-output-range-map-fix output-ranges))
  ;;                 (equal rest-ranges nil)))
  ;;   :hints(("Goal" :in-theory (enable aignet-output-range-map-length
  ;;                                     aignet-output-range-map-fix))))
  
                  

  (local (in-theory (enable aignet-output-range-map-fix))))



(local
 (defthm dfs-copy-onto-invar-of-init-copy-comb
   (b* (((mv new-copy new-aignet2)
         (init-copy-comb aignet copy aignet2)))
     (dfs-copy-onto-invar aignet (resize-list nil n 0) new-copy new-aignet2))
   :hints(("Goal" :in-theory (enable dfs-copy-onto-invar)))))

(local (defthm output-eval-of-take-ins
         (equal (output-eval n (take (stype-count :pi aignet) invals) regvals aignet)
                (output-eval n invals regvals aignet))
         :hints(("Goal" :in-theory (enable output-eval)))))

(local (defthm output-eval-of-take-regs
         (equal (output-eval n invals (take (stype-count :reg aignet) regvals) aignet)
                (output-eval n invals regvals aignet))
         :hints(("Goal" :in-theory (enable output-eval)))))

(local (defthm dfs-copy-onto-invar-of-aignet-extension
         (implies (and (aignet-extension-binding)
                       (dfs-copy-onto-invar aignet mark copy orig)
                       (aignet-copies-in-bounds copy orig))
                  (dfs-copy-onto-invar aignet mark copy new))
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))))))))

(local (defthm dfs-copy-onto-invar-of-resize
         (dfs-copy-onto-invar aignet (resize-list nil n 0) copy aignet2)
         :hints(("Goal" :in-theory (enable dfs-copy-onto-invar)))))


(defcong bits-equiv bits-equiv (take n x) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(defcong bits-equiv equal (conjoin-output-range start count invals regvals aignet) 3
  :hints(("Goal" :in-theory (enable conjoin-output-range))))

(defcong bits-equiv equal (conjoin-output-range start count invals regvals aignet) 4
  :hints(("Goal" :in-theory (enable conjoin-output-range))))



(local
 (defthm conjoin-output-range-rewrite-invals-with-take
   (implies (and (bits-equiv new-invals (double-rewrite (take (stype-count :pi aignet) invals)))
                 (bind-free
                  (case-match new-invals
                    (('take & new-invals1) `((new-invals1 . ,new-invals1)))
                    (& `((new-invals1 . ,new-invals))))
                  (new-invals1))
                 (bits-equiv (take (stype-count :pi aignet) new-invals1) new-invals)
                 (syntaxp (not (equal new-invals1 invals))))
            (equal (conjoin-output-range start count invals regvals aignet)
                   (conjoin-output-range start count new-invals1 regvals aignet)))
   :hints (("goal" :use ((:instance conjoin-output-range-of-take-ins
                          (n count))
                         (:instance conjoin-output-range-of-take-ins
                          (n count) (invals new-invals1)))
            :in-theory (disable conjoin-output-range-of-take-ins)))))

(local
 (defthm conjoin-output-range-rewrite-regvals-with-take
   (implies (and (bits-equiv new-regvals (double-rewrite (take (stype-count :reg aignet) regvals)))
                 (bind-free
                  (case-match new-regvals
                    (('take & new-regvals1) `((new-regvals1 . ,new-regvals1)))
                    (& `((new-regvals1 . ,new-regvals))))
                  (new-regvals1))
                 (bits-equiv (take (stype-count :reg aignet) new-regvals1) new-regvals)
                 (syntaxp (not (equal new-regvals1 regvals))))
            (equal (conjoin-output-range start count invals regvals aignet)
                   (conjoin-output-range start count invals new-regvals1 aignet)))
   :hints (("goal" :use ((:instance conjoin-output-range-of-take-regs
                          (n count))
                         (:instance conjoin-output-range-of-take-regs
                          (n count) (regvals new-regvals1)))
            :in-theory (disable conjoin-output-range-of-take-regs)))))

(define aignet-parametrize-m-n ((m natp)
                                (n natp)
                                (aignet  "Input aignet")
                                (aignet2 "New aignet -- will be emptied")
                                (config parametrize-config-p
                                        "Settings for the transform")
                                (output-ranges aignet-output-range-map-p))
  :guard (<= (+ m n) (num-outs aignet))
  :returns new-aignet2
  (declare (ignorable n))
  :guard-debug t
  :guard-hints ((and stable-under-simplificationp
                     '(:cases ((<= m (aignet-output-range-map-length output-ranges))))))
  (b* (((acl2::local-stobjs litarr in-ubdds reg-ubdds mark mark2 ubdd-arr u32arr copy copy2 strash)
        (mv litarr in-ubdds reg-ubdds mark mark2 ubdd-arr u32arr copy copy2 strash aignet2))
       ((parametrize-config config))
       ;; ((mv output-types output-ranges)
       ;;  (aignet-parametrize-m-n-output-types/ranges
       ;;   m (num-outs aignet) config.output-types output-ranges))
       ((mv litarr in-ubdds reg-ubdds)
        ;; litarr: map from BDD variable nums to aignet pi/reg lits
        ;; in-ubdds: map from aignet pi numbers to UBDD variables
        ;; reg-ubdds: map from aignet reg numbers to UBDD variables
        (aignet-parametrize-collect-bdd-order
         output-ranges config.output-types litarr in-ubdds reg-ubdds aignet))
       (mark (resize-bits (num-fanins aignet) mark))
       (mark2 (resize-bits (num-fanins aignet) mark2))
       (ubdd-arr (resize-ubdds (num-fanins aignet) ubdd-arr))
       (u32arr (resize-u32 (num-fanins aignet) u32arr))
       ((mv hyp-ubdd ?hyp-count mark mark2 ubdd-arr u32arr)
        ;; ubdd-arr: map from aignet nodes to UBDDs
        (aignet-output-range-conjoin-ubdds
         0 m config.build-limit config.conjoin-limit
         t 0 mark mark2 ubdd-arr in-ubdds reg-ubdds u32arr aignet))

       ;; parametrize in-ubdds and reg-ubdds -- now map from aignet pi/reg
       ;; numbers to parametrized UBDD vars
       (in-ubdds (ubdd-arr-to-param-space 0 (num-ins aignet) hyp-ubdd in-ubdds))
       (reg-ubdds (ubdd-arr-to-param-space 0 (num-regs aignet) hyp-ubdd reg-ubdds))

       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       ;; copy -- now maps aignet pi/reg nodes to aignet2 literals

       ;; We don't really need the old litarr (I think) so we'll just convert
       ;; it in place.
       (litarr (copy-lits-compose-in-place aignet litarr copy))
       
       (gatesimp (default-gatesimp))
       (mark (resize-bits 0 mark))
       (mark (resize-bits (num-fanins aignet) mark))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-output-range 0 m aignet mark copy strash gatesimp aignet2))
       ;; copy -- now maps marked aignet nodes to aignet2 literals, not in param space

       (mark2 (resize-bits 0 mark2))
       (mark2 (resize-bits (num-fanins aignet) mark2))
       
       ;; copy2 needs to map aignet pi/reg nodes to copies of parametrized BDDs
       ;; in aignet2.  to do this we need to encode the parametrized ubdds into
       ;; aignet2, and to do this (using ubdd-to-aignet) we need a litarr which
       ;; maps ubdd variable numbers to aignet2 input/reg literals.
       ((mv copy2 strash aignet2)
        (aignet-parametrize-copy-init litarr ;; UBDD variable nums to aignet2 literals
                                      in-ubdds ;; pi nums to parametrized ubdds
                                      reg-ubdds ;; reg nums to parametrized ubdds
                                      aignet
                                      copy2
                                      strash
                                      gatesimp
                                      aignet2))

       ((mv & output-ranges) (split-output-ranges m output-ranges))
       ((mv mark copy mark2 copy2 strash aignet2)
        (aignet-parametrize-output-ranges
         m output-ranges config.output-types aignet mark copy mark2 copy2 strash gatesimp aignet2)))
    (mv litarr in-ubdds reg-ubdds mark mark2 ubdd-arr u32arr copy copy2 strash aignet2))
  ///

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (implies (<= (+ (nfix m) (nfix n)) (stype-count :po aignet))
             (<= (+ (nfix m) (nfix n)) (stype-count :po new-aignet2)))
    :rule-classes :linear)

  (defret num-outs-of-<fn>-relative-to-output-map-length
    (implies (<= (aignet-output-range-map-length output-ranges)
                 (stype-count :po aignet))
             (<= (aignet-output-range-map-length output-ranges)
                 (stype-count :po new-aignet2)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (a b) (nfix (+ a b)))))))
    :rule-classes :linear)

  (defret <fn>-eval-assumptions
    (implies (< (nfix i) (nfix m))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet))))

  (defret <fn>-eval-conclusion
    (implies (And (< (nfix i) (+ (nfix m) (nfix n)))
                  (equal (conjoin-output-range 0 m invals regvals aignet) 1))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (a b) (nfix (+ a b))))))))

  (defret normalize-aignet2-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal new-aignet2
                    (let ((aignet2 nil)) <call>)))))
