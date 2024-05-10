; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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

(in-package "SV")

(include-book "symbolic")
(include-book "envs-agree-on-masks")
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/bfr" :dir :system)
(include-book "centaur/fgl/simplify-defs" :dir :system)
(include-book "centaur/fgl/checks" :dir :system)
(include-book "centaur/fgl/make-isomorphic-def" :dir :system)
(include-book "centaur/fgl/list-to-tree" :dir :system)
(local (include-book "alist-thms"))
;; (include-book "centaur/aignet/transforms" :dir :System)


(defxdoc svex-focused-equivalence-checking
  :parents (bit-blasting)
  :short "Tools for equivalence checking the evaluations of two
sets of svex @(see expressions) under different environments."
  :long " <p>Typically when we want to equivalence check the evaluation of some
SVEX expressions against something else, e.g. a spec for some operation, we
just bitblast both sides into an AIG and use FRAIGing along with other AIG
transformations, followed by SAT to finish the proof.</p>

<p>The FRAIGing step is important because it speeds up the common case where
the two sides are equivalent because they have a lot of equivalent subterms.
To find candidate equivalent subterms, the transformation does a bunch of
random simulation of the AIG and puts nodes which have identical simulation
signatures into equivalence classes.  Then it starts sweeping over the nodes
with SAT to prove the equivalences.  When it disproves an equivalence, this
gives a counterexample which is again simulated on the AIG to further refine
the equivalence classes.</p>

<p>A weakness of this algorithm is that sometimes many non-equivalent nodes
seem to have the same behavior under simulation because their differences are
improbable to be covered by random simulation.  When there are lots of these
nodes that aren't closely related in terms of their equivalence
counterexamples, then we spend a lot of useless time on SAT checking.  Or
sometimes perhaps there are equivalent nodes within one side of the equivalence
to be checked, but this equivalence doesn't help us prove that side equivalent
to the other.</p>

<p>In the particular case where we are equivalence checking an evaluation of
SVEX expressions against another evaluation of the same expressions, we can
improve on this.  We tweak our FRAIGing operation to begin with equivalence
classes consisting only of the corresponding nodes between the two
designs. This cuts down a lot on useless SAT checks; not all of the
corresponding nodes are necessarily equivalent, but typically we expect the
overall evaluations to be equivalent because of relatively simple equivalences
near the inputs, not because of deep properties that SAT is ill-equipped to
check.</p>

<p>We do this using FGL's @(see fgl::fgl-simplify-ordered) operation.  This
operation produces an AIG from an existing symbolic object, arranging the
outputs of the AIG in a predictable order corresponding to the traversal order
of the symbolic object -- e.g., car before cdr, integer bits LSB first, etc.
We arrange the symbolic object so that the miter for the actual equivalence
check is first, followed by many bits for subexpressions of the first
evaluation, followed by bits for the same subexpressions of the second
evaluation.  We then use an option for our FRAIG transform to begin with
equivalence classes formed by pairing outputs O-N+i, O-2N+i, for i=0 up to N-1,
where O is the total number of outputs and N is the number of subexpression
bits for each evaluation.  The FRAIG transformation then uses random simulation
to further refine these equivalence classes and proceeds with the equivalence
check.</p>

")



(define svexlist-evals-equal ((x svexlist-p)
                              (env1 svex-env-p)
                              (env2 svex-env-p))
  (equal (svexlist-eval x env1)
         (svexlist-eval x env2)))



(define svexlist-mask-alist/toposort-memo ((x svexlist-p))
  :enabled t
  (svexlist-mask-alist/toposort x)
  ///
  (memoize 'svexlist-mask-alist/toposort-memo))


(define svexlists->a4vec-top ((x svexlist-p) (y svexlist-p) (env svex-a4vec-env-p) (masks svex-mask-alist-p))
  ;; note: env must be fast
  ;; :prepwork ((local (defthm svexlist->a4vec-decomp
  ;;                     (equal (list (mv-nth 0 (svexlist->a4vec x env masks memo))
  ;;                                  (mv-nth 1 (svexlist->a4vec x env masks memo)))
  ;;                            (svexlist->a4vec x env masks memo))
  ;;                     :hints (("goal" :expand ((svexlist->a4vec x env masks memo)))))))
  :enabled t
  (mbe :logic (mv (svexlist->a4vec x env masks)
                  (svexlist->a4vec y env masks))
       :exec
       (b* (((mv x-res y-res memo)
             (with-local-stobj acl2::nrev
               (mv-let (x-res y-res memo acl2::nrev)
                 (b* (((mv acl2::nrev memo)
                       (svexlist->a4vec-nrev x env masks nil acl2::nrev))
                      ((mv x-res acl2::nrev) (acl2::nrev-finish acl2::nrev))
                      ((mv acl2::nrev memo)
                       (svexlist->a4vec-nrev y env masks memo acl2::nrev))
                      ((mv y-res acl2::nrev) (acl2::nrev-finish acl2::nrev)))
                   (mv x-res y-res memo acl2::nrev))
                 (mv x-res y-res memo)))))
         (fast-alist-free memo)
         (mv x-res y-res))))

(define svexlist->a4vecs-for-varlist-with-subexprs ((x svexlist-p)
                                                    (vars svarlist-p)
                                                    (boolmasks svar-boolmasks-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (x-a4vecs a4veclist-p)
               (subexp-a4vecs a4veclist-p))
  :short "Creates a symbolic bit-level representation for x, assuming that vars
          are the only vars relevant to x and that the bits of vars given in boolmasks
          are Boolean-valued."
  :long "<p>Steps: First creates a symbolic environment mapping the variables
to a4vec structures, each bit of which is a free variable.  (For bits
constrained to be Boolean by boolmasks, the same variable is shared for
upper/lower.)  Then uses @('svexlist->a4vec-top') to generate a4vecs corresponding
to the svexes.</p>"

  (b* (;; (- (sneaky-push 'svexlist x))
       ((mv masks toposort) (svexlist-mask-alist/toposort-memo x))
       ((mv err a4env) (svex-varmasks->a4env vars masks boolmasks))
       ((when err) (mv err nil nil))
       (a4env (make-fast-alist a4env))
       ((mv x-res sub-res) (svexlists->a4vec-top x toposort a4env masks))
       (?ign (fast-alist-free a4env)))
    (mv nil x-res sub-res))
  ///
  (memoize 'svexlist->a4vecs-for-varlist-with-subexprs)

  (defret <fn>-equals-svexlist->a4vecs-for-varlist
    (b* (((mv err-spec a4vec-spec) (svexlist->a4vecs-for-varlist x vars boolmasks)))
      (and (equal err err-spec)
           (equal x-a4vecs a4vec-spec)))
    :hints(("Goal" :in-theory (enable svexlist->a4vecs-for-varlist)))))


(local (defthm true-listp-nthcdr
         (implies (true-listp x)
                  (true-listp (nthcdr n x)))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))
         :rule-classes :type-prescription))

(local (defthm nthcdr-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y))
                         y))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))))

(local (defthm nthcdr-of-append-2-equal-len
         (implies (equal (nfix n) (+ (len x) (len y)))
                  (equal (nthcdr n (append x y z))
                         z))
         :hints(("Goal" :use ((:instance nthcdr-of-append-equal-len
                               (x (append x y)) (y z)))))))

(local (defthm take-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (take n (append x y))
                         (list-fix x)))
         :hints(("Goal" :in-theory (e/d (acl2::take))
                 :induct (nthcdr n x)))))

(define my-replace-assoc ((key symbolp) val alist)
  (if (atom alist)
      alist
    (if (and (consp (car alist))
             (eq key (caar alist)))
        (cons (cons key val) (cdr alist))
      (cons (car alist) (my-replace-assoc key val (cdr alist))))))
        


(define transforms-update-fraig-configs-for-n-outputs ((n natp) transforms)
  ;; BOZO We don't want to load the fraig book just to be able to write an updater for its config.
  ;; So we're going to assume the basic form of a fraig config object which is (:fraig . alist)
  (if (atom transforms)
      nil
    (cons (b* ((x (car transforms))
               ((unless (and (consp x)
                             (eq (car x) :fraig-config)
                             (alistp (cdr x))))
                x)
               ;; Change the config: find the AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES entry
               ;; and replace it with `(AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES . ,n)
               (alist (cdr x))
               (n-outputs-entry (cdr (assoc 'AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES alist)))
               ((unless n-outputs-entry)
                (cons :fraig-config alist))
               (alist (my-replace-assoc 
                       'AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES (lnfix n) alist))
               (alist (my-replace-assoc
                       'AIGNET::INITIAL-EQUIV-CLASSES-LAST t alist)))
            (cons :fraig-config alist))
          (transforms-update-fraig-configs-for-n-outputs n (cdr transforms)))))

;; (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "std/lists/nth" :dir :system))

;; (define fgl-fix-boolean-list-to-g-booleans-rec (n x rest)
;;   :enabled t
;;   (append (ec-call (take n x)) rest)
;;   ///
;;   (local (in-theory (enable bitops::logtail**)))
;;   (local (defthm logcar-plus-logcdr
;;            (implies (natp x)
;;                     (<= (+ (logcar x) (logcdr x)) x))
;;            :hints (("goal" :use ((:instance bitops::logcons-destruct))
;;                     :in-theory (e/d (logcons)
;;                                     (bitops::logcons-destruct
;;                                      acl2::logcar-logcdr-elim))))
;;            :rule-classes :linear))
;;   (local (defthm logcar-plus-logcdr-gte-1
;;            (implies (posp x)
;;                     (<= 1 (+ (logcar x) (logcdr x))))
;;            :hints (("goal" :use ((:instance bitops::logcons-destruct))
;;                     :in-theory (e/d (logcons)
;;                                     (bitops::logcons-destruct
;;                                      acl2::logcar-logcdr-elim))))
;;            :rule-classes :linear))
;;   (local (defthm append-take-nthcdr
;;            (equal (append (take n x) (take m (nthcdr n x)))
;;                   (take (+ (nfix n) (nfix m)) x))
;;            :hints(("Goal" :in-theory (enable take nthcdr)
;;                    :induct (take m (nthcdr n x))))))
;;   (local (defthm cdr-of-nthcdr
;;            (equal (cdr (nthcdr n x))
;;                   (nthcdr n (cdr x)))))
;;   (local (in-theory (disable acl2::cdr-nthcdr)))

;;   (local (defthm append-take-nthcdr-2
;;            (equal (append (take n x) (take m (nthcdr n x)) y)
;;                   (append (take (+ (nfix n) (nfix m)) x) y))
;;            :hints (("goal" :use ((:instance ACL2::ASSOCIATIVITY-OF-APPEND
;;                                   (a (take n x)) (b (take m (nthcdr n x))) (c y)))
;;                     :in-theory (disable acl2::associativity-of-append)))))
  
;;   (fgl::def-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-rec-impl
;;     (equal (fgl-fix-boolean-list-to-g-booleans-rec n x rest)
;;            (b* (((When (zp n)) rest)
;;                 (first (b* ((x1 (car x))
;;                             ((when (fgl::check-equal x1-is-t x1 t))
;;                              (fgl::symbolic-t))
;;                             ((when (fgl::check-equal x-is-nil x1 nil))
;;                              (fgl::symbolic-nil)))
;;                          x1))
;;                 (x (cdr x))
;;                 (n (1- n))
;;                 (halfn (ash n -1))
;;                 (restn (- n halfn))
;;                 (rest (fgl-fix-boolean-list-to-g-booleans-rec restn (nthcdr halfn x) rest))
;;                 (rest (fgl-fix-boolean-list-to-g-booleans-rec halfn x rest)))
;;              (cons first rest)))
;;     :hints (("goal" :in-theory (enable fgl::check-equal))))

;;   (fgl::remove-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-rec))
    


;; (define fgl-fix-boolean-list-to-g-booleans (x)
;;   :enabled t
;;   (true-list-fix x)
;;   ///
;;   (fgl::def-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-impl
;;     (equal (fgl-fix-boolean-list-to-g-booleans x)
;;            (fgl-fix-boolean-list-to-g-booleans-rec (len x) x nil)))

;;   (fgl::remove-fgl-rewrite fgl-fix-boolean-list-to-g-booleans))



;; (define a4veclist-eval-for-evals-equal ((x a4veclist-p) (sub a4veclist-p) (env1) (env2) (transforms))
;;   ;; Flattens sub and x (a4veclists) into AIG lists, evaluates them under two
;;   ;; envs, orders them so that the respective evaluations of y can be used as
;;   ;; simplifies them with the special form of the FRAIG transform, then
;;   ;; recovers those from x and transforms it back to an a4veclist.
;;   :enabled t
;;   (declare (ignorable sub transforms))
;;   (mv (a4veclist-eval x env1)
;;       (a4veclist-eval x env2))
;;   ///
;;   (fgl::def-fgl-rewrite a4veclist-eval-for-evals-equal-fgl
;;     (equal (a4veclist-eval-for-evals-equal x sub env1 env2 transforms)
;;            (b* ((sub-aiglist (time$ (a4veclist->aiglist sub)
;;                                     :msg "; SV bit-blasting: a4veclist->aiglist (sub): ~st sec, ~sa bytes.~%"))
;;                 (sub-len (time$ (len sub-aiglist)
;;                                 :msg "; SV bit-blasting: len(sub): ~st sec, ~sa bytes.~%"))
;;                 (x-aiglist (time$ (a4veclist->aiglist x)
;;                                   :msg "; SV bit-blasting: a4veclist->aiglist (x): ~st sec, ~sa bytes.~%"))
;;                 (x-len (time$ (len x-aiglist)
;;                               :msg "; SV bit-blasting: len(x): ~st sec, ~sa bytes.~%"))
;;                 (env1 (make-fast-alist env1))
;;                 (env2 (make-fast-alist env2))
;;                 (sub-bits1 (time$ (fgl-fix-boolean-list-to-g-booleans
;;                                    (aig-eval-list sub-aiglist env1))
;;                                   :msg "; SV bit-blasting: aig-eval-list (sub, env1): ~st sec, ~sa bytes.~%"))
;;                 (sub-bits2 (time$ (fgl-fix-boolean-list-to-g-booleans
;;                                    (aig-eval-list sub-aiglist env2))
;;                                   :msg "; SV bit-blasting: aig-eval-list (sub, env2): ~st sec, ~sa bytes.~%"))
;;                 (x-bits1 (time$ (aig-eval-list x-aiglist env1)
;;                                 :msg "; SV bit-blasting: aig-eval-list (x, env1): ~st sec, ~sa bytes.~%"))
;;                 (x-bits2 (time$ (aig-eval-list x-aiglist env2)
;;                                 :msg "; SV bit-blasting: aig-eval-list (x, env2): ~st sec, ~sa bytes.~%"))
;;                 (?ign (fast-alist-free env1))
;;                 (?ign (fast-alist-free env2))
;;                 (full-bits (append sub-bits1 sub-bits2 x-bits1 x-bits2))
;;                 (transforms (transforms-update-fraig-configs-for-n-outputs sub-len transforms))
;;                 (full-bits-simp (fgl::fgl-simplify-ordered full-bits transforms :use-pathcond nil :use-constraint nil))
;;                 (x-bits-simp (nthcdr (* 2 sub-len) full-bits-simp))
;;                 (x-bits1 (take x-len x-bits-simp))
;;                 (x-bits2 (nthcdr x-len x-bits-simp))
;;                 (x-4vecs1 (time$ (4veclist-from-bitlist x x-bits1)
;;                                  :msg "; bits->4vecs 1: ~st sec, ~sa bytes.~%"))
;;                 (x-4vecs2 (time$ (4veclist-from-bitlist x x-bits2)
;;                                  :msg "; bits->4vecs 1: ~st sec, ~sa bytes.~%"))
;;                 (?ign (fgl::fgl-gatecount 4vecs (cons x-4vecs1 x-4vecs2))))
;;              (mv x-4vecs1 x-4vecs2))))
  
;;   (fgl::remove-fgl-rewrite a4veclist-eval-for-evals-equal))

(local (include-book "std/lists/sets" :dir :system))

(local (defthm setp-of-svexlist-vars-for-symbolic-eval
         (set::setp (svexlist-vars-for-symbolic-eval
                     x env symbolic-params))
         :hints(("Goal" :in-theory (enable svexlist-vars-for-symbolic-eval)))))

(local (defthm subsetp-of-append-1
         (implies (subsetp x y)
                  (subsetp x (append y z)))))

(local (defthm subsetp-of-append-2
         (implies (subsetp x z)
                  (subsetp x (append y z)))))


(local (defthm subsetp-maybe-svexlist-rewrite-fixpoint-of-x-out-unused-vars
         (subsetp-equal (svexlist-vars (maybe-svexlist-rewrite-fixpoint
                                        (svexlist-x-out-unused-vars x vars params)
                                        simp))
                        (svexlist-vars x))
         :hints ((set-reasoning))))

(local (defthm subsetp-intersection-maybe-svexlist-rewrite-fixpoint-of-x-out-unused-vars
         (implies (subsetp (intersection-equal
                            (svexlist-vars x) envkeys)
                           vars2)
                  (subsetp (intersection-equal
                            (svexlist-vars (maybe-svexlist-rewrite-fixpoint
                                        (svexlist-x-out-unused-vars x vars params)
                                        simp))
                            envkeys)
                           vars2))
         :hints ((set-reasoning))))










(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))


(define 4veclist-separate-upper-lower-rec-log ((n natp)
                                               (x 4veclist-p)
                                               (rest-upper integer-listp)
                                               (rest-lower integer-listp))
  :measure (nfix n)
  :guard (<= n (len x))
  :returns (mv (uppers integer-listp :hyp (integer-listp rest-upper))
               (lowers integer-listp :hyp (integer-listp rest-lower)))
  :verify-guards nil
  :hints(("Goal" :in-theory (enable bitops::logtail**)))
  :prepwork ((local (defthm logcar-plus-logcdr
                      (implies (natp x)
                               (<= (+ (logcar x) (logcdr x)) x))
                      :hints (("goal" :use ((:instance bitops::logcons-destruct))
                               :in-theory (e/d (logcons)
                                               (bitops::logcons-destruct
                                                acl2::logcar-logcdr-elim))))
                      :rule-classes :linear)))
  (if (zp n)
      (mv rest-upper rest-lower)
    (b* (((4vec x1) (car x))
         (n (1- n))
         (x (cdr x))
         (halfn (ash n -1))
         (restn (- n halfn))
         ((mv rest-upper rest-lower) (4veclist-separate-upper-lower-rec-log
                                      restn (nthcdr halfn x) rest-upper rest-lower))
         ((mv rest-upper rest-lower) (4veclist-separate-upper-lower-rec-log
                                      halfn x rest-upper rest-lower)))
      (mv (cons x1.upper rest-upper)
          (cons x1.lower rest-lower))))
  ///
  (verify-guards 4veclist-separate-upper-lower-rec-log
    :hints(("Goal" :in-theory (enable bitops::logtail** len)))))


(define 4veclist-separate-upper-lower ((x 4veclist-p))
  :returns (mv (uppers integer-listp)
               (lowers integer-listp))
  (if (atom x)
      (mv nil nil)
    (b* (((mv rest-up rest-low) (4veclist-separate-upper-lower (cdr x)))
         ((4vec x1) (car X)))
      (mv (cons x1.upper rest-up)
          (cons x1.lower rest-low))))

  ///
  (local (in-theory (enable bitops::logtail**)))
  (local (defthm logcar-plus-logcdr
           (implies (natp x)
                    (<= (+ (logcar x) (logcdr x)) x))
           :hints (("goal" :use ((:instance bitops::logcons-destruct))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct
                                     acl2::logcar-logcdr-elim))))
           :rule-classes :linear))
  (local (defthm logcar-plus-logcdr-gte-1
           (implies (posp x)
                    (<= 1 (+ (logcar x) (logcdr x))))
           :hints (("goal" :use ((:instance bitops::logcons-destruct))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct
                                     acl2::logcar-logcdr-elim))))
           :rule-classes :linear))
  (local (defthm append-take-nthcdr
           (equal (append (take n x) (take m (nthcdr n x)))
                  (take (+ (nfix n) (nfix m)) x))
           :hints(("Goal" :in-theory (enable take nthcdr)
                   :induct (take m (nthcdr n x))))))
  (local (defthm cdr-of-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr n (cdr x)))))
  (local (in-theory (disable acl2::cdr-nthcdr)))

  (local (defthm append-take-nthcdr-2
           (equal (append (take n x) (take m (nthcdr n x)) y)
                  (append (take (+ (nfix n) (nfix m)) x) y))
           :hints (("goal" :use ((:instance ACL2::ASSOCIATIVITY-OF-APPEND
                                  (a (take n x)) (b (take m (nthcdr n x))) (c y)))
                    :in-theory (disable acl2::associativity-of-append)))))

  (local (in-theory (disable acl2::nthcdr-of-cdr)))

  (local (defthm equal-list
           (equal (equal x (list y z))
                  (and (true-listp x)
                       (Equal (len x) 2)
                       (equal (mv-nth 0 x) y)
                       (equal (mv-nth 1 x) z)))
           :hints(("Goal" :in-theory (enable mv-nth len)))))

  (local (defthm 4veclist-separate-upper-lower-append-take
           (b* (((mv upper1 lower1) (4veclist-separate-upper-lower (take n x)))
                ((mv upper2 lower2) (4veclist-separate-upper-lower (take m (nthcdr n x))))
                ((mv upper lower) (4veclist-separate-upper-lower (take (+ (nfix n) (nfix m)) x))))
             (and (equal (append upper1 upper2 rest)
                         (append upper rest))
                  (equal (append lower1 lower2 rest)
                         (append lower rest))))))
  
  (defthm 4veclist-separate-upper-lower-rec-log-elim
    (equal (4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)
           (b* (((mv uppers lowers) (4veclist-separate-upper-lower (take n x))))
             (mv (append uppers rest-upper)
                 (append lowers rest-lower))))
    :hints(("Goal" :in-theory (enable (:i 4veclist-separate-upper-lower-rec-log))
            :induct (4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)
            :expand ((4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)))))

  (fgl::def-fgl-rewrite 4veclist-separate-upper-lower-fgl
    (equal (4veclist-separate-upper-lower x)
           (4veclist-separate-upper-lower-rec-log (len x) x nil nil)))
)







(define hons-aig-accumulate-nodes (x acc)
  (b* (((when (atom x))
        (if (or (booleanp x)
                (hons-get x acc))
            acc
          (hons-acons x t acc)))
       ((when (eq (cdr x) nil))
        (hons-aig-accumulate-nodes (car x) acc))
       ((when (hons-get x acc)) acc)
       (acc (hons-acons x t acc))
       (acc (hons-aig-accumulate-nodes (car x) acc)))
    (hons-aig-accumulate-nodes (cdr x) acc)))

(define hons-aiglist-accumulate-nodes (x acc)
  (if (atom x)
      acc
    (hons-aiglist-accumulate-nodes
     (cdr x) (hons-aig-accumulate-nodes (car x) acc))))

(define a4vec-accumulate-nodes ((x a4vec-p) acc)
  (b* (((a4vec x)))
    (hons-aiglist-accumulate-nodes x.upper (hons-aiglist-accumulate-nodes x.lower acc))))

 (define a4veclist-accumulate-nodes ((x a4veclist-p) acc)
  (if (atom x)
      acc
    (a4veclist-accumulate-nodes (cdr x) (a4vec-accumulate-nodes (car x) acc))))


(define a4veclist-subnodes ((x a4veclist-p))
  (b* ((acc (a4veclist-accumulate-nodes x nil)))
    (fast-alist-free acc)
    (alist-keys acc)))


(define a4veclist-accumulate-upper-nodes ((x a4veclist-p) acc)
  (if (atom x)
      acc
    (a4veclist-accumulate-nodes (cdr x)
                                (hons-aiglist-accumulate-nodes (a4vec->upper (car x))
                                                               acc))))


(define a4veclist-upper-subnodes ((x a4veclist-p))
  (b* ((acc (a4veclist-accumulate-upper-nodes x nil)))
    (fast-alist-free acc)
    (alist-keys acc)))



(define 4veclist->upper-4vecs ((x 4veclist-p))
  :returns (new-x 4veclist-p)
  (if (Atom x)
      nil
    (cons (2vec (4vec->upper (car x)))
          (4veclist->upper-4vecs (cdr x))))
  ///
  (defret 4veclist->upper-4vecs-when-integer-listp
    (implies (integer-listp x)
             (equal (4veclist->upper-4vecs x) x))
    :hints(("Goal" :in-theory (enable 4vec->upper 2vec 4vec)))))

(define a4veclist->upper-a4vecs-acc ((x a4veclist-p) (acc true-listp))
  (if (atom x)
      (reverse (llist-fix acc))
    (a4veclist->upper-a4vecs-acc (cdr x)
                                 (cons (b* ((upper (a4vec->upper (car x))))
                                         (a4vec upper upper))
                                       acc))))

(define a4veclist->upper-a4vecs ((x a4veclist-p))
  :returns (new-x a4veclist-p)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  nil
                (cons (b* ((upper (a4vec->upper (car x))))
                        (a4vec upper upper))
                      (a4veclist->upper-a4vecs (cdr x))))
       :exec (a4veclist->upper-a4vecs-acc x nil))
  ///
  (local (defthm a4veclist->upper-a4vecs-acc-elim
           (equal (a4veclist->upper-a4vecs-acc x acc)
                  (revappend acc (a4veclist->upper-a4vecs x)))
           :hints(("Goal" :in-theory (enable a4veclist->upper-a4vecs-acc)))))

  (verify-guards a4veclist->upper-a4vecs)

  (defret eval-of-<fn>
    (equal (a4veclist-eval new-x env)
           (4veclist->upper-4vecs (a4veclist-eval x env)))
    :hints(("Goal" :in-theory (enable a4veclist-eval
                                      4veclist->upper-4vecs)))))


(defsection svex-mask-env-common-constants
  :parents (svex-focused-equivalence-checking)
  :short "FGL binder to find common constants (under a set of masks)
in two symbolic SVEX environments."
  (define svex-mask-env-common-constants ((ans svex-env-p)
                                          (masks svex-mask-alist-p)
                                          (env1 svex-env-p)
                                          (env2 svex-env-p))
    :returns (const-env)
    :hooks ((:fix :omit (masks)))
    (let ((ans (svex-env-fix ans)))
      (if (and (ec-call (svex-envs-agree-on-masks masks (append ans env1) env1))
               (ec-call (svex-envs-agree-on-masks masks (append ans env2) env2)))
          ans
        nil))
    ///
    (defret svex-env-common-constants-correct
      (and (svex-envs-agree-on-masks masks (append const-env env1) env1)
           (svex-envs-agree-on-masks masks (append const-env env2) env2)))

    (local
     (defthm svex-envs-agree-on-masks-implies-svexlist-eval
       (implies (svex-envs-agree-on-masks
                 (mv-nth 0 (svexlist-mask-alist/toposort x))
                 env1 env2)
                (equal (equal (svexlist-eval x env1)
                              (svexlist-eval x env2))
                       t))
       :hints (("goal" :use ((:instance
                              svex-envs-agree-on-masks-implies-svexlist-eval-when-svex-mask-alist-complete
                              (masks (mv-nth 0 (svexlist-mask-alist/toposort x)))))
                :in-theory (disable svex-envs-agree-on-masks-implies-svexlist-eval-when-svex-mask-alist-complete)))))

    (defret svexlist-eval-of-svex-mask-env-common-constants
      :pre-bind ((masks (svexlist-mask-alist x)))
      (and
       (equal (svexlist-eval x (append const-env env1))
              (svexlist-eval x env1))
       (equal (svexlist-eval x (append const-env env2))
              (svexlist-eval x env2)))))


  (define svex-envs-common-constants-aux ((keys svarlist-p)
                                          (masks svex-mask-alist-p)
                                          (env1 svex-env-p)
                                          (env2 svex-env-p)
                                          (acc svex-env-p))
    :returns (new-env svex-env-p)
    (b* (((when (atom keys)) (svex-env-fix acc))
         (key (car keys))
         (mask (svex-mask-lookup (svex-var key) masks))
         ((when (equal mask 0))
          (svex-envs-common-constants-aux (cdr keys) masks env1 env2 acc))
         (boundp1 (svex-env-boundp key env1))
         ((unless boundp1)
          (svex-envs-common-constants-aux (cdr keys) masks env1 env2 acc))
         (boundp2 (svex-env-boundp key env2))
         ((unless boundp2)
          (svex-envs-common-constants-aux (cdr keys) masks env1 env2 acc))
         (val1 (4vec-mask mask (svex-env-lookup key env1)))
         (val2 (4vec-mask mask (svex-env-lookup key env2)))
         (acc (if (equal val1 val2)
                  (hons-acons (svar-fix key) val1 acc)
                acc)))
      (svex-envs-common-constants-aux
       (cdr keys) masks env1 env2 acc))
    ///
    (defret svex-env-lookup-of-<fn>
      (equal (svex-env-lookup key new-env)
             (if (member-equal (svar-fix key) (svarlist-fix keys))
                 (b* ((mask (svex-mask-lookup (svex-var key) masks))
                      (val1 (4vec-mask mask (svex-env-lookup key env1)))
                      (val2 (4vec-mask mask (svex-env-lookup key env2))))
                   (if (and (svex-env-boundp key env1)
                            (svex-env-boundp key env2)
                            (not (equal 0 mask))
                            (equal val1 val2))
                       val1
                     (svex-env-lookup key acc)))
               (svex-env-lookup key acc)))
      :hints(("Goal" :induct <call>
              :in-theory (enable svex-env-lookup)
              :expand (<call>
                       (svarlist-fix keys)))))

    (defret svex-env-boundp-of-<fn>
      (equal (svex-env-boundp key new-env)
             (if (member-equal (svar-fix key) (svarlist-fix keys))
                 (b* ((mask (svex-mask-lookup (svex-var key) masks))
                      (val1 (4vec-mask mask (svex-env-lookup key env1)))
                      (val2 (4vec-mask mask (svex-env-lookup key env2))))
                   (or (and (svex-env-boundp key env1)
                            (svex-env-boundp key env2)
                            (not (equal 0 mask))
                            (equal val1 val2))
                       (svex-env-boundp key acc)))
               (svex-env-boundp key acc)))
      :hints(("Goal" :induct <call>
              :in-theory (enable svex-env-boundp
                                 svex-env-lookup)
              :expand (<call>
                       (svarlist-fix keys))))))

  (local (in-theory (disable acl2::hons-union)))

  (local (include-book "centaur/misc/hons-sets" :dir :system))

  (local (defthmd svarlist-p-set-equiv
           (implies (and (set-equiv y (double-rewrite x))
                         (svarlist-p y)
                         (true-listp x))
                    (svarlist-p x))
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (local (defthm svarlist-p-alist-keys-of-svex-env
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm true-listp-hons-union2
           (implies (true-listp acc)
                    (true-listp (acl2::hons-union2 x y acc)))))

  (local (defthm true-listp-hons-union1
           (implies (true-listp acc)
                    (true-listp (acl2::hons-union1 x y acc)))))

  (local (defthm true-listp-hons-union
           (implies (and (true-listp x)
                         (true-listp y))
                    (true-listp (acl2::hons-union x y)))
           :hints(("Goal" :in-theory (e/d (acl2::hons-union)
                                          (acl2::hons-union1
                                           acl2::hons-union2))))))

  (define svex-envs-common-constants ((masks svex-mask-alist-p)
                                      (env1 svex-env-p)
                                      (env2 svex-env-p))
    :returns (consts svex-env-p)
    :guard-hints (("goal" :in-theory (enable svarlist-p-set-equiv)))
    (svex-envs-common-constants-aux (acl2::hons-union (alist-keys (svex-env-fix env1))
                                                      (alist-keys (svex-env-fix env2)))
                                    masks env1 env2 nil)
    ///
    (defret not-boundp-of-<fn>
      (implies (or (not (svex-env-boundp v env1))
                   (not (svex-env-boundp v env2)))
               (not (svex-env-boundp v consts))))
  
    (defretd lookup-when-boundp-of-<fn>-equals-env1
      (implies (svex-env-boundp v consts)
               (equal (svex-env-lookup v consts)
                      (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                 (svex-env-lookup v env1)))))
    (defretd lookup-when-boundp-of-<fn>-equals-env2
      (implies (svex-env-boundp v consts)
               (equal (svex-env-lookup v consts)
                      (4vec-mask (svex-mask-lookup (svex-var v) masks)
                                 (svex-env-lookup v env2))))))

  (encapsulate nil
    (local (defthm svex-env-boundp-of-alist-const-pairs
             (implies (not (svex-env-boundp v x))
                      (not (svex-env-boundp v (fgl::alist-const-pairs ans x))))
             :hints(("Goal" :in-theory (enable svex-env-boundp
                                               fgl::alist-const-pairs)
                     :use ((:instance acl2::sub-alistp-hons-assoc-equal
                            (x (svar-fix v)) (a ans) (b x)))))))

    (local (defthm svex-env-lookup-of-alist-const-pairs
             (implies (case-split (svex-env-boundp v (fgl::alist-const-pairs ans x)))
                      (equal (svex-env-lookup v (fgl::alist-const-pairs ans x))
                             (svex-env-lookup v x)))
             :hints(("Goal" :in-theory (enable svex-env-boundp
                                               svex-env-lookup
                                               fgl::alist-const-pairs)
                     :use ((:instance acl2::sub-alistp-hons-assoc-equal
                            (x (svar-fix v)) (a ans) (b x)))))))
  
    (local
     (defthm svex-envs-common-constants-agree-on-masks-env1
       (SVEX-ENVS-AGREE-ON-MASKS
        MASKS
        (APPEND
         (SVEX-ENVS-COMMON-CONSTANTS MASKS
                                     (FGL::ALIST-CONST-PAIRS ENV1-CONSTS ENV1)
                                     (FGL::ALIST-CONST-PAIRS ENV2-CONSTS ENV2))
         ENV1)
        ENV1)
       :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks
                                         lookup-when-boundp-of-svex-envs-common-constants-equals-env1
                                         svex-env-lookup-when-not-boundp)))))

    (local
     (defthm svex-envs-common-constants-agree-on-masks-env2
       (SVEX-ENVS-AGREE-ON-MASKS
        MASKS
        (APPEND
         (SVEX-ENVS-COMMON-CONSTANTS MASKS
                                     (FGL::ALIST-CONST-PAIRS ENV1-CONSTS ENV1)
                                     (FGL::ALIST-CONST-PAIRS ENV2-CONSTS ENV2))
         ENV2)
        ENV2)
       :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks
                                         lookup-when-boundp-of-svex-envs-common-constants-equals-env2
                                         svex-env-lookup-when-not-boundp)))))
    
    (fgl::def-fgl-brewrite svex-mask-env-common-constants-binder-rule
      (implies (equal ans (b* ((env1-consts (fgl::alist-const-pairs env1-consts env1))
                               (env2-consts (fgl::alist-const-pairs env2-consts env2)))
                            (svex-envs-common-constants masks env1-consts env2-consts)))
               (equal (svex-mask-env-common-constants ans masks env1 env2)
                      ans))
      :hints(("Goal" :in-theory (enable svex-mask-env-common-constants))))))

(define my-binary-append ((x true-listp) y)
  :enabled t
  (mbe :logic (binary-append x y)
       :exec (if (eq y nil)
                 x
               (binary-append x y)))
  ///
  (defmacro my-append (&rest rst)
    (cond ((null rst) nil)
          ((null (cdr rst)) (car rst))
          (t (xxxjoin 'my-binary-append rst)))))

(define eval-collection-of-a4vecs-and-aigs
  ((a4vecs1 a4veclist-p)
   (a4vecs2 a4veclist-p)
   (aigs1 true-listp)
   (aigs2 true-listp)
   (aigs3 true-listp)
   (env))
  :returns (mv (a4vecs1-eval 4veclist-p)
               (a4vecs2-eval 4veclist-p)
               (aigs1-eval true-listp)
               (aigs2-eval true-listp)
               (aigs3-eval true-listp))
  (b* ((a4vecs1-aiglist (sv::a4veclist->aiglist a4vecs1))
       (a4vecs2-aiglist (sv::a4veclist->aiglist a4vecs2))
       (all-aigs (my-append a4vecs1-aiglist a4vecs2-aiglist aigs1 aigs2 aigs3))
       (bitlist (time$ (acl2::aig-eval-list all-aigs env)
                       :msg "; SV bit-blasting: aig-eval-list: ~st sec, ~sa bytes.~%"))
       (a4vecs1-len (length a4vecs1-aiglist))
       (a4vecs2-len (length a4vecs2-aiglist))
       (aigs1-len (len aigs1))
       (aigs2-len (len aigs2))

       ;; 4veclist-from-bitlist doesn't care about extra bits so we don't need to use take here
       (a4vecs1-eval (time$ (sv::4veclist-from-bitlist a4vecs1 bitlist)
                            :msg "; bits->4vecs: ~st sec, ~sa bytes.~%"))
       (bitlist-tail (nthcdr a4vecs1-len bitlist))
       (a4vecs2-eval (time$ (sv::4veclist-from-bitlist a4vecs2 bitlist-tail)
                            :msg "; bits->4vecs: ~st sec, ~sa bytes.~%"))
       (bitlist-tail (nthcdr a4vecs2-len bitlist-tail))
       (aigs1-eval (take aigs1-len bitlist-tail))
       (bitlist-tail (nthcdr aigs1-len bitlist-tail))
       (aigs2-eval (take aigs2-len bitlist-tail))
       (aigs3-eval (nthcdr aigs2-len bitlist-tail)))
    (mv a4vecs1-eval a4vecs2-eval aigs1-eval aigs2-eval aigs3-eval))
  ///
  (local (include-book "std/lists/nthcdr" :dir :system))
  (local (include-book "std/lists/take" :dir :system))

  (local (defthm take-of-nthcdr
           (equal (take n (nthcdr m x))
                  (nthcdr m (take (+ (nfix n) (nfix m)) x)))
           :hints(("Goal" :in-theory (e/d (take nthcdr)
                                          ())))))

  (local (defthm nthcdr-less-than-first-len-of-append
           (implies (<= (nfix n) (len a))
                    (equal (nthcdr n (append a b))
                           (append (nthcdr n a) b)))))
  (local (defthm 4vec-from-bitlist-of-append
           (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
                    (Equal (4vec-from-bitlist upper-len lower-len (append a b))
                           (b* (((mv 4vec rest)
                                 (4vec-from-bitlist upper-len lower-len a)))
                             (mv 4vec (append rest b)))))
           :hints(("Goal" :in-theory (enable 4vec-from-bitlist)
                   :do-not-induct t)
                  (and stable-under-simplificationp
                       '(:cases ((natp upper-len)))))))

  (local (defthm len-of-4vec-from-bitlist-rest
           (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
                    (equal (len (mv-nth 1 (4vec-from-bitlist upper-len lower-len a)))
                           (- (len a) (+ (nfix upper-len) (nfix lower-len)))))
           :hints(("Goal" :in-theory (enable 4vec-from-bitlist)))))
  
  (local (defthm 4veclist-from-bitlist-of-append
           (implies (<= (len (a4veclist->aiglist x)) (len a))
                    (equal (4veclist-from-bitlist x (append a b))
                           (4veclist-from-bitlist x a)))
           :hints(("Goal" :in-theory (enable 4veclist-from-bitlist a4veclist->aiglist
                                             a4vec->aiglist)))))
  
  (defret <fn>-correct
    (and (equal a4vecs1-eval (a4veclist-eval a4vecs1 env))
         (equal a4vecs2-eval (a4veclist-eval a4vecs2 env))
         (equal aigs1-eval (acl2::aig-eval-list aigs1 env))
         (equal aigs2-eval (acl2::aig-eval-list aigs2 env))
         (equal aigs3-eval (acl2::aig-eval-list aigs3 env)))))


;; (define eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
;;   ((x-a4vecs a4veclist-p)
;;    (hint-a4vecs a4veclist-p)
;;    (subnodes)
;;    (env))
;;   :returns (mv (x-eval 4veclist-p)
;;                (hint-eval 4veclist-p)
;;                (subnodes-eval boolean-listp))
;;   (b* ((x-aiglist (sv::a4veclist->aiglist x-a4vecs))
;;        (hint-aiglist (sv::a4veclist->aiglist hint-a4vecs))
;;        (all-aigs (append x-aiglist hint-aiglist subnodes))
;;        (bitlist (time$ (acl2::aig-eval-list all-aigs env)
;;                        :msg "; SV bit-blasting: aig-eval-list: ~st sec, ~sa bytes.~%"))
;;        (x-aig-len (length x-aiglist))
;;        (hint-aig-len (length hint-aiglist))
;;        ;; 4veclist-from-bitlist doesn't care about extra bits so we don't need to use take.
;;        (hint-bitlist (nthcdr x-aig-len bitlist))
;;        (subnodes-bitlist (nthcdr hint-aig-len hint-bitlist)))
;;     (mv (time$ (sv::4veclist-from-bitlist x-a4vecs bitlist) :msg "; bits->4vecs: ~st sec, ~sa bytes.~%")
;;         (time$ (sv::4veclist-from-bitlist hint-a4vecs hint-bitlist) :msg "; bits->4vecs: ~st sec, ~sa bytes.~%")
;;         subnodes-bitlist))
;;   ///
;;   (local (include-book "std/lists/nthcdr" :dir :system))
;;   (local (include-book "std/lists/take" :dir :system))

;;   (local (defthm take-of-nthcdr
;;            (equal (take n (nthcdr m x))
;;                   (nthcdr m (take (+ (nfix n) (nfix m)) x)))
;;            :hints(("Goal" :in-theory (e/d (take nthcdr)
;;                                           ())))))

;;   (local (defthm nthcdr-less-than-first-len-of-append
;;            (implies (<= (nfix n) (len a))
;;                     (equal (nthcdr n (append a b))
;;                            (append (nthcdr n a) b)))))
;;   (local (defthm 4vec-from-bitlist-of-append
;;            (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
;;                     (Equal (4vec-from-bitlist upper-len lower-len (append a b))
;;                            (b* (((mv 4vec rest)
;;                                  (4vec-from-bitlist upper-len lower-len a)))
;;                              (mv 4vec (append rest b)))))
;;            :hints(("Goal" :in-theory (enable 4vec-from-bitlist)
;;                    :do-not-induct t)
;;                   (and stable-under-simplificationp
;;                        '(:cases ((natp upper-len)))))))

;;   (local (defthm len-of-4vec-from-bitlist-rest
;;            (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
;;                     (equal (len (mv-nth 1 (4vec-from-bitlist upper-len lower-len a)))
;;                            (- (len a) (+ (nfix upper-len) (nfix lower-len)))))
;;            :hints(("Goal" :in-theory (enable 4vec-from-bitlist)))))
  
;;   (local (defthm 4veclist-from-bitlist-of-append
;;            (implies (<= (len (a4veclist->aiglist x)) (len a))
;;                     (equal (4veclist-from-bitlist x (append a b))
;;                            (4veclist-from-bitlist x a)))
;;            :hints(("Goal" :in-theory (enable 4veclist-from-bitlist a4veclist->aiglist
;;                                              a4vec->aiglist)))))
  
;;   (defret <fn>-correct
;;     (and (equal x-eval (a4veclist-eval x-a4vecs env))
;;          (equal hint-eval (a4veclist-eval hint-a4vecs env))
;;          (equal subnodes-eval (acl2::aig-eval-list subnodes env)))))


(define a4veclist-separate-upper-lower-aux ((x a4veclist-p)
                                            (uppers true-listp)
                                            (lowers true-listp))
  :returns (mv (ups true-listp :rule-classes :type-prescription)
               (lows true-listp :rule-classes :type-prescription))
  (if (atom x)
      (mbe :logic (mv (acl2::true-list-fix uppers)
                      (acl2::true-list-fix lowers))
           :exec (mv uppers lowers))
    (b* (((a4vec x1) (car x))
         (up-len (len x1.upper))
         (low-len (len x1.lower))
         ((mv up low)
          (cond ((eql up-len low-len) (mv x1.upper x1.lower))
                ((< up-len low-len) (mv (append x1.upper
                                                (repeat (- low-len up-len)
                                                        (car (last x1.upper))))
                                        x1.lower))
                (t                  (mv x1.upper
                                        (append x1.lower
                                                (repeat (- up-len low-len)
                                                        (car (last x1.lower)))))))))
      (a4veclist-separate-upper-lower-aux (cdr x)
                                          (append up uppers)
                                          (append low lowers)))))
      
  
(define a4veclist-separate-upper-lower ((x a4veclist-p))
  :returns (mv (ups true-listp :rule-classes :type-prescription)
               (lows true-listp :rule-classes :type-prescription))
  (a4veclist-separate-upper-lower-aux x nil nil))





(define svexlist-evals-equal-with-transforms ((x svexlist-p)
                                              (env1 svex-env-p)
                                              (env2 svex-env-p)
                                              (symbolic-params alistp)
                                              (transforms))
  (declare (ignorable symbolic-params transforms))
  (svexlist-evals-equal x env1 env2)
  ///


  
  (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl
    (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))

                (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                                :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                                  :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                                :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                                  :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal (equal x-eval1 x-eval2))
                ((mv iso-ok hint-eval1 hint-eval2) (fgl::fgl-make-isomorphic iso-ok hint-eval1 hint-eval2))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal transforms
                                        :tracked-obj
                                        (cons hint-eval1 hint-eval2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct)))))

  (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl-less-extreme
    (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                ((mv masks ?toposort)
                 (svexlist-mask-alist/toposort-memo x))
                (const-env
                 (time$ (svex-mask-env-common-constants const-env masks env1 env2)))
                (x (time$
                         (svexlist-compose-rw x
                                              (make-svex-substconfig
                                               :alist (make-fast-alist
                                                       (svex-env-to-subst const-env))
                                               :simp 10))))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))

                ((mv err x-a4vecs subexp-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))
                ;; (x-upper-a4vecs (a4veclist->upper-a4vecs x-a4vecs))
                ((mv x-eval1 sub-eval1 & & &)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs subexp-a4vecs nil nil nil aig-env1))
                ((mv x-eval2 sub-eval2 & & &)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs subexp-a4vecs nil nil nil aig-env2 ))
                ;; (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                ;;                 :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                ;;                   :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                ;; (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                ;;                 :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                ;;                   :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal (equal x-eval1 x-eval2))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.  
                (sub-eval1 (acl2::list-to-tree sub-eval1))
                (sub-eval2 (acl2::list-to-tree sub-eval2))
                ((mv iso-ok hint-iso1 hint-iso2) (time$ (fgl::fgl-make-isomorphic iso-ok sub-eval1 sub-eval2)))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct)))))
  

  (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl-extreme
    (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                ((mv masks ?toposort)
                 (svexlist-mask-alist/toposort-memo x))
                (const-env
                 (time$ (svex-mask-env-common-constants const-env masks env1 env2)))
                (x (time$
                         (svexlist-compose-rw x
                                              (make-svex-substconfig
                                               :alist (make-fast-alist
                                                       (svex-env-to-subst const-env))
                                               :simp 10))))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))

                ((mv err x-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))
                (aigs (a4veclist-subnodes x-a4vecs))
                ;; (x-upper-a4vecs (a4veclist->upper-a4vecs x-a4vecs))
                ((mv x-eval1 & & & aigs-eval1)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs nil nil nil aigs aig-env1))
                ((mv x-eval2 & & & aigs-eval2)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs nil nil nil aigs aig-env2 ))
                ;; (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                ;;                 :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                ;;                   :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                ;; (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                ;;                 :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                ;;                   :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal (equal x-eval1 x-eval2))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.  
                (aigs-eval1 (acl2::list-to-tree aigs-eval1))
                (aigs-eval2 (acl2::list-to-tree aigs-eval2))
                ((mv iso-ok hint-iso1 hint-iso2) (time$ (fgl::fgl-make-isomorphic iso-ok aigs-eval1 aigs-eval2)))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))


(define svexlist-evals-equal-and-integerp-with-transforms ((x svexlist-p)
                                                           (env1 svex-env-p)
                                                           (env2 svex-env-p)
                                                           (symbolic-params alistp)
                                                           (transforms))
  (declare (ignorable symbolic-params transforms))
  (and (svexlist-evals-equal x env1 env2)
       (integer-listp (svexlist-eval x env1)))
  ///




  (fgl::def-fgl-rewrite svexlist-evals-equal-and-integerp-with-transforms-fgl
    (equal (svexlist-evals-equal-and-integerp-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))
                ((mv upper-aigs lower-aigs) (a4veclist-separate-upper-lower hint-a4vecs))
                (subnodes (a4veclist-upper-subnodes x-a4vecs))
                ;; (x-upper-a4vecs (a4veclist->upper-a4vecs x-a4vecs))
                ((mv x-eval1 & upper-eval1 lower-eval1 subnodes-eval1)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs nil upper-aigs lower-aigs subnodes aig-env1))
                ((mv x-eval2 & upper-eval2 lower-eval2 subnodes-eval2)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs nil upper-aigs lower-aigs subnodes aig-env2))
                (evals-equal-and-integerp (and (equal x-eval1 x-eval2) (integer-listp x-eval1)))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.  
                (hint1 (list (time$ (acl2::list-to-tree upper-eval1))
                             (time$ (acl2::list-to-tree upper-eval2))
                             (time$ (acl2::list-to-tree subnodes-eval1))))
                (hint2 (list (time$ (acl2::list-to-tree lower-eval1))
                             (time$ (acl2::list-to-tree lower-eval2))
                             (time$ (acl2::list-to-tree subnodes-eval2))))
                ((mv iso-ok hint-iso1 hint-iso2) (time$ (fgl::fgl-make-isomorphic iso-ok hint1 hint2)))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal-and-integerp transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))




(define svexlist-eval-integer-listp-with-transforms ((x svexlist-p)
                                                      (env svex-env-p)
                                                      (symbolic-params alistp)
                                                      (transforms))
  (declare (ignorable symbolic-params transforms))
  (integer-listp (svexlist-eval x env))
  ///


  
  (fgl::def-fgl-rewrite svexlist-eval-integer-listp-with-transforms-fgl
    (equal (svexlist-eval-integer-listp-with-transforms x env symbolic-params transforms)
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
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))

                ((mv ?err aig-env)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env (make-fast-alist aig-env))

                (?ign (fast-alist-free env))

                (x-eval (time$ (a4veclist-eval x-a4vecs aig-env)
                                :msg "; a4veclist-eval x: ~st sec, ~sa bytes.~%"))
                (hint-eval (time$ (a4veclist-eval hint-a4vecs aig-env)
                                  :msg "; a4veclist-eval sub: ~st sec, ~sa bytes.~%"))
                ;; (?ign (fgl::fgl-prog2 (fgl::syntax-interp (prog2$ (cw "x-eval: ~x0~%" x-eval)
                ;;                                 (cw "hint-eval: ~x0~%" hint-eval)))
                ;;                  nil))
                (evals-integer-listp (integer-listp x-eval))
                ((mv hint-upper hint-lower) (4veclist-separate-upper-lower hint-eval))
                ((mv iso-ok hint-upper hint-lower) (fgl::fgl-make-isomorphic iso-ok hint-upper hint-lower))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-upper)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-lower)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-integer-listp transforms
                                        :tracked-obj
                                        (cons hint-upper hint-lower))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct)))))

  (fgl::def-fgl-rewrite svexlist-eval-integer-listp-with-transforms-fgl-extreme-2
    (equal (svexlist-eval-integer-listp-with-transforms x env symbolic-params transforms)
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
         
                ((unless (and (svex-env-check-boolmasks boolmasks env)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (integer-listp (svexlist-eval orig-x env))))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (integer-listp (svexlist-eval orig-x env))))))

                ((mv ?err aig-env)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env (make-fast-alist aig-env))

                (?ign (fast-alist-free env))
                ((mv upper-aigs lower-aigs) (a4veclist-separate-upper-lower (append hint-a4vecs)))
                ;; (x-upper-a4vecs (a4veclist->upper-a4vecs x-a4vecs))
                ((mv x-eval & &  upper-eval lower-eval)
                 (eval-collection-of-a4vecs-and-aigs
                  x-a4vecs nil nil  upper-aigs lower-aigs aig-env))
                ;; (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                ;;                 :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                ;;                   :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                ;; (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                ;;                 :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                ;;                   :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (integer-listp (integer-listp x-eval))
                ((mv iso-ok upper-eval lower-eval) (time$ (fgl::fgl-make-isomorphic iso-ok upper-eval lower-eval)))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (integer-listp (svexlist-eval orig-x env))))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist upper-eval)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist lower-eval)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (integer-listp (svexlist-eval orig-x env))))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered integer-listp transforms
                                        :tracked-obj
                                        (cons upper-eval lower-eval))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))
