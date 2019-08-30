; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")
(include-book "semantics")
(include-book "lit-lists")
(include-book "refcounts")
(include-book "centaur/satlink/cnf" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(local (std::add-default-post-define-hook :fix))

;; ;; BOZO skipping node-list-fix congruence proofs here
;; (local (table fty::fixtypes 'fty::fixtype-alist
;;               (b* ((fixtype-alist (cdr (assoc 'fty::fixtype-alist (table-alist 'fty::fixtypes world)))))
;;                 (remove-equal (assoc 'aignet fixtype-alist)
;;                               fixtype-alist))))

(defxdoc aignet-cnf
  :parents (aignet)
  :short "Discussion of CNF generation for aignets."
  :long "
<p>Generating CNF from a circuit representation is pretty simple to write, but
the correctness conditions are tricky to state.</p>

<p>Basically, we want to show that a SAT proof corresponds to a proof about the
AIG, and a SAT counterexample corresponds to a counterexample in the AIG.</p>

<p>Taking the proof case first.  We want to show that if the CNF is
unsatisfiable, then -- what?  Well, the CNF we produce from just the circuit
will always be satisfiable: in fact, this is the first thing we'll prove --

<blockquote>Every assignment of values to the CIs of the AIG can be translated
to a satisfying assignment of the generated CNF by setting, for every circuit
node that is assigned a SAT variable, the evaluation of the node to be the
value of the variable.</blockquote>

It's when we add additional constraints to the CNF that it may become
unsatisfiable.  So suppose we want to show that some cube among the nodes of
the circuit is unsat -- say, @('A & B & ~C').  We first convert their
subcircuits to CNF and then add the three singleton clauses.  Now, suppose that
we have some assignment to the CIs that satisfies @('A & B & ~C').  That
induces a satisfying assignment for the generated part of the CNF where (in
particular) the literals corresponding to A, B, and ~C are assigned true.  That
makes the three singleton clauses also true, so the whole CNF is satisfied.
Therefore, if we prove the CNF unsatisfiable, then we've proven that no
assignment to the CIs can simultaneously satisfy @('A & B & ~C').</p>

<p>Now the counterexample case.  We want to show that any satisfying assignment
of the CNF is a satisfying assignment for whatever circuit constraints we've
added to it.  Basically, this amounts to:

<blockquote>Every satisfying assignment to the generated CNF induces an
assignment to the CIs of the circuit, under which, for every circuit node
assigned a SAT variable, the value of the SAT literal is the same as the
evaluation of the circuit node.</blockquote>

Of course, this theorem is less critical to correctness -- if we get a SAT
counterexample, it can easily be verified on the circuit.  Still, we'd like to
prove it to show that our CNF generation is correct.</p>

<p>To summarize, we need to show:<br/>
<blockquote>An evaluation of the circuit induces a satisfying assignment, and a
satisfying assignment induces an evaluation of the circuit, in which the
evaluations of circuit nodes that are assigned SAT literals is the same as the
values of those literals under the satisfying assignment.</blockquote></p>

<p>To formalize this, we'll define:
<ul>
<li>a predicate @('aignet-vals-agree-with-cnf') which compares a satisfying
assignment to an aignet evaluation to determine whether all values agree as
specified above,</li>
<li>a function @('cnf->aignet-vals') that transforms a satisfying assignment into
a vals object.  We'll show that the input and output satisfy
<tt>cnf/aignet-evals-agree</tt> if the assignment satisfies the generated
CNF.</li>
<li>a function @('aignet->cnf-vals') that creates a CNF variable assignment from a
vals object.  We'll show that this satisfies
<tt>cnf/aignet-evals-agree</tt> and that the CNF assignment
satisfies the generated CNF.</li>
</ul></p>

<p>When actually converting an aignet to CNF, we of course process the AIG
recursively.  We do this in chunks, where each chunk is either:
<ul>
<li>a <i>supergate</i>, representing a single large AND or OR gate, or</li>
<li>a mux.</li>
</ul>
For both of these cases, we prove that the chunk we've just added preserves the
correctness criterion we've described.</p>

")

;; (local (defun trivial-worse-than-or-equal (term1 term2)
;;          (declare (xargs :guard t)
;;                   (ignorable term1 term2))
;;          nil))

;; (local (defattach acl2::worse-than-or-equal trivial-worse-than-or-equal))

(local (in-theory (disable acl2::nth-with-large-index
                           nth update-nth
                           set::double-containment)))

(local (defthmd equal-1-by-bitp
         (implies (acl2::bitp x)
                  (equal (equal x 1) (not (equal x 0))))
         :hints(("Goal" :in-theory (enable acl2::bitp)))))


;; Utilities for recognizing muxes and XORs.

(local (in-theory (disable lookup-id-in-bounds-when-positive
                           ;; lookup-id-out-of-bounds
                           satlink::equal-of-lit-negate-backchain
                           satlink::lit-negate-not-equal-when-vars-mismatch
                           )))

;; Returns (mv is-mux cond-lit tb-lit fb-lit).
;; A mux node is of the form
;; (and (not (and c (not tb))) (not (and (not c) (not fb))))
;; or a permutation.
(define id-is-mux ((id natp) aignet)
  :guard (id-existsp id aignet)
  :returns (mv is-mux
               (cond-lit litp)
               (true-branch litp)
               (false-branch litp))
  (b* (((unless (int= (id->type id aignet) (gate-type)))
        (mv nil 0 0 0))
       (f0 (gate-id->fanin0 id aignet))
       (f1 (gate-id->fanin1 id aignet))
       ((when (int= (id->regp id aignet) 1))
        ;; XOR gate can be viewed as a type of mux -- (if f0 (not f1) f1)
        (mv t f0 (lit-negate f1) f1))
       ((unless (and (int= (lit-neg f0) 1)
                     (int= (lit-neg f1) 1)
                     (int= (id->type (lit-id f0) aignet) (gate-type))
                     (int= (id->regp (lit-id f0) aignet) 0)
                     (int= (id->type (lit-id f1) aignet) (gate-type))
                     (int= (id->regp (lit-id f1) aignet) 0)))
        (mv nil 0 0 0))
       (f00 (gate-id->fanin0 (lit-id f0) aignet))
       (f10 (gate-id->fanin1 (lit-id f0) aignet))
       (f01 (gate-id->fanin0 (lit-id f1) aignet))
       (f11 (gate-id->fanin1 (lit-id f1) aignet))
       (nf01 (lit-negate f01))
       (nf11 (lit-negate f11))
       ((when (int= f00 nf01))
        (mv t f00 (lit-negate f10) nf11))
       ((when (int= f00 nf11))
        (mv t f00 (lit-negate f10) nf01))
       ((when (int= f10 nf01))
        (mv t f10 (lit-negate f00) nf11))
       ((when (int= f10 nf11))
        (mv t f10 (lit-negate f00) nf01)))
    (mv nil 0 0 0))
  ///

  (defcong nat-equiv equal (id-is-mux id aignet) 1)

  (defthm id-is-mux-produces-aignet-lits
    (b* (((mv ?muxp c tb fb) (id-is-mux id aignet)))
      (and (aignet-litp c aignet)
           (aignet-litp tb aignet)
           (aignet-litp fb aignet))))

  (defthmd lit-eval-of-mk-lit-split-rw
    (implies (equal lit1 (mk-lit (lit-id lit) neg))
             (equal (lit-eval lit1 in-vals reg-vals aignet)
                    (acl2::b-xor (acl2::b-xor neg (lit-neg lit))
                                 (lit-eval lit in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable lit-eval acl2::B-xor))))

  (local (defthm bit-mux-rws
           (and (equal (b-and (b-not (b-and a b)) (b-not (b-and (b-not a) d)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and a b)) (b-not (b-and d (b-not a))))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and b a)) (b-not (b-and d (b-not a))))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and b a)) (b-not (b-and (b-not a) d)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and (b-not a) d)) (b-not (b-and a b)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and d (b-not a))) (b-not (b-and a b)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and d (b-not a))) (b-not (b-and b a)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and (b-not a) d)) (b-not (b-and b a)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d)))))
           :hints(("Goal" :in-theory (enable b-and b-ior)))))

  ;; This is a pretty awkward rewrite rule, but maybe not as bad as it
  ;; appears.  The first hyp will basically fail immediately if we don't know
  ;; that the ID is a mux.  Might need other tricks to prevent it from opening
  ;; when we don't want it to.
  (defthmd id-eval-when-id-is-mux
    (b* (((mv muxp c tb fb) (id-is-mux id aignet)))
      (implies (and muxp
                    (aignet-idp id aignet))
               (equal (id-eval id in-vals reg-vals aignet)
                      (acl2::b-ior (acl2::b-and
                                    (lit-eval c in-vals reg-vals aignet)
                                    (lit-eval tb in-vals reg-vals aignet))
                                   (acl2::b-and
                                    (acl2::b-not (lit-eval c in-vals reg-vals aignet))
                                    (lit-eval fb in-vals reg-vals aignet))))))
    :hints (("goal" :in-theory (e/d ;; (lit-eval-of-mk-lit-split-rw
                                    ;;  equal-1-by-bitp
                                    ;;  eval-and-of-lits)
                                (id-eval eval-and-of-lits eval-xor-of-lits
                                         lit-eval-of-mk-lit-split-rw)
                                ( acl2::b-xor acl2::b-and
                                              acl2::b-ior acl2::b-not))
             :expand ((:free (ftype) (lit-eval (fanin ftype (lookup-id id aignet))
                                               in-vals reg-vals aignet))))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-ior b-and b-xor))))))






(defsection collect-supergate


  (defthm aignet-lit-listp-of-append
    (implies (and (aignet-lit-listp a aignet)
                  (aignet-lit-listp b aignet))
             (aignet-lit-listp (append a b) aignet)))


  

  (local
   (progn

     (in-theory (enable aignet-eval-conjunction))

     (defthm b-and-associative
       (equal (acl2::b-and (acl2::b-and a b) c)
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm b-and-commute-2
       (equal (acl2::b-and b (acl2::b-and a c))
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm aignet-eval-conjunction-of-append
       (equal (aignet-eval-conjunction (append a b) invals regvals aignet)
              (acl2::b-and (aignet-eval-conjunction a invals regvals aignet)
                           (aignet-eval-conjunction b invals regvals aignet))))

     (local (in-theory (enable equal-1-by-bitp)))

     (defthm acl2::b-xor-of-nonzero
       (implies (equal x 1)
                (equal (acl2::b-xor x y)
                       (acl2::b-not y))))

     (defthm acl2::b-xor-of-zero
       (implies (not (equal x 1))
                (equal (acl2::b-xor x y)
                       (acl2::bfix y)))
       :hints(("Goal" :in-theory (enable acl2::b-xor))))

     (defthm acl2::b-and-collapse
       (equal (acl2::b-and x (acl2::b-and x y))
              (acl2::b-and x y))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm and-of-eval-list-when-member
       (implies (member lit lst)
                (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                    (aignet-eval-conjunction lst invals regvals aignet))
                       (aignet-eval-conjunction lst invals regvals aignet))))

     (defthm and-of-eval-list-when-fix-member
       (implies (member (lit-fix lit) (lit-list-fix lst))
                (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                    (aignet-eval-conjunction lst invals regvals aignet))
                       (aignet-eval-conjunction lst invals regvals aignet))))))

  (defthm aignet-eval-conjunction-when-0
    (implies (member 0 lst)
             (equal (aignet-eval-conjunction lst invals regvals aignet)
                    0)))

  (local (defthm and-of-eval-list-when-complement-member
           (implies (member (lit-negate lit) lst)
                    (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                        (aignet-eval-conjunction lst invals regvals aignet))
                           0))
           :hints(("Goal" :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::b-and b-xor lit-eval))))))

  (local (defthmd lit-eval-when-negate-equal
           (implies (equal (lit-negate a) b)
                    (equal (lit-eval a invals regvals aignet)
                           (b-not (lit-eval b invals regvals aignet))))
           :hints (("goal" :expand ((lit-eval a invals regvals aignet)
                                    (lit-eval b invals regvals aignet))))))

  (local (defthm and-of-eval-list-when-complement-member-fix
           (implies (member (lit-negate lit) (lit-list-fix lst))
                    (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                        (aignet-eval-conjunction lst invals regvals aignet))
                           0))
           :hints(("Goal" :induct t :in-theory (enable lit-list-fix))
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::b-and b-xor lit-eval
                                            lit-eval-when-negate-equal))))))

  (define lit-collect-supergate ((lit litp)
                                 top use-muxes
                                 (limit natp)
                                 (supergate lit-listp)
                                 aignet-refcounts aignet)
    :guard (and (< (lit-id lit) (u32-length aignet-refcounts))
                (fanin-litp lit aignet)
                (true-listp supergate))
    :measure (lit-id lit)
    :verify-guards nil
    :returns (mv (res lit-listp :hyp (and (lit-listp supergate) (litp lit)))
                 (rem-limit natp :rule-classes :type-prescription))
    (b* ((lit (lit-fix lit))
         (supergate (lit-list-fix supergate))
         (limit (lnfix limit))
         ((when (or (int= (lit-neg lit) 1)
                    (not (int= (id->type (lit-id lit) aignet) (gate-type)))
                    (int= (id->regp (lit-id lit) aignet) 1) ;; xor
                    (and (not top) (< 1 (get-u32 (lit-id lit) aignet-refcounts)))
                    (and use-muxes
                         (b* (((mv muxp & & &) (id-is-mux (lit-id lit) aignet)))
                           muxp))
                    (eql 0 limit)))
          (mv (cond ((or (member (lit-negate lit) supergate)
                         (int= (lit-fix lit) 0))
                     ;; Complementary literal is in the supergate, so add 0.
                     (list 0))
                    ((member lit supergate) supergate)
                    (t (cons lit supergate)))
              (if (eql 0 limit) limit (1- limit))))
         ((mv supergate limit)
          (lit-collect-supergate (gate-id->fanin0 (lit-id lit) aignet)
                                 nil use-muxes limit supergate aignet-refcounts aignet)))
      (lit-collect-supergate (gate-id->fanin1 (lit-id lit) aignet)
                             nil use-muxes limit supergate aignet-refcounts aignet))
    ///
  ;; (defthm true-listp-of-collect-supergate
  ;;   (implies (true-listp supergate)
  ;;            (true-listp (lit-collect-supergate lit top use-muxes supergate
  ;;                                               aignet-refcounts aignet)))
  ;;   :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
  ;;                                                  aignet-refcounts aignet)
  ;;            :do-not-induct t
  ;;            :in-theory (enable (:induction lit-collect-supergate))
  ;;            :expand ((:free (top use-muxes)
  ;;                      (lit-collect-supergate lit top use-muxes supergate
  ;;                                             aignet-refcounts aignet))))))
    (local (defthm lit-listp-true-listp
             (implies (lit-listp x) (true-listp x))
             :rule-classes :forward-chaining))
    (verify-guards lit-collect-supergate)
    (defret aignet-lit-listp-of-collect-supergate
      (implies (and (aignet-litp lit aignet)
                    (aignet-lit-listp supergate aignet))
               (aignet-lit-listp res aignet))
      :hints (("goal" :induct <call>
               :do-not-induct t
               :in-theory (disable (:definition lit-collect-supergate))
               :expand ((:free (top use-muxes) <call>)))))

    (defret collect-supergate-correct
      (equal (aignet-eval-conjunction res invals regvals aignet)
             (acl2::b-and (lit-eval lit invals regvals aignet)
                          (aignet-eval-conjunction supergate invals regvals aignet)))
      :hints (("goal" :induct <call>
               :do-not-induct t
               :in-theory (e/d (eval-and-of-lits)
                               ((:definition lit-collect-supergate)))
               :expand ((:free (top use-muxes) <call>)))
              (and stable-under-simplificationp
                   '(:expand ((lit-eval lit invals regvals aignet)
                              (id-eval (lit-id lit) invals regvals aignet))))))

    (local (in-theory (disable lookup-id-out-of-bounds
                               member
                               (:d lit-collect-supergate))))))



(defsection sat-lits
  ;; Mapping from aignet IDs to sat vars and back.  Actually, each array maps IDs
  ;; to literals.  Identities:
  ;; (lit-id (sat-id->aignet-lit (lit-id (aignet-sat-lit id)))) = (id-fix id)
  ;; (lit-id (aignet-id->sat-lit (lit-id (sat-id->aignet-lit id)))) = (id-fix id)
  ;; (lit-neg (sat-id->aignet-lit (lit-id (aignet-id->sat-lit id)))) = (aignet-id->sat-lit id)
  ;; (lit-neg (aignet-id->sat-lit (lit-id (sat-id->aignet-lit id)))) = (lit-neg (sat-id->aignet-lit id))
  (defstobj sat-lits
    (sat-next-var$ :type (integer 1 *) :initially 1)
    (aignet->sat :type (array (and (unsigned-byte 32)
                                   (satisfies satlink::litp)) (0))
                 :resizable t
                 :initially 0)
    ;; SAT var 0 is not mapped to anything.
    (sat->aignet :type (array (and (unsigned-byte 32)
                                   (satisfies litp)) (1))
                 :resizable t
                 :initially 0))

  (in-theory (disable create-sat-lits (create-sat-lits) resize-aignet->sat))
  (local (in-theory (enable create-sat-lits)))
  (local (in-theory (enable resize-aignet->sat)))

  (defun-inline sat-next-var (sat-lits)
    (declare (xargs :stobjs sat-lits))
    (mbe :logic (acl2::pos-fix (sat-next-var$ sat-lits))
         :exec (sat-next-var$ sat-lits)))

  (defun sat-lits-sizedp (sat-lits)
    (declare (xargs :stobjs (sat-lits)))
    (<= (lnfix (sat-next-var sat-lits)) (sat->aignet-length sat-lits)))

  (local (defthm litp-of-nth-aignet->sat
           (implies (and (aignet->satp x)
                         (< (nfix n) (len x)))
                    (satlink::litp (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (in-theory (enable acl2::nth-with-large-index)))


  (definlined aignet-id->sat-lit (id sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (natp id)
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    ;; Could use the phase here, won't for now
    (mbe :logic (non-exec (satlink::lit-fix (nth id (nth *aignet->sati* sat-lits))))
         :exec (if (< id (aignet->sat-length sat-lits))
                   (aignet->sati id sat-lits)
                 0)))

  (local (in-theory (enable aignet-id->sat-lit)))

  (defcong nat-equiv equal (aignet-id->sat-lit id sat-lits) 1)

  (defthm satlink-litp-of-aignet-id->sat-lit
    (satlink::litp (aignet-id->sat-lit id sat-lits)))

  (definlined set-aignet-id->sat-lit (id lit sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (and (natp id)
                                (satlink::litp lit))
                    :guard-hints ('(:in-theory (enable update-nth-lit satlink::litp)))))
    (b* ((sat-lits (if (< (lnfix id) (aignet->sat-length sat-lits))
                       sat-lits
                     (resize-aignet->sat
                      (max (* 2 (lnfix id)) 16)
                      sat-lits))))
      (mbe :logic (non-exec (update-nth *aignet->sati*
                                        (update-nth id (satlink::lit-fix lit)
                                                    (nth *aignet->sati* sat-lits))
                                        sat-lits))
           :exec (if (< (the (integer 0 *) lit) (expt 2 32))
                     (update-aignet->sati id lit sat-lits)
                   (ec-call (update-aignet->sati id lit sat-lits))))))

  (defthm set-aignet-id->sat-lit-frame
    (implies (not (equal n *aignet->sati*))
             (equal (nth n (set-aignet-id->sat-lit id lit sat-lits))
                    (nth n sat-lits)))
    :hints(("Goal" :in-theory (enable set-aignet-id->sat-lit))))

  (defthm aignet-id->sat-lit-of-set-aignet-id->sat-lit
    (satlink::lit-equiv (nth n (nth *aignet->sati* (set-aignet-id->sat-lit id lit sat-lits)))
                        (if (equal (nfix n) (nfix id))
                            lit
                          (nth n (nth *aignet->sati* sat-lits))))
    :hints(("Goal" :in-theory (enable set-aignet-id->sat-lit
                                      acl2::nth-of-resize-list-split))))

  (defund sat-varp (x sat-lits)
    (declare (xargs :stobjs sat-lits))
    (and (satlink::varp x)
         (< 0 x)
         (< x (lnfix (sat-next-var sat-lits)))))

  (local (in-theory (enable sat-varp)))

  (defthm sat-varp-when-varp
    (implies (and (satlink::varp x)
                  (< 0 x)
                  (< x (lnfix (sat-next-var sat-lits))))
             (sat-varp x sat-lits)))

  (local (defthm litp-of-nth-sat->aignet
           (implies (and (sat->aignetp x)
                         (< (nfix n) (len x)))
                    (litp (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (definlined sat-var->aignet-lit (var sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (and (sat-varp var sat-lits)
                                (sat-lits-sizedp sat-lits))
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    ;; Could use the phase here, won't for now
    (mbe :logic (non-exec (nth-lit (var-fix var) (nth *sat->aigneti* sat-lits)))
         :exec (sat->aigneti (var-fix var) sat-lits)))

  (local (in-theory (enable sat-var->aignet-lit)))

  (defcong satlink::var-equiv equal (sat-var->aignet-lit var sat-lits) 1)

  (defthm litp-sat-var->aignet-lit
    (litp (sat-var->aignet-lit var sat-lits)))

  (definline set-sat-var->aignet-lit (var lit sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (and (sat-varp var sat-lits)
                                (litp lit)
                                (sat-lits-sizedp sat-lits))
                    :guard-hints ('(:in-theory (enable update-nth-lit)))))
    (mbe :logic (non-exec (update-nth *sat->aigneti*
                                      (update-nth-lit (var-fix var) (lit-fix lit)
                                                      (nth *sat->aigneti* sat-lits))
                                      sat-lits))
         :exec (if (< (the (integer 0 *) lit) (expt 2 32))
                   (update-sat->aigneti var lit sat-lits)
                 (ec-call (update-sat->aigneti var lit sat-lits)))))


  (definlined aignet-id-has-sat-var (id sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (natp id)))
    (b* ((lit (aignet-id->sat-lit id sat-lits)))
      (not (int= (satlink::lit->var lit) 0))))

  (local (in-theory (enable aignet-id-has-sat-var)))

  (defcong nat-equiv equal (aignet-id-has-sat-var id sat-lits) 1)

  (defun aignet->sat-well-formedp (n sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (and (natp n)
                                (sat-lits-sizedp sat-lits))))
    (if (zp n)
        t
      (b* ((n (1- n))
           (nid n))
        (and (b* ((sat-lit (aignet-id->sat-lit nid sat-lits))
                  ((when (int= (satlink::lit->var sat-lit) 0)) t)
                  ((unless (id-existsp nid aignet)) nil)
                  ((unless (sat-varp (satlink::lit->var sat-lit) sat-lits))
                   nil)
                  (aignet-lit (sat-var->aignet-lit (satlink::lit->var sat-lit) sat-lits)))
               (int= aignet-lit
                     (mk-lit nid (satlink::lit->neg sat-lit))))
             (aignet->sat-well-formedp n sat-lits aignet)))))


  (defthm aignet->sat-well-formedp-implies
    (implies (and (aignet-id-has-sat-var m sat-lits)
                  (< (var-fix m) (nfix n))
                  (aignet->sat-well-formedp n sat-lits aignet))
             (and (equal (sat-var->aignet-lit
                          (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                          sat-lits)
                         (mk-lit
                          m (satlink::lit->neg (aignet-id->sat-lit m sat-lits))))
                  (sat-varp (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                            sat-lits))))

  (defthm aignet->sat-well-formedp-implies-when-not-aignet-idp
    (implies (and (aignet->sat-well-formedp n sat-lits aignet)
                  (not (aignet-idp m aignet))
                  (< (nfix m) (nfix n)))
             (satlink::var-equiv (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                                 0)))

  (local (defthm aignet->sat-well-formedp-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet->sat-well-formedp n sat-lits orig))
                    (aignet->sat-well-formedp n sat-lits new))))


  (defun sat->aignet-well-formedp (n sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (and (posp n)
                                (<= n (sat-next-var sat-lits))
                                (sat-lits-sizedp sat-lits))
                    :guard-hints (("goal" :in-theory (enable sat-varp)))
                    :guard-debug t))
    (b* ((n (1- n))
         ((when (zp n)) t)
         (nvar n))
      (and (b* ((aignet-lit (sat-var->aignet-lit nvar sat-lits))
                (aignet-id (lit-id aignet-lit))
                ((unless (and (fanin-litp aignet-lit aignet)
                              (aignet-id-has-sat-var aignet-id sat-lits)))
                 nil)
                (sat-lit (aignet-id->sat-lit aignet-id sat-lits)))
             (int= sat-lit
                   (satlink::make-lit
                    nvar (lit-neg aignet-lit))))
           (sat->aignet-well-formedp n sat-lits aignet))))

  (defthm sat->aignet-well-formedp-implies
    (implies (and (< (var-fix m) (nfix n))
                  (< 0 (var-fix m))
                  (sat->aignet-well-formedp n sat-lits aignet))
             (and (equal (aignet-id->sat-lit
                          (lit-id (sat-var->aignet-lit m sat-lits))
                          sat-lits)
                         (satlink::make-lit
                          m (lit-neg (sat-var->aignet-lit m sat-lits))))
                  (aignet-id-has-sat-var
                   (lit-id (sat-var->aignet-lit m sat-lits))
                   sat-lits)
                  (aignet-litp (sat-var->aignet-lit m sat-lits) aignet))))

  (local (defthm sat->aignet-well-formedp-of-extension
           (implies (and (aignet-extension-binding)
                         (sat->aignet-well-formedp n sat-lits orig))
                    (sat->aignet-well-formedp n sat-lits new))))


  (defund sat-lits-wfp (sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)))
    (and (sat-lits-sizedp sat-lits)
         (<= 1 (lnfix (sat-next-var sat-lits)))
         (aignet->sat-well-formedp (aignet->sat-length sat-lits) sat-lits aignet)
         (sat->aignet-well-formedp (lnfix (sat-next-var sat-lits)) sat-lits aignet)))

  (local (in-theory (enable sat-lits-wfp)))


  (defthm sat-lits-wfp-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (sat-lits-wfp sat-lits new)))


  ;; (defthm sat-lits-wfp-sat-next-var-type
  ;;   (implies (sat-lits-wfp sat-lits aignet)
  ;;            (posp (nth *sat-next-var$* sat-lits)))
  ;;   :rule-classes :forward-chaining)

  (defthm sat-lits-wfp-implies-sat-lits-sizedp
    (implies (sat-lits-wfp sat-lits aignet)
             (sat-lits-sizedp sat-lits)))

  (local (defthmd nth-lit-when-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth-lit n x) 0))
           :hints(("Goal" :in-theory (enable nth-lit
                                             acl2::nth-with-large-index)))))


  (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-id-has-sat-var n sat-lits))
             (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                       sat-lits))
    :hints(("Goal" :in-theory (e/d (aignet-idp nth-lit-when-out-of-bounds)
                                   (aignet->sat-well-formedp-implies))
            :use ((:instance aignet->sat-well-formedp-implies
                   (n (aignet->sat-length sat-lits)) (m n))))))

  (defthm sat-lits-wfp-implies-lookup-aignet-id
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'satlink::var-equiv 'id '(satlink::lit->var (aignet-id->sat-lit n sat-lits))
                    mfc state)
                   (n))
                  (satlink::var-equiv id (satlink::lit->var (aignet-id->sat-lit n sat-lits)))
                  (aignet-id-has-sat-var n sat-lits))
             (equal (sat-var->aignet-lit id sat-lits)
                    (mk-lit
                     n (satlink::lit->neg (aignet-id->sat-lit n sat-lits)))))
    :hints(("Goal" :in-theory (enable aignet-idp nth-lit-when-out-of-bounds)
            :use ((:instance aignet->sat-well-formedp-implies
                   (n (aignet->sat-length sat-lits)) (m n))))))

  (defthm sat-lits-wfp-implies-when-not-aignet-idp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (not (aignet-idp m aignet)))
             (satlink::var-equiv (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                                 0))
    :hints (("goal" :in-theory (e/d (aignet-idp nth-lit-when-out-of-bounds)
                                    (aignet->sat-well-formedp-implies-when-not-aignet-idp))
             :use ((:instance aignet->sat-well-formedp-implies-when-not-aignet-idp
                    (n (aignet->sat-length sat-lits)))))))

  (defthm sat-lits-wfp-implies-aignet-litp-of-lookup-sat-var
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (sat-varp n sat-lits))
             (aignet-litp (sat-var->aignet-lit n sat-lits) aignet))
    :hints (("goal" :use ((:instance sat->aignet-well-formedp-implies
                           (n (nfix (sat-next-var sat-lits))) (m n)))
             :do-not-induct t)))

  (defthm sat-lits-wfp-implies-bound-of-lookup-sat-var-id
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (sat-varp n sat-lits))
             (<= (lit-id (sat-var->aignet-lit n sat-lits))
                 (fanin-count aignet)))
    :hints (("goal" :use ((:instance sat->aignet-well-formedp-implies
                           (n (nfix (sat-next-var sat-lits))) (m n)))
             :in-theory (enable aignet-idp)
             :do-not-induct t))
    :rule-classes ((:linear :trigger-terms
                    ((lit-id (sat-var->aignet-lit n sat-lits))))))

  (defthm sat-lits-wfp-implies-lookup-sat-var
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'acl2::nat-equiv$inline 'id '(lit-id (sat-var->aignet-lit n sat-lits))
                    mfc state)
                   (n))
                  (nat-equiv id (lit-id (sat-var->aignet-lit n sat-lits)))
                  (sat-varp n sat-lits))
             (and (equal (aignet-id->sat-lit id sat-lits)
                         (satlink::make-lit
                          n (lit-neg (sat-var->aignet-lit n sat-lits))))
                  (aignet-id-has-sat-var id sat-lits)))
    :hints (("goal" :use ((:instance sat->aignet-well-formedp-implies
                           (n (nfix (sat-next-var sat-lits))) (m n)))
             :do-not-induct t)))

  (local (defthm equal-of-len-rw
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (if (zp n)
                               (and (equal n 0)
                                    (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- n))))))))

  (local (in-theory (disable len)))

  ;; empty sat-lits, resize things for an aignet of size n
  (defun sat-lits-empty (n sat-lits)
    (declare (xargs :stobjs sat-lits
                    :guard (natp n)
                    :guard-hints (("goal" :in-theory (e/d (update-nth)
                                                          (resize-aignet->sat))
                                   :expand ((:free (lst)
                                             (resize-list lst 1 0))
                                            (:free (sat-lits)
                                             (resize-aignet->sat 1 sat-lits))
                                            (:free (sat-lits)
                                             (resize-aignet->sat 0 sat-lits)))))))
    (mbe :logic (non-exec (resize-aignet->sat n (create-sat-lits)))
         :exec
         (b* ((sat-lits (update-sat-next-var$ 1 sat-lits))
              (sat-lits (resize-sat->aignet 1 sat-lits))
              (sat-lits (update-sat->aigneti 0 0 sat-lits))
              (sat-lits (resize-aignet->sat 0 sat-lits)))
           (resize-aignet->sat n sat-lits))))


  (defthmd sat-lits-wfp-implies-no-sat-var-when-out-of-range
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (< (fanin-count aignet) (nfix id)))
             (not (aignet-id-has-sat-var id sat-lits)))
    :hints (("goal" :in-theory (e/d (aignet-idp
                                     aignet-id-has-sat-var)
                                    (sat-lits-wfp-implies-when-not-aignet-idp))
             :use ((:instance sat-lits-wfp-implies-when-not-aignet-idp
                    (m id))))))

  (defthmd sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (not (aignet-idp id aignet)))
             (not (aignet-id-has-sat-var id sat-lits)))
    :hints (("goal" :in-theory (e/d (aignet-id-has-sat-var)
                                    (sat-lits-wfp-implies-when-not-aignet-idp))
             :use ((:instance sat-lits-wfp-implies-when-not-aignet-idp
                    (m id)))))))

(defsection sat-lit-extension-p
  (defun-sk sat-lit-extension-p (sat-lits2 sat-lits1)
    (forall var/id
            (and (implies (sat-varp (satlink::var-fix var/id) sat-lits1)
                          (and (sat-varp (satlink::var-fix var/id) sat-lits2)
                               (equal (sat-var->aignet-lit var/id sat-lits2)
                                      (sat-var->aignet-lit var/id sat-lits1))))
                 (implies (aignet-id-has-sat-var var/id sat-lits1)
                          (and (aignet-id-has-sat-var var/id sat-lits2)
                               (equal (aignet-id->sat-lit var/id sat-lits2)
                                      (aignet-id->sat-lit var/id sat-lits1))))))
    :rewrite :direct)

  (defmacro sat-lit-extension-binding (&key (new 'sat-lits2)
                                         (orig 'sat-lits1)
                                         (fall-through 't))
    `(bind-free (acl2::prev-stobj-binding ,new ',orig mfc state)
                . ,(if fall-through nil `((,orig)))))

  ;; expands sat-lit-extension-p if it appears as a positive literal
  (defthmd prove-sat-lit-extension-p
    (implies (acl2::rewriting-positive-literal `(sat-lit-extension-p ,sat-lits2 ,sat-lits1))
             (equal (sat-lit-extension-p sat-lits2 sat-lits1)
                    (let ((var/id (sat-lit-extension-p-witness sat-lits2 sat-lits1)))
                      (and (implies (sat-varp (satlink::var-fix var/id) sat-lits1)
                                    (and (sat-varp (satlink::var-fix var/id) sat-lits2)
                                         (equal (sat-var->aignet-lit var/id sat-lits2)
                                                (sat-var->aignet-lit var/id sat-lits1))))
                           (implies (aignet-id-has-sat-var var/id sat-lits1)
                                    (and (aignet-id-has-sat-var var/id sat-lits2)
                                         (equal (aignet-id->sat-lit var/id sat-lits2)
                                                (aignet-id->sat-lit var/id sat-lits1)))))))))

  (defthm sat-lit-extension-p-transitive
    (implies (and (sat-lit-extension-binding :new sat-lits3 :orig sat-lits2)
                  (sat-lit-extension-p sat-lits3 sat-lits2)
                  (sat-lit-extension-p sat-lits2 sat-lits1))
             (sat-lit-extension-p sat-lits3 sat-lits1))
    :hints(("Goal" :in-theory (disable sat-lit-extension-p)
            :expand ((sat-lit-extension-p sat-lits3 sat-lits1))
            :use ((:instance sat-lit-extension-p-necc
                   (sat-lits2 sat-lits2) (sat-lits1 sat-lits1)
                   (var/id (sat-lit-extension-p-witness sat-lits3 sat-lits1)))
                  (:instance sat-lit-extension-p-necc
                   (sat-lits2 sat-lits3) (sat-lits1 sat-lits2)
                   (var/id (sat-lit-extension-p-witness sat-lits3 sat-lits1))))))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm sat-lit-extension-p-reflexive
    (sat-lit-extension-p sat-lits sat-lits))

  (in-theory (disable sat-lit-extension-p))

  (defthm sat-varp-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-varp var sat-lits1))
             (sat-varp var sat-lits2))
    :hints (("goal" :use ((:instance sat-lit-extension-p-necc
                           (var/id var)))
             :in-theory (e/d (sat-varp)
                             (sat-lit-extension-p-necc)))))

  (defthm sat-var->aignet-lit-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-varp (satlink::var-fix var) sat-lits1))
             (equal (sat-var->aignet-lit var sat-lits2)
                    (sat-var->aignet-lit var sat-lits1))))

  (defthm aignet-id-has-sat-var-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (aignet-id-has-sat-var id sat-lits1))
             (aignet-id-has-sat-var id sat-lits2)))

  (defthm aignet-id->sat-lit-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (aignet-id-has-sat-var id sat-lits1))
             (equal (aignet-id->sat-lit id sat-lits2)
                    (aignet-id->sat-lit id sat-lits1))))

  (in-theory (disable sat-lit-extension-p-necc))

  (defun sat-litp (x sat-lits)
    (Declare (xargs :stobjs sat-lits))
    (and (satlink::litp x)
         (sat-varp (satlink::lit->var x) sat-lits)))

  (defun sat-lit-listp (x sat-lits)
    (declare (xargs :stobjs sat-lits
                    :guard t))
    (if (atom x)
        (eq x nil)
      (and (sat-litp (car x) sat-lits)
           (sat-lit-listp (cdr x) sat-lits))))

  (defun sat-lit-list-listp (x sat-lits)
    (declare (xargs :stobjs sat-lits))
    (if (atom x)
        (eq x nil)
      (and (sat-lit-listp (car x) sat-lits)
           (sat-lit-list-listp (cdr x) sat-lits))))

  (defthm sat-litp-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-litp lit sat-lits1))
             (sat-litp lit sat-lits2)))

  (defthm sat-lit-listp-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-listp lits sat-lits1))
             (sat-lit-listp lits sat-lits2)))

  (defthm sat-lit-list-listp-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-list-listp clauses sat-lits1))
             (sat-lit-list-listp clauses sat-lits2)))


  (defun aignet-lits-have-sat-vars (lits sat-lits)
    (Declare (xargs :stobjs (sat-lits)
                    :guard (lit-listp lits)))
    (if (atom lits)
        t
      (and (aignet-id-has-sat-var (lit-id (car lits)) sat-lits)
           (aignet-lits-have-sat-vars (cdr lits) sat-lits))))

  (defthm aignet-lits-have-sat-vars-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (aignet-lits-have-sat-vars lits sat-lits1))
             (aignet-lits-have-sat-vars lits sat-lits2)))

  (definline aignet-lit->sat-lit (lit sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (litp lit)
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    (satlink::lit-negate-cond (aignet-id->sat-lit (lit-id lit) sat-lits)
                              (lit-neg lit)))

  (defcong lit-equiv equal (aignet-lit->sat-lit lit sat-lits) 1)

  (defthm aignet-lit->sat-lit-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits1))
             (equal (aignet-lit->sat-lit lit sat-lits2)
                    (aignet-lit->sat-lit lit sat-lits1))))

  (defun aignet-lits->sat-lits (lits sat-lits)
    (declare (Xargs :stobjs (sat-lits)
                    :guard (lit-listp lits)))
    (if (atom lits)
        nil
      (cons (aignet-lit->sat-lit (car lits) sat-lits)
            (aignet-lits->sat-lits (cdr lits) sat-lits))))

  (defthm aignet-lits->sat-lits-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (aignet-lits-have-sat-vars lits sat-lits1))
             (equal (aignet-lits->sat-lits lits sat-lits2)
                    (aignet-lits->sat-lits lits sat-lits1))))

  (defthm sat-lit-listp-of-aignet-lits->sat-lits
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (sat-lit-listp (aignet-lits->sat-lits lits sat-lits)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (defthm lit-listp-of-aignet-lits->sat-lits
    (lit-listp (aignet-lits->sat-lits lits sat-lits))))



(defsection sat-add-aignet-lit

  (local (in-theory (enable create-sat-lits (create-sat-lits))))
  (local (in-theory (enable resize-aignet->sat)))

  (definline maybe-grow-sat->aignet (sat-lits)
    (declare (xargs :stobjs sat-lits))
    (let ((target (+ 1 (lnfix (sat-next-var sat-lits)))))
      (if (< (sat->aignet-length sat-lits) target)
          (resize-sat->aignet (max 16 (* 2 target)) sat-lits)
        sat-lits)))

  (local (in-theory (enable sat-varp)))

  (define sat-add-aignet-lit ((lit litp) sat-lits aignet)
    :guard (and (sat-lits-wfp sat-lits aignet)
                (fanin-litp lit aignet))
    (b* ((lit (lit-fix lit))
         ((unless (mbt (fanin-litp lit aignet)))
          sat-lits)
         (id (lit-id lit))
         ((when (aignet-id-has-sat-var id sat-lits))
          sat-lits)
         (sat-lits (maybe-grow-sat->aignet sat-lits))
         (new-var  (var-fix (sat-next-var sat-lits)))
         (sat-lits (update-sat-next-var$ (+ 1 new-var) sat-lits))
         (new-lit  (satlink::make-lit new-var (lit-neg lit)))
         (sat-lits (set-sat-var->aignet-lit new-var lit sat-lits))
         (sat-lits (set-aignet-id->sat-lit id new-lit sat-lits)))
      sat-lits)
    ///

    (local (in-theory (enable aignet-id-has-sat-var
                              aignet-id->sat-lit
                              sat-var->aignet-lit)))

    (defcong lit-equiv equal (sat-add-aignet-lit lit sat-lits aignet) 1)

    (defthm sat-lit-extension-p-of-sat-add-aignet-lit
      (sat-lit-extension-p
       (sat-add-aignet-lit lit sat-lits aignet) sat-lits)
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable prove-sat-lit-extension-p)))
              (b* ((witness-terms
                    (acl2::find-calls-lst
                     'sat-lit-extension-p-witness
                     clause))
                   ((unless witness-terms)
                    nil)
                   (wit (car witness-terms))
                   (alist
                    `((,wit . id/var))))
                `(:clause-processor
                  (acl2::simple-generalize-cp
                   clause ',alist)))))

    (defthm sat-lits-sizedp-of-sat-add-aignet-lit
      (implies (sat-lits-sizedp sat-lits)
               (sat-lits-sizedp (sat-add-aignet-lit lit sat-lits aignet))))

    (defthm sat-add-aignet-lit-of-aignet-extension
      (implies (and (aignet-extension-binding)
                    (aignet-litp lit orig))
               (equal (sat-add-aignet-lit lit sat-lits new)
                      (sat-add-aignet-lit lit sat-lits orig))))


    (defthm sat-add-aignet-lit-new-id-not-varp-in-previous
      (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                    (aignet-litp (lit-fix lit) aignet))
               (not (sat-varp (satlink::lit->var (aignet-lit->sat-lit
                                                  lit (sat-add-aignet-lit lit sat-lits aignet)))
                              sat-lits))))

    (defthm sat-add-aignet-lit-new-id-not-varp-in-previous-by-id
      (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                    (aignet-litp (lit-fix lit) aignet)
                    (equal (nfix id) (lit-id lit)))
               (not (sat-varp (satlink::lit->var (aignet-id->sat-lit
                                                  id (sat-add-aignet-lit lit sat-lits aignet)))
                              sat-lits))))


    (defthm aignet-id-has-sat-var-preserved-when-not-same-id-of-sat-add-aignet-lit
      (implies (not (equal (nfix id) (lit-id lit)))
               (equal
                (aignet-id-has-sat-var
                 id (sat-add-aignet-lit lit sat-lits aignet))
                (aignet-id-has-sat-var id sat-lits))))

    (defthm aignet-id-has-sat-var-after-sat-add-aignet-lit
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (aignet-litp (lit-fix lit) aignet))
               (aignet-id-has-sat-var
                (lit-id lit) (sat-add-aignet-lit lit sat-lits aignet))))

    (defthmd aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (aignet-litp (lit-fix lit) aignet))
               (equal (aignet-id-has-sat-var
                       id (sat-add-aignet-lit lit sat-lits aignet))
                      (or (equal (lit-id lit) (nfix id))
                          (aignet-id-has-sat-var id sat-lits)))))

    (defthmd aignet-id->sat-lit-preserved-of-sat-add-aignet-lit-when-not-added
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (not (equal (lit-id lit) (nfix id))))
               (equal (aignet-id->sat-lit
                       id (sat-add-aignet-lit lit sat-lits aignet))
                      (aignet-id->sat-lit id sat-lits))))

    (local (defthm nth-special
             (and (equal (lit-id (nth n '(0))) 0)
                  (equal (lit-neg (nth n '(0))) 0)
                  (equal (lit-fix (nth n '(0))) 0)
                  (equal (satlink::lit-fix (nth n '(0))) 0))
             :hints(("Goal" :in-theory (enable nth)))))

    (defthm aignet-id->sat-var-of-create
      (equal (aignet-id->sat-lit id (create-sat-lits)) 0)
      :hints(("Goal" :in-theory (enable nth-lit))))

    (defthm aignet-id->sat-var-of-resize-of-create
      (equal (aignet-id->sat-lit id (resize-aignet->sat n (create-sat-lits))) 0)
      :hints(("Goal" :in-theory (e/d (ACL2::NTH-OF-RESIZE-LIST-SPLIT
                                      nth-lit resize-aignet->sat)
                                     (make-list-ac
                                      ACL2::RESIZE-LIST-WHEN-EMPTY)))))


    (defthm sat-var->aignet-lit-of-create
      (equal (sat-var->aignet-lit var (create-sat-lits)) 0)
      :hints(("Goal" :in-theory (enable nth-lit))))

    (defthm sat-var->aignet-lit-of-resize-of-create
      (equal (sat-var->aignet-lit var (resize-aignet->sat n (create-sat-lits))) 0)
      :hints(("Goal" :in-theory (enable nth-lit))))


    (local (defthm aignet->sat-well-formedp-of-resize-of-create
             (aignet->sat-well-formedp m (resize-aignet->sat n (create-sat-lits))
                                       aignet)
             :hints (("goal" :induct (aignet->sat-well-formedp m (resize-aignet->sat n
                                                                                     (create-sat-lits))
                                                               aignet)
                      :in-theory (e/d (acl2::nth-of-resize-list-split
                                       nth-lit)
                                      (acl2::make-list-ac-redef
                                       acl2::resize-list-when-empty))))))

    (local (defthm aignet->sat-well-formedp-of-create
             (aignet->sat-well-formedp m (create-sat-lits) aignet)
             :hints (("goal" :induct (aignet->sat-well-formedp m (create-sat-lits)
                                                               aignet)
                      :in-theory (e/d (nth-lit))))))

    (local (in-theory (disable create-sat-lits)))

    (defthm lit-neg-of-sat-add-aignet-lit-new-lit
      (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                    (aignet-litp (lit-fix lit) aignet))
               (equal (satlink::lit->neg (aignet-lit->sat-lit lit (sat-add-aignet-lit lit
                                                                                      sat-lits
                                                                                      aignet)))
                      0)))

    (local (in-theory (enable sat-lits-wfp)))

    (defthm sat-lits-wfp-of-resize-of-create
      ;; (implies (<= (nfix (num-fanins aignet)) (nfix n))
      (sat-lits-wfp (resize-aignet->sat n (create-sat-lits)) aignet)
      :hints(("Goal" :in-theory (e/d (nth-lit nth update-nth create-sat-lits)
                                     (aignet->sat-well-formedp-of-resize-of-create))
              :use ((:instance aignet->sat-well-formedp-of-resize-of-create
                     (m (nfix n)))))))

    (defthm sat-lits-wfp-of-create
      ;; (implies (<= (nfix (num-fanins aignet)) (nfix n))
      (sat-lits-wfp (create-sat-lits) aignet)
      :hints(("Goal" :in-theory (e/d (nth-lit nth update-nth create-sat-lits sat-lits-wfp)
                                     (aignet->sat-well-formedp-of-create))
              :use ((:instance aignet->sat-well-formedp-of-create
                     (m (nfix n)))))))

    (local (in-theory (disable resize-aignet->sat)))

    (local (in-theory (disable aignet-id->sat-lit
                               sat-var->aignet-lit
                               aignet-id-has-sat-var
                               sat-lits-wfp
                               sat-add-aignet-lit
                               sat-varp
                               acl2::nth-with-large-index)))

    (local (defthm aignet->sat-well-formedp-of-sat-add-aignet-lit
             (implies (sat-lits-wfp sat-lits aignet)
                      (let ((sat-lits (sat-add-aignet-lit lit sat-lits aignet)))
                        (aignet->sat-well-formedp n sat-lits aignet)))
             :hints (("goal" :induct (aignet->sat-well-formedp n sat-lits aignet)
                      :expand ((:free (sat-lits)
                                (aignet->sat-well-formedp n sat-lits aignet)))
                      :in-theory (e/d (aignet-id-has-sat-var
                                       sat-add-aignet-lit
                                       aignet-id->sat-lit
                                       sat-var->aignet-lit
                                       sat-varp)
                                      (sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                                       sat-lits-wfp-implies-lookup-aignet-id
                                       sat-lits-wfp-implies-when-not-aignet-idp
                                       (:definition aignet->sat-well-formedp))))
                     '(:use ((:instance sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                              (n (+ -1 n)))
                             (:instance sat-lits-wfp-implies-lookup-aignet-id
                              (n (+ -1 n))
                              (id (satlink::lit->var (aignet-id->sat-lit (1- n) sat-lits))))
                             (:instance sat-lits-wfp-implies-when-not-aignet-idp
                              (m (+ -1 n))))))))

    (local (defthm sat->aignet-well-formedp-of-sat-add-aignet-lit
             (implies (and (sat-lits-wfp sat-lits aignet)
                           (posp n)
                           (<= n (nfix (sat-next-var sat-lits))))
                      (let ((sat-lits (sat-add-aignet-lit lit sat-lits aignet)))
                        (sat->aignet-well-formedp n sat-lits aignet)))
             :hints (("goal" :induct (sat->aignet-well-formedp n sat-lits aignet)))))



    (local (defthm aignet->sat-well-formedp-increase-index
             (implies (sat-lits-wfp sat-lits aignet)
                      (aignet->sat-well-formedp n sat-lits aignet))
             :hints (("goal" :induct (aignet->sat-well-formedp n sat-lits aignet))
                     '(:use ((:instance sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                              (n (+ -1 n)))
                             (:instance sat-lits-wfp-implies-lookup-aignet-id
                              (n (+ -1 n))
                              (id (satlink::lit->var (aignet-id->sat-lit (1- n) sat-lits))))
                             (:instance sat-lits-wfp-implies-when-not-aignet-idp
                              (m (1- n))))
                       :in-theory (enable acl2::nth-with-large-index nth-lit
                                          aignet-id-has-sat-var
                                          aignet-id->sat-lit)))))


    (defthm sat-lits-wfp-of-sat-add-aignet-lit
      (implies (sat-lits-wfp sat-lits aignet)
               (sat-lits-wfp (sat-add-aignet-lit lit sat-lits aignet) aignet))
      :hints (("goal" :use ((:instance sat->aignet-well-formedp-of-sat-add-aignet-lit
                             (n (nfix (sat-next-var sat-lits))))
                            (:instance aignet->sat-well-formedp-of-sat-add-aignet-lit
                             (n (aignet->sat-length
                                 (sat-add-aignet-lit lit sat-lits aignet)))))
               :in-theory (disable aignet->sat-well-formedp-of-sat-add-aignet-lit
                                   sat->aignet-well-formedp-of-sat-add-aignet-lit)
               :expand ((sat-lits-wfp (sat-add-aignet-lit lit sat-lits
                                                          aignet) aignet)))
              (and stable-under-simplificationp
                   '(:expand ((sat-add-aignet-lit lit sat-lits aignet))
                     :in-theory (e/d (sat-var->aignet-lit
                                      aignet-id-has-sat-var
                                      aignet-id->sat-lit)
                                     (aignet->sat-well-formedp-of-sat-add-aignet-lit
                                      sat->aignet-well-formedp-of-sat-add-aignet-lit))))
              (and stable-under-simplificationp
                   '(:expand ((sat-lits-wfp sat-lits aignet))))))



    (acl2::def-stobj-preservation-macros
      :name sat-lits
      :default-stobjname sat-lits
      :templates sat-lits-preservation-templates
      :history sat-lits-preservation-history)

    (add-sat-lits-preservation-thm
     sat-lits-wfp
     :body `(implies (sat-lits-wfp ,orig-stobj aignet)
                     (sat-lits-wfp ,new-stobj aignet))
     :hints `(,@expand/induct-hints))

    (add-sat-lits-preservation-thm
     sat-lit-extension-p
     :body `(sat-lit-extension-p ,new-stobj ,orig-stobj)
     :hints `(,@expand/induct-hints))

    (def-sat-lits-preservation-thms sat-add-aignet-lit)))


(defsection sat-clauses
  (defstobj-clone cnf-vals bitarr :strsubst (("BIT" . "CNF-VAL")))

  ;; bozo maybe move to satlink
  ;; satlink::eval-cube ?
  ;; (defun cnf-eval-conjunction (lits cnf-vals)
  ;;   (declare (xargs :stobjs cnf-vals
  ;;                   :guard (satlink::lit-listp lits)))
  ;;   (if (atom lits)
  ;;       1
  ;;     (acl2::b-and (satlink::eval-lit (car lits) cnf-vals)
  ;;                  (cnf-eval-conjunction (cdr lits) cnf-vals))))

  ;; (defthm bitp-cnf-eval-conjunction
  ;;   (acl2::bitp (cnf-eval-conjunction lits cnf-vals)))

  ;; (defcong bits-equiv equal (cnf-eval-conjunction lits cnf-vals) 2)


  (defun var-in-clause (var lits)
    (declare (xargs :guard (and (satlink::varp var)
                                (satlink::lit-listp lits))))
    (and (consp lits)
         (or (equal (satlink::var-fix var) (satlink::lit->var (car lits)))
             (var-in-clause var (cdr lits)))))

  (defcong satlink::var-equiv equal (var-in-clause var lits) 1)

  (defun var-in-cnf (var clauses)
    (declare (xargs :guard (and (satlink::varp var)
                                (satlink::lit-list-listp clauses))))
    (and (consp clauses)
         (or (var-in-clause var (car clauses))
             (var-in-cnf var (cdr clauses)))))

  (defthm satlink::eval-lit-of-update-unused
    (implies (not (equal (satlink::lit->var lit) (var-fix var)))
             (equal (satlink::eval-lit lit (update-nth var val bits))
                    (satlink::eval-lit lit bits)))
    :hints(("Goal" :in-theory (enable satlink::eval-lit
                                      satlink::eval-var))))

  (defthm satlink::eval-clause-of-update-unused
    (implies (not (var-in-clause var clause))
             (equal (satlink::eval-clause clause (update-nth var val bits))
                    (satlink::eval-clause clause bits)))
    :hints(("Goal" :in-theory (enable satlink::eval-clause))))

  (defthm eval-cube-of-update-unused
    (implies (not (var-in-clause var conjunction))
             (equal (eval-cube conjunction (update-nth var val bits))
                    (eval-cube conjunction bits))))

  (defthm satlink::eval-formula-of-update-unused
    (implies (not (var-in-cnf var cnf))
             (equal (satlink::eval-formula cnf (update-nth var val bits))
                    (satlink::eval-formula cnf bits)))
    :hints(("Goal" :in-theory (enable satlink::eval-formula))))

  (defthm not-in-clause-when-not-sat-varp
    (implies (and (sat-lit-listp clause sat-lits)
                  (satlink::varp var)
                  (not (sat-varp var sat-lits)))
             (not (var-in-clause var clause))))

  (defthm not-in-cnf-when-not-sat-varp
    (implies (and (sat-lit-list-listp cnf sat-lits)
                  (satlink::varp var)
                  (not (sat-varp var sat-lits)))
             (not (var-in-cnf var cnf)))))

(defsection aignet->cnf-vals

  (defiteration aignet->cnf-vals (invals regvals cnf-vals sat-lits aignet)
    (declare (xargs :stobjs (cnf-vals sat-lits invals regvals aignet)
                    :guard (and (sat-lits-wfp sat-lits aignet)
                                (<= (num-ins aignet) (bits-length invals))
                                (<= (num-regs aignet) (bits-length regvals))
                                (<= (sat-next-var sat-lits) (bits-length cnf-vals)))))
    (b* ((var (var-fix n))
         (lit (sat-var->aignet-lit var sat-lits))
         (val (lit-eval lit invals regvals aignet)))
      (set-bit n val cnf-vals))
    :iter-guard (posp n)
    :returns cnf-vals
    :first 1
    :last (sat-next-var sat-lits))
  
  (in-theory (disable aignet->cnf-vals))
  (local (in-theory (enable aignet->cnf-vals
                            (:i aignet->cnf-vals-iter))))


  (defthm nth-of-aignet->cnf-vals-iter
    (equal (nth m (aignet->cnf-vals-iter n invals regvals cnf-vals sat-lits aignet))
           (if (and (posp m)
                    (< m (ifix n)))
               (lit-eval (sat-var->aignet-lit m sat-lits) invals regvals aignet)
             (nth m cnf-vals)))
    :hints (("goal" :induct (aignet->cnf-vals-iter n invals regvals cnf-vals sat-lits aignet)
             :expand ((aignet->cnf-vals-iter n invals regvals cnf-vals sat-lits aignet)))))

  (defthm nth-of-aignet->cnf-vals
    (equal (nth m (aignet->cnf-vals invals regvals cnf-vals sat-lits aignet))
           (if (sat-varp (nfix m) sat-lits)
               (lit-eval (sat-var->aignet-lit m sat-lits) invals regvals aignet)
             (nth m cnf-vals)))
    :hints(("Goal" :in-theory (enable aignet->cnf-vals sat-varp))))

  (defthm eval-var-in-aignet->cnf-vals-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-varp (nfix var) sat-lits1))
             (equal (satlink::eval-var
                     var (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits2 aignet))
                    (satlink::eval-var
                     var (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits1 aignet))))
    :hints(("Goal" :in-theory (e/d (satlink::eval-var sat-varp)
                                   (aignet->cnf-vals)))))

  (defthm eval-lit-in-aignet->cnf-vals-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-litp lit sat-lits1))
             (equal (satlink::eval-lit
                     lit (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits2 aignet))
                    (satlink::eval-lit
                     lit (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits1 aignet))))
    :hints(("Goal" :in-theory (e/d (satlink::eval-lit)
                                   (aignet->cnf-vals)))))

  (defthm eval-clause-in-aignet->cnf-vals-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-listp clause sat-lits1))
             (equal (satlink::eval-clause
                     clause (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits2 aignet))
                    (satlink::eval-clause
                     clause (aignet->cnf-vals
                             invals regvals cnf-vals sat-lits1 aignet))))
    :hints(("Goal" :in-theory (e/d (satlink::eval-clause)
                                   (aignet->cnf-vals)))))

  (defthm eval-conjunction-in-aignet->cnf-vals-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-listp conjunction sat-lits1))
             (equal (eval-cube
                     conjunction (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits2 aignet))
                    (eval-cube
                     conjunction (aignet->cnf-vals
                             invals regvals cnf-vals sat-lits1 aignet))))
    :hints(("Goal" :in-theory (e/d (eval-cube)
                                   (aignet->cnf-vals)))))

  (defthm eval-formula-in-aignet->cnf-vals-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-list-listp formula sat-lits1))
             (equal (satlink::eval-formula
                     formula (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits2 aignet))
                    (satlink::eval-formula
                     formula (aignet->cnf-vals
                             invals regvals cnf-vals sat-lits1 aignet))))
    :hints(("Goal" :in-theory (e/d (satlink::eval-formula)
                                   (aignet->cnf-vals)))))


  (defthm eval-var-of-aignet->cnf-vals
    (implies (sat-varp (satlink::var-fix var) sat-lits)
             (equal (satlink::eval-var
                     var (aignet->cnf-vals invals regvals cnf-vals sat-lits
                                           aignet))
                    (lit-eval (sat-var->aignet-lit var sat-lits)
                              invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d (satlink::eval-var)
                                   (aignet->cnf-vals)))))

  (defun sat-lit->aignet-lit (lit sat-lits)
    (declare (xargs :stobjs sat-lits
                    :guard (and (sat-lits-sizedp sat-lits)
                                (sat-litp lit sat-lits))
                    :guard-hints (("goal" :in-theory (enable sat-varp)))))
    (let ((lit1 (sat-var->aignet-lit (satlink::lit->var lit) sat-lits)))
      (mk-lit (lit-id lit1) (b-xor (satlink::lit->neg lit)
                                   (lit-neg lit1)))))

  (defun sat-lits->aignet-lits (lits sat-lits)
    (declare (xargs :stobjs sat-lits
                    :guard (and (sat-lits-sizedp sat-lits)
                                (sat-lit-listp lits sat-lits))))
    (if (atom lits)
        nil
      (cons (sat-lit->aignet-lit (car lits) sat-lits)
            (sat-lits->aignet-lits (cdr lits) sat-lits))))

  (defthm eval-lit-of-aignet->cnf-vals
    (implies (sat-litp lit sat-lits)
             (equal (satlink::eval-lit
                     lit (aignet->cnf-vals invals regvals cnf-vals sat-lits
                                           aignet))
                    (lit-eval (sat-lit->aignet-lit lit sat-lits)
                              invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d (satlink::eval-lit
                                    satlink::eval-var)
                                   (aignet->cnf-vals)))))

  (defthm eval-cube-of-aignet->cnf-vals
    (implies (sat-lit-listp lits sat-lits)
             (equal (eval-cube
                     lits
                     (aignet->cnf-vals invals regvals cnf-vals sat-lits
                                       aignet))
                    (aignet-eval-conjunction
                     (sat-lits->aignet-lits lits sat-lits)
                     invals regvals aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-eval-conjunction)
                                   (aignet->cnf-vals)))))

  (defthm aignet-lit-listp-of-sat-lits->aignet-lits
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (sat-lit-listp lits sat-lits))
             (aignet-lit-listp (sat-lits->aignet-lits lits sat-lits) aignet)))

  (defthm sat-lits->aignet-lits-of-aignet-lits->sat-lits
    (implies (and (bind-free '((aignet . aignet)) (aignet))
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits)
                  (lit-listp lits))
             (equal (sat-lits->aignet-lits
                     (aignet-lits->sat-lits
                      lits sat-lits)
                     sat-lits)
                    lits)))

  (defthm sat-lits->aignet-lits-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lit-listp lits sat-lits1))
             (equal (sat-lits->aignet-lits lits sat-lits2)
                    (sat-lits->aignet-lits lits sat-lits1))))

  ;(local (in-theory (disable aignet-eval)))

  (local (defthm integerp-when-ifix-nonzero
           (implies (not (equal 0 (ifix n)))
                    (integerp n))))
  ;; (local (defthm sat-varp-of-decr
  ;;          (implies (and (< 1 (ifix n))
  ;;                        (<= n (acl2::pos-fix (nth *sat-next-var$* sat-lits))))
  ;;                   (sat-varp (+ -1 (ifix n)) sat-lits))
  ;;          :hints(("Goal" :in-theory (enable sat-varp ifix)))))

  (defthm aignet->cnf-vals-iter-of-aignet-eval-of-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig)
                  (<= n (sat-next-var sat-lits)))
             (equal (aignet->cnf-vals-iter
                     n invals regvals
                     cnf-vals sat-lits new)
                    (aignet->cnf-vals-iter
                     n invals regvals
                     cnf-vals sat-lits orig)))
    :hints((acl2::just-induct-and-expand
            (aignet->cnf-vals-iter
             n invals regvals cnf-vals sat-lits new)
            :expand-others
            ((:free (aignet)
              (aignet->cnf-vals-iter
               n invals regvals cnf-vals sat-lits aignet))))
           (and stable-under-simplificationp
                '(:in-theory (enable sat-varp)))))

  (defthm aignet->cnf-vals-of-aignet-eval-of-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (equal (aignet->cnf-vals invals regvals cnf-vals sat-lits new)
                    (aignet->cnf-vals invals regvals cnf-vals sat-lits orig)))))


;; (defsection aignet->cnf-vals
;;   (defiteration aignet->cnf-vals (vals cnf-vals sat-lits aignet)
;;     (declare (xargs :stobjs (vals cnf-vals sat-lits aignet)
;;                     :guard (and (sat-lits-wfp sat-lits aignet)
;;                                 (<= (num-fanins aignet) (bits-length vals))
;;                                 (<= (sat-next-var sat-lits) (bits-length
;;                                                              cnf-vals)))))
;;     (b* ((var (var-fix n))
;;          (lit (sat-var->aignet-lit var sat-lits))
;;          (val (aignet-eval-lit lit vals)))
;;       (set-bit n val cnf-vals))
;;     :iter-guard (posp n)
;;     :returns cnf-vals
;;     :first 1
;;     :last (sat-next-var sat-lits))

;;   (in-theory (disable aignet->cnf-vals))
;;   (local (in-theory (enable aignet->cnf-vals
;;                             (:induction aignet->cnf-vals-iter))))

;;   (defthm aignet->cnf-vals-iter-normalize-aignet
;;     (implies (syntaxp (not (equal aignet ''nil)))
;;              (equal (aignet->cnf-vals-iter n vals cnf-vals sat-lits aignet)
;;                     (aignet->cnf-vals-iter n vals cnf-vals sat-lits nil)))
;;     :hints((acl2::just-induct-and-expand
;;             (aignet->cnf-vals-iter n vals cnf-vals sat-lits aignet)
;;             :expand-others
;;             ((:free (aignet)
;;               (aignet->cnf-vals-iter n vals cnf-vals sat-lits aignet))))))

;;   (defthm aignet->cnf-vals-normalize-aignet
;;     (implies (syntaxp (not (equal aignet ''nil)))
;;              (equal (aignet->cnf-vals vals cnf-vals sat-lits aignet)
;;                     (aignet->cnf-vals vals cnf-vals sat-lits nil))))

;;   (local (defthm ifix-greater-than-n
;;            (implies (and (acl2::rewriting-negative-literal
;;                           `(< ,n (ifix ,m)))
;;                          (syntaxp (quotep n))
;;                          (natp n))
;;                     (equal (< n (ifix m))
;;                            (and (integerp m)
;;                                 (< n m))))))

;;   (defthm nth-of-aignet->cnf-vals-iter
;;     (equal (nth n (aignet->cnf-vals-iter m vals cnf-vals sat-lits
;;                                          aignet))
;;            (if (and (posp n)
;;                     (< n (nfix m)))
;;                (aignet-eval-lit
;;                 (sat-var->aignet-lit n sat-lits)
;;                 vals)
;;              (nth n cnf-vals)))
;;     :hints((acl2::just-induct-and-expand
;;             (aignet->cnf-vals-iter m vals cnf-vals sat-lits aignet))))


;;   (defthm nth-of-aignet->cnf-vals
;;     (equal (nth n (aignet->cnf-vals vals cnf-vals sat-lits aignet))
;;            (if (sat-varp (var-fix n) sat-lits)
;;                (aignet-eval-lit
;;                 (sat-var->aignet-lit n sat-lits)
;;                 vals)
;;              (nth n cnf-vals)))
;;     :hints(("Goal" :in-theory (enable sat-varp))))

;;   (defthm len-of-aignet->cnf-vals-iter
;;     (implies (and (<= (nfix (sat-next-var sat-lits))
;;                       (bits-length cnf-vals))
;;                   (<= (nfix m) (bits-length cnf-vals)))
;;              (equal (len (aignet->cnf-vals-iter m vals cnf-vals sat-lits
;;                                                 aignet))
;;                     (len cnf-vals)))
;;     :hints((acl2::just-induct-and-expand
;;             (aignet->cnf-vals-iter m vals cnf-vals sat-lits aignet))))

;;   (defthm len-of-aignet->cnf-vals
;;     (implies (and (<= (nfix (sat-next-var sat-lits))
;;                       (bits-length cnf-vals)))
;;              (equal (len (aignet->cnf-vals vals cnf-vals sat-lits
;;                                            aignet))
;;                     (len cnf-vals))))

;;   (defthm eval-var-in-aignet->cnf-vals-of-sat-lit-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-varp (nfix var) sat-lits1))
;;              (equal (satlink::eval-var
;;                      var (aignet->cnf-vals
;;                           vals cnf-vals sat-lits2 aignet))
;;                     (satlink::eval-var
;;                      var (aignet->cnf-vals
;;                           vals cnf-vals sat-lits1 aignet))))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-var)
;;                                    (aignet->cnf-vals)))))

;;   (defthm eval-lit-in-aignet->cnf-vals-of-sat-lit-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-litp lit sat-lits1))
;;              (equal (satlink::eval-lit
;;                      lit (aignet->cnf-vals
;;                           vals cnf-vals sat-lits2 aignet))
;;                     (satlink::eval-lit
;;                      lit (aignet->cnf-vals
;;                           vals cnf-vals sat-lits1 aignet))))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-lit)
;;                                    (aignet->cnf-vals)))))

;;   (defthm eval-clause-in-aignet->cnf-vals-of-sat-lit-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-lit-listp clause sat-lits1))
;;              (equal (satlink::eval-clause
;;                      clause (aignet->cnf-vals
;;                           vals cnf-vals sat-lits2 aignet))
;;                     (satlink::eval-clause
;;                      clause (aignet->cnf-vals
;;                              vals cnf-vals sat-lits1 aignet))))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-clause)
;;                                    (aignet->cnf-vals)))))

;;   (defthm eval-conjunction-in-aignet->cnf-vals-of-sat-lit-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-lit-listp conjunction sat-lits1))
;;              (equal (eval-cube
;;                      conjunction (aignet->cnf-vals
;;                           vals cnf-vals sat-lits2 aignet))
;;                     (eval-cube
;;                      conjunction (aignet->cnf-vals
;;                              vals cnf-vals sat-lits1 aignet))))
;;     :hints(("Goal" :in-theory (e/d (eval-cube)
;;                                    (aignet->cnf-vals)))))

;;   (defthm eval-formula-in-aignet->cnf-vals-of-sat-lit-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-lit-list-listp formula sat-lits1))
;;              (equal (satlink::eval-formula
;;                      formula (aignet->cnf-vals
;;                           vals cnf-vals sat-lits2 aignet))
;;                     (satlink::eval-formula
;;                      formula (aignet->cnf-vals
;;                              vals cnf-vals sat-lits1 aignet))))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-formula)
;;                                    (aignet->cnf-vals)))))


;;   (defthm eval-var-of-aignet->cnf-vals
;;     (implies (sat-varp (satlink::var-fix var) sat-lits)
;;              (equal (satlink::eval-var
;;                      var (aignet->cnf-vals vals cnf-vals sat-lits
;;                                            aignet))
;;                     (aignet-eval-lit
;;                      (sat-var->aignet-lit var sat-lits)
;;                      vals)))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-var)
;;                                    (aignet->cnf-vals)))))

;;   (defun sat-lit->aignet-lit (lit sat-lits)
;;     (declare (xargs :stobjs sat-lits
;;                     :guard (and (sat-lits-sizedp sat-lits)
;;                                 (sat-litp lit sat-lits))
;;                     :guard-hints (("goal" :in-theory (enable sat-varp)))))
;;     (let ((lit1 (sat-var->aignet-lit (satlink::lit->var lit) sat-lits)))
;;       (mk-lit (lit-id lit1) (b-xor (satlink::lit->neg lit)
;;                                    (lit-neg lit1)))))

;;   (defun sat-lits->aignet-lits (lits sat-lits)
;;     (declare (xargs :stobjs sat-lits
;;                     :guard (and (sat-lits-sizedp sat-lits)
;;                                 (sat-lit-listp lits sat-lits))))
;;     (if (atom lits)
;;         nil
;;       (cons (sat-lit->aignet-lit (car lits) sat-lits)
;;             (sat-lits->aignet-lits (cdr lits) sat-lits))))

;;   (defthm eval-lit-of-aignet->cnf-vals
;;     (implies (sat-litp lit sat-lits)
;;              (equal (satlink::eval-lit
;;                      lit (aignet->cnf-vals vals cnf-vals sat-lits
;;                                            aignet))
;;                     (aignet-eval-lit
;;                      (sat-lit->aignet-lit lit sat-lits)
;;                      vals)))
;;     :hints(("Goal" :in-theory (e/d (satlink::eval-lit
;;                                     satlink::eval-var)
;;                                    (aignet->cnf-vals)))))

;;   (defun aignet-vals-conjunction (lits vals)
;;     (declare (xargs :stobjs vals
;;                     :verify-guards nil))
;;     (if (atom lits)
;;         1
;;       (b-and (aignet-eval-lit (car lits) vals)
;;              (aignet-vals-conjunction (cdr lits) vals))))

;;   (defthm eval-cube-of-aignet->cnf-vals
;;     (implies (sat-lit-listp lits sat-lits)
;;              (equal (eval-cube
;;                      lits
;;                      (aignet->cnf-vals vals cnf-vals sat-lits
;;                                        aignet))
;;                     (aignet-vals-conjunction
;;                      (sat-lits->aignet-lits lits sat-lits)
;;                      vals)))
;;     :hints(("Goal" :in-theory (disable aignet->cnf-vals))))

;;   (defthm aignet-lit-listp-of-sat-lits->aignet-lits
;;     (implies (and (sat-lits-wfp sat-lits aignet)
;;                   (sat-lit-listp lits sat-lits))
;;              (aignet-lit-listp (sat-lits->aignet-lits lits sat-lits) aignet)))

;;   (defthm sat-lits->aignet-lits-of-aignet-lits->sat-lits
;;     (implies (and (bind-free '((aignet . aignet)) (aignet))
;;                   (sat-lits-wfp sat-lits aignet)
;;                   (aignet-lits-have-sat-vars lits sat-lits)
;;                   (lit-listp lits))
;;              (equal (sat-lits->aignet-lits
;;                      (aignet-lits->sat-lits
;;                       lits sat-lits)
;;                      sat-lits)
;;                     lits)))

;;   (defthm sat-lits->aignet-lits-of-extension
;;     (implies (and (sat-lit-extension-binding)
;;                   (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-lit-listp lits sat-lits1))
;;              (equal (sat-lits->aignet-lits lits sat-lits2)
;;                     (sat-lits->aignet-lits lits sat-lits1))))

;;   (local (in-theory (disable aignet-eval)))

;;   (defthm aignet->cnf-vals-iter-of-aignet-eval-of-extension
;;     (implies (and (aignet-extension-binding)
;;                   (sat-lits-wfp sat-lits orig)
;;                   (<= n (sat-next-var sat-lits)))
;;              (equal (aignet->cnf-vals-iter
;;                      n
;;                      (aignet-eval vals new)
;;                      cnf-vals sat-lits aignet1)
;;                     (aignet->cnf-vals-iter
;;                      n
;;                      (aignet-eval vals orig)
;;                      cnf-vals sat-lits aignet1)))
;;     :hints((acl2::just-induct-and-expand
;;             (aignet->cnf-vals-iter
;;              n
;;              (aignet-eval vals new)
;;              cnf-vals sat-lits aignet1)
;;             :expand-others
;;             ((:free (vals)
;;               (aignet->cnf-vals-iter
;;                n vals cnf-vals sat-lits aignet1))))))

;;   (defthm aignet->cnf-vals-of-aignet-eval-of-extension
;;     (implies (and (aignet-extension-binding)
;;                   (sat-lits-wfp sat-lits orig))
;;              (equal (aignet->cnf-vals
;;                      (aignet-eval vals new)
;;                      cnf-vals sat-lits aignet1)
;;                     (aignet->cnf-vals
;;                      (aignet-eval vals orig)
;;                      cnf-vals sat-lits aignet1)))))



(local (defthm fanin-count-of-new-stype-in-extension
         (implies (and (aignet-extension-p new orig)
                       (<= (stype-count stype orig) (nfix n))
                       (< (nfix n) (stype-count stype new))
                       (not (equal (ctype stype) (out-ctype))))
                  (< (fanin-count orig)
                     (fanin-count (lookup-stype n stype new))))
         :hints(("Goal" :in-theory (enable lookup-stype fanin-count aignet-extension-p stype-count
                                           fanin-node-p)
                 :induct (lookup-stype n stype new)))))

(defsection cnf->aignet-invals
  ;; BOZO this is probably a good logical definition for this but it might be
  ;; nice to have an exec that iterates over the sat-lits/cnf-vals instead of
  ;; having to skip all the IDs with no sat-vars in vals
  (defiteration cnf->aignet-invals (invals cnf-vals sat-lits aignet)
    (declare (xargs :stobjs (invals cnf-vals sat-lits aignet)
                    :guard (and (sat-lits-wfp sat-lits aignet)
                                (<= (num-ins aignet) (bits-length invals)))))
    (b* ((id (innum->id n aignet))
         ((unless (aignet-id-has-sat-var id sat-lits))
          invals)
         (lit (aignet-id->sat-lit id sat-lits))
         (val (satlink::eval-lit lit cnf-vals)))
      (set-bit n val invals))
    :returns invals
    :iter-guard (<= n (num-ins aignet))
    :last (num-ins aignet))

  (in-theory (disable cnf->aignet-invals))
  (local (in-theory (enable cnf->aignet-invals
                            (:induction cnf->aignet-invals-iter))))

  (defthm nth-of-cnf->aignet-invals-iter
    (equal (nth n (cnf->aignet-invals-iter m invals cnf-vals sat-lits
                                         aignet))
           (b* ((id (innum->id n aignet)))
             (if (and (< (nfix n) (nfix m))
                      (aignet-id-has-sat-var id sat-lits))
                 (satlink::eval-lit
                  (aignet-id->sat-lit id sat-lits)
                  cnf-vals)
               (nth n invals))))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-invals-iter m invals cnf-vals sat-lits aignet))))

  (defthm nth-of-cnf->aignet-invals
    (equal (nth n (cnf->aignet-invals invals cnf-vals sat-lits aignet))
           (if (and (< (nfix n) (num-ins aignet))
                    (aignet-id-has-sat-var (innum->id n aignet) sat-lits))
               (satlink::eval-lit
                (aignet-id->sat-lit (innum->id n aignet) sat-lits)
                cnf-vals)
             (nth n invals))))

  (defthm len-of-cnf->aignet-invals-iter
    (implies (and (<= (num-ins aignet)
                      (bits-length invals))
                  (<= (nfix m) (bits-length invals)))
             (equal (len (cnf->aignet-invals-iter m invals cnf-vals sat-lits aignet))
                    (len invals)))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-invals-iter m invals cnf-vals sat-lits aignet))))

  (defthm len-of-cnf->aignet-invals
    (implies (and (<= (num-ins aignet) (bits-length invals)))
             (equal (len (cnf->aignet-invals invals cnf-vals sat-lits aignet))
                    (len invals))))

  (local (in-theory (disable cnf->aignet-invals)))

  (defthmd cnf->aignet-invals-of-aignet-extension-lemma
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bit-equiv (nth n (cnf->aignet-invals invals cnf-vals sat-lits new))
                        (nth n (cnf->aignet-invals invals cnf-vals sat-lits orig))))
    :hints (("goal" :in-theory (enable
                                aignet-idp
                                sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp
                                lookup-stype-in-bounds
                                lookup-stype-out-of-bounds)
             :cases ((< (nfix n) (num-ins orig))))))

  (local (in-theory (e/d (cnf->aignet-invals-of-aignet-extension-lemma))))

  (defthm cnf->aignet-invals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bits-equiv (cnf->aignet-invals invals cnf-vals sat-lits new)
                         (cnf->aignet-invals invals cnf-vals sat-lits orig)))
    :hints (("goal" :in-theory (enable bits-equiv))))


  (defthm cnf->aignet-invals-of-sat-lit-extension-idempotent
    (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet))
             (let ((invals1 (cnf->aignet-invals
                                  invals cnf-vals sat-lits2 aignet)))
               (bits-equiv (cnf->aignet-invals
                            invals1 cnf-vals sat-lits1 aignet)
                           invals1)))
    :hints(("Goal" :in-theory (enable bits-equiv)))))


(defsection cnf->aignet-regvals
  ;; BOZO this is probably a good logical definition for this but it might be
  ;; nice to have an exec that iterates over the sat-lits/cnf-vals instead of
  ;; having to skip all the IDs with no sat-vars in vals
  (defiteration cnf->aignet-regvals (regvals cnf-vals sat-lits aignet)
    (declare (xargs :stobjs (regvals cnf-vals sat-lits aignet)
                    :guard (and (sat-lits-wfp sat-lits aignet)
                                (<= (num-regs aignet) (bits-length regvals)))))
    (b* ((id (regnum->id n aignet))
         ((unless (aignet-id-has-sat-var id sat-lits))
          regvals)
         (lit (aignet-id->sat-lit id sat-lits))
         (val (satlink::eval-lit lit cnf-vals)))
      (set-bit n val regvals))
    :returns regvals
    :iter-guard (<= n (num-regs aignet))
    :last (num-regs aignet))

  (in-theory (disable cnf->aignet-regvals))
  (local (in-theory (enable cnf->aignet-regvals
                            (:induction cnf->aignet-regvals-iter))))

  (defthm nth-of-cnf->aignet-regvals-iter
    (equal (nth n (cnf->aignet-regvals-iter m regvals cnf-vals sat-lits
                                         aignet))
           (b* ((id (regnum->id n aignet)))
             (if (and (< (nfix n) (nfix m))
                      (aignet-id-has-sat-var id sat-lits))
                 (satlink::eval-lit
                  (aignet-id->sat-lit id sat-lits)
                  cnf-vals)
               (nth n regvals))))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-regvals-iter m regvals cnf-vals sat-lits aignet))))

  (defthm nth-of-cnf->aignet-regvals
    (equal (nth n (cnf->aignet-regvals regvals cnf-vals sat-lits aignet))
           (if (and (< (nfix n) (num-regs aignet))
                    (aignet-id-has-sat-var (regnum->id n aignet) sat-lits))
               (satlink::eval-lit
                (aignet-id->sat-lit (regnum->id n aignet) sat-lits)
                cnf-vals)
             (nth n regvals))))

  (defthm len-of-cnf->aignet-regvals-iter
    (implies (and (<= (num-regs aignet)
                      (bits-length regvals))
                  (<= (nfix m) (bits-length regvals)))
             (equal (len (cnf->aignet-regvals-iter m regvals cnf-vals sat-lits aignet))
                    (len regvals)))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-regvals-iter m regvals cnf-vals sat-lits aignet))))

  (defthm len-of-cnf->aignet-regvals
    (implies (and (<= (num-regs aignet) (bits-length regvals)))
             (equal (len (cnf->aignet-regvals regvals cnf-vals sat-lits aignet))
                    (len regvals))))

  (local (in-theory (disable cnf->aignet-regvals)))

  (defthmd cnf->aignet-regvals-of-aignet-extension-lemma
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bit-equiv (nth n (cnf->aignet-regvals regvals cnf-vals sat-lits new))
                        (nth n (cnf->aignet-regvals regvals cnf-vals sat-lits orig))))
    :hints (("goal" :in-theory (enable
                                aignet-idp
                                sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp
                                lookup-stype-in-bounds
                                lookup-stype-out-of-bounds)
             :cases ((< (nfix n) (num-regs orig))))))

  (local (in-theory (e/d (cnf->aignet-regvals-of-aignet-extension-lemma))))

  (defthm cnf->aignet-regvals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bits-equiv (cnf->aignet-regvals regvals cnf-vals sat-lits new)
                         (cnf->aignet-regvals regvals cnf-vals sat-lits orig)))
    :hints (("goal" :in-theory (enable bits-equiv))))


  (defthm cnf->aignet-regvals-of-sat-lit-extension-idempotent
    (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet))
             (let ((regvals1 (cnf->aignet-regvals
                                  regvals cnf-vals sat-lits2 aignet)))
               (bits-equiv (cnf->aignet-regvals
                            regvals1 cnf-vals sat-lits1 aignet)
                           regvals1)))
    :hints(("Goal" :in-theory (enable bits-equiv)))))

;; (defsection cnf->aignet-vals
;;   ;; BOZO this is probably a good logical definition for this but it might be
;;   ;; nice to have an exec that iterates over the sat-lits/cnf-vals instead of
;;   ;; having to skip all the IDs with no sat-vars in vals
;;   (defiteration cnf->aignet-vals (vals cnf-vals sat-lits aignet)
;;     (declare (xargs :stobjs (vals cnf-vals sat-lits aignet)
;;                     :guard (and (sat-lits-wfp sat-lits aignet)
;;                                 (<= (num-fanins aignet) (bits-length vals)))))
;;     (b* ((id n)
;;          ((unless (aignet-id-has-sat-var id sat-lits))
;;           vals)
;;          (lit (aignet-id->sat-lit id sat-lits))
;;          (val (satlink::eval-lit lit cnf-vals)))
;;       (set-bit n val vals))
;;     :returns vals
;;     :last (num-fanins aignet))

;;   (in-theory (disable cnf->aignet-vals))
;;   (local (in-theory (enable cnf->aignet-vals
;;                             (:induction cnf->aignet-vals-iter))))

;;   (defthm cnf->aignet-vals-iter-normalize-aignet
;;     (implies (syntaxp (not (equal aignet ''nil)))
;;              (equal (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet)
;;                     (cnf->aignet-vals-iter n vals cnf-vals sat-lits nil)))
;;     :hints((acl2::just-induct-and-expand
;;             (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet)
;;             :expand-others
;;             ((:free (aignet)
;;               (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet))))))

;;   (defthm nth-of-cnf->aignet-vals-iter
;;     (equal (nth n (cnf->aignet-vals-iter m vals cnf-vals sat-lits
;;                                          aignet))
;;            (if (and (< (nfix n) (nfix m))
;;                     (aignet-id-has-sat-var n sat-lits))
;;                (satlink::eval-lit
;;                 (aignet-id->sat-lit n sat-lits)
;;                 cnf-vals)
;;              (nth n vals)))
;;     :hints((acl2::just-induct-and-expand
;;             (cnf->aignet-vals-iter m vals cnf-vals sat-lits aignet))))

;;   (defthm nth-of-cnf->aignet-vals
;;     (equal (nth n (cnf->aignet-vals vals cnf-vals sat-lits aignet))
;;            (if (and (aignet-idp n aignet)
;;                     (aignet-id-has-sat-var n sat-lits))
;;                (satlink::eval-lit
;;                 (aignet-id->sat-lit n sat-lits)
;;                 cnf-vals)
;;              (nth n vals)))
;;     :hints(("Goal" :in-theory (enable aignet-idp))))

;;   (defthm len-of-cnf->aignet-vals-iter
;;     (implies (and (<= (nfix (num-fanins aignet))
;;                       (bits-length vals))
;;                   (<= (nfix m) (bits-length vals)))
;;              (equal (len (cnf->aignet-vals-iter m vals cnf-vals sat-lits
;;                                                 aignet))
;;                     (len vals)))
;;     :hints((acl2::just-induct-and-expand
;;             (cnf->aignet-vals-iter m vals cnf-vals sat-lits aignet))))

;;   (defthm len-of-cnf->aignet-vals
;;     (implies (and (<= (nfix (num-fanins aignet))
;;                       (bits-length vals)))
;;              (equal (len (cnf->aignet-vals vals cnf-vals sat-lits
;;                                            aignet))
;;                     (len vals))))

;;   (local (in-theory (disable cnf->aignet-vals)))

;;   (defthmd cnf->aignet-vals-of-aignet-extension-lemma
;;     (implies (and (aignet-extension-binding)
;;                   (sat-lits-wfp sat-lits orig))
;;              (bit-equiv (nth n (cnf->aignet-vals vals cnf-vals sat-lits new))
;;                         (nth n (cnf->aignet-vals vals cnf-vals sat-lits orig))))
;;     :hints (("goal" :in-theory (enable
;;                                 sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp))))

;;   (local (in-theory (e/d (cnf->aignet-vals-of-aignet-extension-lemma))))

;;   (defthm cnf->aignet-vals-of-aignet-extension
;;     (implies (and (aignet-extension-binding)
;;                   (sat-lits-wfp sat-lits orig))
;;              (bits-equiv (cnf->aignet-vals vals cnf-vals sat-lits new)
;;                          (cnf->aignet-vals vals cnf-vals sat-lits orig)))
;;     :hints (("goal" :in-theory (enable bits-equiv))))


;;   (defthm cnf->aignet-vals-of-sat-lit-extension-idempotent
;;     (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
;;                   (sat-lits-wfp sat-lits1 aignet)
;;                   (sat-lits-wfp sat-lits2 aignet))
;;              (let ((aignet-vals1 (cnf->aignet-vals
;;                                   vals cnf-vals sat-lits2 aignet)))
;;                (bits-equiv (cnf->aignet-vals
;;                             aignet-vals1 cnf-vals sat-lits1 aignet)
;;                            aignet-vals1)))
;;     :hints(("Goal" :in-theory (enable bits-equiv)))))

(defsection aignet-agrees-with-cnf

  (defun-sk aignet-agrees-with-cnf (aignet sat-lits cnf-vals)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (aignet-id-has-sat-var id sat-lits))
                     (equal (id-eval id
                                     (cnf->aignet-invals 
                                      invals cnf-vals sat-lits aignet)
                                     (cnf->aignet-regvals 
                                      regvals cnf-vals sat-lits aignet)
                                     aignet)
                            (satlink::eval-lit
                             (aignet-id->sat-lit id sat-lits)
                             cnf-vals))))
    :rewrite :direct)

  (in-theory (disable aignet-agrees-with-cnf))

  (defthm aignet-agrees-with-cnf-of-resize-of-create-sat-lits
;    (implies (aignet-well-formedp aignet)
             (aignet-agrees-with-cnf
              aignet
              (resize-aignet->sat n (create-sat-lits))
              cnf-vals)
    :hints(("Goal" :in-theory (e/d (aignet-agrees-with-cnf
                                    aignet-id-has-sat-var))
            :expand ((:free (invals regvals)
                      (id-eval 0 invals regvals aignet))))))

  (defthm aignet-agrees-with-cnf-of-create-sat-lits
;    (implies (aignet-well-formedp aignet)
             (aignet-agrees-with-cnf
              aignet
              (create-sat-lits)
              cnf-vals)
    :hints(("Goal" :in-theory (e/d (aignet-agrees-with-cnf
                                    aignet-id-has-sat-var))
            :expand ((:free (invals regvals)
                      (id-eval 0 invals regvals aignet))))))



  (defthmd aignet-agrees-with-cnf-of-aignet-extension-lemma
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig)
                  (aignet-agrees-with-cnf
                   orig sat-lits cnf-vals))
             (let ((aignet new))
               (implies (and (aignet-idp id aignet)
                             (aignet-id-has-sat-var id sat-lits))
                        (equal (id-eval id
                                        (cnf->aignet-invals 
                                         invals cnf-vals sat-lits aignet)
                                        (cnf->aignet-regvals 
                                         regvals cnf-vals sat-lits aignet)
                                        aignet)
                               (satlink::eval-lit
                                (aignet-id->sat-lit id sat-lits)
                                cnf-vals)))))
    :hints (("goal" :cases ((aignet-idp id orig))
             :in-theory (e/d
                         (sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)
                         ;; (aignet-vals->invals
                         ;;  aignet-vals->regvals)
                         ))))

  (local (in-theory (enable aignet-agrees-with-cnf-of-aignet-extension-lemma)))

  (defthm aignet-agrees-with-cnf-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig)
                  (aignet-agrees-with-cnf
                   orig sat-lits cnf-vals))
             (aignet-agrees-with-cnf
              new sat-lits cnf-vals))
    :hints(("Goal" :in-theory
            '(aignet-agrees-with-cnf
              aignet-agrees-with-cnf-of-aignet-extension-lemma))))

  (defthm aignet-agrees-with-cnf-with-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (aignet-idp id aignet)
                  (aignet-id-has-sat-var id sat-lits1)
                  (aignet-agrees-with-cnf aignet sat-lits1 cnf-vals))
             (equal (id-eval id
                             (cnf->aignet-invals 
                              invals cnf-vals sat-lits2 aignet)
                             (cnf->aignet-regvals 
                              regvals cnf-vals sat-lits2 aignet)
                             aignet)
                    (satlink::eval-lit
                     (aignet-id->sat-lit id sat-lits1)
                     cnf-vals)))
    :hints (("goal" :use ((:instance aignet-agrees-with-cnf-necc
                           (sat-lits sat-lits1)
                           (invals (cnf->aignet-invals invals cnf-vals sat-lits2 aignet))
                           (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits2 aignet))))
             :in-theory (disable aignet-agrees-with-cnf-necc))))


  ;; (local (in-theory (disable aignet-vals->invals
  ;;                            aignet-vals->regvals)))

  (defthm aignet-eval-conjunction-when-aignet-agrees-with-cnf-with-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (aignet-lit-listp lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits1)
                  (aignet-agrees-with-cnf aignet sat-lits1 cnf-vals))
             (equal (aignet-eval-conjunction
                     lits
                     (cnf->aignet-invals 
                      invals cnf-vals sat-lits2 aignet)
                     (cnf->aignet-regvals 
                      regvals cnf-vals sat-lits2 aignet)
                     aignet)
                    (eval-cube
                     (aignet-lits->sat-lits lits sat-lits1)
                     cnf-vals)))
    :hints(("Goal" :in-theory (enable lit-eval satlink::eval-lit
                                      aignet-eval-conjunction))))

  (defthm lit-eval-when-aignet-agrees-with-cnf-with-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (aignet-litp lit aignet)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits1)
                  (aignet-agrees-with-cnf aignet sat-lits1 cnf-vals))
             (equal (lit-eval
                     lit
                     (cnf->aignet-invals 
                      invals cnf-vals sat-lits2 aignet)
                     (cnf->aignet-regvals 
                      regvals cnf-vals sat-lits2 aignet)
                     aignet)
                    (satlink::eval-lit
                     (aignet-lit->sat-lit lit sat-lits1)
                     cnf-vals)))
    :hints(("Goal" :in-theory (enable lit-eval satlink::eval-lit)))))



(defsection mux-clauses
  (defthmd satlink-eval-lit-of-make-lit-of-lit-var
    (equal (satlink::eval-lit (satlink::make-lit (satlink::lit->var lit) neg) env)
           (b-xor (b-xor (satlink::lit->neg lit) neg)
                  (satlink::eval-lit lit env)))
    :hints(("Goal" :in-theory (enable satlink::eval-lit))))


  (defund mux-add-clauses (res-id c tb fb sat-lits cnf-acc)
    (declare (Xargs :stobjs (sat-lits)
                    :guard (and (natp res-id) (litp c) (litp tb) (litp fb))))
    (b* ((rl (aignet-id->sat-lit res-id sat-lits))
         (cl (aignet-lit->sat-lit c sat-lits))
         (tl (aignet-lit->sat-lit tb sat-lits))
         (fl (aignet-lit->sat-lit fb sat-lits))
         (rlb (satlink::lit-negate rl))
         (clb (satlink::lit-negate cl))
         (tlb (satlink::lit-negate tl))
         (flb (satlink::lit-negate fl)))
      (if (int= tb fb)          ;; fanins are equal
          (list* (list tl rlb)  ;;  tb <-> res
                 (list tlb rl)
                 cnf-acc)
        (list* (list clb tlb rl)     ;;   c &  tb ->  res
               (list cl  flb rl)     ;;  ~c &  fb ->  res
               (list clb tl  rlb)    ;;   c & ~tb -> ~res
               (list cl  fl  rlb)    ;;  ~c & ~fb -> ~res
               (if (int= tb (lit-negate fb))
                   ;; xor, omit last two since they are always satisfied
                   cnf-acc
                 (list* (list tlb flb rl)  ;;  tb &  fb ->  res
                        (list tl  fl  rlb) ;; ~tb & ~fb -> ~res
                        cnf-acc))))))

  (local (in-theory (enable mux-add-clauses)))

  (defthm lit-list-listp-of-mux-add-clauses
    (implies (satlink::lit-list-listp cnf-acc)
             (satlink::lit-list-listp (mux-add-clauses res c tb fb sat-lits cnf-acc))))


  (defthm b-xor-of-b-not
    (and (equal (acl2::b-xor (acl2::b-not x) y)
                (acl2::b-not (acl2::b-xor x y)))
         (equal (acl2::b-xor y (acl2::b-not x))
                (acl2::b-not (acl2::b-xor y x))))
    :hints(("Goal" :in-theory (enable acl2::b-xor acl2::b-not))))

  (local (in-theory (disable satlink::eval-lit)))


  (defthm mux-add-clauses-correct
    (equal (satlink::eval-formula (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
                                  cnf-vals)
           (if (and (equal (satlink::eval-formula orig-cnf cnf-vals) 1)
                    (equal (satlink::eval-lit (aignet-id->sat-lit res-id sat-lits) cnf-vals)
                           (acl2::b-ior
                            (acl2::b-and (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-vals)
                                         (satlink::eval-lit (aignet-lit->sat-lit tb sat-lits) cnf-vals))
                            (acl2::b-and (acl2::b-not (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-vals))
                                         (satlink::eval-lit (aignet-lit->sat-lit fb sat-lits)
                                                            cnf-vals)))))
               1 0))
    :hints (("goal" :in-theory (enable satlink::eval-lit))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior)
                                   (satlink::eval-lit))))))

  (defthm sat-lit-list-listp-of-mux-clauses
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (sat-lit-list-listp orig-cnf sat-lits)
                  (aignet-id-has-sat-var (lit-id c) sat-lits)
                  (aignet-id-has-sat-var (lit-id tb) sat-lits)
                  (aignet-id-has-sat-var (lit-id fb) sat-lits)
                  (aignet-id-has-sat-var id sat-lits))
             (sat-lit-list-listp
              (mux-add-clauses id c tb fb sat-lits orig-cnf)
              sat-lits)))

  (defthm sat-lit-list-listp-of-mux-clauses-bind-free
    (implies (and (bind-free '((aignet . aignet)))
                  (sat-lits-wfp sat-lits aignet)
                  (sat-lit-list-listp orig-cnf sat-lits)
                  (aignet-id-has-sat-var (lit-id c) sat-lits)
                  (aignet-id-has-sat-var (lit-id tb) sat-lits)
                  (aignet-id-has-sat-var (lit-id fb) sat-lits)
                  (aignet-id-has-sat-var id sat-lits))
             (sat-lit-list-listp
              (mux-add-clauses id c tb fb sat-lits orig-cnf)
              sat-lits)))

  (local (in-theory (disable mux-add-clauses)))



  (defthm id-order-of-id-is-mux
    (b* (((mv is-mux c tb fb) (id-is-mux id aignet)))
      (implies is-mux
               (and (< (lit-id c) (nfix id))
                    (< (lit-id tb) (nfix id))
                    (< (lit-id fb) (nfix id)))))
    :hints(("Goal" :in-theory (enable id-is-mux)))
    :rule-classes (:rewrite :linear))


  (defthm id-type-when-is-mux
    (implies (mv-nth 0 (id-is-mux id aignet))
             (equal (ctype (stype (car (lookup-id id aignet))))
                    (gate-ctype)))
    :hints(("Goal" :in-theory (enable id-is-mux))))


  (defthmd mux-add-clauses-normalize-cnf-acc
    (implies (syntaxp (not (equal cnf-acc ''nil)))
             (equal (mux-add-clauses res-id c tb fb sat-lits cnf-acc)
                    (append (mux-add-clauses res-id c tb fb sat-lits nil) cnf-acc)))
    :hints(("Goal" :in-theory (enable mux-add-clauses)))))



(defsection supergate-add-clauses

  (defun supergate-add-clauses1 (lit supergate sat-lits cnf-acc)
    (declare (Xargs :stobjs (sat-lits)
                    :guard (and (litp lit) (lit-listp supergate))))
    (if (atom supergate)
        cnf-acc
      (cons (list (aignet-lit->sat-lit (car supergate) sat-lits)
                  (satlink::lit-negate (aignet-lit->sat-lit lit sat-lits)))
            ;; ~fanin -> ~res
            (supergate-add-clauses1 lit (cdr supergate) sat-lits cnf-acc))))

  (defun supergate-collect-neg-fanins (supergate sat-lits)
    (declare (Xargs :stobjs (sat-lits)
                    :guard (lit-listp supergate)))
    (if (atom supergate)
        nil
      (cons (satlink::lit-negate (aignet-lit->sat-lit (car supergate) sat-lits))
            (supergate-collect-neg-fanins (cdr supergate) sat-lits))))

  (defun supergate-add-clauses (res supergate sat-lits cnf-acc)
    (declare (xargs :stobjs (sat-lits)
                    :guard (and (litp res) (lit-listp supergate))))
    (cons (cons (aignet-lit->sat-lit res sat-lits)
                (supergate-collect-neg-fanins supergate sat-lits))
          (supergate-add-clauses1 res supergate sat-lits cnf-acc)))

  (local (in-theory (disable satlink::eval-lit aignet-lit->sat-lit)))
  (local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                         (satlink::eval-lit-of-make-lit))))

  (defthm lit-list-listp-of-supergate-add-clauses1
    (implies (satlink::lit-list-listp cnf-acc)
             (satlink::lit-list-listp (supergate-add-clauses1 lit supergate sat-lits cnf-acc)))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (defthm lit-listp-of-supergate-collect-neg-fanins
    (satlink::lit-listp (supergate-collect-neg-fanins supergate sat-lits)))

  (defthm lit-list-listp-of-supergate-add-clauses
    (implies (satlink::lit-list-listp cnf-acc)
             (satlink::lit-list-listp (supergate-add-clauses res supergate sat-lits cnf-acc)))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (defthm supergate-add-clauses1-meaning
    (equal (satlink::eval-formula (supergate-add-clauses1
                                   lit supergate sat-lits cnf-acc)
                                  cnf-vals)
           (if (and (equal (satlink::eval-formula cnf-acc cnf-vals) 1)
                    (or (equal (eval-cube
                                (aignet-lits->sat-lits supergate sat-lits)
                                cnf-vals)
                               1)
                        (equal (satlink::eval-lit
                                (aignet-lit->sat-lit lit sat-lits)
                                cnf-vals)
                               0)))
               1 0))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not))))))

  (defthm supergate-collect-neg-fanins-val
    (equal (satlink::eval-clause
            (supergate-collect-neg-fanins
             supergate sat-lits)
            cnf-vals)
           (acl2::b-not (eval-cube
                         (aignet-lits->sat-lits supergate sat-lits)
                         cnf-vals)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::b-and acl2::b-ior acl2::b-not
                                      acl2::b-xor)))))

  (defthm supergate-add-clauses1-sat-lit-list-listp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars supergate sat-lits)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits)
                  (sat-lit-list-listp orig-cnf sat-lits))
             (sat-lit-list-listp (supergate-add-clauses1 lit supergate sat-lits
                                                    orig-cnf)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (defthm supergate-collect-neg-fanins-sat-lit-listp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars supergate sat-lits))
             (sat-lit-listp (supergate-collect-neg-fanins supergate sat-lits)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (local (in-theory (disable supergate-add-clauses1
                             supergate-collect-neg-fanins)))

  (defthm supergate-add-clauses-correct
    (equal (satlink::eval-formula
            (supergate-add-clauses lit supergate sat-lits orig-cnf)
            cnf-vals)
           (if (and (equal (satlink::eval-formula orig-cnf cnf-vals) 1)
                    (equal (satlink::eval-lit (aignet-lit->sat-lit lit sat-lits)
                                         cnf-vals)
                           (eval-cube
                            (aignet-lits->sat-lits supergate sat-lits)
                            cnf-vals)))
               1 0))
    :hints(("Goal" :in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not)
                                   (satlink::eval-lit aignet-lit->sat-lit)))))


  (defthm supergate-add-clauses-sat-lit-list-listp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars supergate sat-lits)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits)
                  (sat-lit-list-listp orig-cnf sat-lits))
             (sat-lit-list-listp (supergate-add-clauses lit supergate sat-lits
                                                        orig-cnf)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (defthm supergate-add-clauses-sat-lit-list-listp-bind-free
    (implies (and (bind-free '((aignet . aignet)))
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars supergate sat-lits)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits)
                  (sat-lit-list-listp orig-cnf sat-lits))
             (sat-lit-list-listp (supergate-add-clauses lit supergate sat-lits
                                                        orig-cnf)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))


  (defthmd supergate-add-clauses1-normalize-cnf-acc
    (implies (syntaxp (not (equal cnf-acc ''nil)))
             (equal (supergate-add-clauses1 lit supergate sat-lits cnf-acc)
                    (append (supergate-add-clauses1 lit supergate sat-lits nil) cnf-acc)))
    :hints(("Goal" :in-theory (enable supergate-add-clauses1))))

  (defthmd supergate-add-clauses-normalize-cnf-acc
    (implies (syntaxp (not (equal cnf-acc ''nil)))
             (equal (supergate-add-clauses res supergate sat-lits cnf-acc)
                    (append (supergate-add-clauses res supergate sat-lits nil) cnf-acc)))
    :hints(("Goal" :in-theory (enable supergate-add-clauses1-normalize-cnf-acc))))

  (local (in-theory (disable supergate-add-clauses))))

(defsection lits-max-id-val-supergate
  (local (in-theory (enable lits-max-id-val)))
  (defthmd lits-max-id-val-of-supergate
    (<= (lits-max-id-val (mv-nth 0 (lit-collect-supergate
                                    lit top use-muxes limit supergate aignet-refcounts aignet)))
        (max (lit-id lit)
             (lits-max-id-val supergate)))
    :hints(("Goal" :in-theory (enable lit-collect-supergate))))


  ;; measure decreases on children of a supergate
  (defthm supergate-decr-top
    (implies (and (int= (id->type id aignet) (gate-type))
                  (not (and (or use-muxes
                                (eql (id->regp id aignet) 1))
                            (mv-nth 0 (id-is-mux id aignet))))
                  (not (zp limit)))
             (< (lits-max-id-val (mv-nth 0 (lit-collect-supergate
                                            (mk-lit id 0)
                                            t use-muxes limit nil aignet-refcounts aignet)))
                (nfix id)))
    :hints (("goal" :expand ((:free (use-muxes)
                              (lit-collect-supergate
                               (mk-lit id 0)
                               t use-muxes limit nil aignet-refcounts aignet)))
             :use ((:instance lits-max-id-val-of-supergate
                    (lit (gate-id->fanin0 id aignet))
                    (top nil)
                    (supergate nil))
                   (:instance lits-max-id-val-of-supergate
                    (lit (gate-id->fanin1 id aignet))
                    (top nil)
                    (supergate (mv-nth 0 (lit-collect-supergate
                                          (gate-id->fanin0 id aignet)
                                          nil use-muxes limit nil aignet-refcounts aignet)))
                    (limit (mv-nth 1 (lit-collect-supergate
                                      (gate-id->fanin0 id aignet)
                                      nil use-muxes limit nil aignet-refcounts aignet)))))
             :in-theory (e/d () (lits-max-id-val-of-supergate)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (id-is-mux)
                                   (id-type-when-is-mux)))))
    :rule-classes (:rewrite :linear)))


(defines aignet-lit->cnf
  :prepwork ((local (defthm aignet-lit-listp-implies-cdr
                      (implies (aignet-lit-listp x aignet)
                               (aignet-lit-listp (cdr x) aignet))))
             (local (defthm aignet-lit-listp-implies-aignet-litp-car
                      (implies (and (aignet-lit-listp x aignet)
                                    (consp x))
                               (aignet-litp (car x) aignet))))
             (local (defthm aignet-lit-listp-of-nil
                      (aignet-lit-listp nil aignet)))
             (local (in-theory (disable satlink::lit-listp-of-car-when-lit-list-listp
                                        acl2::consp-append
                                        ;; fanin-if-co-when-output
                                        lookup-id-out-of-bounds
                                        default-car
                                        not
                                        sat-lit-listp
                                        aignet-lit-listp
                                        satlink::equal-of-lit-negate-cond-component-rewrites
                                        satlink::equal-of-lit-negate-component-rewrites
                                        ;; fanin-if-co-id-lte-fanin-count-strong
                                        fanin-count-of-atom
                                        acl2::true-listp-append)))
             (local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                                    (satlink::eval-lit-of-make-lit)))))
  (define aignet-lit->cnf ((x litp           "Literal to encode in the CNF")
                           (use-muxes        "Flag saying whether to recognize muxes and encode them specially")
                           (aignet-refcounts "Reference counts of aignet nodes")
                           (sat-lits         "Records assignment of SAT variables to aignet nodes")
                           (aignet           "AIG network")
                           (cnf              "Accumulated formula"))
    :guard (and (< (lit-id x) (u32-length aignet-refcounts))
                (fanin-litp x aignet)
                (sat-lits-wfp sat-lits aignet))
    :returns (mv (new-sat-lits (implies (sat-lits-wfp sat-lits aignet)
                                        (sat-lits-wfp new-sat-lits aignet))
                               "Updated assignment of SAT variables to aignet nodes")
                 (new-cnf      "CNF with additional clauses for the fanin cone of @('x')."))
    :verify-guards nil
    :flag lit
    :measure (acl2::two-nats-measure (lit-id x) 0)
    :parents (aignet-cnf)
    :short "Add clauses encoding the fanin cone of literal @('x') of the aignet to the cnf."
    :long "<p>Assumes that aignet nodes that have SAT variables assigned in
@('sat-lits') already have their fanin cones encoded, and maintains that invariant.</p>"
    (b* ((id (lit-id x))
         ((when (aignet-id-has-sat-var id sat-lits))
          ;; already added, so done
          (mv sat-lits cnf))
         ((when (int= (id->type id aignet) (in-type)))
          ;; input: add variable but no clauses, so it's free
          (b* ((sat-lits
                (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet)))
            (mv sat-lits cnf)))
         ((unless (int= (id->type id aignet) (gate-type)))
          ;; constant, add variable and a unary clause setting the ID to false
          (b* ((sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits
                                             aignet))
               (sat-lit (aignet-id->sat-lit id sat-lits)))
            (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
         ;; now we have a gate node -- check first for a mux if we're doing that
         ;; if it's an xor, we say it's a mux regardless
         ((mv muxp c tb fb) (if (or use-muxes (eql 1 (id->regp id aignet)))
                                (id-is-mux id aignet)
                              (mv nil nil nil nil)))
         ((when muxp)
          ;; recur on the three children, add the node, add the mux clauses
          (b* (((mv sat-lits cnf)
                (aignet-lit->cnf c use-muxes aignet-refcounts sat-lits aignet cnf))
               ((mv sat-lits cnf)
                (aignet-lit->cnf tb use-muxes aignet-refcounts sat-lits aignet cnf))
               ((mv sat-lits cnf)
                (aignet-lit->cnf fb use-muxes aignet-refcounts sat-lits aignet cnf))
               (sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet))
               (cnf (mux-add-clauses id c tb fb sat-lits cnf)))
            (mv sat-lits cnf)))
         (lit (mk-lit id 0))
         ((mv supergate &)
          (lit-collect-supergate
           lit t use-muxes
           1000 ;; size limit -- bozo make configurable
           nil aignet-refcounts aignet))
         ((when (member 0 supergate))
          ;; one of the fanins is const 0, so the node is const 0
          (b* ((sat-lits (sat-add-aignet-lit lit sat-lits aignet))
               (sat-lit (aignet-id->sat-lit id sat-lits)))
            (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
         ;; recur on the children of the supergate, add the parent literal,
         ;; add the supergate clauses.
         ((mv sat-lits cnf)
          (aignet-lit-list->cnf supergate use-muxes aignet-refcounts sat-lits aignet cnf))
         (sat-lits (sat-add-aignet-lit lit sat-lits aignet))
         (cnf (supergate-add-clauses
               lit supergate sat-lits cnf)))
      (mv sat-lits cnf)))

  (define aignet-lit-list->cnf ((x lit-listp)
                                (use-muxes)
                                (aignet-refcounts)
                                (sat-lits)
                                (aignet)
                                (cnf))
    :guard (and (< (lits-max-id-val x) (u32-length aignet-refcounts))
                (aignet-lit-listp x aignet)
                (sat-lits-wfp sat-lits aignet))
    :returns (mv (new-sat-lits (implies (sat-lits-wfp sat-lits aignet)
                                        (sat-lits-wfp new-sat-lits aignet)))
                 (new-cnf))
    :measure (acl2::two-nats-measure (lits-max-id-val x) (+ 1 (len x)))
    :flag list
    (if (atom x)
        (mv sat-lits cnf)
      (b* (((mv sat-lits cnf)
            (aignet-lit->cnf (car x) use-muxes aignet-refcounts sat-lits aignet cnf)))
        (aignet-lit-list->cnf (cdr x) use-muxes aignet-refcounts sat-lits aignet
                              cnf))))


  ///
  (in-theory (disable aignet-lit->cnf aignet-lit-list->cnf))

  (std::defret-mutual sat-lit-extension-p-of-aignet-lit->cnf
    (defret sat-lit-extension-p-of-aignet-lit->cnf
      (sat-lit-extension-p new-sat-lits sat-lits)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->cnf)
    (defret sat-lit-extension-p-of-aignet-lit-list->cnf
      (sat-lit-extension-p new-sat-lits sat-lits)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->cnf))

  (local (defthm lit-listp-true-listp
           (implies (lit-listp x) (true-listp x))))
  ;; that's all we need for verifying the guards...
  (verify-guards aignet-lit->cnf)

  ;; hints to be used in flag proofs to expand aignet-lit->cnf/aignet-lit-list->cnf
  (local (defmacro expand-aignet-lit->cnf-flg (&key free)
           `(flag::flag-hint-cases
             (lit `(:expand ((:free (use-muxes . ,',free)
                              (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits
                                            aignet cnf)))))
             (list
              `(:expand ((:free (use-muxes . ,',free)
                          (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits
                                             aignet cnf))
                         (:free (use-muxes . ,',free)
                          (aignet-lit-list->cnf nil use-muxes aignet-refcounts sat-lits
                                             aignet cnf))))))))


  ;; For rewrite rules where the AIGNET variable(s) in the LHS are irrelevant, we
  ;; need to bind AIGNET as a free variable to establhish sat-lits-wfp.  Since we
  ;; are not modifying AIGNET here, we want to just always use AIGNET itself as the
  ;; binding.
  (local (DEFTHM SAT-LITS-WFP-IMPLIES-LOOKUP-AIGNET-ID-bind-free
           (IMPLIES (AND (bind-free '((aignet . aignet)))
                         (SAT-LITS-WFP SAT-LITS AIGNET)
                         (AIGNET-IDP N AIGNET)
                         (AIGNET-ID-HAS-SAT-VAR N SAT-LITS))
                    (AND
                     (EQUAL (SAT-VAR->AIGNET-LIT
                             (satlink::lit->var (AIGNET-ID->SAT-LIT N SAT-LITS))
                             SAT-LITS)
                            (MK-LIT
                             N
                             (satlink::LIT->NEG (AIGNET-ID->SAT-LIT N SAT-LITS))))
                     (SAT-VARP (satlink::lit->var (AIGNET-ID->SAT-LIT N SAT-LITS))
                               SAT-LITS)))))

  (local (in-theory (disable supergate-add-clauses
                             mux-add-clauses)))

  (local (in-theory (enable aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)))

  (encapsulate nil
    (local (defun concl-formula (fn)
             `(implies (syntaxp (not (equal cnf ''nil)))
                       (b* (((mv new-sat-lits new-cnf)
                             (,fn x use-muxes aignet-refcounts sat-lits aignet cnf))
                            ((mv new-sat-lits2 new-cnf2)
                             (,fn x use-muxes aignet-refcounts sat-lits aignet nil)))
                         (and (equal new-sat-lits new-sat-lits2)
                              (equal new-cnf (append new-cnf2 cnf)))))))
    (local
     (make-event
      `(defun-sk aignet-lit->cnf-normalize-cnf-req
         (x use-muxes aignet-refcounts sat-lits aignet)
         (forall (cnf)
                 ,(concl-formula 'aignet-lit->cnf))
         :rewrite :direct)))
    (local
     (make-event
      `(defun-sk aignet-lit-list->cnf-normalize-cnf-req
         (x use-muxes aignet-refcounts sat-lits aignet)
         (forall (cnf)
                 ,(concl-formula 'aignet-lit-list->cnf))
         :rewrite :direct)))

    (local (in-theory (disable aignet-lit->cnf-normalize-cnf-req
                               aignet-lit-list->cnf-normalize-cnf-req)))

    (local
     (std::defret-mutual aignet-lit->cnf-normalize-cnf-lemma
       (defret aignet-lit->cnf-normalize-cnf-lemma
         (aignet-lit->cnf-normalize-cnf-req x use-muxes aignet-refcounts sat-lits aignet)
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))
                                 (:free (use-muxes cnf) <call>))
                        :in-theory (enable supergate-add-clauses-normalize-cnf-acc
                                           mux-add-clauses-normalize-cnf-acc))))
         :fn aignet-lit->cnf)
       (defret aignet-lit-list->cnf-normalize-cnf-lemma
         (aignet-lit-list->cnf-normalize-cnf-req x use-muxes aignet-refcounts sat-lits aignet)
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))
                                 (:free (use-muxes cnf) <call>)))))
         :fn aignet-lit-list->cnf)))

    (make-event
     `(defthm aignet-lit->cnf-normalize-cnf
        ,(concl-formula 'aignet-lit->cnf)))

    (make-event
     `(defthm aignet-lit-list->cnf-normalize-cnf
        ,(concl-formula 'aignet-lit-list->cnf))))

  ;; two results: CNF generated satisfies sat-lit-list-listp, and the top-level
  ;; arguments get sat variables.
  (std::defret-mutual good-cnf-of-aignet-lit->cnf
    (defret good-cnf-of-aignet-lit->cnf
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (aignet-litp x aignet))
                 (and (implies (sat-lit-list-listp cnf sat-lits)
                               (sat-lit-list-listp new-cnf new-sat-lits))
                      (aignet-id-has-sat-var (lit-id x) new-sat-lits)))
      :fn aignet-lit->cnf)
    (defret good-cnf-of-aignet-lit-list->cnf
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (aignet-lit-listp x aignet))
               (and (implies (sat-lit-list-listp cnf sat-lits)
                             (sat-lit-list-listp new-cnf new-sat-lits))
                    (aignet-lits-have-sat-vars x new-sat-lits)))
      :fn aignet-lit-list->cnf)
    :hints ((expand-aignet-lit->cnf-flg)
            (and stable-under-simplificationp
                 '(:expand ((:free (a b sat-lits) (sat-lit-listp
                                                   (cons a b) sat-lits))
                            (:free (sat-lits) (sat-lit-listp nil sat-lits))
                            ;; (:free (a b aignet) (aignet-lit-listp
                            ;;                        (cons a b) aignet))
                            ;; (:free (aignet) (aignet-lit-listp nil aignet))
                            (:free (a b sat-lits) (sat-lit-list-listp
                                                   (cons a b) sat-lits))
                            (:free (sat-lits) (sat-lit-list-listp nil sat-lits)))))))

  (defret good-cnf-of-aignet-lit->cnf-rw
    (implies (and (equal (lit-id x1) (lit-id x))
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp x aignet))
             (aignet-id-has-sat-var (lit-id x1) new-sat-lits))
    :hints (("goal" :use ((:instance good-cnf-of-aignet-lit->cnf))
             :in-theory (disable good-cnf-of-aignet-lit->cnf)))
    :fn aignet-lit->cnf)

  (std::defret-mutual lit-list-listp-of-aignet-lit->cnf
    (defret lit-list-listp-of-aignet-lit->cnf
      (implies (satlink::lit-list-listp cnf)
               (satlink::lit-list-listp new-cnf))
      :fn aignet-lit->cnf)
    (defret lit-list-listp-of-aignet-lit-list->cnf
      (b* (((mv ?sat-lits1 cnf1)
            (aignet-lit-list->cnf x use-muxes
                                  aignet-refcounts sat-lits aignet cnf)))
        (implies (satlink::lit-list-listp cnf)
                 (satlink::lit-list-listp cnf1)))
      :fn aignet-lit-list->cnf)
    :hints ((expand-aignet-lit->cnf-flg)))

  ;; Can't satisfy the generated CNF unless the original CNF is satisfied.
  (std::defret-mutual aignet-lit->cnf-cnf-satisfied-implies-orig-cnf-satisfied
    (defret aignet-lit->cnf-cnf-satisfied-implies-orig-cnf-satisfied
      (and (implies (equal (satlink::eval-formula cnf cnf-vals) 0)
                    (equal (satlink::eval-formula new-cnf cnf-vals) 0))
           (implies (not (equal (satlink::eval-formula cnf cnf-vals) 1))
                    (not (equal (satlink::eval-formula new-cnf cnf-vals) 1))))
      :rule-classes (:rewrite
                     (:forward-chaining
                      :corollary
                      (implies (equal (satlink::eval-formula new-cnf cnf-vals) 1)
                               (equal (satlink::eval-formula cnf cnf-vals) 1))))
      :fn aignet-lit->cnf)
    (defret aignet-lit-list->cnf-cnf-satisfied-implies-orig-cnf-satisfied
      (and (implies (equal (satlink::eval-formula cnf cnf-vals) 0)
                    (equal (satlink::eval-formula new-cnf cnf-vals) 0))
           (implies (not (equal (satlink::eval-formula cnf cnf-vals) 1))
                    (not (equal (satlink::eval-formula new-cnf cnf-vals) 1))))
      :rule-classes (:rewrite
                     (:forward-chaining
                      :corollary
                      (implies (equal (satlink::eval-formula new-cnf cnf-vals) 1)
                               (equal (satlink::eval-formula cnf cnf-vals) 1))))
      :fn aignet-lit-list->cnf)
    :hints ((expand-aignet-lit->cnf-flg)))


  ;; (local (in-theory (disable aignet-vals->regvals
  ;;                            aignet-vals->invals)))

  ;; A few lemmas for the final couple of theorems.
  (local (defthmd b-and-equal-1
           (equal (equal (b-and x y) 1)
                  (and (equal x 1)
                       (equal y 1)))
           :hints(("Goal" :in-theory (enable b-and)))))

  (local (defthm b-not-equal-1
           (equal (equal (b-not x) 1)
                  (not (equal x 1)))
           :hints(("Goal" :in-theory (enable b-not)))))

  (local (in-theory (enable equal-1-by-bitp)))

  (local (encapsulate nil

           (defthm lemma1
             (implies (and (equal (lit-id x) (nfix id))
                           (aignet-litp x aignet)
                           (not (equal (id->type id aignet) (gate-type)))
                           (not (equal (id->type id aignet) (in-type))))
                      (equal (id-eval id invals regvals aignet) 0))
             :hints(("Goal"
                     :expand ((id-eval id invals regvals aignet)
                              (id-eval (lit-id x) invals regvals aignet)))))

           (defthm lemma2
             (implies (and (aignet-litp x aignet)
                           (not (equal (id->type (lit-id x) aignet) (gate-type)))
                           (not (equal (id->type (lit-id x) aignet) (in-type))))
                      (equal (id-eval (lit-id x) invals regvals aignet) 0))
             :hints(("Goal"
                     :expand ((id-eval id invals regvals aignet)
                              (id-eval (lit-id x) invals regvals aignet)))))))


  (defthmd eval-cube-when-aignet-vals-agree
    (implies (and (aignet-agrees-with-cnf
                   aignet sat-lits cnf-vals)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-lit-listp lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (equal (aignet-eval-conjunction
                     lits
                     (cnf->aignet-invals 
                      invals cnf-vals sat-lits aignet)
                     (cnf->aignet-regvals 
                      regvals cnf-vals sat-lits aignet)
                     aignet)
                    (eval-cube
                     (aignet-lits->sat-lits lits sat-lits)
                     cnf-vals)))
    :hints(("Goal" :in-theory (e/d (lit-eval
                                    ;; aignet-lit-listp
                                    aignet-eval-conjunction
                                    satlink::eval-lit)))))


  (defthmd collect-supergate-correct-rw
    (implies (and
              ;; this hyp isn't logically necessary but just helps us bind the free vars
              (not (member-equal 0 (mv-nth 0 (lit-collect-supergate
                                              (mk-lit id 0) top use-muxes limit nil
                                              aignet-refcounts aignet))))
              (aignet-litp (mk-lit id 0) aignet))
             (equal (id-eval id invals regvals aignet)
                    (aignet-eval-conjunction
                     (mv-nth 0 (lit-collect-supergate
                                (mk-lit id 0) top use-muxes limit nil
                                aignet-refcounts aignet))
                     invals regvals aignet)))
    :hints (("goal" :in-theory (enable lit-eval collect-supergate-correct
                                       aignet-eval-conjunction))))

  (defthmd collect-supergate-correct-rw-when-0
    (implies (and (member-equal 0 (mv-nth 0 (lit-collect-supergate
                                             (mk-lit id 0) top use-muxes 1000 nil
                                             aignet-refcounts aignet)))
                  (aignet-litp (mk-lit id 0) aignet))
             (equal (id-eval id invals regvals aignet)
                    0))
    :hints (("goal" :use ((:instance collect-supergate-correct
                           (lit (mk-lit id 0))
                           (supergate nil)
                           (limit 1000)))
             :in-theory (e/d (lit-eval
                              aignet-eval-conjunction)
                             (collect-supergate-correct)))))

  (local (in-theory (e/d ()
                         (collect-supergate-correct))))


  (local (defthm aignet-litp-of-mk-lit-when-nat-equiv
           (implies (and (equal (nfix id) (lit-id x))
                         (aignet-litp x aignet))
                    (aignet-litp (mk-lit id neg) aignet))))

  (local (defthm aignet-idp-of-when-nat-equiv
           (implies (and (equal (nfix id) (lit-id x))
                         (aignet-litp x aignet))
                    (aignet-idp id aignet))
           :hints(("Goal" :in-theory (e/d (aignet-idp))))))
  (defthm aignet-agrees-with-cnf-of-add-input
    (implies (and (aignet-agrees-with-cnf aignet sat-lits cnf-vals)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp (mk-lit id neg) aignet)
                  (equal (id->type id aignet) (in-type)))
             (aignet-agrees-with-cnf
              aignet (sat-add-aignet-lit (mk-lit id neg) sat-lits aignet)
              cnf-vals))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (b* ((witness-terms
                       (acl2::find-calls-lst
                        'aignet-agrees-with-cnf-witness
                        clause))
                      ((unless witness-terms)
                       nil)
                      (wit (car witness-terms))
                      (alist
                       `(((mv-nth '0 ,wit) . id-wit)
                         ((mv-nth '1 ,wit) . vals-wit)
                         ((mv-nth '2 ,wit) . invals-wit)
                         ((mv-nth '3 ,wit) . regvals-wit))))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause ',alist))))
            (and stable-under-simplificationp
                 '(:cases ((aignet-id-has-sat-var
                            id-wit sat-lits))
                   :in-theory (enable
                               aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)))
            (and stable-under-simplificationp
                 '(:expand ((:free (invals regvals) (id-eval id invals regvals aignet))
                            (:free (invals regvals) (id-eval id invals regvals aignet)))))))

  ;; Direction 1: aignet-agrees-with-cnf is preserved for satisfying
  ;; cnf-vals.
  (std::defret-mutual aignet-lit->cnf-preserves-aignet-agrees-with-cnf
    (defret aignet-lit->cnf-preserves-aignet-agrees-with-cnf
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (aignet-litp x aignet)
                    (equal (satlink::eval-formula new-cnf cnf-vals) 1)
                    (aignet-agrees-with-cnf aignet sat-lits cnf-vals))
               (aignet-agrees-with-cnf
                aignet new-sat-lits cnf-vals))
      :fn aignet-lit->cnf)
    (defret aignet-lit-list->cnf-preserves-aignet-agrees-with-cnf
      (implies (and (aignet-lit-listp x aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (equal (satlink::eval-formula new-cnf cnf-vals) 1)
                    (aignet-agrees-with-cnf aignet sat-lits cnf-vals))
               (aignet-agrees-with-cnf
                aignet new-sat-lits cnf-vals))
      :fn aignet-lit-list->cnf)
    :hints ((expand-aignet-lit->cnf-flg)
            '(:do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable lit-eval)))
            (and stable-under-simplificationp
                 (b* ((witness-terms
                       (acl2::find-calls-lst
                        'aignet-agrees-with-cnf-witness
                        clause))
                      ((unless witness-terms)
                       nil)
                      (wit (car witness-terms))
                      (alist
                       `(((mv-nth '0 ,wit) . id-wit)
                         ((mv-nth '1 ,wit) . vals-wit)
                         ((mv-nth '2 ,wit) . invals-wit)
                         ((mv-nth '3 ,wit) . regvals-wit))))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause ',alist))))
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               eval-cube-when-aignet-vals-agree
                               collect-supergate-correct-rw
                               collect-supergate-correct-rw-when-0
                               id-eval-when-id-is-mux)))))


  ;; (local (in-theory (disable aignet-eval)))

  (local (in-theory (enable lit-eval)))

  (defthmd sat-lit-listp-of-aignet-lits->sat-lits-rw
    (implies (and (bind-free '((aignet . aignet)) (aignet))
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (sat-lit-listp (aignet-lits->sat-lits lits sat-lits)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (local (in-theory (enable sat-lit-listp-of-aignet-lits->sat-lits-rw)))

  ;; (defthm aignet-vals-conjunction-of-aignet-eval
  ;;   (implies (aignet-lit-listp lits aignet)
  ;;            (equal (aignet-vals-conjunction
  ;;                    lits (aignet-eval vals aignet))
  ;;                   (aignet-eval-conjunction
  ;;                    lits
  ;;                    (aignet-vals->invals nil vals aignet)
  ;;                    (aignet-vals->regvals nil vals aignet)
  ;;                    aignet)))
  ;;   :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (local (in-theory (disable
                     AIGNET-LIT->CNF-CNF-SATISFIED-IMPLIES-ORIG-CNF-SATISFIED
                     sat-varp-when-varp
                     sat-lit-listp
                     sat-lit-list-listp)))

  (defthm mux-add-clauses-correct-rw1
    (equal (equal (satlink::eval-formula
                   (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
                   cnf-vals)
                  0)
           (not (and (equal (satlink::eval-formula orig-cnf cnf-vals) 1)
                     (equal (satlink::eval-lit (aignet-id->sat-lit res-id sat-lits)
                                               cnf-vals)
                            (b-ior
                             (b-and
                              (satlink::eval-lit (aignet-lit->sat-lit c sat-lits)
                                                 cnf-vals)
                              (satlink::eval-lit (aignet-lit->sat-lit tb sat-lits)
                                                 cnf-vals))
                             (b-and
                              (b-not
                               (satlink::eval-lit (aignet-lit->sat-lit c sat-lits)
                                                  cnf-vals))
                              (satlink::eval-lit (aignet-lit->sat-lit fb sat-lits)
                                                 cnf-vals))))))))

  (local (in-theory (disable mux-add-clauses-correct)))
  (local (in-theory (enable aignet-eval-conjunction)))

  (defthm sat-lit-list-listp-of-nil
    (sat-lit-list-listp nil sat-lits)
    :hints(("Goal" :in-theory (enable sat-lit-list-listp))))

  (defthm sat-lit-list-listp-of-append
    (implies (and (sat-lit-list-listp x sat-lits)
                  (sat-lit-list-listp y sat-lits))
             (sat-lit-list-listp (append x y) sat-lits))
    :hints(("Goal" :in-theory (enable sat-lit-list-listp))))

  (std::defret-mutual aignet-lit->cnf-satisfiable
    (defret aignet-lit->cnf-satisfiable
      (b* ((cnf-vals (aignet->cnf-vals
                      invals regvals
                      cnf-vals new-sat-lits aignet)))
        (implies (and (sat-lits-wfp sat-lits aignet)
                      (aignet-litp x aignet)
                      (sat-lit-list-listp cnf sat-lits)
                      (equal (satlink::eval-formula cnf cnf-vals) 1))
                 (equal (satlink::eval-formula new-cnf cnf-vals) 1)))
      :fn aignet-lit->cnf)
    (defret aignet-lit-list->cnf-satisfiable
      (b* ((cnf-vals (aignet->cnf-vals
                      invals regvals
                      cnf-vals new-sat-lits aignet)))
        (implies (and (sat-lits-wfp sat-lits aignet)
                      (aignet-lit-listp x aignet)
                      (sat-lit-list-listp cnf sat-lits)
                      (equal (satlink::eval-formula cnf cnf-vals) 1))
                 (equal (satlink::eval-formula new-cnf cnf-vals) 1)))
      :fn aignet-lit-list->cnf)
    :hints ((expand-aignet-lit->cnf-flg)
            '(:do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable collect-supergate-correct
                                      collect-supergate-correct-rw-when-0
                                      id-eval-when-id-is-mux)))))

  (local (defthm cdr-of-lit-list-fix
           (equal (cdr (lit-list-fix x))
                  (lit-list-fix (cdr x)))))

  (local (defthm car-of-lit-list-fix
           (implies (consp x)
                    (equal (car (lit-list-fix x))
                           (lit-fix (car x))))))

  (fty::deffixequiv-mutual aignet-lit->cnf))
      
                

(defsection cnf-for-aignet
  ;; This is the critical invariant for CNF generation.  We show that
  ;;  - cnf-for-aignet holds of an empty cnf/sat-lits
  ;;  - it is preserved by aignet-lit->cnf
  ;;  - it is preserved by aignet extensions
  ;;  - it implies that we can translate satisfying assignments to/from aig evaluations.

  ;; This isn't quite the whole invariant, but the other parts are basic
  ;; well-formedness stuff -- the CNF contains valid sat variables according to
  ;; sat-lits; sat-lits is well-formed; aignet is well-formed.

  (defun-sk cnf-for-aignet (aignet cnf sat-lits)
    (forall (invals regvals cnf-vals)
            (and (implies (equal (satlink::eval-formula cnf cnf-vals) 1)
                          (aignet-agrees-with-cnf
                           aignet sat-lits cnf-vals))
                 (equal (satlink::eval-formula
                         cnf
                         (aignet->cnf-vals
                          invals regvals cnf-vals sat-lits aignet))
                        1)))
    :rewrite :direct)

  (in-theory (disable cnf-for-aignet))

  (defthm cnf-for-aignet-of-resize-of-create
    (cnf-for-aignet aignet nil (resize-aignet->sat n (create-sat-lits)))
    :hints(("Goal" :in-theory (enable cnf-for-aignet))))

  (defthm cnf-for-aignet-of-create-sat-lits
    (cnf-for-aignet aignet nil (create-sat-lits))
    :hints(("Goal" :in-theory (enable cnf-for-aignet))))

  ; (local (in-theory (disable aignet-eval)))

  (defthm cnf-for-aignet-preserved-by-aignet-lit->cnf
    (b* (((mv new-sat-lits new-cnf)
          (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
      (implies (and (cnf-for-aignet aignet cnf sat-lits)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-litp x aignet)
                    (sat-lit-list-listp cnf sat-lits))
               (cnf-for-aignet aignet new-cnf new-sat-lits)))
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            ;; (and stable-under-simplificationp
            ;;      (b* ((witness-terms
            ;;            (acl2::find-calls-lst
            ;;             'cnf-for-aignet
            ;;             clause))
            ;;           ((unless witness-terms)
            ;;            nil)
            ;;           (wit (car witness-terms))
            ;;           (alist
            ;;            `(((mv-nth '0 ,wit) . invals)
            ;;              ((mv-nth '1 ,wit) . regvals)
            ;;              ((mv-nth '2 ,wit) . cnf-vals)
            ;;              ((mv-nth '3 ,wit) . ))))
            ;;        `(:clause-processor
            ;;          (acl2::simple-generalize-cp
            ;;           clause ',alist))))
            ))

  (defthm cnf-for-aignet-preserved-by-aignet-lit-list->cnf
    (b* (((mv new-sat-lits new-cnf)
          (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
      (implies (and (cnf-for-aignet aignet cnf sat-lits)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-lit-listp x aignet)
                    (sat-lit-list-listp cnf sat-lits))
               (cnf-for-aignet aignet new-cnf new-sat-lits)))
    :hints (("goal" :do-not-induct t
             :in-theory (disable aignet-lit-list->cnf-normalize-cnf))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm cnf-for-aignet-preserved-by-aignet-lit->cnf-normalized
    (b* (((mv new-sat-lits new-cnf)
          (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet nil)))
      (implies (and (cnf-for-aignet aignet cnf sat-lits)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-litp x aignet)
                    (sat-lit-list-listp cnf sat-lits))
               (cnf-for-aignet aignet (append new-cnf cnf) new-sat-lits)))
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm cnf-for-aignet-preserved-by-aignet-extension
    (implies (and (aignet-extension-binding)
                  (cnf-for-aignet orig cnf sat-lits)
                  (sat-lits-wfp sat-lits orig))
             (cnf-for-aignet new cnf sat-lits))
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))
    :otf-flg t)


  ;; (local (in-theory (disable aignet-invals->vals
  ;;                            aignet-regvals->vals)))

  ;; When cnf-for-aignet holds and a cube of literals are all marked, a
  ;; satisfying assignment of the CNF + cube literals gives a satisfying
  ;; evaluation of the cube.
  (defthm cnf-for-aignet-implies-cube-sat-when-cnf-sat
    (b* ((invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
         (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits aignet)))
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (cnf-for-aignet aignet cnf sat-lits)
                    (aignet-lit-listp cube aignet)
                    (aignet-lits-have-sat-vars cube sat-lits)
                    (equal 1 (satlink::eval-formula cnf cnf-vals)))
               (equal (aignet-eval-conjunction
                       cube invals regvals aignet)
                      (eval-cube
                       (aignet-lits->sat-lits cube sat-lits)
                       cnf-vals))))
    :hints(("Goal" :in-theory (enable lit-eval
                                      satlink::eval-lit
                                      aignet-eval-conjunction))))

  ;; And vice versa.
  (defthm cnf-for-aignet-implies-cnf-sat-when-cube-sat
    (b* ((cnf-vals (aignet->cnf-vals
                    invals regvals cnf-vals sat-lits aignet)))
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (cnf-for-aignet aignet cnf sat-lits)
                    (aignet-lit-listp cube aignet)
                    (aignet-lits-have-sat-vars cube sat-lits))
               (equal (eval-cube
                       (aignet-lits->sat-lits cube sat-lits)
                       cnf-vals)
                      (aignet-eval-conjunction cube invals regvals aignet))))
    :hints(("Goal" :in-theory (enable lit-eval
                                      satlink::eval-lit
                                      aignet-eval-conjunction))))

  ;; Same thing but for a single literal instead of a cube
  (defthm cnf-for-aignet-implies-lit-sat-when-cnf-sat
    (b* ((invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
         (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits aignet)))
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (cnf-for-aignet aignet cnf sat-lits)
                    (aignet-litp lit aignet)
                    (aignet-id-has-sat-var (lit-id lit) sat-lits)
                    (equal 1 (satlink::eval-formula cnf cnf-vals)))
               (equal (lit-eval lit invals regvals aignet)
                      (satlink::eval-lit
                       (aignet-lit->sat-lit lit sat-lits)
                       cnf-vals))))
    :hints(("Goal" :in-theory (enable lit-eval
                                      satlink::eval-lit))))

  (defthm cnf-for-aignet-implies-cnf-sat-when-lit-sat
    (b* ((cnf-vals (aignet->cnf-vals
                    invals regvals cnf-vals sat-lits aignet)))
      (implies (and (sat-lits-wfp sat-lits aignet)
                    (cnf-for-aignet aignet cnf sat-lits)
                    (aignet-litp lit aignet)
                    (aignet-id-has-sat-var (lit-id lit) sat-lits))
               (equal (satlink::eval-lit
                       (aignet-lit->sat-lit lit sat-lits)
                       cnf-vals)
                      (lit-eval lit invals regvals aignet)
                      ;; (lit-eval lit invals regvals aignet)
                      )))
    :hints(("Goal" :in-theory (enable lit-eval
                                      satlink::eval-lit)))))




(define aignet-one-lit->cnf ((lit litp)
                             sat-lits aignet)
  :guard (fanin-litp lit aignet)
  :returns (mv (cnf satlink::lit-list-listp)
               (sat-lits (sat-lits-wfp sat-lits aignet)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* ((sat-lits (sat-lits-empty (num-fanins aignet) sat-lits))
       ((when (eql (mbe :logic (lit-fix lit) :exec lit) 1))
        ;; true -- empty cnf
        (mv nil sat-lits))
       ((when (eql (mbe :logic (lit-fix lit) :exec lit) 0))
        ;; false -- empty clause
        (mv '(nil) sat-lits))
       ((local-stobjs aignet-refcounts)
        (mv cnf sat-lits aignet-refcounts))
       (aignet-refcounts (resize-u32 (num-fanins aignet) aignet-refcounts))
       (aignet-refcounts (aignet-count-refs aignet-refcounts aignet))
       ((mv sat-lits cnf)
        (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet nil))
       (sat-lit (aignet-lit->sat-lit lit sat-lits)))
    (mv (list* (list sat-lit) ;; lit is true
               cnf)
        sat-lits aignet-refcounts))
  ///
  (defthm aignet-one-lit->cnf-normalize-sat-lits
    (implies (syntaxp (not (equal sat-lits ''nil)))
             (equal (aignet-one-lit->cnf lit sat-lits aignet)
                    (aignet-one-lit->cnf lit nil aignet))))


  (local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                         (satlink::eval-lit-of-make-lit))))

  ;; (local (defthm lit-when-var-and-neg-known
  ;;          (implies (and (syntaxp (quotep var))
  ;;                        (natp var)
  ;;                        (syntaxp (or (acl2::rewriting-negative-literal-fn
  ;;                                      `(equal (satlink::lit->var$inline ,lit) ,var)
  ;;                                      mfc state)
  ;;                                     (acl2::rewriting-negative-literal-fn
  ;;                                      `(equal ,var (satlink::lit->var$inline ,lit))
  ;;                                      mfc state)))
  ;;                        (equal (lit->neg lit) neg)
  ;;                        (syntaxp (quotep neg)))
  ;;                   (equal (equal (lit->var lit) var)
  ;;                          (lit-equiv lit (make-lit var neg))))))

  ;; (local (in-theory (disable satlink::equal-of-lit-fix-hyp)))
                         

  (defthm aignet-satisfying-assign-induces-cnf-satisfying-assign
    (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
         (cnf-vals (aignet->cnf-vals invals regvals cnf-vals sat-lits aignet)))
      (implies (and (aignet-litp lit aignet)
                    (sat-lits-wfp sat-lits aignet))
               (equal (satlink::eval-formula cnf cnf-vals)
                      (lit-eval lit invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d ()
                                   (cnf-for-aignet-implies-cnf-sat-when-lit-sat))
            :use ((:instance cnf-for-aignet-implies-cnf-sat-when-lit-sat
                   (cnf-vals cnf-vals)
                   (cnf (cdr (mv-nth 0 (aignet-one-lit->cnf lit sat-lits aignet))))
                   (sat-lits (mv-nth 1 (aignet-one-lit->cnf lit sat-lits aignet))))))))




  (defthm cnf-satisfying-assign-induces-aignet-satisfying-assign
    (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
         (invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
         (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits aignet)))
      (implies (and (aignet-litp lit aignet)
                    (equal (satlink::eval-formula cnf cnf-vals) 1))
               (equal (lit-eval lit invals regvals aignet)
                      1)))
    :hints (("goal" :use ((:instance
                           cnf-for-aignet-implies-lit-sat-when-cnf-sat
                           (cnf (cdr (mv-nth 0 (aignet-one-lit->cnf lit sat-lits aignet))))
                           (sat-lits (mv-nth 1 (aignet-one-lit->cnf lit sat-lits aignet)))
                           (cnf-vals cnf-vals)))
             :in-theory (e/d ()
                             (aignet-lit->cnf
                              cnf-for-aignet-implies-lit-sat-when-cnf-sat))))))



#!aignet
(defsection cnf->aignet-vals
  ;; BOZO this is probably a good logical definition for this but it might be
  ;; nice to have an exec that iterates over the sat-lits/cnf-vals instead of
  ;; having to skip all the IDs with no sat-vars in vals
  (defiteration cnf->aignet-vals (bitarr cnf-vals sat-lits aignet)
    (declare (xargs :stobjs (bitarr cnf-vals sat-lits aignet)
                    :guard (and (sat-lits-wfp sat-lits aignet)
                                (<= (num-fanins aignet) (bits-length bitarr)))))
    (b* ((id n)
         ((unless (aignet-id-has-sat-var id sat-lits))
          bitarr)
         (lit (aignet-id->sat-lit id sat-lits))
         (val (satlink::eval-lit lit cnf-vals)))
      (set-bit n val bitarr))
    :returns bitarr
    :last (num-fanins aignet))

  (in-theory (disable cnf->aignet-vals))
  (local (in-theory (enable cnf->aignet-vals
                            (:induction cnf->aignet-vals-iter))))

  (defthm cnf->aignet-vals-iter-normalize-aignet
    (implies (syntaxp (not (equal aignet ''nil)))
             (equal (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet)
                    (cnf->aignet-vals-iter n vals cnf-vals sat-lits nil)))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet)
            :expand-others
            ((:free (aignet)
              (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet))))))

  (defthm nth-of-cnf->aignet-vals-iter
    (equal (nth n (cnf->aignet-vals-iter m vals cnf-vals sat-lits
                                         aignet))
           (if (and (< (nfix n) (nfix m))
                    (aignet-id-has-sat-var n sat-lits))
               (satlink::eval-lit
                (aignet-id->sat-lit n sat-lits)
                cnf-vals)
             (nth n vals)))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-vals-iter m vals cnf-vals sat-lits aignet))))

  (defthm nth-of-cnf->aignet-vals
    (equal (nth n (cnf->aignet-vals vals cnf-vals sat-lits aignet))
           (if (and (aignet-idp n aignet)
                    (aignet-id-has-sat-var n sat-lits))
               (satlink::eval-lit
                (aignet-id->sat-lit n sat-lits)
                cnf-vals)
             (nth n vals)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm len-of-cnf->aignet-vals-iter
    (implies (and (<= (nfix (num-fanins aignet))
                      (bits-length vals))
                  (<= (nfix m) (bits-length vals)))
             (equal (len (cnf->aignet-vals-iter m vals cnf-vals sat-lits
                                                aignet))
                    (len vals)))
    :hints((acl2::just-induct-and-expand
            (cnf->aignet-vals-iter m vals cnf-vals sat-lits aignet))))

  (defthm len-of-cnf->aignet-vals
    (implies (and (<= (nfix (num-fanins aignet))
                      (bits-length vals)))
             (equal (len (cnf->aignet-vals vals cnf-vals sat-lits
                                           aignet))
                    (len vals))))

  (local (in-theory (disable cnf->aignet-vals)))

  (defthmd cnf->aignet-vals-of-aignet-extension-lemma
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bit-equiv (nth n (cnf->aignet-vals vals cnf-vals sat-lits new))
                        (nth n (cnf->aignet-vals vals cnf-vals sat-lits orig))))
    :hints (("goal" :in-theory (enable
                                sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp))))

  (local (in-theory (e/d (cnf->aignet-vals-of-aignet-extension-lemma))))

  (defthm cnf->aignet-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (sat-lits-wfp sat-lits orig))
             (bits-equiv (cnf->aignet-vals vals cnf-vals sat-lits new)
                         (cnf->aignet-vals vals cnf-vals sat-lits orig)))
    :hints (("goal" :in-theory (enable bits-equiv))))


  (defthm cnf->aignet-vals-of-sat-lit-extension-idempotent
    (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet))
             (let ((aignet-vals1 (cnf->aignet-vals
                                  vals cnf-vals sat-lits2 aignet)))
               (bits-equiv (cnf->aignet-vals
                            aignet-vals1 cnf-vals sat-lits1 aignet)
                           aignet-vals1)))
    :hints(("Goal" :in-theory (enable bits-equiv)))))
