; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "aignet-base")
(include-book "aignet-refcounts")
(include-book "centaur/satlink/cnf" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (include-book "bit-lemmas"))

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
the circuit is unsat -- say, A & B & ~C.  We first convert their subcircuits to
CNF and then add the three singleton clauses.  Now, suppose that we have some
assignment to the CIs that satisfies A & B & ~C.  That induces a satisfying
assignment for the generated part of the CNF where (in particular) the literals
corresponding to A, B, and ~C are assigned true.  That makes the three
singleton clauses also true, so the whole CNF is satisfied.  Therefore, if we
prove the CNF unsatisfiable, then we've proven that no assignment to the CIs
can simultaneously satisfy A & B & ~C.</p>

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
<li>a predicate @('cnf/aignet-evals-agree') which compares a satisfying assignment
to an aignet evaluation to determine whether all values agree as specified
above,</li>
<li>a function @('cnf->aignet-vals') that transforms a satisfying assignment into
a aignet-vals object.  We'll show that the input and output satisfy
<tt>cnf/aignet-evals-agree</tt> if the assignment satisfies the generated
CNF.</li>
<li>a function @('aignet->cnf-eval') that creates a CNF variable assignment from a
aignet-vals object.  We'll show that this satisfies
<tt>cnf/aignet-evals-agree</tt> and that the CNF assignment
satisfies the generated CNF.</li>
</ul>

<p>When actually converting an aignet to CNF, we of course process the AIG
recursively.  We do this in chunks, where each chunk is either:
<ul>
<li>a <i>supergate</i>, representing a single large AND or OR gate, or</li>
<li>a mux.</li>
</ul>
For both of these cases, we prove that the chunk we've just added preserves the
correctness criterion we've described.
</p>

")

(local (defun trivial-worse-than-or-equal (term1 term2)
         (declare (xargs :guard t)
                  (ignorable term1 term2))
         nil))

(local (defattach acl2::worse-than-or-equal trivial-worse-than-or-equal))

(local (in-theory (disable acl2::nth-with-large-index
                           nth update-nth
                           sets::double-containment)))

(local (defthmd equal-1-by-bitp
         (implies (acl2::bitp x)
                  (equal (equal x 1) (not (equal x 0))))
         :hints(("Goal" :in-theory (enable acl2::bitp)))))



;; Utilities for recognizing muxes and XORs.
(defsection id-is-mux

  ;; bozo move to aignet-base
  (defcong id-equiv equal (gate-orderedp id aignet) 1
    :hints(("Goal" :in-theory (enable gate-orderedp))))

  ;; Returns (mv is-mux cond-lit tb-lit fb-lit).
  ;; A mux node is of the form
  ;; (and (not (and c (not tb))) (not (and (not c) (not fb))))
  ;; or a permutation.
  (defund id-is-mux (id aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-idp id aignet))))
    (b* (((unless (int= (id->type id aignet) (gate-type)))
          (mv nil 0 0 0))
         (f0 (gate-id->fanin0 id aignet))
         (f1 (gate-id->fanin1 id aignet))
         ((unless (and (int= (lit-neg f0) 1)
                       (int= (lit-neg f1) 1)
                       (int= (id->type (lit-id f0) aignet) (gate-type))
                       (int= (id->type (lit-id f1) aignet) (gate-type))
                       (mbt (and (gate-orderedp id aignet)
                                 (gate-orderedp (lit-id f0) aignet)
                                 (gate-orderedp (lit-id f1) aignet)))))
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
      (mv nil 0 0 0)))

  (local (in-theory (enable id-is-mux)))

  (defcong id-equiv equal (id-is-mux id aignet) 1)

  (defthm id-is-mux-produces-aignet-lits
    (b* (((mv ?muxp c tb fb) (id-is-mux id aignet)))
      (implies (and (aignet-well-formedp aignet)
                    (aignet-idp id aignet))
               (and (aignet-litp c aignet)
                    (aignet-litp tb aignet)
                    (aignet-litp fb aignet)))))

  (defthm id-is-mux-produces-lits
    (b* (((mv ?muxp c tb fb) (id-is-mux id aignet)))
      (and (litp c) (litp tb) (litp fb))))

  (defthmd lit-eval-of-mk-lit-split-rw
    (implies (equal lit1 (mk-lit (lit-id lit) neg))
             (equal (lit-eval lit1 in-vals reg-vals aignet)
                    (acl2::b-xor (acl2::b-xor neg (lit-neg lit))
                                 (lit-eval lit in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable lit-eval acl2::B-xor))))

  ;; This is a pretty awkward rewrite rule, but maybe not as bad as it
  ;; appears.  The first hyp will basically fail immediately if we don't know
  ;; that the ID is a mux.  Might need other tricks to prevent it from opening
  ;; when we don't want it to.
  (defthmd id-eval-when-id-is-mux
    (b* (((mv muxp c tb fb) (id-is-mux id aignet)))
      (implies (and muxp
                    (aignet-well-formedp aignet)
                    (aignet-idp id aignet))
               (equal (id-eval id in-vals reg-vals aignet)
                      (acl2::b-ior (acl2::b-and
                                    (lit-eval c in-vals reg-vals aignet)
                                    (lit-eval tb in-vals reg-vals aignet))
                                   (acl2::b-and
                                    (acl2::b-not (lit-eval c in-vals reg-vals aignet))
                                    (lit-eval fb in-vals reg-vals aignet))))))
    :hints (("goal" :in-theory (e/d (lit-eval-of-mk-lit-split-rw
                                     equal-1-by-bitp)
                                    (lit-eval acl2::b-xor acl2::b-and
                                              acl2::b-ior acl2::b-not))
             :expand ((id-eval id in-vals reg-vals aignet)
                      (lit-eval (gate-node->fanin0 (nth-node id (nth *nodesi* aignet)))
                                in-vals reg-vals aignet)
                      (lit-eval (gate-node->fanin1 (nth-node id (nth *nodesi* aignet)))
                                in-vals reg-vals aignet)
                      (id-eval (lit-id (gate-node->fanin0 (nth-node id (nth *nodesi* aignet))))
                               in-vals reg-vals aignet)
                      (id-eval (lit-id (gate-node->fanin1 (nth-node id (nth *nodesi* aignet))))
                               in-vals reg-vals aignet)))
            (and stable-under-simplificationp
                 '(:in-theory (enable  acl2::b-xor acl2::b-and
                                       acl2::b-ior acl2::b-not))))))





(defsection collect-supergate


  (defthm aignet-lit-listp-of-append
    (implies (and (aignet-lit-listp a aignet)
                  (aignet-lit-listp b aignet))
             (aignet-lit-listp (append a b) aignet)))


  (defun eval-supergate-list (lits in-vals reg-vals aignet)
    (declare (xargs :stobjs (aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-lit-listp lits aignet)
                                (true-listp in-vals)
                                (true-listp reg-vals))))
    (if (atom lits)
        1
      (acl2::b-and (lit-eval (car lits) in-vals reg-vals aignet)
                   (eval-supergate-list (cdr lits) in-vals reg-vals aignet))))

  (local
   (progn

     (defthm bitp-of-eval-supergate-list
       (acl2::bitp (eval-supergate-list lits in-vals reg-vals aignet)))

     (defthm b-and-associative
       (equal (acl2::b-and (acl2::b-and a b) c)
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm b-and-commute-2
       (equal (acl2::b-and b (acl2::b-and a c))
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm eval-supergate-list-of-append
       (equal (eval-supergate-list (append a b) in-vals reg-vals aignet)
              (acl2::b-and (eval-supergate-list a in-vals reg-vals aignet)
                           (eval-supergate-list b in-vals reg-vals aignet))))

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

     (defthm lit-eval-0
       (implies (aignet-well-formedp aignet)
                (equal (lit-eval 0 in-vals reg-vals aignet) 0))
       :hints(("Goal" :in-theory (enable lit-eval id-eval))))

     (defthm and-of-eval-list-when-member
       (implies (member lit lst)
                (equal (acl2::b-and (lit-eval lit in-vals reg-vals aignet)
                                    (eval-supergate-list lst in-vals reg-vals aignet))
                       (eval-supergate-list lst in-vals reg-vals aignet))))

     (defthm eval-supergate-list-when-0
       (implies (and (member 0 lst)
                     (aignet-well-formedp aignet))
                (equal (eval-supergate-list lst in-vals reg-vals aignet)
                       0)))

     (defthm and-of-eval-list-when-complement-member
       (implies (member (lit-negate lit) lst)
                (equal (acl2::b-and (lit-eval lit in-vals reg-vals aignet)
                                    (eval-supergate-list lst in-vals reg-vals aignet))
                       0))
       :hints(("Goal" :induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::b-and)))))))


  (defund lit-collect-supergate (lit top use-muxes supergate aignet-refcounts aignet)
    (declare (xargs :stobjs (aignet-refcounts aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (u32arr-sizedp aignet-refcounts aignet)
                                (aignet-litp lit aignet)
                                (true-listp supergate))
                    :measure (id-val (lit-id lit))
                    :hints(("Goal" :in-theory (enable gate-orderedp)))
                    :verify-guards nil))
    (b* (((when (or (int= (lit-neg lit) 1)
                    (not (int= (id->type (lit-id lit) aignet) (gate-type)))
                    (and (not top) (< 1 (get-id->nat (lit-id lit) aignet-refcounts)))
                    (and use-muxes
                         (b* (((mv muxp & & &) (id-is-mux (lit-id lit) aignet)))
                           muxp))))
          (if (member (lit-negate lit) supergate)
              ;; Complementary literal is in the supergate, so add 0.
              (list 0)
            (if (member lit supergate)
                supergate
              (cons lit supergate))))
         ((unless (mbt (gate-orderedp (lit-id lit) aignet)))
          (list 0))
         (supergate (lit-collect-supergate (gate-id->fanin0 (lit-id lit) aignet)
                                           nil use-muxes supergate aignet-refcounts aignet)))
      (lit-collect-supergate (gate-id->fanin1 (lit-id lit) aignet)
                             nil use-muxes supergate aignet-refcounts aignet)))

  (defthm true-listp-of-collect-supergate
    (implies (true-listp supergate)
             (true-listp (lit-collect-supergate lit top use-muxes supergate
                                                aignet-refcounts aignet)))
    :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
                                                   aignet-refcounts aignet)
             :do-not-induct t
             :in-theory (enable (:induction lit-collect-supergate))
             :expand ((:free (top use-muxes)
                       (lit-collect-supergate lit top use-muxes supergate
                                              aignet-refcounts aignet))))))

  (defthm aignet-lit-listp-of-collect-supergate
    (implies (and (aignet-well-formedp aignet)
                  (aignet-litp lit aignet)
                  (aignet-lit-listp supergate aignet))
             (aignet-lit-listp
              (lit-collect-supergate lit top use-muxes supergate
                                     aignet-refcounts aignet)
              aignet))
    :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
                                                   aignet-refcounts aignet)
             :do-not-induct t
             :in-theory (enable (:induction lit-collect-supergate))
             :expand ((:free (top use-muxes)
                       (lit-collect-supergate lit top use-muxes supergate
                                              aignet-refcounts aignet))))))

  (defthm lit-listp-of-collect-supergate
    (implies (and (litp lit)
                  (lit-listp supergate))
             (lit-listp
              (lit-collect-supergate lit top use-muxes supergate
                                     aignet-refcounts aignet)))
    :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
                                                   aignet-refcounts aignet)
             :do-not-induct t
             :in-theory (enable (:induction lit-collect-supergate))
             :expand ((:free (top use-muxes)
                       (lit-collect-supergate lit top use-muxes supergate
                                              aignet-refcounts aignet))))))

  (verify-guards lit-collect-supergate)

  (defthm collect-supergate-correct
    (implies (and (aignet-well-formedp aignet)
                  (aignet-litp lit aignet))
             (equal (eval-supergate-list
                     (lit-collect-supergate
                      lit top use-muxes supergate
                      aignet-refcounts aignet)
                     in-vals reg-vals aignet)
                    (acl2::b-and (lit-eval lit in-vals reg-vals aignet)
                                 (eval-supergate-list supergate in-vals reg-vals aignet))))
    :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
                                                   aignet-refcounts aignet)
             :do-not-induct t
             :in-theory (enable (:induction lit-collect-supergate))
             :expand ((:free (top use-muxes)
                       (lit-collect-supergate lit top use-muxes supergate
                                              aignet-refcounts aignet))))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval lit in-vals reg-vals aignet)
                            (id-eval (lit-id lit) in-vals reg-vals aignet)))))))



(defsection sat-lits
  ;; Mapping from aignet IDs to sat vars and back.  Actually, each array maps IDs
  ;; to literals.  Identities:
  ;; (lit-id (sat-id->aignet-lit (lit-id (aignet-id->sat-lit id)))) = (id-fix id)
  ;; (lit-id (aignet-id->sat-lit (lit-id (sat-id->aignet-lit id)))) = (id-fix id)
  ;; (lit-neg (sat-id->aignet-lit (lit-id (aignet-id->sat-lit id)))) = (aignet-id->sat-lit id)
  ;; (lit-neg (aignet-id->sat-lit (lit-id (sat-id->aignet-lit id)))) = (lit-neg (sat-id->aignet-lit id))
  (defstobj sat-lits
    (sat-next-var :type (integer 0 *) :initially 1)
    ;; Initially has aignet id 0 (const) mapped to SAT lit 0
    (aignet->sat :type (array (and (unsigned-byte 32)
                                (satisfies satlink::litp)) (1))
              :resizable t
              :initially 0)
    ;; and SAT var 0 mapped to aignet ID 0.
    (sat->aignet :type (array (and (unsigned-byte 32)
                                (satisfies litp)) (1))
              :resizable t
              :initially 0))

  (in-theory (disable create-sat-lits (create-sat-lits) resize-aignet->sat))
  (local (in-theory (enable create-sat-lits)))
  (local (in-theory (enable resize-aignet->sat)))

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
                    :guard (idp id)
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    ;; Could use the phase here, won't for now
    (mbe :logic (non-exec (satlink::lit-fix (nth (id-val id) (nth *aignet->sati* sat-lits))))
         :exec (if (< (id-val id) (aignet->sat-length sat-lits))
                   (aignet->sati (id-val id) sat-lits)
                 0)))

  (local (in-theory (enable aignet-id->sat-lit)))

  (defcong id-equiv equal (aignet-id->sat-lit id sat-lits) 1)

  (defthm satlink-litp-of-aignet-id->sat-lit
    (satlink::litp (aignet-id->sat-lit id sat-lits)))

  (definlined set-aignet-id->sat-lit (id lit sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (and (idp id)
                                (satlink::litp lit))
                    :guard-hints ('(:in-theory (enable update-nth-lit satlink::litp)))))
    (b* ((sat-lits (if (< (id-val id) (aignet->sat-length sat-lits))
                       sat-lits
                     (resize-aignet->sat
                      (max (* 2 (id-val id)) 16)
                      sat-lits))))
      (mbe :logic (non-exec (update-nth *aignet->sati*
                                        (update-nth (id-val id) (satlink::lit-fix lit)
                                                    (nth *aignet->sati* sat-lits))
                                        sat-lits))
           :exec (if (< (the (integer 0 *) lit) (expt 2 32))
                     (update-aignet->sati (id-val id) lit sat-lits)
                   (ec-call (update-aignet->sati (id-val id) lit sat-lits))))))

  (defthm set-aignet-id->sat-lit-frame
    (implies (not (equal n *aignet->sati*))
             (equal (nth n (set-aignet-id->sat-lit id lit sat-lits))
                    (nth n sat-lits)))
    :hints(("Goal" :in-theory (enable set-aignet-id->sat-lit))))

  (defthm aignet-id->sat-lit-of-set-aignet-id->sat-lit
    (satlink::lit-equiv (nth n (nth *aignet->sati* (set-aignet-id->sat-lit id lit sat-lits)))
                        (if (equal (nfix n) (id-val id))
                            lit
                          (nth n (nth *aignet->sati* sat-lits))))
    :hints(("Goal" :in-theory (enable set-aignet-id->sat-lit
                                      acl2::nth-of-resize-list-split))))

  (defund sat-varp (x sat-lits)
    (declare (xargs :stobjs sat-lits))
    (and (satlink::varp x)
         (< (satlink::var->index x) (lnfix (sat-next-var sat-lits)))))

  (local (in-theory (enable sat-varp)))

  (defthm sat-varp-when-varp
    (implies (and (satlink::varp x)
                  (< (satlink::var->index x) (lnfix (sat-next-var sat-lits))))
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
    (mbe :logic (non-exec (nth-lit (satlink::var->index var) (nth *sat->aigneti* sat-lits)))
         :exec (sat->aigneti (satlink::var->index var) sat-lits)))

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
                                      (update-nth-lit (satlink::var->index var) (lit-fix lit)
                                                      (nth *sat->aigneti* sat-lits))
                                      sat-lits))
         :exec (if (< (the (integer 0 *) lit) (expt 2 32))
                   (update-sat->aigneti (satlink::var->index var) lit sat-lits)
                 (ec-call (update-sat->aigneti (satlink::var->index var) lit sat-lits)))))


  (definlined aignet-id-has-sat-var (id sat-lits)
    (declare (xargs :stobjs (sat-lits)
                    :guard (idp id)))
    (b* (((when (int= (id-val id) 0)) t)
         (lit (aignet-id->sat-lit id sat-lits)))
      (not (int= (satlink::var->index (satlink::lit->var lit)) 0))))

  (local (in-theory (enable aignet-id-has-sat-var)))

  (defcong id-equiv equal (aignet-id-has-sat-var id sat-lits) 1)

  (defun aignet->sat-well-formedp (n sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (and (natp n)
                                (sat-lits-sizedp sat-lits))))
    (if (zp n)
        t
      (b* ((n (1- n))
           (nid (to-id n)))
        (and (b* ((sat-lit (aignet-id->sat-lit nid sat-lits))
                  ((when (int= (satlink::var->index (satlink::lit->var sat-lit)) 0)) t)
                  ((unless (aignet-idp nid aignet)) nil)
                  ((unless (sat-varp (satlink::lit->var sat-lit) sat-lits))
                   nil)
                  (aignet-lit (sat-var->aignet-lit (satlink::lit->var sat-lit) sat-lits)))
               (int= aignet-lit
                     (mk-lit nid (satlink::lit->neg sat-lit))))
             (aignet->sat-well-formedp n sat-lits aignet)))))


  (defthm aignet->sat-well-formedp-implies
    (implies (and (aignet-id-has-sat-var m sat-lits)
                  (not (equal (id-val m) 0))
                  (< (id-val m) (nfix n))
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
                  (not (aignet-idp (id-fix m) aignet))
                  (< (id-val m) (nfix n)))
             (satlink::var-equiv (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                                 0)))

  (local (defthm aignet->sat-well-formedp-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet-extension-p new-aignet orig-aignet)
                         (aignet->sat-well-formedp n sat-lits orig-aignet))
                    (aignet->sat-well-formedp n sat-lits new-aignet))))

  ;; (local (retroactive-add-aignet-preservation-thm
  ;;         aignet->sat-well-formedp-preserved-aignet
  ;;         :vars (n sat-lits)
  ;;         :body `(implies (aignet->sat-well-formedp n sat-lits ,orig-stobj)
  ;;                         (aignet->sat-well-formedp n sat-lits ,new-stobj))
  ;;         :hints `((acl2::just-induct-and-expand
  ;;                   (aignet->sat-well-formedp n sat-lits ,orig-stobj)
  ;;                   :expand-others ((:free (,orig-stobj)
  ;;                                    (aignet->sat-well-formedp n sat-lits ,orig-stobj)))))))

  (defun sat->aignet-well-formedp (n sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (and (natp n)
                                (<= n (sat-next-var sat-lits))
                                (sat-lits-sizedp sat-lits)
                                (aignet-sizes-ok aignet))
                    :guard-hints (("goal" :in-theory (enable sat-varp)))
                    :guard-debug t))
    (if (zp n)
        t
      (b* ((n (1- n))
           (nvar (satlink::make-var n)))
        (and (b* ((aignet-lit (sat-var->aignet-lit nvar sat-lits))
                  (aignet-id (lit-id aignet-lit))
                  ((unless (and (aignet-litp aignet-lit aignet)
                                (aignet-id-has-sat-var aignet-id sat-lits)))
                   nil)
                  (sat-lit (aignet-id->sat-lit aignet-id sat-lits)))
               (int= sat-lit
                     (satlink::make-lit
                      nvar (lit-neg aignet-lit))))
             (sat->aignet-well-formedp n sat-lits aignet)))))

  (defthm sat->aignet-well-formedp-implies
    (implies (and (< (satlink::var->index m) (nfix n))
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
                         (aignet-extension-p new-aignet orig-aignet)
                         (sat->aignet-well-formedp n sat-lits orig-aignet))
                    (sat->aignet-well-formedp n sat-lits new-aignet))))

  ;; (local (retroactive-add-aignet-preservation-thm
  ;;         sat->aignet-well-formedp-preserved-aignet
  ;;         :vars (n sat-lits)
  ;;         :body `(implies (sat->aignet-well-formedp n sat-lits ,orig-stobj)
  ;;                         (sat->aignet-well-formedp n sat-lits ,new-stobj))
  ;;         :hints `((acl2::just-induct-and-expand
  ;;                   (sat->aignet-well-formedp n sat-lits ,orig-stobj)
  ;;                   :expand-others ((:free (,orig-stobj)
  ;;                                    (sat->aignet-well-formedp n sat-lits ,orig-stobj)))))))

  (defund sat-lits-wfp (sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (aignet-well-formedp aignet)))
    (and (sat-lits-sizedp sat-lits)
         (aignet->sat-well-formedp (aignet->sat-length sat-lits) sat-lits aignet)
         (sat->aignet-well-formedp (lnfix (sat-next-var sat-lits)) sat-lits aignet)
         (<= 1 (lnfix (sat-next-var sat-lits)))
         (equal (aignet-id->sat-lit 0 sat-lits) 0)
         (equal (sat-var->aignet-lit 0 sat-lits) 0)))

  (local (in-theory (enable sat-lits-wfp)))


  (defthm sat-lits-wfp-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet))
             (sat-lits-wfp sat-lits new-aignet)))

  ;; (retroactive-add-aignet-preservation-thm
  ;;  sat-lits-wfp-preserved-aignet
  ;;  :vars (sat-lits)
  ;;  :body `(implies (sat-lits-wfp sat-lits ,orig-stobj)
  ;;                  (sat-lits-wfp sat-lits ,new-stobj))
  ;;  :enable '(aignet-frame-thms)
  ;;  :hints `(("goal" :in-theory (enable sat-lits-wfp))))

  (defthm sat-lits-wfp-sat-next-var-type
    (implies (sat-lits-wfp sat-lits aignet)
             (posp (nth *sat-next-var* sat-lits)))
    :rule-classes :forward-chaining)

  (defthm sat-lits-wfp-implies-sat-lits-sizedp
    (implies (sat-lits-wfp sat-lits aignet)
             (sat-lits-sizedp sat-lits)))

  (local (defthmd nth-lit-when-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth-lit n x) 0))
           :hints(("Goal" :in-theory (enable nth-lit
                                             acl2::nth-with-large-index)))))

  ;; (defthm sat-lits-wfp-implies-lookup-aignet-id
  ;;   (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                 (aignet-id-has-sat-var n sat-lits))
  ;;            (and (equal (sat-var->aignet-lit
  ;;                         (lit-id (aignet-id->sat-lit n sat-lits))
  ;;                         sat-lits)
  ;;                        (mk-lit
  ;;                         n (lit-neg (aignet-id->sat-lit n sat-lits))))
  ;;                 (sat-varp (lit-id (aignet-id->sat-lit n sat-lits))
  ;;                           sat-lits)))
  ;;   :hints(("Goal" :in-theory (enable aignet-idp nth-lit-when-out-of-bounds)
  ;;           :use ((:instance aignet->sat-well-formedp-implies
  ;;                  (n (aignet->sat-length sat-lits)) (m n))))))

  (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-id-has-sat-var n sat-lits))
             (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                       sat-lits))
    :hints(("Goal" :in-theory (enable aignet-idp nth-lit-when-out-of-bounds)
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
                  (not (aignet-idp (id-fix m) aignet)))
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

  (defthm sat-lits-wfp-implies-lookup-sat-var
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'id '(lit-id (sat-var->aignet-lit n sat-lits))
                    mfc state)
                   (n))
                  (id-equiv id (lit-id (sat-var->aignet-lit n sat-lits)))
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
                                             (resize-aignet->sat 1 sat-lits)))))))
    (mbe :logic (non-exec (resize-aignet->sat n (create-sat-lits)))
         :exec
         (b* ((sat-lits (update-sat-next-var 1 sat-lits))
              (sat-lits (resize-sat->aignet 1 sat-lits))
              (sat-lits (update-sat->aigneti 0 0 sat-lits))
              (sat-lits (resize-aignet->sat 1 sat-lits))
              (sat-lits (update-aignet->sati 0 0 sat-lits)))
           (resize-aignet->sat n sat-lits)))))

(defsection sat-lit-extension-p
  (defun-sk sat-lit-extension-p (sat-lits2 sat-lits1)
    (forall var/id
            (and (implies (sat-varp var/id sat-lits1)
                          (and (sat-varp var/id sat-lits2)
                               (equal (sat-var->aignet-lit var/id sat-lits2)
                                      (sat-var->aignet-lit var/id sat-lits1))))
                 (implies (aignet-id-has-sat-var var/id sat-lits1)
                          (and (aignet-id-has-sat-var var/id sat-lits2)
                               (equal (aignet-id->sat-lit var/id sat-lits2)
                                      (aignet-id->sat-lit var/id sat-lits1))))))
    :rewrite :direct)

  (defmacro sat-lit-extension-binding (&key (new 'sat-lits2)
                                         (orig 'sat-lits1)
                                         (fall-through 't)
                                         (iters '1))
    `(bind-free (prev-stobj-binding ,new ',orig ',iters mfc state)
                . ,(if fall-through nil `((,orig)))))

  ;; expands sat-lit-extension-p if it appears as a positive literal
  (defthmd prove-sat-lit-extension-p
    (implies (acl2::rewriting-positive-literal `(sat-lit-extension-p ,sat-lits2 ,sat-lits1))
             (equal (sat-lit-extension-p sat-lits2 sat-lits1)
                    (let ((var/id (sat-lit-extension-p-witness sat-lits2 sat-lits1)))
                      (and (implies (sat-varp var/id sat-lits1)
                                    (and (sat-varp var/id sat-lits2)
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
             (sat-varp var sat-lits2)))

  (defthm sat-varp-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-varp var sat-lits1))
             (sat-varp var sat-lits2)))

  (defthm sat-var->aignet-lit-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-varp var sat-lits1))
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
                    (aignet-lits->sat-lits lits sat-lits1)))))



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

  (defund sat-add-aignet-lit (lit sat-lits aignet)
    (declare (xargs :stobjs (sat-lits aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (sat-lits-wfp sat-lits aignet)
                                (aignet-litp lit aignet))))
    (b* ((lit (lit-fix lit))
         ((unless (mbt (aignet-litp lit aignet)))
          sat-lits)
         (id (lit-id lit))
         ((when (aignet-id-has-sat-var id sat-lits))
          sat-lits)
         (sat-lits (maybe-grow-sat->aignet sat-lits))
         (new-var  (satlink::make-var (sat-next-var sat-lits)))
         (sat-lits (update-sat-next-var (+ 1 (satlink::var->index new-var)) sat-lits))
         (new-lit  (satlink::make-lit new-var (lit-neg lit)))
         (sat-lits (set-sat-var->aignet-lit new-var lit sat-lits))
         (sat-lits (set-aignet-id->sat-lit id new-lit sat-lits)))
      sat-lits))

  (local (in-theory (enable sat-add-aignet-lit
                            aignet-id-has-sat-var
                            aignet-id->sat-lit
                            sat-var->aignet-lit)))

  (defcong lit-equiv equal (sat-add-aignet-lit lit sat-lits aignet) 1)

  (defthm sat-lit-extension-p-of-sat-add-aignet-lit
    (sat-lit-extension-p
     (sat-add-aignet-lit lit sat-lits aignet) sat-lits)
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable prove-sat-lit-extension-p)))))

  (defthm sat-lits-sizedp-of-sat-add-aignet-lit
    (implies (sat-lits-sizedp sat-lits)
             (sat-lits-sizedp (sat-add-aignet-lit lit sat-lits aignet))))

  (defthm sat-add-aignet-lit-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-litp lit orig-aignet))
             (equal (sat-add-aignet-lit lit sat-lits new-aignet)
                    (sat-add-aignet-lit lit sat-lits orig-aignet))))

  ;; (defthm sat-varp-preserved-of-sat-add-aignet-lit
  ;;   (implies (sat-varp n sat-lits)
  ;;            (sat-varp n (sat-add-aignet-lit lit sat-lits aignet))))

  ;; (defthm sat-var->aignet-lit-preserved-of-sat-add-aignet-lit
  ;;   (implies (sat-varp n sat-lits)
  ;;            (equal (sat-var->aignet-lit
  ;;                    n (sat-add-aignet-lit lit sat-lits aignet))
  ;;                   (sat-var->aignet-lit n sat-lits))))

  ;; (defthm aignet-id->sat-lit-preserved-of-sat-add-aignet-lit
  ;;   (implies (aignet-id-has-sat-var id sat-lits)
  ;;            (equal (aignet-id->sat-lit
  ;;                    id (sat-add-aignet-lit lit sat-lits aignet))
  ;;                   (aignet-id->sat-lit id sat-lits))))

  ;; (defthm aignet-id-has-sat-var-preserved-of-sat-add-aignet-lit
  ;;   (implies (aignet-id-has-sat-var id sat-lits)
  ;;            (aignet-id-has-sat-var
  ;;             id (sat-add-aignet-lit lit sat-lits aignet))))

  (defthm sat-add-aignet-lit-new-id-not-varp-in-previous
    (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                  (aignet-litp (lit-fix lit) aignet))
             (not (sat-varp (satlink::lit->var (aignet-lit->sat-lit
                                                lit (sat-add-aignet-lit lit sat-lits aignet)))
                            sat-lits))))

  (defthm sat-add-aignet-lit-new-id-not-varp-in-previous-by-id
    (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                  (aignet-litp (lit-fix lit) aignet)
                  (equal (id-fix id) (lit-id lit)))
             (not (sat-varp (satlink::lit->var (aignet-id->sat-lit
                                                id (sat-add-aignet-lit lit sat-lits aignet)))
                            sat-lits))))


  (defthm aignet-id-has-sat-var-preserved-when-not-same-id-of-sat-add-aignet-lit
    (implies (not (equal (id-val id) (id-val (lit-id lit))))
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
                    (or (equal (id-val (lit-id lit)) (id-val id))
                        (aignet-id-has-sat-var id sat-lits)))))

  (defthmd aignet-id->sat-lit-preserved-of-sat-add-aignet-lit-when-not-added
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (not (equal (id-val (lit-id lit)) (id-val id))))
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


  (local (defthm aignet->sat-well-formedp-of-create
           (aignet->sat-well-formedp m (resize-aignet->sat n (create-sat-lits))
                                     aignet)
           :hints (("goal" :induct (aignet->sat-well-formedp m (resize-aignet->sat n
                                                                                   (create-sat-lits))
                                                             aignet)
                    :in-theory (e/d (acl2::nth-of-resize-list-split
                                     nth-lit)
                                    (acl2::make-list-ac-redef
                                     acl2::resize-list-when-empty))))))

  (local (in-theory (disable create-sat-lits)))

  (defthm lit-neg-of-sat-add-aignet-lit-new-lit
    (implies (and (not (aignet-id-has-sat-var (lit-id lit) sat-lits))
                  (aignet-litp (lit-fix lit) aignet))
             (equal (satlink::lit->neg (aignet-lit->sat-lit lit (sat-add-aignet-lit lit
                                                                                    sat-lits
                                                                                    aignet)))
                    0)))

  (local (in-theory (enable sat-lits-wfp)))

  (defthm sat-lits-wfp-of-create
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix (num-nodes aignet)) (nfix n)))
             (sat-lits-wfp (resize-aignet->sat n (create-sat-lits)) aignet))
    :hints(("Goal" :in-theory (e/d (nth-lit nth update-nth create-sat-lits)
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
                                     sat-varp
                                     aignet-litp)
                                    (sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                                     sat-lits-wfp-implies-lookup-aignet-id
                                     sat-lits-wfp-implies-when-not-aignet-idp
                                     (:definition aignet->sat-well-formedp))))
                   '(:use ((:instance sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                                      (n (to-id (+ -1 n))))
                           (:instance sat-lits-wfp-implies-lookup-aignet-id
                                      (n (to-id (+ -1 n)))
                                      (id (satlink::lit->var (aignet-id->sat-lit (to-id (1- n)) sat-lits))))
                           (:instance sat-lits-wfp-implies-when-not-aignet-idp
                                      (m (to-id (+ -1 n)))))))))

  (local (defthm sat->aignet-well-formedp-of-sat-add-aignet-lit
           (implies (and (sat-lits-wfp sat-lits aignet)
                         (<= (nfix n) (nfix (sat-next-var sat-lits))))
                    (let ((sat-lits (sat-add-aignet-lit lit sat-lits aignet)))
                      (sat->aignet-well-formedp n sat-lits aignet)))
           :hints (("goal" :induct (sat->aignet-well-formedp n sat-lits aignet)))))

  (local (defthm sat-lits-wfp-aignet->sat-nth-lit-0
           (implies (sat-lits-wfp sat-lits aignet)
                    (satlink::lit-equiv (nth 0 (nth *aignet->sati* sat-lits))
                                        0))
           :hints(("Goal" :in-theory (enable sat-lits-wfp
                                             aignet-id->sat-lit)))))

  (local (defthm sat-lits-wfp-sat->aignet-nth-lit-0
           (implies (sat-lits-wfp sat-lits aignet)
                    (equal (nth-lit 0 (nth *sat->aigneti* sat-lits))
                           0))
           :hints(("Goal" :in-theory (enable sat-lits-wfp
                                             sat-var->aignet-lit)))))

  (local (defthm aignet->sat-well-formedp-increase-index
           (implies (sat-lits-wfp sat-lits aignet)
                    (aignet->sat-well-formedp n sat-lits aignet))
           :hints (("goal" :induct (aignet->sat-well-formedp n sat-lits aignet))
                   '(:use ((:instance sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
                                      (n (to-id (+ -1 n))))
                           (:instance sat-lits-wfp-implies-lookup-aignet-id
                                      (n (to-id (+ -1 n)))
                                      (id (satlink::lit->var (aignet-id->sat-lit (to-id (1- n)) sat-lits))))
                           (:instance sat-lits-wfp-implies-when-not-aignet-idp
                                      (m (to-id (1- n)))))
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

  (def-sat-lits-preservation-thms sat-add-aignet-lit))


(defsection sat-clauses
  (defabsstobj cnf-eval
    :concrete acl2::bitarr$c
    :creator (create-cnf-eval :exec acl2::create-bitarr$c :logic acl2::create-bitarr$a)
    :recognizer (cnf-evalp :exec acl2::bitarr$cp :logic acl2::bitarr$ap)
    :exports ((cnf-eval-length :exec acl2::bits$c-length :logic acl2::bits$a-length)
              (get-cnf-val :exec acl2::bits$ci :logic acl2::bits$ai)
              (set-cnf-val :exec acl2::update-bits$ci :logic acl2::update-bits$ai)
              (resize-cnf-eval :exec acl2::resize-bits$c :logic acl2::resize-bits$a))
    :congruent-to bitarr)

  ;;
  ;; these are just semantics, don't need to be particularly efficient, so
  ;; we'll do bounds checks in the exec for simpler semantics.
  ;; (defun satlink::eval-var (var cnf-eval)
  ;;   (declare (xargs :stobjs cnf-eval
  ;;                   :guard (idp var)
  ;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  ;;   (mbe :logic (get-id->bit var cnf-eval)
  ;;        :exec (if (< (id-val var) (bits-length cnf-eval))
  ;;                  (get-id->bit var cnf-eval)
  ;;                (ec-call (get-id->bit$inline var cnf-eval)))))

  ;; (defthm bitp-satlink::eval-var
  ;;   (acl2::bitp (satlink::eval-var var cnf-eval)))

  ;; (defcong id-equiv equal (satlink::eval-var var cnf-eval) 1)
  ;; (defcong nth-equiv equal (satlink::eval-var var cnf-eval) 2)

  ;; (defun set-satlink::eval-var (var val cnf-eval)
  ;;   (declare (xargs :stobjs cnf-eval
  ;;                   :guard (and (idp var) (acl2::bitp val))
  ;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  ;;   (mbe :logic (set-id->bit var val cnf-eval)
  ;;        :exec (if (< (id-val var) (bits-length cnf-eval))
  ;;                  (set-id->bit var val cnf-eval)
  ;;                (ec-call (set-id->bit$inline var val cnf-eval)))))

  ;; (defun satlink::eval-lit (lit cnf-eval)
  ;;   (declare (xargs :stobjs cnf-eval
  ;;                   :guard (litp lit)))
  ;;   (acl2::b-xor (lit-neg lit) (satlink::eval-var (lit-id lit) cnf-eval)))

  ;; (defthm bitp-satlink::eval-lit
  ;;   (acl2::bitp (satlink::eval-lit lit cnf-eval)))

  ;; (defcong lit-equiv equal (satlink::eval-lit lit cnf-eval) 1)
  ;; (defcong nth-equiv equal (satlink::eval-lit lit cnf-eval) 2)

  ;; (defun satlink::eval-clause (lits cnf-eval)
  ;;   (declare (xargs :stobjs cnf-eval
  ;;                   :guard (lit-listp lits)))
  ;;   (if (atom lits)
  ;;       0
  ;;     (acl2::b-ior (satlink::eval-lit (car lits) cnf-eval)
  ;;                  (satlink::eval-clause (cdr lits) cnf-eval))))

  ;; (defthm bitp-satlink::eval-clause
  ;;   (acl2::bitp (satlink::eval-clause lits cnf-eval)))

  ;; (defcong nth-equiv equal (satlink::eval-clause lits cnf-eval) 2)

  (defun cnf-eval-conjunction (lits cnf-eval)
    (declare (xargs :stobjs cnf-eval
                    :guard (satlink::lit-listp lits)))
    (if (atom lits)
        1
      (acl2::b-and (satlink::eval-lit (car lits) cnf-eval)
                   (cnf-eval-conjunction (cdr lits) cnf-eval))))

  (defthm bitp-cnf-eval-conjunction
    (acl2::bitp (cnf-eval-conjunction lits cnf-eval)))

  (defcong bits-equiv equal (cnf-eval-conjunction lits cnf-eval) 2)


  ;; (defun satlink::eval-formula (clauses cnf-eval)
  ;;   (declare (xargs :stobjs cnf-eval
  ;;                   :guard (lit-list-listp clauses)))
  ;;   (if (atom clauses)
  ;;       1
  ;;     (acl2::b-and (satlink::eval-clause (car clauses) cnf-eval)
  ;;                  (satlink::eval-formula (cdr clauses) cnf-eval))))

  ;; (defthm bitp-satlink::eval-formula
  ;;   (acl2::bitp (satlink::eval-formula clauses cnf-eval)))

  ;; (defcong nth-equiv equal (satlink::eval-formula clauses cnf-eval) 2)

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
    (implies (not (equal (satlink::lit->var lit) (satlink::make-var var)))
             (equal (satlink::eval-lit lit (update-nth var val bits))
                    (satlink::eval-lit lit bits)))
    :hints(("Goal" :in-theory (enable satlink::eval-lit
                                      satlink::eval-var))))

  (defthm satlink::eval-clause-of-update-unused
    (implies (not (var-in-clause (satlink::make-var var) clause))
             (equal (satlink::eval-clause clause (update-nth var val bits))
                    (satlink::eval-clause clause bits)))
    :hints(("Goal" :in-theory (enable satlink::eval-clause))))

  (defthm cnf-eval-conjunction-of-update-unused
    (implies (not (var-in-clause (satlink::make-var var) conjunction))
             (equal (cnf-eval-conjunction conjunction (update-nth var val bits))
                    (cnf-eval-conjunction conjunction bits))))

  (defthm satlink::eval-formula-of-update-unused
    (implies (not (var-in-cnf (satlink::make-var var) cnf))
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
             (not (var-in-cnf var cnf))))


)


(defsection cnf/aignet-evals-agree
  (defun cnf/aignet-evals-agree (n in-vals reg-vals sat-lits cnf-eval aignet)
    (declare (xargs :stobjs (sat-lits cnf-eval aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (true-listp in-vals)
                                (true-listp reg-vals)
                                (sat-lits-wfp sat-lits aignet)
                                (natp n)
                                (aignet-iterator-p n aignet))
                    :measure (nfix (- (nfix (num-nodes aignet))
                                      (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-nodes aignet))
                           (nfix n)))
             :exec (int= (num-nodes aignet) n))
        t
      (and (or (not (aignet-id-has-sat-var (to-id n) sat-lits))
               (b* ((eval (id-eval (to-id n) in-vals reg-vals aignet))
                    (assign (satlink::eval-lit (aignet-id->sat-lit (to-id n)
                                                           sat-lits)
                                          cnf-eval)))
                 (int= eval assign)))
           (cnf/aignet-evals-agree (1+ (lnfix n)) in-vals reg-vals sat-lits cnf-eval
                                aignet))))

  (local (in-theory (disable satlink::eval-lit)))

  (defthm cnf/aignet-evals-agree-implies
    (implies (and (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)
                  (<= (nfix n) (id-val m))
                  (aignet-idp m aignet)
                  (aignet-id-has-sat-var m sat-lits))
             (equal (satlink::eval-lit (aignet-id->sat-lit m sat-lits) cnf-eval)
                    (id-eval m in-vals reg-vals aignet))))

  (defthm cnf/aignet-evals-agree-implies-mk-lit
    (implies (and (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)
                  (<= (nfix n) (id-val m))
                  (aignet-idp m aignet)
                  (aignet-id-has-sat-var m sat-lits))
             (equal (satlink::eval-lit (satlink::make-lit
                                        (satlink::lit->var (aignet-id->sat-lit m sat-lits))
                                        neg)
                                       cnf-eval)
                    (acl2::b-xor (acl2::b-xor neg (satlink::lit->neg (aignet-id->sat-lit m sat-lits)))
                                 (id-eval m in-vals reg-vals aignet))))
    :hints (("goal" :use cnf/aignet-evals-agree-implies
             :in-theory (e/d (satlink::eval-lit acl2::b-xor)
                             (satlink::eval-var
                              cnf/aignet-evals-agree-implies)))))

  (defthm cnf/aignet-evals-agree-implies-aignet-lit->sat-lit
    (implies (and (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)
                  (<= (nfix n) (id-val (lit-id m)))
                  (aignet-idp (lit-id m) aignet)
                  (aignet-id-has-sat-var (lit-id m) sat-lits))
             (equal (satlink::eval-lit (aignet-lit->sat-lit m sat-lits) cnf-eval)
                    (lit-eval m in-vals reg-vals aignet)))
    :hints(("Goal" :in-theory (enable acl2::b-xor lit-eval))))

  (defthmd sat-lits-wfp-implies-no-sat-var-when-out-of-range
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (<= (nfix (nth *num-nodes* aignet)) (id-val id))
                  (aignet-well-formedp aignet))
             (not (aignet-id-has-sat-var id sat-lits)))
    :hints (("goal" :in-theory (e/d (aignet-idp
                                     aignet-id-has-sat-var)
                                    (sat-lits-wfp-implies-when-not-aignet-idp))
             :use ((:instance sat-lits-wfp-implies-when-not-aignet-idp
                    (m id))))))

  (defthmd sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (not (aignet-idp (id-fix id) aignet))
                  (aignet-well-formedp aignet))
             (not (aignet-id-has-sat-var id sat-lits)))
    :hints (("goal" :in-theory (e/d (aignet-id-has-sat-var)
                                    (sat-lits-wfp-implies-when-not-aignet-idp))
             :use ((:instance sat-lits-wfp-implies-when-not-aignet-idp
                    (m id))))))

  (defthm cnf/aignet-evals-agree-of-extended-aignet
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval orig-aignet))
             (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval new-aignet))
    :hints ((acl2::just-induct-and-expand
             (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval new-aignet)
             :expand-others
             ((:free (aignet)
               (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet))))
            '(:in-theory (enable sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)
              :cases ((aignet-idp (to-id n) orig-aignet)))
            (and stable-under-simplificationp
                 '(:expand ((cnf/aignet-evals-agree (+ 1 n)
                                                 in-vals reg-vals sat-lits cnf-eval
                                                 orig-aignet)))))))


(defsection aignet->cnf-eval
  (defthm aignet-id->sat-lit-var-index-bound
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-id-has-sat-var n sat-lits))
             (< (satlink::var->index
                 (satlink::lit->var (aignet-id->sat-lit n sat-lits)))
                (nth *sat-next-var* sat-lits)))
    :hints (("goal" :use sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id
             :in-theory (e/d (sat-varp)
                             (sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id))))
    :rule-classes
    ((:rewrite)
     (:linear :trigger-terms ((satlink::var->index
                               (satlink::lit->var (aignet-id->sat-lit n sat-lits)))))))

  (defun aignet->cnf-eval (n in-vals reg-vals sat-lits cnf-eval aignet)
    (declare (xargs :stobjs (sat-lits cnf-eval aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (true-listp in-vals)
                                (true-listp reg-vals)
                                (sat-lits-wfp sat-lits aignet)
                                (natp n)
                                (aignet-iterator-p n aignet)
                                (<= (sat-next-var sat-lits) (bits-length cnf-eval)))
                    :measure (nfix (- (nfix (num-nodes aignet))
                                      (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-nodes aignet))
                           (nfix n)))
             :exec (int= (num-nodes aignet) n))
        cnf-eval
      (if (aignet-id-has-sat-var (to-id n) sat-lits)
          (b* ((eval (id-eval (to-id n) in-vals reg-vals aignet))
               (sat-lit (aignet-id->sat-lit (to-id n) sat-lits))
               (cnf-eval (set-bit
                          (satlink::var->index (satlink::lit->var sat-lit))
                          (acl2::b-xor eval (satlink::lit->neg sat-lit))
                          cnf-eval)))
            (aignet->cnf-eval (1+ (lnfix n)) in-vals reg-vals sat-lits cnf-eval aignet))
        (aignet->cnf-eval (1+ (lnfix n)) in-vals reg-vals sat-lits cnf-eval aignet))))

  (defthm sat-var->aignet-lit-0-when-sat-lits-wfp
    (implies (sat-lits-wfp sat-lits aignet)
             (equal (sat-var->aignet-lit 0 sat-lits) 0))
    :hints(("Goal" :in-theory (enable sat-lits-wfp))))

  (defthm aignet-id->sat-lit-0-when-sat-lits-wfp
    (implies (sat-lits-wfp sat-lits aignet)
             (equal (aignet-id->sat-lit 0 sat-lits) 0))
    :hints(("Goal" :in-theory (enable sat-lits-wfp))))

  (defthm aignet-id-has-sat-var-of-0
    (aignet-id-has-sat-var 0 sat-lits)
    :hints(("Goal" :in-theory (enable aignet-id-has-sat-var))))

  (defthm equal-of-aignet-id->sat-lits
    (implies (and (sat-lits-wfp sat-lits aignet)
                  ; (aignet-well-formedp aignet)
                  ;; (aignet-idp n aignet)
                  ;; (aignet-idp m aignet)
                  )
             (equal (equal (satlink::var->index (satlink::lit->var (aignet-id->sat-lit m sat-lits)))
                           (satlink::var->index (satlink::lit->var (aignet-id->sat-lit n sat-lits))))
                    (or (and (not (aignet-id-has-sat-var n sat-lits))
                             (not (aignet-id-has-sat-var m sat-lits)))
                        (and (not (aignet-id-has-sat-var n sat-lits))
                             (equal (id-val m) 0))
                        (and (not (aignet-id-has-sat-var m sat-lits))
                             (equal (id-val n) 0))
                        (equal (id-val m) (id-val n)))))
    :hints (("goal" :use ((:instance sat-lits-wfp-implies-lookup-aignet-id
                           (n n)
                           (id (satlink::lit->var (aignet-id->sat-lit n sat-lits))))
                          (:instance sat-lits-wfp-implies-lookup-aignet-id
                           (n m)
                           (id (satlink::lit->var (aignet-id->sat-lit m sat-lits))))
                          (:instance sat-lits-wfp-implies-lookup-aignet-id
                           (n 0)
                           (id (satlink::lit->var (aignet-id->sat-lit 0 sat-lits))))
                          (:instance lit-id-of-mk-lit
                           (id m) (neg (satlink::lit->neg (AIGNET-ID->SAT-LIT M SAT-LITS))))
                          (:instance lit-id-of-mk-lit
                           (id n) (neg (satlink::lit->neg (AIGNET-ID->SAT-LIT N
                                                                    SAT-LITS)))))
             :in-theory (disable sat-lits-wfp-implies-lookup-aignet-id
                                 lit-id-of-mk-lit
                                 equal-of-id-vals-when-idp))
            (and stable-under-simplificationp
                 '(:expand ((aignet-id-has-sat-var n sat-lits)
                            (aignet-id-has-sat-var m sat-lits))))))

  (defthm lookup-in-aignet->cnf-eval-prev
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (< (id-val m) (nfix n))
                  (aignet-idp m aignet))
             (equal (satlink::eval-lit
                     (aignet-id->sat-lit m sat-lits)
                     (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet))
                    (satlink::eval-lit
                     (aignet-id->sat-lit m sat-lits)
                     cnf-eval)))
    :hints (("goal" :induct t
             :in-theory (enable satlink::eval-lit
                                satlink::eval-var))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))))

  (local (in-theory (disable satlink::eval-lit)))

  (defthm lookup-in-aignet->cnf-eval
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (<= (nfix n) (id-val m))
                  (aignet-idp m aignet)
                  (aignet-id-has-sat-var m sat-lits))
             (equal (satlink::eval-lit
                     (aignet-id->sat-lit m sat-lits)
                     (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet))
                    (id-eval m in-vals reg-vals aignet)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable satlink::eval-lit
                                      satlink::eval-var)))))

  (local (defthm satlink::eval-lit-of-update
           (equal (satlink::eval-lit lit (update-nth id-val bit bits))
                  (if (equal (satlink::var->index (satlink::lit->var lit))
                             (nfix id-val))
                      (acl2::b-xor (acl2::bfix bit) (satlink::lit->neg lit))
                    (satlink::eval-lit lit bits)))
           :hints(("Goal" :in-theory (enable satlink::eval-lit
                                             satlink::eval-var)))))

  (defthm cnf/aignet-evals-agree-of-aignet->cnf-eval
    (implies (sat-lits-wfp sat-lits aignet)
             (cnf/aignet-evals-agree
              n in-vals reg-vals sat-lits
              (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet)
              aignet))
    :hints (("goal" :induct (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet))))


  (defthm aignet->cnf-eval-of-update-prev
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (< (id-val (lit-id (sat-var->aignet-lit (satlink::make-var var) sat-lits)))
                     (nfix n)))
             (equal (aignet->cnf-eval
                     n in-vals reg-vals sat-lits
                     (update-nth var val cnf-eval)
                     aignet)
                    (let ((cnf-eval
                           (aignet->cnf-eval
                            n in-vals reg-vals sat-lits cnf-eval aignet)))
                      (update-nth var val cnf-eval))))
    :hints (("goal" :induct (aignet->cnf-eval
                            n in-vals reg-vals sat-lits cnf-eval aignet)
             :expand ((:free (cnf-eval)
                       (aignet->cnf-eval
                        n in-vals reg-vals sat-lits cnf-eval aignet))))
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix var)
                                  (satlink::var->index
                                   (satlink::lit->var
                                    (aignet-id->sat-lit (to-id n)
                                                        sat-lits)))))))
            (and stable-under-simplificationp
                 '(:use ((:instance sat-lits-wfp-implies-lookup-aignet-id
                                    (id (satlink::make-var var))
                                    (n (to-id n))))
                   :in-theory (disable sat-lits-wfp-implies-lookup-aignet-id)))))

  (local (defthm sat-lits-wfp-implies-lookup-aignet-idbind-free
           (implies (and (bind-free '((aignet . aignet)))
                         (sat-lits-wfp sat-lits aignet)
                         (aignet-idp n aignet)
                         (aignet-id-has-sat-var n sat-lits))
                    (and (equal (sat-var->aignet-lit
                                 (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                                 sat-lits)
                                (mk-lit
                                 n (satlink::lit->neg (aignet-id->sat-lit n sat-lits))))
                         (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                                   sat-lits)))))


  (defthm id-eval-in-terms-of-lit-eval
    (equal (id-eval (lit-id lit) in-vals reg-vals aignet)
           (acl2::b-xor (lit-eval lit in-vals reg-vals aignet) (lit-neg lit)))
    :hints(("Goal" :in-theory (e/d (acl2::bitp lit-eval acl2::b-xor)
                                   (bitp-of-id-eval))
            :use ((:instance bitp-of-id-eval (id (lit-id lit)))))))

  (defthm aignet->cnf-eval-of-sat-add-aignet-lit
    (b* ((sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (sat-lit (aignet-lit->sat-lit lit sat-lits)))
      (implies (and (sat-lits-wfp orig-sat-lits aignet)
                    (aignet-litp (lit-fix lit) aignet))
               (equal (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet)
                      (if (or (< (id-val (lit-id lit)) (nfix n)))
                          (aignet->cnf-eval n in-vals reg-vals orig-sat-lits cnf-eval aignet)
                        (let ((cnf-eval (aignet->cnf-eval n in-vals reg-vals orig-sat-lits cnf-eval aignet)))
                          (update-nth (satlink::var->index (satlink::lit->var sat-lit))
                                      (acl2::b-xor (satlink::lit->neg sat-lit)
                                                   (lit-eval lit in-vals reg-vals aignet))
                                      cnf-eval))))))
    :hints (("goal" :induct
             (aignet->cnf-eval n in-vals reg-vals orig-sat-lits cnf-eval aignet)
             :expand ((:free (sat-lits cnf-eval)
                       (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet)))
             :in-theory (enable
                         aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-litp aignet-idp)))
            ))

  (defthmd sat-add-aignet-lit-when-not-aignet-litp
    (implies (not (aignet-litp (lit-fix lit) aignet))
             (equal (sat-add-aignet-lit lit sat-lits aignet)
                    sat-lits))
    :hints(("Goal" :in-theory (enable sat-add-aignet-lit))))

  (defthmd lookup-in-aignet->cnf-eval-special
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (sat-litp lit sat-lits))
             (equal (satlink::eval-lit lit
                                  (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval
                                                 aignet))
                    (acl2::b-xor (satlink::lit->neg lit)
                                 (lit-eval (sat-var->aignet-lit (satlink::lit->var lit) sat-lits)
                                           in-vals reg-vals aignet))))
    :hints (("goal" :use ((:instance lookup-in-aignet->cnf-eval
                           (m (lit-id (sat-var->aignet-lit (satlink::lit->var lit) sat-lits)))
                           (n 0)))
             :in-theory (e/d (satlink::eval-lit lit-eval acl2::b-xor)
                             (id-eval-in-terms-of-lit-eval
                              lookup-in-aignet->cnf-eval)))))


  (defthm satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (sat-litp sat-lit sat-lits1))
             (equal (satlink::eval-lit
                     sat-lit
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits2 cnf-eval aignet))
                    (satlink::eval-lit
                     sat-lit
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits1 cnf-eval aignet))))
    :hints(("Goal" :in-theory (enable lookup-in-aignet->cnf-eval-special))))


  (local (defthm sat-varp-of-id-fix
           (implies (sat-varp var sat-lits)
                    (sat-varp (satlink::var-fix var) sat-lits))
           :hints(("Goal" :in-theory (enable sat-varp)))))

  (defthm satlink::eval-var-of-aignet->cnf-eval-preserved-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (sat-varp var sat-lits1))
             (equal (satlink::eval-var
                     var
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits2 cnf-eval aignet))
                    (satlink::eval-var
                     var
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits1 cnf-eval aignet))))
    :hints(("Goal" :use ((:instance
                          satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                          (sat-lit (satlink::make-lit var 0))))
            :in-theory (e/d (satlink::eval-lit)
                            (satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                             satlink::eval-var)))))

  (defthm satlink::eval-clause-of-aignet->cnf-eval-preserved-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (sat-lit-listp clause sat-lits1))
             (equal (satlink::eval-clause
                     clause
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits2 cnf-eval aignet))
                    (satlink::eval-clause
                     clause
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits1 cnf-eval aignet))))
    :hints(("Goal" :use ((:instance
                          satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                          (sat-lit (satlink::make-lit var 0))))
            :in-theory (e/d (satlink::eval-lit)
                            (satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                             satlink::eval-var)))))

  (defthm satlink::eval-formula-of-aignet->cnf-eval-preserved-of-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (sat-lits-wfp sat-lits2 aignet)
                  (sat-lit-list-listp cnf sat-lits1))
             (equal (satlink::eval-formula
                     cnf
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits2 cnf-eval aignet))
                    (satlink::eval-formula
                     cnf
                     (aignet->cnf-eval
                      0 in-vals reg-vals sat-lits1 cnf-eval aignet))))
    :hints(("Goal" :use ((:instance
                          satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                          (sat-lit (satlink::make-lit var 0))))
            :in-theory (e/d (satlink::eval-lit)
                            (satlink::eval-lit-of-aignet->cnf-eval-preserved-of-extension
                             satlink::eval-var)))))

  ;; (defthm satlink::eval-lit-of-aignet->cnf-eval-preserved-of-sat-add-aignet-lit
  ;;   (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                 (sat-litp sat-lit sat-lits))
  ;;            (equal (satlink::eval-lit
  ;;                    sat-lit
  ;;                    (aignet->cnf-eval
  ;;                     0 in-vals reg-vals
  ;;                     (sat-add-aignet-lit lit sat-lits aignet)
  ;;                     cnf-eval aignet))
  ;;                   (satlink::eval-lit
  ;;                    sat-lit
  ;;                    (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet))))
  ;;   :hints(("Goal" :in-theory (enable sat-add-aignet-lit-when-not-aignet-litp
  ;;                                     lookup-in-aignet->cnf-eval-special
  ;;                                     satlink::eval-lit))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (e/d (aignet-litp
  ;;                                  aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit))))))


  ;; (defthm satlink::eval-var-of-aignet->cnf-eval-preserved-of-sat-add-aignet-lit
  ;;   (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                 (sat-varp var sat-lits))
  ;;            (equal (satlink::eval-var
  ;;                    var
  ;;                    (aignet->cnf-eval
  ;;                     0 in-vals reg-vals
  ;;                     (sat-add-aignet-lit lit sat-lits aignet)
  ;;                     cnf-eval aignet))
  ;;                   (satlink::eval-var
  ;;                    var
  ;;                    (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet))))
  ;;   :hints(("Goal" :use ((:instance
  ;;                         satlink::eval-lit-of-aignet->cnf-eval-preserved-of-sat-add-aignet-lit
  ;;                         (sat-lit (mk-lit var 0))))
  ;;           :in-theory (e/d (satlink::eval-lit)
  ;;                           (satlink::eval-lit-of-aignet->cnf-eval-preserved-of-sat-add-aignet-lit
  ;;                            satlink::eval-var)))))

  ;; ;; obsoleted by sat-lit-extension-p
  ;; (add-sat-lits-preservation-thm
  ;;  satlink::eval-clause-of-aignet->cnf-eval-preserved
  ;;  :vars (clause in-vals reg-vals cnf-eval)
  ;;  :body `(implies (and (sat-lits-wfp ,orig-stobj aignet)
  ;;                       (sat-lit-listp clause ,orig-stobj))
  ;;                  (equal (satlink::eval-clause
  ;;                          clause
  ;;                          (aignet->cnf-eval 0 in-vals reg-vals ,new-stobj cnf-eval aignet))
  ;;                         (satlink::eval-clause
  ;;                          clause
  ;;                          (aignet->cnf-eval 0 in-vals reg-vals ,orig-stobj cnf-eval
  ;;                                         aignet))))
  ;;  :hints `((acl2::just-induct-and-expand
  ;;            (satlink::eval-clause clause cnf-eval)
  ;;            :expand-others ((:free (cnf-eval) (satlink::eval-clause clause
  ;;                                                               cnf-eval))))))

  ;; ;; obsoleted by sat-lit-extension-p
  ;; (add-sat-lits-preservation-thm
  ;;  satlink::eval-formula-of-aignet->cnf-eval-preserved
  ;;  :vars (cnf in-vals reg-vals cnf-eval)
  ;;  :body `(implies (and (sat-lits-wfp ,orig-stobj aignet)
  ;;                       (sat-lit-list-listp cnf ,orig-stobj))
  ;;                  (equal (satlink::eval-formula
  ;;                          cnf
  ;;                          (aignet->cnf-eval 0 in-vals reg-vals ,new-stobj cnf-eval aignet))
  ;;                         (satlink::eval-formula
  ;;                          cnf
  ;;                          (aignet->cnf-eval 0 in-vals reg-vals ,orig-stobj cnf-eval
  ;;                                         aignet))))
  ;;  :hints `((acl2::just-induct-and-expand
  ;;            (satlink::eval-formula cnf cnf-eval)
  ;;            :expand-others ((:free (cnf-eval) (satlink::eval-formula cnf cnf-eval))))))

  (defthm aignet->cnf-eval-preserved-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet))
             (equal (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval new-aignet)
                    (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval orig-aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval new-aignet)
             :expand-others
             ((:free (aignet)
               (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval aignet))))
            '(:in-theory (e/d* (sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp))
              :cases ((aignet-idp (to-id n) orig-aignet)))
            (and stable-under-simplificationp
                 '(:expand ((aignet->cnf-eval (+ 1 n)
                                           in-vals reg-vals sat-lits cnf-eval
                                           orig-aignet))))))  ;; ;; obsoleted by sat-lit-extension-p
  ;; (retroactive-add-aignet-preservation-thm
  ;;  aignet->cnf-eval-preserved-aignet
  ;;  :vars (n in-vals reg-vals sat-lits cnf-eval)
  ;;  :body `(implies (and (sat-lits-wfp sat-lits ,orig-stobj)
  ;;                       (aignet-well-formedp ,orig-stobj))
  ;;                  (equal (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval
  ;;                                        ,new-stobj)
  ;;                         (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval
  ;;                                        ,orig-stobj)))
  ;;  :deps (id-eval-preserved)
  ;;  :hints `((acl2::just-induct-and-expand
  ;;            (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval ,new-stobj)
  ;;            :expand-others
  ;;            ((:free (stobj)
  ;;              (aignet->cnf-eval n in-vals reg-vals sat-lits cnf-eval stobj))))
  ;;           '(:in-theory (e/d* (aignet-frame-thms
  ;;                               sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)
  ;;                              (,fn))
  ;;             :cases ((aignet-idp (to-id n) ,orig-stobj)))
  ;;           (and stable-under-simplificationp
  ;;                '(:expand ((aignet->cnf-eval (+ 1 n)
  ;;                                          in-vals reg-vals sat-lits cnf-eval
  ;;                                          ,orig-stobj))))))
  )

(defsection cnf->aignet-in-vals
  (defund cnf->aignet-in-vals (n in-vals sat-lits cnf-eval aignet)
    (declare (xargs :stobjs (sat-lits cnf-eval aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (true-listp in-vals)
                                (sat-lits-wfp sat-lits aignet)
                                (natp n)
                                (<= n (num-ins aignet)))
                    :measure (nfix (- (nfix (num-ins aignet))
                                      (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-ins aignet))
                           (nfix n)))
             :exec (int= (num-ins aignet) n))
        in-vals
      (b* ((id (innum->id n aignet))
           ((unless (aignet-id-has-sat-var id sat-lits))
            (cnf->aignet-in-vals (1+ (lnfix n)) in-vals sat-lits cnf-eval aignet))
           (in-vals (update-nth n (satlink::eval-lit
                                   (aignet-id->sat-lit id sat-lits)
                                   cnf-eval)
                                in-vals)))
        (cnf->aignet-in-vals (1+ (lnfix n)) in-vals sat-lits cnf-eval aignet))))

  (local (in-theory (enable (:induction cnf->aignet-in-vals))))

  (defthm lookup-in-cnf->aignet-in-vals-prev
    (implies (< (nfix m) (nfix n))
             (equal (nth m (cnf->aignet-in-vals
                            n in-vals sat-lits cnf-eval aignet))
                    (nth m in-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))

  (defthm lookup-in-cnf->aignet-in-vals-no-sat-var
    (implies (not (aignet-id-has-sat-var (innum->id m aignet) sat-lits))
             (equal (nth m (cnf->aignet-in-vals
                            n in-vals sat-lits cnf-eval aignet))
                    (nth m in-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))

  (defthm lookup-in-cnf->aignet-in-vals
    (equal (nth m (cnf->aignet-in-vals
                   n in-vals sat-lits cnf-eval
                   aignet))
           (if (and (<= (nfix n) (nfix m))
                    (< (nfix m) (nfix (num-ins aignet)))
                    (aignet-id-has-sat-var (innum->id m aignet) sat-lits))
               (satlink::eval-lit (aignet-id->sat-lit (innum->id m aignet) sat-lits)
                             cnf-eval)
             (nth m in-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))

  (defthm cnf->aignet-in-vals-of-update-previous
    (implies (< (nfix m) (nfix n))
             (equal (cnf->aignet-in-vals n
                                         (update-nth m v in-vals)
                                         sat-lits cnf-eval aignet)
                    (let ((in-vals
                           (cnf->aignet-in-vals n in-vals
                                          sat-lits cnf-eval aignet)))
                      (update-nth m v in-vals))))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-in-vals n in-vals sat-lits cnf-eval
                                  aignet)
             :expand-others
             ((:free (in-vals)
               (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))))

  (defthm cnf->aignet-in-vals-of-sat-add-aignet-lit-prev
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (< (io-id->ionum (lit-id lit) aignet) (nfix n)))
             (equal (cnf->aignet-in-vals n in-vals (sat-add-aignet-lit lit sat-lits aignet)
                                         cnf-eval aignet)
                    (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)))
    :hints (("goal" :induct (cnf->aignet-in-vals n in-vals (sat-add-aignet-lit lit sat-lits aignet) cnf-eval aignet)
             :expand ((:free (sat-lits)
                       (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)))
             :in-theory (enable* ; aignet-litp aignet-idp
                         aignet-well-formedp-strong-rules
                         AIGNET-ID-HAS-SAT-VAR-PRESERVED-SPLIT-OF-SAT-ADD-AIGNET-LIT))))

  (defthm cnf->aignet-in-vals-of-sat-add-aignet-lit
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (equal (id->type (lit-id lit) aignet) (in-type))
                  (equal (io-id->regp (lit-id lit) aignet) 0)
                  (<= (nfix n) (io-id->ionum (lit-id lit) aignet)))
             (equal (cnf->aignet-in-vals n in-vals (sat-add-aignet-lit lit sat-lits aignet)
                                         cnf-eval aignet)
                    (let ((in-vals (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)))
                      (update-nth (io-id->ionum (lit-id lit) aignet)
                                  (satlink::eval-lit
                                   (aignet-id->sat-lit
                                    (lit-id lit)
                                    (sat-add-aignet-lit
                                     lit sat-lits aignet))
                                   cnf-eval)
                                  in-vals))))
    :hints (("goal" :induct (cnf->aignet-in-vals n in-vals (sat-add-aignet-lit lit sat-lits aignet) cnf-eval aignet)
             :expand ((:free (sat-lits)
                       (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)))
             :in-theory (enable* ; aignet-litp aignet-idp
                                       aignet-well-formedp-strong-rules
                                       AIGNET-ID-HAS-SAT-VAR-PRESERVED-SPLIT-OF-SAT-ADD-AIGNET-LIT))))


  (defthm cnf->aignet-in-vals-of-add-non-input-lit
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (not (equal (id->type (lit-id lit) aignet) (in-type))))
             (equal (cnf->aignet-in-vals n in-vals
                                   (sat-add-aignet-lit lit sat-lits
                                                    aignet)
                                   cnf-eval aignet)
                    (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)))
    :hints (("goal" :induct (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)
             :in-theory (enable*
                         aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit
                         aignet-well-formedp-strong-rules)
             :expand ((:free (sat-lits)
                       (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))))

  (defthm cnf->aignet-in-vals-of-aignet-extension
    (implies (and (aignet-extension-binding :new-aignet aignet)
                  (aignet-extension-p aignet orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp aignet))
             (equal (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)
                    (cnf->aignet-in-vals n in-vals sat-lits cnf-eval orig-aignet)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet)
             :expand-others
             ((:free (aignet)
               (cnf->aignet-in-vals n in-vals sat-lits cnf-eval aignet))))
            '(:in-theory (e/d*
                          (sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)
                          (aignet-well-formedp-innum))
              :use ((:instance aignet-well-formedp-innum
                     (n n)
                     (aignet aignet))))
            '(:cases ((aignet-idp (nth-id n (nth *insi* aignet)) orig-aignet)))
            (and stable-under-simplificationp
                 '(:expand ((cnf->aignet-in-vals (+ 1 (nfix n))
                                           in-vals sat-lits cnf-eval
                                           orig-aignet))))))


  (local (defthm equal-of-b-xor-equal
           (equal (equal (acl2::b-xor c a) (acl2::b-xor c b))
                  (equal (acl2::bfix a) (acl2::bfix b)))
           :hints(("Goal" :in-theory (enable acl2::b-xor acl2::bfix)))))

  (defthm id-eval-of-cnf->aignet-in-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-idp id orig-aignet))
             (equal (id-eval id (cnf->aignet-in-vals n in-vals sat-lits cnf-eval
                                               new-aignet)
                             reg-vals orig-aignet)
                    (id-eval id (cnf->aignet-in-vals n in-vals sat-lits cnf-eval
                                               orig-aignet)
                             reg-vals orig-aignet)))
    :hints (("goal" :induct
             (id-eval-ind id in-vals reg-vals orig-aignet)
             :expand
             ((:free (in-vals) (id-eval id in-vals reg-vals orig-aignet))))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-extension-implies-num-ins-incr))))))

  (defthm lit-eval-of-cnf->aignet-in-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-litp lit orig-aignet))
             (equal (lit-eval lit (cnf->aignet-in-vals n in-vals sat-lits
                                                       cnf-eval new-aignet)
                              reg-vals orig-aignet)
                    (lit-eval lit (cnf->aignet-in-vals n in-vals sat-lits
                                                       cnf-eval orig-aignet)
                              reg-vals orig-aignet)))
    :hints (("goal" :in-theory (disable id-eval-in-terms-of-lit-eval)
             :expand ((:free (in-vals aignet) (lit-eval lit in-vals reg-vals
                                                        aignet)))))))

(defsection cnf->aignet-reg-vals
  (defund cnf->aignet-reg-vals (n reg-vals sat-lits cnf-eval aignet)
    (declare (xargs :stobjs (sat-lits cnf-eval aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (true-listp reg-vals)
                                (sat-lits-wfp sat-lits aignet)
                                (natp n)
                                (<= n (num-regs aignet)))
                    :measure (nfix (- (nfix (num-regs aignet))
                                      (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-regs aignet))
                           (nfix n)))
             :exec (int= (num-regs aignet) n))
        reg-vals
      (b* ((id (regnum->ro n aignet))
           ((unless (aignet-id-has-sat-var id sat-lits))
            (cnf->aignet-reg-vals (1+ (lnfix n)) reg-vals sat-lits cnf-eval aignet))
           (reg-vals (update-nth n (satlink::eval-lit
                                   (aignet-id->sat-lit id sat-lits)
                                   cnf-eval)
                                reg-vals)))
        (cnf->aignet-reg-vals (1+ (lnfix n)) reg-vals sat-lits cnf-eval aignet))))

  (local (in-theory (enable (:induction cnf->aignet-reg-vals))))

  (defthm lookup-in-cnf->aignet-reg-vals-prev
    (implies (< (nfix m) (nfix n))
             (equal (nth m (cnf->aignet-reg-vals
                            n reg-vals sat-lits cnf-eval aignet))
                    (nth m reg-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))

  (defthm lookup-in-cnf->aignet-reg-vals-no-sat-var
    (implies (not (aignet-id-has-sat-var (regnum->ro m aignet) sat-lits))
             (equal (nth m (cnf->aignet-reg-vals
                            n reg-vals sat-lits cnf-eval aignet))
                    (nth m reg-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))

  (defthm lookup-in-cnf->aignet-reg-vals
    (equal (nth m (cnf->aignet-reg-vals
                   n reg-vals sat-lits cnf-eval
                   aignet))
           (if (and (<= (nfix n) (nfix m))
                    (< (nfix m) (nfix (num-regs aignet)))
                    (aignet-id-has-sat-var (regnum->ro m aignet) sat-lits))
               (satlink::eval-lit (aignet-id->sat-lit (regnum->ro m aignet) sat-lits)
                             cnf-eval)
             (nth m reg-vals)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))

  (defthm cnf->aignet-reg-vals-of-update-previous
    (implies (< (nfix m) (nfix n))
             (equal (cnf->aignet-reg-vals n
                                         (update-nth m v reg-vals)
                                         sat-lits cnf-eval aignet)
                    (let ((reg-vals
                           (cnf->aignet-reg-vals n reg-vals
                                          sat-lits cnf-eval aignet)))
                      (update-nth m v reg-vals))))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval
                                  aignet)
             :expand-others
             ((:free (reg-vals)
               (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))))

  (defthm cnf->aignet-reg-vals-of-sat-add-aignet-lit-prev
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (< (io-id->ionum (lit-id lit) aignet) (nfix n)))
             (equal (cnf->aignet-reg-vals n reg-vals (sat-add-aignet-lit lit sat-lits aignet)
                                         cnf-eval aignet)
                    (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)))
    :hints (("goal" :induct (cnf->aignet-reg-vals n reg-vals (sat-add-aignet-lit lit sat-lits aignet) cnf-eval aignet)
             :expand ((:free (sat-lits)
                       (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)))
             :in-theory (enable* ; aignet-litp aignet-idp
                         aignet-well-formedp-strong-rules
                         AIGNET-ID-HAS-SAT-VAR-PRESERVED-SPLIT-OF-SAT-ADD-AIGNET-LIT))))

  (defthm cnf->aignet-reg-vals-of-sat-add-aignet-lit
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (equal (id->type (lit-id lit) aignet) (in-type))
                  (equal (io-id->regp (lit-id lit) aignet) 1)
                  (<= (nfix n) (io-id->ionum (lit-id lit) aignet)))
             (equal (cnf->aignet-reg-vals n reg-vals (sat-add-aignet-lit lit sat-lits aignet)
                                         cnf-eval aignet)
                    (let ((reg-vals (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)))
                      (update-nth (io-id->ionum (lit-id lit) aignet)
                                  (satlink::eval-lit
                                   (aignet-id->sat-lit
                                    (lit-id lit)
                                    (sat-add-aignet-lit
                                     lit sat-lits aignet))
                                   cnf-eval)
                                  reg-vals))))
    :hints (("goal" :induct (cnf->aignet-reg-vals n reg-vals (sat-add-aignet-lit lit sat-lits aignet) cnf-eval aignet)
             :expand ((:free (sat-lits)
                       (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)))
             :in-theory (enable* ; aignet-litp aignet-idp
                                       aignet-well-formedp-strong-rules
                                       AIGNET-ID-HAS-SAT-VAR-PRESERVED-SPLIT-OF-SAT-ADD-AIGNET-LIT))))


  (defthm cnf->aignet-reg-vals-of-add-non-input-lit
    (implies (and (aignet-well-formedp aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit aignet)
                  (not (equal (id->type (lit-id lit) aignet) (in-type))))
             (equal (cnf->aignet-reg-vals n reg-vals
                                   (sat-add-aignet-lit lit sat-lits
                                                    aignet)
                                   cnf-eval aignet)
                    (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)))
    :hints (("goal" :induct (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)
             :in-theory (enable*
                         aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit
                         aignet-well-formedp-strong-rules)
             :expand ((:free (sat-lits)
                       (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))))

  (defthm cnf->aignet-reg-vals-of-aignet-extension
    (implies (and (aignet-extension-binding :new-aignet aignet)
                  (aignet-extension-p aignet orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp aignet))
             (equal (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)
                    (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval orig-aignet)))
    :hints ((acl2::just-induct-and-expand
             (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet)
             :expand-others
             ((:free (aignet)
               (cnf->aignet-reg-vals n reg-vals sat-lits cnf-eval aignet))))
            '(:in-theory (e/d*
                          (sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)
                          (regin-id->ro-of-regnum-id)))
            ;; '(:cases ((aignet-idp (regnum->ro n aignet) orig-aignet)))
            (and stable-under-simplificationp
                 '(:expand ((cnf->aignet-reg-vals (+ 1 (nfix n))
                                           reg-vals sat-lits cnf-eval
                                           orig-aignet))))))


  (local (defthm equal-of-b-xor-equal
           (equal (equal (acl2::b-xor c a) (acl2::b-xor c b))
                  (equal (acl2::bfix a) (acl2::bfix b)))
           :hints(("Goal" :in-theory (enable acl2::b-xor acl2::bfix)))))

  (defthm id-eval-of-cnf->aignet-reg-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-idp id orig-aignet))
             (equal (id-eval id in-vals
                             (cnf->aignet-reg-vals
                              n reg-vals sat-lits cnf-eval new-aignet)
                             orig-aignet)
                    (id-eval id in-vals
                             (cnf->aignet-reg-vals
                              n reg-vals sat-lits cnf-eval orig-aignet)
                             orig-aignet)))
    :hints (("goal" :induct
             (id-eval-ind id in-vals reg-vals orig-aignet)
             :expand
             ((:free (reg-vals) (id-eval id in-vals reg-vals orig-aignet))))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-extension-implies-num-regs-incr))))))

  (defthm lit-eval-of-cnf->aignet-reg-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-litp lit orig-aignet))
             (equal (lit-eval lit in-vals
                              (cnf->aignet-reg-vals n reg-vals sat-lits
                                                    cnf-eval new-aignet)
                              orig-aignet)
                    (lit-eval lit in-vals
                              (cnf->aignet-reg-vals n reg-vals sat-lits
                                                       cnf-eval orig-aignet)
                              orig-aignet)))
    :hints (("goal" :in-theory (disable id-eval-in-terms-of-lit-eval)
             :expand ((:free (reg-vals aignet) (lit-eval lit in-vals reg-vals
                                                        aignet)))))))




(defsection sat-lits-covered
  ;; (defun sat-add-aignet-lits (lits sat-lits aignet)
  ;;   (Declare (xargs :stobjs (sat-lits aignet)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (sat-lits-wfp sat-lits aignet)
  ;;                               (aignet-lit-listp lits aignet))))
  ;;   (if (atom lits)
  ;;       sat-lits
  ;;     (let ((sat-lits (sat-add-aignet-lits (cdr lits) sat-lits aignet)))
  ;;       (sat-add-aignet-lit (car lits) sat-lits aignet))))

  ;; (retroactive-add-aignet-preservation-thm
  ;;  sat-add-aignet-lit-preserved-aignet
  ;;  :vars (lit sat-lits)
  ;;  :body `(implies (aignet-litp lit ,orig-stobj)
  ;;                  (equal (sat-add-aignet-lit lit sat-lits ,new-stobj)
  ;;                         (sat-add-aignet-lit lit sat-lits ,orig-stobj)))
  ;;  :hints `('(:expand ((sat-add-aignet-lit lit sat-lits ,new-stobj)
  ;;                      (sat-add-aignet-lit lit sat-lits ,orig-stobj)))))

  ;; (retroactive-add-aignet-preservation-thm
  ;;  sat-add-aignet-lits-preserved-aignet
  ;;  :vars (lits sat-lits)
  ;;  :body `(implies (aignet-lit-listp lits ,orig-stobj)
  ;;                  (equal (sat-add-aignet-lits lits sat-lits ,new-stobj)
  ;;                         (sat-add-aignet-lits lits sat-lits ,orig-stobj)))
  ;;  :hints `((acl2::just-induct-and-expand
  ;;            (sat-add-aignet-lits lits sat-lits ,orig-stobj)
  ;;            :expand-others
  ;;            ((:free (stobj)
  ;;              (sat-add-aignet-lits lits sat-lits stobj))))))

  ;; (def-sat-lits-preservation-thms sat-add-aignet-lits)

  ;; (defthm sat-lits-wfp-of-sat-add-aignet-lits
  ;;   (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                 (aignet-lit-listp lits aignet))
  ;;            (sat-lits-wfp (sat-add-aignet-lits lits sat-lits aignet) aignet)))

  ;; ;; Old definition pre sat-lit-extension-p
  ;; ;; We need to know this invariant about sat-lits to show that adding a CI
  ;; ;; doesn't disrupt the evaluations of previously added nodes.  Basically,
  ;; ;; we're requiring that for any node with a SAT var, a sufficient set of CIs
  ;; ;; have SAT vars to force the node's value.
  ;; ;; We need to allow sat-add-aignet-lits rather than the singular because
  ;; ;; otherwise we get into a logical trap when trying to prove
  ;; ;; SAT-LITS-COVERED-OF-ADD-NON-GATE, below, where we run into a situation
  ;; ;; where adding lit 1 or lit 2 is no problem but adding both breaks it.
  ;; (defun-sk sat-lits-covered (sat-lits aignet)
  ;;   (forall (lit add-lits cnf-eval aignet-vals)
  ;;           (implies (and (aignet-id-has-sat-var (lit-id lit) sat-lits)
  ;;                         (aignet-litp lit aignet))
  ;;                    (equal (lit-eval lit (cnf->aignet-vals
  ;;                                          0 aignet-vals
  ;;                                          (sat-add-aignet-lits add-lits sat-lits aignet)
  ;;                                          cnf-eval aignet)
  ;;                                     aignet)
  ;;                           (lit-eval lit (cnf->aignet-vals
  ;;                                          0 aignet-vals sat-lits cnf-eval aignet)
  ;;                                     aignet))))
  ;;   :rewrite :direct)



  ;; We need to know this invariant about sat-lits to show that adding a CI
  ;; doesn't disrupt the evaluations of previously added nodes.  Basically,
  ;; we're requiring that for any node with a SAT var, a sufficient set of CIs
  ;; have SAT vars to force the node's value.
  (defun-sk sat-lits-covered (sat-lits1 aignet)
    (forall (lit sat-lits2 cnf-eval in-vals reg-vals)
            (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
                          ;; (sat-lits-wfp sat-lits2 aignet)
                          (aignet-id-has-sat-var (lit-id lit) sat-lits1)
                          (aignet-litp lit aignet))
                     (equal (lit-eval lit
                                      (cnf->aignet-in-vals
                                       0 in-vals sat-lits2 cnf-eval aignet)
                                      (cnf->aignet-reg-vals
                                       0 reg-vals sat-lits2 cnf-eval aignet)
                                      aignet)
                            (lit-eval lit
                                      (cnf->aignet-in-vals
                                       0 in-vals sat-lits1 cnf-eval aignet)
                                      (cnf->aignet-reg-vals
                                       0 reg-vals sat-lits1 cnf-eval aignet)
                                      aignet))))
    :rewrite :direct)


  (defthm sat-lits-covered-of-create
    (implies (aignet-well-formedp aignet)
             (sat-lits-covered (create-sat-lits) aignet))
    :hints(("Goal" :in-theory (e/d (aignet-id-has-sat-var
                                    nth lit-eval)
                                   (create-sat-lits)))))

  (defthm sat-lits-covered-of-resize-of-create
    (implies (aignet-well-formedp aignet)
             (sat-lits-covered (resize-aignet->sat n (create-sat-lits))
                               aignet))
    :hints(("Goal" :in-theory (e/d (aignet-id-has-sat-var
                                    sat-lits-covered
                                    nth lit-eval)
                                   (create-sat-lits)))))

  (in-theory (disable sat-lits-covered
                      sat-lits-covered-necc))

  (defun-sk has-covered-ancestor-with-var (id sat-lits2 aignet)
    (exists sat-lits1
            (and (sat-lit-extension-p sat-lits2 sat-lits1)
                 (sat-lits-covered sat-lits1 aignet)
                 (aignet-id-has-sat-var id sat-lits1))))

  (in-theory (disable has-covered-ancestor-with-var
                      has-covered-ancestor-with-var-suff))

  (defthm has-covered-ancestor-iterate
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (has-covered-ancestor-with-var id sat-lits1 aignet))
             (has-covered-ancestor-with-var id sat-lits2 aignet))
    :hints(("Goal" :in-theory (disable has-covered-ancestor-with-var
                                       has-covered-ancestor-with-var-suff)
            :expand ((has-covered-ancestor-with-var id sat-lits1 aignet))
            :use ((:instance has-covered-ancestor-with-var-suff
                   (sat-lits1 (has-covered-ancestor-with-var-witness
                               id sat-lits1 aignet)))))))

  (defthm has-covered-ancestor-self
    (implies (and (sat-lits-covered sat-lits2 aignet)
                  (aignet-id-has-sat-var id sat-lits2))
             (has-covered-ancestor-with-var id sat-lits2 aignet))
    :hints (("goal" :use ((:instance has-covered-ancestor-with-var-suff
                           (sat-lits1 sat-lits2))))))

  (defthm sat-lits-covered-rw
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-covered sat-lits1 aignet)
                  (aignet-id-has-sat-var (lit-id lit) sat-lits1)
                  ;; (sat-lits-wfp sat-lits2 aignet)
                  (aignet-litp lit aignet))
             (equal (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits2 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits2 cnf-eval aignet)
                              aignet)
                    (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits1 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits1 cnf-eval aignet)
                              aignet)))
    :hints(("Goal" :use ((:instance sat-lits-covered-necc))
                         ;;  (sat-lits1
                         ;;   (has-covered-ancestor-with-var-witness
                         ;;    (lit-id lit) sat-lits1 aignet)))
                         ;; (:instance sat-lits-covered-necc
                         ;;  (sat-lits1
                         ;;   (has-covered-ancestor-with-var-witness
                         ;;    (lit-id lit) sat-lits1 aignet))
                         ;;  (sat-lits2 sat-lits1)))
            ;; :expand ((has-covered-ancestor-with-var (lit-id lit) sat-lits1 aignet))
            )))

  (defthm sat-lits-covered-ancestor
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (has-covered-ancestor-with-var (lit-id lit) sat-lits1 aignet)
                  (aignet-litp lit aignet))
             (equal (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits2 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits2 cnf-eval aignet)
                              aignet)
                    (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits1 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits1 cnf-eval aignet)
                              aignet)))
    :hints(("Goal" :use ((:instance sat-lits-covered-necc
                          (sat-lits1
                           (has-covered-ancestor-with-var-witness
                            (lit-id lit) sat-lits1 aignet)))
                         (:instance sat-lits-covered-necc
                          (sat-lits1
                           (has-covered-ancestor-with-var-witness
                            (lit-id lit) sat-lits1 aignet))
                          (sat-lits2 sat-lits1)))
            :expand ((has-covered-ancestor-with-var (lit-id lit) sat-lits1 aignet)))))

  (defthm lit-eval-non-gate-of-cnf->aignet-eval-of-sat-lit-extension
    (implies (and (sat-lit-extension-binding)
                  (sat-lit-extension-p sat-lits2 sat-lits1)
                  (sat-lits-wfp sat-lits1 aignet)
                  (aignet-well-formedp aignet)
                  (aignet-litp lit aignet)
                  (not (equal (id->type (lit-id lit) aignet) (gate-type)))
                  (aignet-id-has-sat-var (lit-id lit) sat-lits1))
             (equal (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits2 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits2 cnf-eval aignet)
                              aignet)
                    (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits1 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits1 cnf-eval aignet)
                              aignet)))
    :hints (("goal" :expand ((:free (in-vals reg-vals)
                              (lit-eval lit in-vals reg-vals aignet))
                             (:free (in-vals reg-vals)
                              (id-eval (lit-id lit) in-vals reg-vals aignet)))
             :in-theory (e/d (aignet-litp)
                             (id-eval-in-terms-of-lit-eval)))))

  (local (defun trivial-worse-than-or-equal (term1 term2)
           (declare (xargs :guard t)
                    (ignorable term1 term2))
           nil))

  (local (defattach acl2::worse-than-or-equal trivial-worse-than-or-equal))

  (defthm sat-lits-covered-of-add-non-gate
    (implies (and (sat-lits-covered sat-lits aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-well-formedp aignet)
                  (aignet-litp lit aignet)
                  (not (equal (id->type (lit-id lit) aignet) (gate-type))))
             (sat-lits-covered (sat-add-aignet-lit lit sat-lits aignet) aignet))
    :hints ((and stable-under-simplificationp
                 (let ((concl (car (last clause))))
                   `(:expand (,concl)
                     :in-theory (e/d
                                 (aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                                 (sat-lit-extension-p-transitive))
                     ;; :use ((:instance sat-lit-extension-p-transitive
                     ;;        (sat-lits3 (mv-nth 1 (sat-lits-covered-witness
                     ;;                              (sat-add-aignet-lit lit sat-lits
                     ;;                                               aignet)
                     ;;                              aignet)))
                     ;;        (sat-lits2 (sat-add-aignet-lit lit sat-lits aignet))
                     ;;        (sat-lits1 sat-lits)))
                     ))))
    :otf-flg t)

  (defthm sat-lits-covered-of-aignet-extension-lemma
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (sat-lits-covered sat-lits orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (let ((sat-lits1 sat-lits)
                   (aignet new-aignet))
               (implies (and (sat-lit-extension-p sat-lits2 sat-lits1)
                             (aignet-id-has-sat-var (lit-id lit) sat-lits1)
                             (aignet-litp lit aignet))
                        (equal (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits2 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits2 cnf-eval aignet)
                              aignet)
                    (lit-eval lit
                              (cnf->aignet-in-vals
                               0 in-vals sat-lits1 cnf-eval aignet)
                              (cnf->aignet-reg-vals
                               0 reg-vals sat-lits1 cnf-eval aignet)
                              aignet))
                        ;; (equal (lit-eval lit (cnf->aignet-vals
                        ;;                       0 aignet-vals sat-lits2 cnf-eval aignet)
                        ;;                  aignet)
                        ;;        (lit-eval lit (cnf->aignet-vals
                        ;;                       0 aignet-vals sat-lits1 cnf-eval aignet)
                        ;;                  aignet))
                        )))
    :hints (("goal" :cases ((aignet-idp (lit-id lit) orig-aignet))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp
                               aignet-litp))))
    :otf-flg t)

  (defthm sat-lits-covered-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (sat-lits-covered sat-lits orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (sat-lits-covered sat-lits new-aignet))
    :hints ((and stable-under-simplificationp
                 (let ((concl (car (last clause))))
                   `(:expand (,concl)))))))



(defsection mux-clauses
  (defun mux-add-clauses (res-id c tb fb sat-lits cnf-acc)
    (declare (Xargs :stobjs (sat-lits)
                    :guard (and (idp res-id) (litp c) (litp tb) (litp fb))))
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

  (defthm lit-list-listp-of-mux-add-clauses
    (implies (satlink::lit-list-listp cnf-acc)
             (satlink::lit-list-listp (mux-add-clauses res c tb fb sat-lits cnf-acc))))

  ;; (defthm satlink::eval-lit-of-mk-lit
  ;;   (equal (satlink::eval-lit ( (lit-id lit) neg) cnf-eval)
  ;;          (acl2::b-xor (acl2::b-xor (lit-neg lit) neg)
  ;;                       (satlink::eval-lit lit cnf-eval)))
  ;;   :hints(("Goal" :in-theory (enable acl2::b-xor
  ;;                                     satlink::eval-lit))))

  (defthm b-xor-of-b-not
    (and (equal (acl2::b-xor (acl2::b-not x) y)
                (acl2::b-not (acl2::b-xor x y)))
         (equal (acl2::b-xor y (acl2::b-not x))
                (acl2::b-not (acl2::b-xor y x))))
    :hints(("Goal" :in-theory (enable acl2::b-xor acl2::b-not))))

  (local (in-theory (disable satlink::eval-lit)))

  ;; (defthm mux-add-clauses-forces-res-value
  ;;   (implies (equal (satlink::eval-formula (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
  ;;                                 cnf-eval) 1)
  ;;            (equal (satlink::eval-lit (aignet-id->sat-lit res-id sat-lits) cnf-eval)
  ;;                   (acl2::b-ior
  ;;                    (acl2::b-and (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval)
  ;;                                 (satlink::eval-lit (aignet-lit->sat-lit tb sat-lits) cnf-eval))
  ;;                    (acl2::b-and (acl2::b-not (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval))
  ;;                                 (satlink::eval-lit (aignet-lit->sat-lit fb sat-lits)
  ;;                                               cnf-eval)))))
  ;;   :hints((and stable-under-simplificationp
  ;;               '(:in-theory (e/d (acl2::b-and acl2::b-ior)
  ;;                                 (satlink::eval-lit))))))

  ;; (defthm mux-add-clauses-forces-previous-cnf
  ;;   (implies (not (equal (satlink::eval-formula orig-cnf cnf-eval) 1))
  ;;            (equal (satlink::eval-formula (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
  ;;                                 cnf-eval) 0))
  ;;   :hints((and stable-under-simplificationp
  ;;               '(:in-theory (e/d (acl2::b-and)
  ;;                                 (satlink::eval-lit))))))

  ;; (defthm mux-add-clauses-when-res-value-and-prev-cnf
  ;;   (implies (and (equal (satlink::eval-formula orig-cnf cnf-eval) 1)
  ;;                 (equal (satlink::eval-lit (aignet-id->sat-lit res-id sat-lits) cnf-eval)
  ;;                        (acl2::b-ior
  ;;                         (acl2::b-and (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval)
  ;;                                      (satlink::eval-lit (aignet-lit->sat-lit tb sat-lits) cnf-eval))
  ;;                         (acl2::b-and (acl2::b-not (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval))
  ;;                                      (satlink::eval-lit (aignet-lit->sat-lit fb sat-lits)
  ;;                                                    cnf-eval)))))
  ;;            (equal (satlink::eval-formula (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
  ;;                                 cnf-eval) 1))
  ;;   :hints((and stable-under-simplificationp
  ;;               '(:in-theory (e/d (acl2::b-and acl2::b-ior)
  ;;                                 (satlink::eval-lit))))))

  (defthm mux-add-clauses-correct
    (equal (satlink::eval-formula (mux-add-clauses res-id c tb fb sat-lits orig-cnf)
                         cnf-eval)
           (if (and (equal (satlink::eval-formula orig-cnf cnf-eval) 1)
                    (equal (satlink::eval-lit (aignet-id->sat-lit res-id sat-lits) cnf-eval)
                           (acl2::b-ior
                            (acl2::b-and (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval)
                                         (satlink::eval-lit (aignet-lit->sat-lit tb sat-lits) cnf-eval))
                            (acl2::b-and (acl2::b-not (satlink::eval-lit (aignet-lit->sat-lit c sat-lits) cnf-eval))
                                         (satlink::eval-lit (aignet-lit->sat-lit fb sat-lits)
                                                       cnf-eval)))))
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


  (local (in-theory (disable cnf->aignet-in-vals
                             cnf->aignet-reg-vals
                             cnf/aignet-evals-agree)))

  ;; (defthm id-eval-of-update-greater-id
  ;;   (implies (< (id-val id) (nfix n))
  ;;            (equal (id-eval id (update-nth *bitsi* (update-nth n v bits)
  ;;                                           aignet-vals)
  ;;                            aignet)
  ;;                   (id-eval id (update-nth *bitsi* bits aignet-vals) aignet)))
  ;;   :hints(("Goal" :in-theory (enable gate-orderedp co-orderedp
  ;;                                     id-eval-redef lit-eval)
  ;;           :induct (id-eval id (update-nth *bitsi* bits aignet-vals) aignet))))

  ;; (defthm lit-eval-of-update-greater-id
  ;;   (implies (< (id-val (lit-id lit)) (nfix n))
  ;;            (equal (lit-eval lit (update-nth *bitsi* (update-nth n v bits)
  ;;                                            aignet-vals)
  ;;                             aignet)
  ;;                   (lit-eval lit (update-nth *bitsi* bits aignet-vals) aignet)))
  ;;   :hints(("Goal" :in-theory (enable lit-eval))))

  (defthm id-order-of-id-is-mux
    (b* (((mv is-mux c tb fb) (id-is-mux id aignet)))
      (implies is-mux
               (and (< (id-val (lit-id c)) (id-val id))
                    (< (id-val (lit-id tb)) (id-val id))
                    (< (id-val (lit-id fb)) (id-val id)))))
    :hints(("Goal" :in-theory (enable id-is-mux gate-orderedp)))
    :rule-classes (:rewrite :linear))


  (defthm id-type-when-is-mux
    (implies (mv-nth 0 (id-is-mux id aignet))
             (equal (node->type (nth-node id (nth *nodesi* aignet)))
                    (gate-type)))
    :hints(("Goal" :in-theory (enable id-is-mux))))


  (defthm mux-add-clauses-new-sat-lit-eval-correct
    (b* (((mv is-mux c tb fb) (id-is-mux id aignet))
         (lit (mk-lit id 0))
         (sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (sat-lit (aignet-lit->sat-lit lit sat-lits))
         (cnf (mux-add-clauses id c tb fb sat-lits orig-cnf)))
      (implies (and (cnf/aignet-evals-agree
                     0 in-vals reg-vals
                     orig-sat-lits
                     cnf-eval aignet)
                    (sat-lits-wfp orig-sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-idp id aignet)
                    is-mux
                    (aignet-id-has-sat-var (lit-id c) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id tb) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id fb) orig-sat-lits)
                    (equal (satlink::eval-formula cnf cnf-eval) 1))
               (equal (satlink::eval-lit sat-lit cnf-eval)
                      (id-eval
                       id in-vals reg-vals
                       aignet))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (id-eval-when-id-is-mux
                              equal-1-by-bitp)
                             (satlink::eval-lit
                              commutativity-2-of-b-xor)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not))))))

  (defthm mux-add-clauses-cnf->aignet-eval-agrees
    (b* (((mv is-mux c tb fb) (id-is-mux id aignet))
         (lit (mk-lit id 0))
         (sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (cnf (mux-add-clauses id c tb fb sat-lits orig-cnf)))
      (implies (and (cnf/aignet-evals-agree
                     0 in-vals reg-vals orig-sat-lits cnf-eval aignet)
                    (sat-lits-wfp orig-sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-idp id aignet)
                    is-mux
                    (aignet-id-has-sat-var (lit-id c) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id tb) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id fb) orig-sat-lits)
                    (equal (satlink::eval-formula cnf cnf-eval) 1))
               (cnf/aignet-evals-agree
                n in-vals reg-vals sat-lits cnf-eval aignet)))
    :hints (("Goal" :induct (cnf/aignet-evals-agree
                             n in-vals reg-vals
                             (sat-add-aignet-lit
                              (mk-lit id 0)
                              orig-sat-lits aignet)
                             cnf-eval aignet)
             :do-not-induct t
             :expand ((:free (in-vals reg-vals sat-lits)
                       (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)))
             :in-theory (e/d ((:induction cnf/aignet-evals-agree)
                              aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                             (mux-add-clauses-correct
                              satlink::eval-lit
                              mux-add-clauses-new-sat-lit-eval-correct)))
            (and stable-under-simplificationp
                 '(:use mux-add-clauses-new-sat-lit-eval-correct))))


  ;; The above says:
  ;; A satisfying assignment induces an evaluation of the circuit where the
  ;; evaluation and the satisfying assignment agree.

  ;; Remains to show:
  ;; An evaluation of the circuit induces a satifying assignment.
  ;; (We have already proved that the way we produce an assignment from an
  ;; evaluation, the evaluation and assignment agree:
  ;; see cnf/aignet-evals-agree-of-aignet->cnf-eval.



  ;; (local
  ;;  (encapsulate nil
  ;;      (local (defthm unequal-by-sat-varp
  ;;          (implies (and (bind-free '((sat-lits . orig-sat-lits)))
  ;;                        (sat-varp x sat-lits)
  ;;                        (idp y)
  ;;                        (not (sat-varp y sat-lits)))
  ;;                   (not (equal (id-val x) (id-val y))))
  ;;          :hints(("Goal" :in-theory (enable sat-varp)))))

  ;;      (defthm sat-vars-not-equal-lemma
  ;;        (implies (and (sat-lits-wfp orig-sat-lits aignet)
  ;;                      (aignet-idp id aignet)
  ;;                      (aignet-id-has-sat-var id orig-sat-lits)
  ;;                      (not (aignet-id-has-sat-var id1 orig-sat-lits))
  ;;                      (aignet-litp lit aignet)
  ;;                      (equal (id-fix id1) (lit-id lit)))
  ;;                 (NOT
  ;;                  (EQUAL
  ;;                   (ID-VAL (LIT-ID (AIGNET-ID->SAT-LIT id
  ;;                                                    ORIG-SAT-LITS)))
  ;;                   (ID-VAL (LIT-ID (aignet-id->sat-lit id1
  ;;                                           (SAT-ADD-AIGNET-LIT lit
  ;;                                                            ORIG-SAT-LITS
  ;;                                                            AIGNET)))))))
  ;;        :hints(("Goal" :in-theory (disable equal-of-id-vals-when-idp))))))

  ;; (defthmd equal-0-by-bitp
  ;;   (implies (bitp x)
  ;;            (equal (equal x 0)
  ;;                   (not (equal x 1))))
  ;;   :hints(("Goal" :in-theory (enable bitp))))

  (defthmd satlink-eval-lit-of-make-lit-of-lit-var
    (equal (satlink::eval-lit (satlink::make-lit (satlink::lit->var lit) neg) env)
           (b-xor (b-xor (satlink::lit->neg lit) neg)
                  (satlink::eval-lit lit env)))
    :hints(("Goal" :in-theory (enable satlink::eval-lit))))

  (defthm eval-satisfies-mux-clauses
    (b* (((mv is-mux c tb fb) (id-is-mux id aignet))
         (sat-lits
          (sat-add-aignet-lit (mk-lit id 0) orig-sat-lits aignet))
         (cnf (mux-add-clauses id c tb fb sat-lits orig-cnf))
         (cnf-eval (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet)))
      (implies (and (sat-lits-wfp orig-sat-lits aignet)
                    (sat-lit-list-listp orig-cnf orig-sat-lits)
                    (aignet-well-formedp aignet)
                    (aignet-idp id aignet)
                    is-mux
                    (aignet-id-has-sat-var (lit-id c) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id tb) orig-sat-lits)
                    (aignet-id-has-sat-var (lit-id fb) orig-sat-lits)
                    (not (aignet-id-has-sat-var id orig-sat-lits))
                    (equal (satlink::eval-formula orig-cnf cnf-eval) 1))
               (equal (satlink::eval-formula cnf cnf-eval) 1)))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (id-eval-when-id-is-mux
                              satlink-eval-lit-of-make-lit-of-lit-var)
                             (satlink::eval-lit
                              satlink::eval-var
                              satlink::eval-lit-of-make-lit
                              commutativity-2-of-b-xor))
             :expand ((lit-eval (mk-lit id 0) in-vals reg-vals aignet)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not
                                                acl2::b-xor
                                                satlink::eval-lit

                                                satlink::eval-var)))))))


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
                                  cnf-eval)
           (if (and (equal (satlink::eval-formula cnf-acc cnf-eval) 1)
                    (or (equal (cnf-eval-conjunction
                                (aignet-lits->sat-lits supergate sat-lits)
                                cnf-eval)
                               1)
                        (equal (satlink::eval-lit
                                (aignet-lit->sat-lit lit sat-lits)
                                cnf-eval)
                               0)))
               1 0))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not))))))

  (defthm supergate-collect-neg-fanins-val
    (equal (satlink::eval-clause
            (supergate-collect-neg-fanins
             supergate sat-lits)
            cnf-eval)
           (acl2::b-not (cnf-eval-conjunction
                         (aignet-lits->sat-lits supergate sat-lits)
                         cnf-eval)))
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
            cnf-eval)
           (if (and (equal (satlink::eval-formula orig-cnf cnf-eval) 1)
                    (equal (satlink::eval-lit (aignet-lit->sat-lit lit sat-lits)
                                         cnf-eval)
                           (cnf-eval-conjunction
                            (aignet-lits->sat-lits supergate sat-lits)
                            cnf-eval)))
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

  (local (in-theory (disable supergate-add-clauses)))

  (defthm cnf-eval-conjunction-when-cnf/aignet-evals-agree
    (implies (and (cnf/aignet-evals-agree 0 in-vals reg-vals sat-lits cnf-eval aignet)
                  (aignet-lit-listp lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (equal (cnf-eval-conjunction
                     (aignet-lits->sat-lits lits sat-lits)
                     cnf-eval)
                    (eval-supergate-list lits in-vals reg-vals aignet))))

  (defthm supergate-add-clauses-new-sat-lit-eval-correct
    (b* ((supergate (lit-collect-supergate lit top use-muxes nil
                                           aignet-refcounts aignet))
         (sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (sat-lit (aignet-lit->sat-lit lit sat-lits))
         (cnf (supergate-add-clauses lit supergate sat-lits orig-cnf)))
      (implies (and (cnf/aignet-evals-agree
                     0 in-vals reg-vals orig-sat-lits cnf-eval aignet)
                    (equal (satlink::eval-formula cnf cnf-eval) 1)
                    (sat-lits-wfp orig-sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-litp lit aignet)
                    (equal (id->type (lit-id lit) aignet) (gate-type))
                    (aignet-lits-have-sat-vars supergate orig-sat-lits))
               (equal (satlink::eval-lit sat-lit cnf-eval)
                      (lit-eval lit in-vals reg-vals aignet))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (equal-1-by-bitp)
                             (collect-supergate-correct
                              satlink::eval-lit
                              commutativity-2-of-b-xor
                              cnf/aignet-evals-agree
                              cnf->aignet-in-vals
                              cnf->aignet-reg-vals))
             :use ((:instance collect-supergate-correct (supergate nil))))))

  (defthm supergate-add-clauses-cnf->aignet-eval-agrees
    (b* ((supergate (lit-collect-supergate lit top use-muxes nil
                                           aignet-refcounts aignet))
         (sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (cnf (supergate-add-clauses lit supergate sat-lits orig-cnf)))
      (implies (and (cnf/aignet-evals-agree
                     0 in-vals reg-vals orig-sat-lits cnf-eval aignet)
                    (sat-lits-wfp orig-sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-litp lit aignet)
                    (equal (id->type (lit-id lit) aignet) (gate-type))
                    (aignet-lits-have-sat-vars supergate orig-sat-lits)
                    (equal (satlink::eval-formula cnf cnf-eval) 1))
               (cnf/aignet-evals-agree
                n in-vals reg-vals sat-lits cnf-eval aignet)))
    :hints (("Goal" :induct (cnf/aignet-evals-agree
                             n in-vals reg-vals
                             (sat-add-aignet-lit lit orig-sat-lits aignet)
                             cnf-eval aignet)
             :do-not-induct t
             :expand ((:free (in-vals reg-vals sat-lits)
                       (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)))
             :in-theory (e/d ((:induction cnf/aignet-evals-agree)
                              aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                             (satlink::eval-lit
                              (:definition cnf/aignet-evals-agree)
                              aignet-lit->sat-lit
                              supergate-add-clauses-correct
                              supergate-add-clauses-new-sat-lit-eval-correct)))
            (and stable-under-simplificationp
                 '(:use supergate-add-clauses-new-sat-lit-eval-correct))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-lit->sat-lit)))))


  ;; The above says:
  ;; A satisfying assignment induces an evaluation of the circuit where the
  ;; evaluation and the satisfying assignment agree.

  ;; Remains to show:
  ;; An evaluation of the circuit induces a satifying assignment.
  ;; (We have already proved that the way we produce an assignment from an
  ;; evaluation, the evaluation and assignment agree:
  ;; see cnf/aignet-evals-agree-of-aignet->cnf-eval.



  ;; (local
  ;;  (encapsulate nil
  ;;      (local (defthm unequal-by-sat-varp
  ;;          (implies (and (bind-free '((sat-lits . orig-sat-lits)))
  ;;                        (sat-varp x sat-lits)
  ;;                        (idp y)
  ;;                        (not (sat-varp y sat-lits)))
  ;;                   (not (equal (id-val x) (id-val y))))
  ;;          :hints(("Goal" :in-theory (enable sat-varp)))))

  ;;      (defthm sat-vars-not-equal-lemma
  ;;        (implies (and (sat-lits-wfp orig-sat-lits aignet)
  ;;                      (aignet-idp id aignet)
  ;;                      (aignet-id-has-sat-var id orig-sat-lits nil)
  ;;                      (not (aignet-id-has-sat-var (lit-id lit) orig-sat-lits nil)))
  ;;                 (NOT
  ;;                  (EQUAL
  ;;                   (ID-VAL (LIT-ID (AIGNET-ID->SAT-LIT id
  ;;                                                    ORIG-SAT-LITS NIL)))
  ;;                   (ID-VAL (LIT-ID (MV-NTH 0
  ;;                                           (SAT-ADD-AIGNET-LIT lit
  ;;                                                            ORIG-SAT-LITS
  ;;                                                            AIGNET))))))))))

  ;; (local
  ;;  (encapsulate nil
  ;;      (local (defthm unequal-by-sat-varp
  ;;          (implies (and (bind-free '((sat-lits . orig-sat-lits)))
  ;;                        (sat-varp x sat-lits)
  ;;                        (idp y)
  ;;                        (not (sat-varp y sat-lits)))
  ;;                   (not (equal (id-val x) (id-val y))))
  ;;          :hints(("Goal" :in-theory (enable sat-varp)))))

  ;;      (defthm sat-vars-not-equal-lemma
  ;;        (implies (and (sat-lits-wfp orig-sat-lits aignet)
  ;;                      (aignet-idp id aignet)
  ;;                      (aignet-id-has-sat-var id orig-sat-lits)
  ;;                      (not (aignet-id-has-sat-var id1 orig-sat-lits))
  ;;                      (equal (id-fix id1) (lit-id lit))
  ;;                      (aignet-litp lit aignet))
  ;;                 (NOT
  ;;                  (EQUAL
  ;;                   (ID-VAL (LIT-ID (AIGNET-ID->SAT-LIT id
  ;;                                                    ORIG-SAT-LITS)))
  ;;                   (ID-VAL (LIT-ID (aignet-id->sat-lit id1
  ;;                                           (SAT-ADD-AIGNET-LIT lit
  ;;                                                            ORIG-SAT-LITS aignet))))))))))

  (defthm sat-lit-listp-of-aignet-lits->sat-lits
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (sat-lit-listp (aignet-lits->sat-lits lits sat-lits)
                            sat-lits))
    :hints(("Goal" :in-theory (enable aignet-lit->sat-lit))))

  (local (defthm var-in-clause-lemma
           (b* ((sat-lits
                 (sat-add-aignet-lit lit orig-sat-lits aignet))
                (sat-lit (aignet-lit->sat-lit lit sat-lits)))
             (implies (and (sat-lits-wfp orig-sat-lits aignet)
                           (aignet-lit-listp lits aignet)
                           (aignet-lits-have-sat-vars lits orig-sat-lits)
                           (aignet-litp lit aignet)
                           (not (aignet-id-has-sat-var (lit-id lit) orig-sat-lits)))
                      (not (var-in-clause (satlink::lit->var sat-lit)
                                          (aignet-lits->sat-lits lits orig-sat-lits)))))
           :hints (("goal" :use ((:instance not-in-clause-when-not-sat-varp
                                  (clause (aignet-lits->sat-lits lits
                                                              orig-sat-lits))
                                  (sat-lits orig-sat-lits)
                                  (var (satlink::lit->var (aignet-lit->sat-lit
                                               lit
                                               (sat-add-aignet-lit lit orig-sat-lits
                                                                aignet))))))))))

  (defthm cnf-eval-conjunction-of-aignet->cnf-eval
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-lit-listp lits aignet)
                  (aignet-lits-have-sat-vars lits sat-lits))
             (equal (cnf-eval-conjunction
                     (aignet-lits->sat-lits lits sat-lits)
                     (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet))
                    (eval-supergate-list lits in-vals reg-vals aignet)))
    :hints (("goal" :use ((:instance
                           cnf-eval-conjunction-when-cnf/aignet-evals-agree
                           (cnf-eval (aignet->cnf-eval 0 in-vals reg-vals sat-lits
                                                    cnf-eval aignet)))))))

  (defthm eval-satisfies-supergate
    (b* ((supergate (lit-collect-supergate lit top use-muxes nil
                                           aignet-refcounts aignet))
         (sat-lits
          (sat-add-aignet-lit lit orig-sat-lits aignet))
         (cnf (supergate-add-clauses lit supergate sat-lits orig-cnf))
         (cnf-eval (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet)))
      (implies (and (sat-lits-wfp orig-sat-lits aignet)
                    (sat-lit-list-listp orig-cnf orig-sat-lits)
                    (aignet-well-formedp aignet)
                    (aignet-litp lit aignet)
                    (aignet-lits-have-sat-vars supergate orig-sat-lits)
                    (not (aignet-id-has-sat-var (lit-id lit) orig-sat-lits))
                    (equal (satlink::eval-formula orig-cnf cnf-eval) 1))
               (equal (satlink::eval-formula cnf cnf-eval) 1)))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (equal-1-by-bitp)
                             (satlink::eval-lit
                              commutativity-2-of-b-xor)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::b-and acl2::b-ior acl2::b-not
                                                acl2::b-xor
                                                satlink::eval-lit
                                                satlink::eval-var)))))))


(defsection aignet-lit->cnf
  (local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                         (satlink::eval-lit-of-make-lit))))

  ;; Measure for aignet-lit->cnf is just the id-val of the lit-IDs, but we need to
  ;; take the max over a list of lits for the list case
  (defun lits-max-id-val (lits)
    (declare (xargs :guard (lit-listp lits)))
    (if (atom lits)
        0
      (max (id-val (lit-id (car lits)))
           (lits-max-id-val (cdr lits)))))


  (defthmd lits-max-id-val-of-supergate
    (<= (lits-max-id-val (lit-collect-supergate
                          lit top use-muxes supergate aignet-refcounts aignet))
        (max (id-val (lit-id lit))
             (lits-max-id-val supergate)))
    :hints(("Goal" :in-theory (enable lit-collect-supergate
                                      gate-orderedp))))

  ;; measure decreases on children of a supergate
  (defthm supergate-decr-top
    (implies (and (gate-orderedp id aignet)
                  (int= (id->type id aignet) (gate-type))
                  (not (and use-muxes
                            (mv-nth 0 (id-is-mux id aignet)))))
             (< (lits-max-id-val (lit-collect-supergate
                                  (mk-lit id 0)
                                  t use-muxes nil aignet-refcounts aignet))
                (id-val id)))
    :hints (("goal" :expand ((:free (use-muxes)
                              (lit-collect-supergate
                               (mk-lit id 0)
                               t use-muxes nil aignet-refcounts aignet)))
             :use ((:instance lits-max-id-val-of-supergate
                    (lit (gate-id->fanin0 id aignet))
                    (top nil)
                    (supergate nil))
                   (:instance lits-max-id-val-of-supergate
                    (lit (gate-id->fanin1 id aignet))
                    (top nil)
                    (supergate (lit-collect-supergate
                                (gate-id->fanin0 id aignet)
                                nil use-muxes nil aignet-refcounts aignet))))
             :in-theory (e/d (gate-orderedp) (lits-max-id-val-of-supergate))))
    :rule-classes (:rewrite :linear))


  (mutual-recursion
   (defun aignet-lit->cnf (x use-muxes aignet-refcounts sat-lits aignet cnf)
     (declare (xargs :stobjs (aignet-refcounts sat-lits aignet)
                     :guard (and (aignet-well-formedp aignet)
                                 (u32arr-sizedp aignet-refcounts aignet)
                                 (aignet-litp x aignet)
                                 (sat-lits-wfp sat-lits aignet))
                     :verify-guards nil
                     :measure (acl2::two-nats-measure
                               (id-val (lit-id x)) 0)))
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
          ((mv muxp c tb fb) (if use-muxes
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
          (supergate (lit-collect-supergate
                      lit t use-muxes nil aignet-refcounts aignet))
          ((unless (mbt (gate-orderedp id aignet)))
           ;; convention: a malformed gate evaluates to 0, so we add a clause
           ;; making it so
           (b* ((sat-lits (sat-add-aignet-lit lit sat-lits aignet))
                (sat-lit (aignet-id->sat-lit id sat-lits)))
             (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
          ((when (member (to-lit 0) supergate))
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

   (defun aignet-lit-list->cnf (x use-muxes aignet-refcounts sat-lits aignet cnf)
     (declare (xargs :stobjs (aignet-refcounts sat-lits aignet)
                     :guard (and (aignet-well-formedp aignet)
                                 (u32arr-sizedp aignet-refcounts aignet)
                                 (aignet-lit-listp x aignet)
                                 (sat-lits-wfp sat-lits aignet))
                     :measure (acl2::two-nats-measure
                               (lits-max-id-val x)
                               (+ 1 (len x)))))
     (if (atom x)
         (mv sat-lits cnf)
       (b* (((mv sat-lits cnf)
             (aignet-lit->cnf (car x) use-muxes aignet-refcounts sat-lits aignet cnf)))
         (aignet-lit-list->cnf (cdr x) use-muxes aignet-refcounts sat-lits aignet
                            cnf)))))

  (local (in-theory (disable aignet-lit->cnf aignet-lit-list->cnf)))

  (encapsulate nil
    ;; BOZO -- Defining the flag function by hand so that we can use
    ;; def-sat-lits-preservation-thms.  Kind of gross, but effective.
    (local (defund aignet-lit->cnf-flg (flg x use-muxes aignet-refcounts sat-lits aignet cnf)
             (declare (xargs :stobjs (aignet-refcounts sat-lits aignet)
                             :guard (and (aignet-well-formedp aignet)
                                         (u32arr-sizedp aignet-refcounts aignet)
                                         (if (eq flg 'lit)
                                             (aignet-litp x aignet)
                                           (aignet-lit-listp x aignet))
                                         (sat-lits-wfp sat-lits aignet))
                             :verify-guards nil
                             :measure (if (eq flg 'lit)
                                          (acl2::two-nats-measure
                                           (id-val (lit-id x)) 0)
                                        (acl2::two-nats-measure
                                         (lits-max-id-val x)
                                         (+ 1 (len x))))))
             (if (eq flg 'lit)
                 (b* ((id (lit-id x))
                      ((when (aignet-id-has-sat-var id sat-lits))
                       (mv sat-lits cnf))
                      ((when (int= (id->type id aignet) (in-type)))
                       (b* ((sat-lits
                             (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet)))
                         (mv sat-lits cnf)))
                      ((unless (int= (id->type id aignet) (gate-type)))
                       (b* ((sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits
                                                       aignet))
                            (sat-lit (aignet-id->sat-lit id sat-lits)))
                         (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
                      ((mv muxp c tb fb) (if use-muxes
                                             (id-is-mux id aignet)
                                           (mv nil nil nil nil)))
                      ((when muxp)
                       (b* (((mv sat-lits cnf)
                             (aignet-lit->cnf-flg 'lit c use-muxes aignet-refcounts sat-lits aignet cnf))
                            ((mv sat-lits cnf)
                             (aignet-lit->cnf-flg 'lit tb use-muxes aignet-refcounts sat-lits aignet cnf))
                            ((mv sat-lits cnf)
                             (aignet-lit->cnf-flg 'lit fb use-muxes aignet-refcounts sat-lits aignet cnf))
                            (sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet))
                            (cnf (mux-add-clauses id c tb fb sat-lits cnf)))
                         (mv sat-lits cnf)))
                      (lit (mk-lit id 0))
                      (supergate (lit-collect-supergate
                                  lit t use-muxes nil aignet-refcounts aignet))
                      ((unless (mbt (gate-orderedp id aignet)))
                       ;; must be 0
                       (b* ((sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits
                                                       aignet))
                            (sat-lit (aignet-id->sat-lit id sat-lits)))
                         (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
                      ((when (member (to-lit 0) supergate))
                       ;; one of the fanins is const 0, so the node is const 0
                       (b* ((sat-lits (sat-add-aignet-lit lit sat-lits aignet))
                            (sat-lit (aignet-id->sat-lit id sat-lits)))
                         (mv sat-lits (cons (list (satlink::lit-negate sat-lit)) cnf))))
                      ((mv sat-lits cnf)
                       (aignet-lit->cnf-flg 'list supergate use-muxes aignet-refcounts sat-lits aignet cnf))
                      (sat-lits (sat-add-aignet-lit lit sat-lits aignet))
                      (cnf (supergate-add-clauses
                                lit supergate sat-lits cnf)))
                   (mv sat-lits cnf))
               (if (atom x)
                   (mv sat-lits cnf)
                 (b* (((mv sat-lits cnf)
                       (aignet-lit->cnf-flg 'lit (car x) use-muxes aignet-refcounts sat-lits aignet cnf)))
                   (aignet-lit->cnf-flg 'list (cdr x) use-muxes aignet-refcounts sat-lits aignet cnf))))))

    (local (in-theory (enable (:induction aignet-lit->cnf-flg))))

    (local (def-sat-lits-preservation-thms aignet-lit->cnf-flg))

    (local (in-theory (disable aignet-lit->cnf aignet-lit-list->cnf
                               (:definition aignet-lit->cnf-flg))))

    (local (defthm aignet-lit->cnf-is-flg-lemma
             (if (eq flg 'lit)
                 (equal (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet
                                      cnf)
                        (aignet-lit->cnf-flg flg x use-muxes aignet-refcounts sat-lits
                                          aignet cnf))
               (equal (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet
                                         cnf)
                      (aignet-lit->cnf-flg flg x use-muxes aignet-refcounts sat-lits
                                        aignet cnf)))
             :hints ((acl2::just-induct-and-expand
                      (aignet-lit->cnf-flg flg x use-muxes aignet-refcounts sat-lits
                                        aignet cnf))
                     '(:expand ((:free (use-muxes)
                                 (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet
                                               cnf))
                                (:free (use-muxes)
                                 (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet
                                                    cnf)))))
             :rule-classes nil))

    ;; Locally redefine aignet-lit->cnf and aignet-lit-list->cnf in terms of the flag
    ;; function so that our preservation-thms macro will work.
    (local (defthm aignet-lit->cnf-is-flg
             (equal (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet
                                  cnf)
                    (aignet-lit->cnf-flg 'lit x use-muxes aignet-refcounts sat-lits
                                      aignet cnf))
             :hints (("goal" :in-theory nil
                      :use ((:instance aignet-lit->cnf-is-flg-lemma (flg 'lit)))))
             :rule-classes :definition))

    (local (defthm aignet-lit-list->cnf-is-flg
             (equal (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet
                                       cnf)
                    (aignet-lit->cnf-flg 'list x use-muxes aignet-refcounts sat-lits
                                      aignet cnf))
             :hints (("goal" :in-theory nil
                      :use ((:instance aignet-lit->cnf-is-flg-lemma (flg 'list)))))
             :rule-classes :definition))

    (def-sat-lits-preservation-thms aignet-lit->cnf)
    (def-sat-lits-preservation-thms aignet-lit-list->cnf))

  ;; that's all we need for verifying the guards...
  (verify-guards aignet-lit->cnf)

  ;; set up for inductive proofs on the mutual-recursion
  (flag::make-flag aignet-lit->cnf-flg aignet-lit->cnf
                   :flag-mapping ((aignet-lit->cnf . lit)
                                  (aignet-lit-list->cnf . list)))

  (local (in-theory (disable (:definition aignet-lit->cnf-flg))))

  ;; hints to be used in flag proofs to expand aignet-lit->cnf/aignet-lit-list->cnf
  (local (defmacro expand-aignet-lit->cnf-flg (&key free)
           `(flag::flag-hint-cases
             flag
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


  ;; two results: CNF generated satisfies sat-lit-list-listp, and the top-level
  ;; arguments get sat variables.
  (defthm-aignet-lit->cnf-flg
    (defthm good-cnf-of-aignet-lit->cnf
      (implies (and (aignet-well-formedp aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-litp x aignet))
               (b* (((mv sat-lits1 ?cnf1)
                     (aignet-lit->cnf x use-muxes
                                   aignet-refcounts sat-lits aignet cnf)))
                 (and (implies (sat-lit-list-listp cnf sat-lits)
                               (sat-lit-list-listp cnf1 sat-lits1))
                      (aignet-id-has-sat-var (lit-id x) sat-lits1))))
      :flag lit)
    (defthm good-cnf-of-aignet-lit-list->cnf
      (implies (and (aignet-well-formedp aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-lit-listp x aignet))
               (b* (((mv sat-lits1 ?cnf1)
                     (aignet-lit-list->cnf x use-muxes
                                   aignet-refcounts sat-lits aignet cnf)))
                 (and (implies (sat-lit-list-listp cnf sat-lits)
                               (sat-lit-list-listp cnf1 sat-lits1))
                      (aignet-lits-have-sat-vars x sat-lits1))))
      :flag list)
    :hints ((expand-aignet-lit->cnf-flg)))

  (defthm-aignet-lit->cnf-flg
    (defthm lit-list-listp-of-aignet-lit->cnf
      (b* (((mv ?sat-lits1 cnf1)
            (aignet-lit->cnf x use-muxes
                             aignet-refcounts sat-lits aignet cnf)))
        (implies (satlink::lit-list-listp cnf)
                 (satlink::lit-list-listp cnf1)))
      :flag lit)
    (defthm lit-list-listp-of-aignet-lit-list->cnf
      (b* (((mv ?sat-lits1 cnf1)
            (aignet-lit-list->cnf x use-muxes
                                  aignet-refcounts sat-lits aignet cnf)))
        (implies (satlink::lit-list-listp cnf)
                 (satlink::lit-list-listp cnf1)))
      :flag list)
    :hints ((expand-aignet-lit->cnf-flg)))

  ;; Can't satisfy the generated CNF unless the original CNF is satisfied.
  (defthm-aignet-lit->cnf-flg
    (defthm aignet-lit->cnf-cnf-satisfied-implies-orig-cnf-satisfied
      (b* (((mv ?sat-lits ?cnf1)
            (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
        (and (implies (equal (satlink::eval-formula cnf cnf-eval) 0)
                      (equal (satlink::eval-formula cnf1 cnf-eval) 0))
             (implies (not (equal (satlink::eval-formula cnf cnf-eval) 1))
                      (not (equal (satlink::eval-formula cnf1 cnf-eval) 1)))))
      :flag lit)
    (defthm aignet-lit-list->cnf-cnf-satisfied-implies-orig-cnf-satisfied
      (b* (((mv ?sat-lits ?cnf1)
            (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
        (and (implies (equal (satlink::eval-formula cnf cnf-eval) 0)
                      (equal (satlink::eval-formula cnf1 cnf-eval) 0))
             (implies (not (equal (satlink::eval-formula cnf cnf-eval) 1))
                      (not (equal (satlink::eval-formula cnf1 cnf-eval) 1)))))
      :flag list)
    :hints ((expand-aignet-lit->cnf-flg)))

  ;; In order to make it easier to prove that the sat-lits-covered property is
  ;; preserved, we write an alternate version of lit-eval that recurs like aignet-lit->cnf.

  (local
   (progn

     (defun b-and-list (x)
       (if (atom x)
           1
         (acl2::b-and (car x)
                      (b-and-list (cdr x)))))

     (defthm bitp-of-b-and-list
       (acl2::bitp (b-and-list x)))

     (defthm eval-supergate-list-is-b-and-list-of-lit-eval-list
       (equal (eval-supergate-list x in-vals reg-vals aignet)
              (b-and-list (lit-eval-list x in-vals reg-vals aignet))))

     (defthm b-and-list-when-0-member
       (implies (and (member 0 x)
                     (aignet-well-formedp aignet))
                (equal (b-and-list (lit-eval-list x in-vals reg-vals aignet))
                       0)))

     (mutual-recursion
      (defun lit-eval-cnfstyle (x use-muxes aignet-refcounts in-vals reg-vals aignet)
        (declare (xargs :stobjs (aignet-refcounts aignet)
                        :guard (and (aignet-well-formedp aignet)
                                    (u32arr-sizedp aignet-refcounts aignet)
                                    (true-listp in-vals)
                                    (true-listp reg-vals)
                                    (aignet-litp x aignet))
                        :verify-guards nil
                        :measure (acl2::two-nats-measure
                                  (id-val (lit-id x)) 0)))
        (b* ((id (lit-id x))
             ((when (int= (id->type id aignet) (in-type)))
              (acl2::b-xor (lit-neg x)
                           (if (int= (io-id->regp id aignet) 1)
                               (bfix (nth (io-id->ionum id aignet) reg-vals))
                             (bfix (nth (io-id->ionum id aignet) in-vals)))))
             ((unless (int= (id->type id aignet) (gate-type))) (lit-neg x))
             ((mv muxp c tb fb) (if use-muxes
                                    (id-is-mux id aignet)
                                  (mv nil nil nil nil)))
             ((when muxp)
              (b* ((cval
                    (lit-eval-cnfstyle c use-muxes aignet-refcounts in-vals reg-vals aignet))
                   (tbval
                    (lit-eval-cnfstyle tb use-muxes aignet-refcounts in-vals reg-vals aignet))
                   (fbval
                    (lit-eval-cnfstyle fb use-muxes aignet-refcounts in-vals reg-vals aignet)))
                (acl2::b-xor (lit-neg x)
                             (acl2::b-ior (acl2::b-and cval tbval)
                                          (acl2::b-and (acl2::b-not cval) fbval)))))
             (lit (mk-lit id 0))
             (supergate (lit-collect-supergate
                         lit t use-muxes nil aignet-refcounts aignet))
             ((unless (mbt (gate-orderedp id aignet)))
              (lit-neg x))
             ((when (member (to-lit 0) supergate))
              (lit-neg x))
             (gatevals
              (lit-eval-list-cnfstyle supergate use-muxes aignet-refcounts in-vals reg-vals aignet)))
          (acl2::b-xor (lit-neg x) (b-and-list gatevals))))
      (defun lit-eval-list-cnfstyle (x use-muxes aignet-refcounts in-vals reg-vals aignet)
        (declare (xargs :stobjs (aignet-refcounts aignet)
                        :guard (and (aignet-well-formedp aignet)
                                    (u32arr-sizedp aignet-refcounts aignet)
                                    (true-listp in-vals)
                                    (true-listp reg-vals)
                                    (aignet-lit-listp x aignet))
                        :measure (acl2::two-nats-measure
                                  (lits-max-id-val x)
                                  (+ 1 (len x)))))
        (if (atom x)
            nil
          (cons
           (lit-eval-cnfstyle (car x) use-muxes aignet-refcounts in-vals reg-vals aignet)
           (lit-eval-list-cnfstyle (cdr x) use-muxes aignet-refcounts in-vals reg-vals
                                   aignet)))))

     (flag::make-flag lit-eval-cnfstyle-flg lit-eval-cnfstyle
                      :flag-mapping ((lit-eval-cnfstyle . lit)
                                     (lit-eval-list-cnfstyle . list)))

     (defthm equal-when-bits-true
       (implies (and (syntaxp (not (or (equal x ''0)
                                       (equal y ''0))))
                     (acl2::bitp x)
                     (acl2::bitp y)
                     (iff (equal x 0) (equal y 0)))
                (equal (equal x y) t))
       :hints(("Goal" :in-theory (enable acl2::bitp))))

     (defthm equal-when-bits-false
       (implies (and (syntaxp (not (or (equal x ''0)
                                       (equal y ''0))))
                     (acl2::bitp x)
                     (acl2::bitp y)
                     (not (iff (equal x 0) (equal y 0))))
                (equal (equal x y) nil))
       :hints(("Goal" :in-theory (enable acl2::bitp))))

     (defthm-lit-eval-cnfstyle-flg
       (defthm lit-eval-cnfstyle-is-lit-eval
         (implies (and (aignet-well-formedp aignet)
                       (aignet-litp x aignet))
                  (equal (lit-eval-cnfstyle x use-muxes aignet-refcounts
                                            in-vals reg-vals aignet)
                         (lit-eval x in-vals reg-vals aignet)))
         :hints ('(:expand ((:free (use-muxes)
                             (lit-eval-cnfstyle x use-muxes aignet-refcounts
                                                in-vals reg-vals aignet))))
                 (and stable-under-simplificationp
                      (let* ((type `(node->type (nth-node (lit-id$inline x)
                                                          (nth ',*nodesi* aignet))))

                             (gate-type (member-equal `(not (equal ,type '1))
                                                      clause))

                             (mux-type (member-equal `(not (mv-nth '0 (id-is-mux (lit-id$inline x) aignet)))
                                                     clause)))
                        (cond (mux-type
                               '(:use ((:instance id-eval-when-id-is-mux
                                        (id (lit-id x))))
                                 :in-theory (e/d (acl2::b-xor) (id-eval-when-id-is-mux))))
                              (gate-type
                               '(:use ((:instance collect-supergate-correct
                                        (lit (mk-lit (lit-id x) 0))
                                        (top t) (supergate nil))
                                       (:instance collect-supergate-correct
                                        (lit (mk-lit (lit-id x) 0))
                                        (top t) (supergate nil)
                                        (use-muxes nil)))
                                 :expand ((lit-eval (mk-lit (lit-id x) 0)
                                                    in-vals reg-vals aignet))
                                 :in-theory (e/d (acl2::b-xor)
                                                 (collect-supergate-correct))))
                              (t '(:expand ((lit-eval x in-vals reg-vals aignet)
                                            (id-eval (lit-id x) in-vals reg-vals aignet)
                                            (aignet-litp x aignet))
                                   :in-theory (disable id-eval-in-terms-of-lit-eval)))))))
         :flag lit)
       (defthm lit-eval-list-cnfstyle-is-lit-eval-list
         (implies (and (aignet-well-formedp aignet)
                       (aignet-lit-listp x aignet))
                  (equal (lit-eval-list-cnfstyle x use-muxes aignet-refcounts
                                                 in-vals reg-vals aignet)
                         (lit-eval-list x in-vals reg-vals aignet)))
         :flag list))

     (in-theory (disable lit-eval-cnfstyle-is-lit-eval
                         lit-eval-list-cnfstyle-is-lit-eval-list))


     (defun-sk has-covered-ancestor-with-lits (lits sat-lits2 aignet)
       (exists sat-lits1
               (and (sat-lit-extension-p sat-lits2 sat-lits1)
                    (sat-lits-covered sat-lits1 aignet)
                    (aignet-lits-have-sat-vars lits sat-lits1))))

     (in-theory (disable has-covered-ancestor-with-lits
                         has-covered-ancestor-with-lits-suff))

     (defthm has-covered-ancestor-with-lits-iterate
       (implies (and (sat-lit-extension-binding)
                     (sat-lit-extension-p sat-lits2 sat-lits1)
                     (has-covered-ancestor-with-lits lits sat-lits1 aignet))
                (has-covered-ancestor-with-lits lits sat-lits2 aignet))
       :hints(("Goal" :in-theory (disable has-covered-ancestor-with-lits
                                          has-covered-ancestor-with-lits-suff)
               :expand ((has-covered-ancestor-with-lits lits sat-lits1 aignet))
               :use ((:instance has-covered-ancestor-with-lits-suff
                      (sat-lits1 (has-covered-ancestor-with-lits-witness
                                  lits sat-lits1 aignet)))))))

     (defthm has-covered-ancestor-with-lits-self
       (implies (and (sat-lits-covered sat-lits2 aignet)
                     (aignet-lits-have-sat-vars lits sat-lits2))
                (has-covered-ancestor-with-lits lits sat-lits2 aignet))
       :hints (("goal" :use ((:instance has-covered-ancestor-with-lits-suff
                              (sat-lits1 sat-lits2))))))


     (defthm sat-lits-covered-rw-lit-eval-cnfstyle
       (implies (and (sat-lit-extension-binding)
                     (sat-lit-extension-p sat-lits2 sat-lits1)
                     (has-covered-ancestor-with-var (lit-id lit) sat-lits1 aignet)
; (sat-lits-covered sat-lits1 aignet)
; (aignet-id-has-sat-var (lit-id lit) sat-lits1)
                     (aignet-litp lit aignet)
                     (aignet-well-formedp aignet))
                (equal (lit-eval-cnfstyle lit use-muxes aignet-refcounts
                                          (cnf->aignet-in-vals
                                           0 in-vals sat-lits2 cnf-eval
                                           aignet)
                                          (cnf->aignet-reg-vals
                                           0 reg-vals sat-lits2 cnf-eval
                                           aignet)
                                          aignet)
                       (lit-eval-cnfstyle lit use-muxes aignet-refcounts
                                          (cnf->aignet-in-vals
                                           0 in-vals sat-lits1 cnf-eval
                                           aignet)
                                          (cnf->aignet-reg-vals
                                           0 reg-vals sat-lits1 cnf-eval
                                           aignet)
                                          aignet)))
       :hints(("Goal" :in-theory (e/d (lit-eval-cnfstyle-is-lit-eval)
                                      (lit-eval-cnfstyle-flg
                                       sat-lits-covered-rw))
               :use sat-lits-covered-rw)))

     (defthm sat-lits-covered-rw-lit-eval-list-cnfstyle-1
       (implies (and (sat-lit-extension-binding)
                     (sat-lit-extension-p sat-lits2 sat-lits1)
                     (sat-lits-covered sat-lits1 aignet)
                     (aignet-lits-have-sat-vars lits sat-lits1)
; (has-covered-ancestor-with-lits lits sat-lits1 aignet)
                     (aignet-lit-listp lits aignet)
                     (aignet-well-formedp aignet))
                (equal (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
                                               (cnf->aignet-in-vals
                                                0 in-vals sat-lits2 cnf-eval
                                                aignet)
                                               (cnf->aignet-reg-vals
                                                0 reg-vals sat-lits2 cnf-eval
                                                aignet)
                                               aignet)
                       (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
                                               (cnf->aignet-in-vals
                                                0 in-vals sat-lits1 cnf-eval
                                                aignet)
                                               (cnf->aignet-reg-vals
                                                0 reg-vals sat-lits1 cnf-eval
                                                aignet)
                                               aignet)))
       :hints(("goal" :induct (aignet-lit-listp lits aignet)
               :expand ((:free (in-vals reg-vals use-muxes)
                         (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
                                                 in-vals reg-vals aignet))))))

     (defthm sat-lits-covered-rw-lit-eval-list-cnfstyle-ancestor
       (implies (and (sat-lit-extension-binding)
                     (sat-lit-extension-p sat-lits2 sat-lits1)
                     (has-covered-ancestor-with-lits lits sat-lits1 aignet)
                     (aignet-lit-listp lits aignet)
                     (aignet-well-formedp aignet))
                (equal (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
                                               (cnf->aignet-in-vals
                                                0 in-vals sat-lits2 cnf-eval
                                                aignet)
                                               (cnf->aignet-reg-vals
                                                0 reg-vals sat-lits2 cnf-eval
                                                aignet)
                                               aignet)
                       (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
                                               (cnf->aignet-in-vals
                                                0 in-vals sat-lits1 cnf-eval
                                                aignet)
                                               (cnf->aignet-reg-vals
                                                0 reg-vals sat-lits1 cnf-eval
                                                aignet)
                                               aignet)))
       :hints(("goal" :expand ((has-covered-ancestor-with-lits lits sat-lits1
                                                               aignet))
               :use ((:instance sat-lits-covered-rw-lit-eval-list-cnfstyle-1
                      (sat-lits1 (has-covered-ancestor-with-lits-witness
                                  lits sat-lits1 aignet))))
               :do-not-induct t)))

     ;; (defthm sat-lits-covered-rw-lit-eval-list-cnfstyle-2-back
     ;;   (implies (and (sat-lit-extension-binding :orig sat-litsm)
     ;;                 (sat-lit-extension-binding :new sat-litsm)
     ;;                 (sat-lit-extension-p sat-lits2 sat-lits1)
     ;;                 (sat-lits-covered sat-lits1 aignet)
     ;;                 (aignet-lits-have-sat-vars lits sat-lits1)
     ;;                 ;; (has-covered-ancestor-with-lits lits sat-lits1 aignet)
     ;;                 (aignet-lit-listp lits aignet)
     ;;                 (aignet-well-formedp aignet))
     ;;            (equal (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits2 cnf-eval aignet)
     ;;                                           aignet)
     ;;                   (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits1 cnf-eval aignet)
     ;;                                           aignet)))
     ;;   :hints(("Goal"
     ;;           :induct (aignet-lit-listp lits aignet)
     ;;           :expand ((:free (aignet-vals use-muxes)
     ;;                     (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                             aignet-vals aignet))))))



     ;; (defthm sat-lits-covered-rw-lit-eval-list-cnfstyle
     ;;   (implies (and (sat-lit-extension-binding)
     ;;                 (sat-lit-extension-p sat-lits2 sat-lits1)
     ;;                 (sat-lits-covered sat-lits1 aignet)
     ;;                 (aignet-lits-have-sat-vars lits sat-lits1)
     ;;                 ;; (has-covered-ancestor-with-lits lits sat-lits1 aignet)
     ;;                 (aignet-lit-listp lits aignet)
     ;;                 (aignet-well-formedp aignet))
     ;;            (equal (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits2 cnf-eval aignet)
     ;;                                           aignet)
     ;;                   (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits1 cnf-eval aignet)
     ;;                                           aignet)))
     ;;   :hints(("Goal"
     ;;           :induct (aignet-lit-listp lits aignet)
     ;;           :expand ((:free (aignet-vals use-muxes)
     ;;                     (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                             aignet-vals aignet))))))

     ;; (defthm sat-lits-covered-rw-lit-eval-list-cnfstyle-2-back
     ;;   (implies (and (sat-lit-extension-binding :orig sat-litsm)
     ;;                 (sat-lit-extension-binding :new sat-litsm)
     ;;                 (sat-lit-extension-p sat-lits2 sat-lits1)
     ;;                 (sat-lits-covered sat-lits1 aignet)
     ;;                 (aignet-lits-have-sat-vars lits sat-lits1)
     ;;                 ;; (has-covered-ancestor-with-lits lits sat-lits1 aignet)
     ;;                 (aignet-lit-listp lits aignet)
     ;;                 (aignet-well-formedp aignet))
     ;;            (equal (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits2 cnf-eval aignet)
     ;;                                           aignet)
     ;;                   (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts
     ;;                                           (cnf->aignet-vals 0 aignet-vals sat-lits1 cnf-eval aignet)
     ;;                                           aignet)))
     ;;   :hints(("Goal"
     ;;           :induct (aignet-lit-listp lits aignet)
     ;;           :expand ((:free (aignet-vals use-muxes)
     ;;                     (lit-eval-list-cnfstyle lits use-muxes aignet-refcounts aignet-vals aignet))))))


     (defthmd sat-lits-covered-alt-expansion
       (let ((sat-lits (mv-nth 0 (aignet-lit->cnf x use-muxes
                                               aignet-refcounts sat-lits aignet cnf))))
         (implies
          ;; special syntaxp hyp for the thm below
          (and (syntaxp (equal (cdr (acl2::mfc-current-literal mfc state))
                               (car (last (acl2::mfc-clause mfc)))))
               (aignet-well-formedp aignet))
          (equal (sat-lits-covered sat-lits aignet)
                 (mv-let (lit sat-lits2 cnf-eval in-vals reg-vals)
                   (sat-lits-covered-witness sat-lits aignet)
                   (implies (and (sat-lit-extension-p sat-lits2 sat-lits)
                                 (aignet-id-has-sat-var (lit-id lit) sat-lits)
                                 (aignet-litp lit aignet))
                            (equal
                             (lit-eval-cnfstyle lit use-muxes aignet-refcounts
                                                (cnf->aignet-in-vals 0 in-vals sat-lits2
                                                               cnf-eval aignet)
                                                (cnf->aignet-reg-vals 0 reg-vals sat-lits2
                                                               cnf-eval aignet)
                                                aignet)
                             (lit-eval-cnfstyle lit use-muxes aignet-refcounts
                                                (cnf->aignet-in-vals 0 in-vals sat-lits
                                                               cnf-eval aignet)
                                                (cnf->aignet-reg-vals 0 reg-vals sat-lits
                                                               cnf-eval aignet)
                                                aignet)))))))
       :hints(("Goal" :in-theory (e/d (lit-eval-cnfstyle-is-lit-eval
                                       sat-lits-covered)
                                      (lit-eval-cnfstyle-flg)))))))


  ;;  (defthm sat-lits-covered-implies-lit-eval-cnfstyle-list
  ;;    (implies (and (sat-lits-covered sat-lits aignet)
  ;;                  (aignet-lits-have-sat-vars lits sat-lits aignet)
  ;;                  (aignet-well-formedp aignet)
  ;;                  (aignet-lit-listp lits aignet)
  ;;                  (aignet-lit-listp add-lits aignet)
  ;;                  (aignet-litp add-lit aignet))
  ;;             (equal (lit-eval-list-cnfstyle
  ;;                     lits use-muxes aignet-refcounts
  ;;                     (cnf->aignet-vals 0 aignet-vals
  ;;                                    (sat-add-aignet-lits add-lits
  ;;                                                      (sat-add-aignet-lit
  ;;                                                       add-lit sat-lits aignet)
  ;;                                                      aignet)
  ;;                                    cnf-eval aignet)
  ;;                     aignet)
  ;;                    (lit-eval-list-cnfstyle
  ;;                     lits use-muxes aignet-refcounts
  ;;                     (cnf->aignet-vals 0 aignet-vals sat-lits cnf-eval aignet)
  ;;                     aignet)))
  ;;    :hints (("goal" :induct (len lits)
  ;;             :in-theory (enable lit-eval-cnfstyle-is-lit-eval))))

  ;; (defthm sat-lits-covered-implies-lit-eval-cnfstyle
  ;;   (implies (and (sat-lits-covered sat-lits aignet)
  ;;                 (aignet-id-has-sat-var (lit-id lit) sat-lits)
  ;;                 (aignet-well-formedp aignet)
  ;;                 (aignet-litp lit aignet)
  ;;                 (aignet-lit-listp add-lits aignet)
  ;;                 (aignet-litp add-lit aignet))
  ;;            (equal (lit-eval-cnfstyle
  ;;                    lit use-muxes aignet-refcounts
  ;;                    (cnf->aignet-vals 0 aignet-vals
  ;;                                   (sat-add-aignet-lits add-lits
  ;;                                                     (sat-add-aignet-lit
  ;;                                                      add-lit sat-lits aignet)
  ;;                                                     aignet)
  ;;                                   cnf-eval aignet)
  ;;                    aignet)
  ;;                   (lit-eval-cnfstyle
  ;;                    lit use-muxes aignet-refcounts
  ;;                    (cnf->aignet-vals 0 aignet-vals sat-lits cnf-eval aignet)
  ;;                    aignet)))
  ;;   :hints (("goal"
  ;;            :in-theory (enable lit-eval-cnfstyle-is-lit-eval))))


  ;; finally can prove that our magic invariant holds:
  ;; the crux is that when we add a sat var for a gate, we've already added
  ;; variables for that gate's supergate or mux children, so its value is
  ;; determined by the variables present.
  (defthm-aignet-lit->cnf-flg
    (defthm sat-lits-covered-of-aignet-lit->cnf
      (implies (and (sat-lits-covered sat-lits aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-litp x aignet))
               (sat-lits-covered
                (mv-nth 0 (aignet-lit->cnf x use-muxes
                                        aignet-refcounts sat-lits aignet cnf))
                aignet))
      :hints ((and
               stable-under-simplificationp
               (cond ((or (member-equal
                           `(not (equal (node->type (nth-node (lit-id$inline x)
                                                              (nth ',*nodesi* aignet)))
                                        '1))
                           clause)
                          (member-equal
                           '(not (mv-nth '0 (id-is-mux (lit-id$inline x) aignet)))
                           clause))
                      '(:computed-hint-replacement
                        ((and stable-under-simplificationp
                              '(:expand ((:free (use-muxes flg)
                                          (aignet-lit->cnf x use-muxes aignet-refcounts
                                           sat-lits aignet cnf))))))
                        :in-theory (enable sat-lits-covered-alt-expansion
                                           aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit
                                           lit-eval-cnfstyle)))
                     (t
                      '(:expand ((:free (use-muxes)
                                  (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf))))))))
      :flag lit)
    (defthm sat-lits-covered-of-aignet-lit-list->cnf
      (implies (and (sat-lits-covered sat-lits aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (aignet-well-formedp aignet)
                    (aignet-lit-listp x aignet))
               (sat-lits-covered
                (mv-nth 0 (aignet-lit-list->cnf x use-muxes
                                             aignet-refcounts sat-lits aignet cnf))
                aignet))
      :hints ('(:expand ((:free (use-muxes)
                          (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits
                                             aignet cnf))
                         (:free (use-muxes)
                          (aignet-lit-list->cnf nil use-muxes aignet-refcounts sat-lits
                                             aignet cnf)))))
      :flag list))

  (encapsulate nil

    ;; Gearing up for our major correctness theorem,
    ;; aignet-lit->cnf-preserves-cnf->aignet-vals, which shows that aignet-lit->cnf
    ;; preserves the property that from any satisfying assignment you can
    ;; construct a CI assignment under which aignet nodes evaluate to the values
    ;; of their corresponding variables.  This is the "lesser" theorem because
    ;; we could quickly check any satisfying assignment we get instead of
    ;; proving it.
    (local (in-theory (disable (:definition cnf/aignet-evals-agree))))

    (local (defthm cnf/aignet-evals-agree-of-add-const-node
             (implies (and (cnf/aignet-evals-agree
                            n in-vals reg-vals sat-lits cnf-eval aignet)
                           (not (equal (id->type (lit-id x) aignet) (gate-type)))
                           (not (equal (id->type (lit-id x) aignet) (in-type)))
                           (equal (satlink::eval-lit
                                   (aignet-id->sat-lit (lit-id x)
                                                    (sat-add-aignet-lit x sat-lits aignet))
                                   cnf-eval)
                                  0)
                           (sat-lits-wfp sat-lits aignet)
                           (aignet-litp x aignet))
                      (cnf/aignet-evals-agree
                       n in-vals reg-vals
                       (sat-add-aignet-lit x sat-lits aignet)
                       cnf-eval aignet))
             :hints ((acl2::just-induct-and-expand
                      (cnf/aignet-evals-agree
                       n in-vals reg-vals sat-lits cnf-eval aignet)
                      :expand-others
                      ((:free (sat-lits)
                        (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet))))
                     (and stable-under-simplificationp
                          '(:in-theory (e/d (acl2::b-xor
                                             aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                                            (id-eval-in-terms-of-lit-eval))
                            :expand ((lit-eval x in-vals reg-vals aignet)
                                     (id-eval (lit-id x) in-vals reg-vals aignet)
                                     (aignet-litp x aignet)))))))

    (local (defthm cnf/aignet-evals-agree-of-add-const-supergate
             (implies (and (cnf/aignet-evals-agree
                            n in-vals reg-vals sat-lits cnf-eval aignet)
                           (equal (id->type (lit-id x) aignet) (gate-type))
                           (equal (lit-neg x) 0)
                           (member-equal 0 (lit-collect-supergate
                                            x top use-muxes nil
                                            aignet-refcounts aignet))
                           (equal (satlink::eval-lit
                                   (aignet-id->sat-lit (lit-id x)
                                                    (sat-add-aignet-lit x sat-lits aignet))
                                   cnf-eval)
                                  0)
                           (sat-lits-wfp sat-lits aignet)
                           (aignet-well-formedp aignet)
                           (aignet-litp x aignet))
                      (cnf/aignet-evals-agree
                       n in-vals reg-vals
                       (sat-add-aignet-lit x sat-lits aignet)
                       cnf-eval aignet))
             :hints ((acl2::just-induct-and-expand
                      (cnf/aignet-evals-agree
                       n in-vals reg-vals sat-lits cnf-eval aignet)
                      :expand-others
                      ((:free (sat-lits)
                        (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval
                                             aignet))))
                     (and stable-under-simplificationp
                          '(:use ((:instance collect-supergate-correct
                                   (lit x) (supergate nil)))
                            :in-theory (e/d (acl2::b-and)
                                            (collect-supergate-correct))))
                     ;; (and stable-under-simplificationp
                     ;;      '(:in-theory (e/d (acl2::b-xor
                     ;;                         aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                     ;;                        (id-eval-in-terms-of-lit-eval))
                     ;;        :expand ((lit-eval x in-vals reg-vals aignet)
                     ;;                 (id-eval (lit-id x) in-vals reg-vals aignet)
                     ;;                 (aignet-litp x aignet))))
                     )))

    (local (defthm id-eval-of-add-lit-when-covered
             (implies (and (sat-lits-covered sat-lits aignet)
                           (aignet-id-has-sat-var id sat-lits)
                           (sat-lits-wfp sat-lits aignet)
                           (aignet-well-formedp aignet)
                           (aignet-litp lit aignet)
                           (aignet-idp id aignet)
                           (not (equal (id->type id aignet) (out-type))))
                      (equal (id-eval id
                                      (cnf->aignet-in-vals
                                       0 in-vals
                                       (sat-add-aignet-lit lit sat-lits aignet)
                                       cnf-eval aignet)
                                      (cnf->aignet-reg-vals
                                       0 reg-vals
                                       (sat-add-aignet-lit lit sat-lits aignet)
                                       cnf-eval aignet)
                                      aignet)
                             (id-eval id
                                      (cnf->aignet-in-vals
                                       0 in-vals sat-lits cnf-eval aignet)
                                      (cnf->aignet-reg-vals
                                       0 reg-vals sat-lits cnf-eval aignet)
                                      aignet)))
             :hints (("goal" ;; :use ((:instance sat-lits-covered-rw-single
                             ;;        (lit (mk-lit id 0))
                             ;;        (add-lit lit)))
                      :use ((:instance sat-lits-covered-rw
                             (sat-lits2 (sat-add-aignet-lit lit sat-lits aignet))
                             (sat-lits1 sat-lits)
                             (lit (mk-lit id 0))))
                      :in-theory (e/d (lit-eval)
                                      (id-eval-in-terms-of-lit-eval
                                       sat-lits-covered-rw
                                       sat-lits-covered-ancestor))
                      :do-not-induct t))))

    (local (defthm not-out-type-by-sat-lit-lookup
             (implies (and (sat-lits-wfp sat-lits aignet)
                           (aignet-id-has-sat-var id sat-lits)
                           (aignet-idp id aignet))
                      (not (equal (node->type
                                   (nth-node id (nth *nodesi* aignet)))
                                  (out-type))))
             :hints (("goal" :use
                      ((:instance sat-lits-wfp-implies-aignet-litp-of-lookup-sat-var
                                  (n (satlink::lit->var (aignet-id->sat-lit id sat-lits)))))
                      :in-theory (e/d (aignet-litp)
                                      (sat-lits-wfp-implies-aignet-litp-of-lookup-sat-var))))))

    (local (in-theory (disable cnf->aignet-in-vals-of-sat-add-aignet-lit
                               cnf->aignet-reg-vals-of-sat-add-aignet-lit)))

    (local (defthm cnf/aignet-evals-agree-of-add-input
             (implies (and (sat-lits-covered sat-lits aignet)
                           (cnf/aignet-evals-agree
                            n
                            (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval
                                                 aignet)
                            (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval
                                                  aignet)
                            sat-lits cnf-eval aignet)
                           (equal (id->type (lit-id x) aignet) (in-type))
                           (sat-lits-wfp sat-lits aignet)
                           (aignet-well-formedp aignet)
                           (aignet-litp x aignet))
                      (cnf/aignet-evals-agree
                       n
                       (cnf->aignet-in-vals
                        0 in-vals
                        (sat-add-aignet-lit x sat-lits aignet) cnf-eval aignet)
                       (cnf->aignet-reg-vals
                        0 reg-vals
                        (sat-add-aignet-lit x sat-lits aignet) cnf-eval aignet)
                       (sat-add-aignet-lit x sat-lits aignet)
                       cnf-eval aignet))
             :hints ((acl2::just-induct-and-expand
                      (cnf/aignet-evals-agree
                       n
                       (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval
                                            aignet)
                       (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval
                                             aignet)
                       sat-lits cnf-eval aignet)
                      :expand-others
                      ((:free (in-vals reg-vals sat-lits)
                        (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet))))
                     '(:do-not-induct t
                       :in-theory (e/d
                                   (aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)
                                   (cnf->aignet-in-vals
                                    cnf->aignet-reg-vals)))
                     (and stable-under-simplificationp
                          '(:in-theory (e/d
                                        (cnf->aignet-in-vals-of-sat-add-aignet-lit
                                         cnf->aignet-reg-vals-of-sat-add-aignet-lit)
                                            (id-eval-in-terms-of-lit-eval
                                             cnf->aignet-in-vals
                                             cnf->aignet-reg-vals))
                            :expand ((:free (in-vals reg-vals)
                                      (lit-eval x in-vals reg-vals aignet))
                                     (:free (in-vals reg-vals)
                                      (id-eval (lit-id x) in-vals reg-vals aignet))))))))

    (local (in-theory (disable (:definition aignet-lit->cnf-flg)
                               cnf/aignet-evals-agree
                               cnf->aignet-in-vals
                               cnf->aignet-reg-vals
                               satlink::eval-lit)))
    (local (in-theory (enable equal-1-by-bitp)))

    (local (defthm supergate-add-clauses-cnf->aignet-eval-agrees-special
             (B*
                 ((SUPERGATE (LIT-COLLECT-SUPERGATE
                              LIT
                              TOP USE-MUXES NIL AIGNET-REFCOUNTS AIGNET))
                  (SAT-LITS (SAT-ADD-AIGNET-LIT LIT ORIG-SAT-LITS AIGNET))
                  (CNF (SUPERGATE-ADD-CLAUSES
                        LIT SUPERGATE SAT-LITS ORIG-CNF)))
               (IMPLIES
                (AND (bind-free '((orig-cnf . cnf)
                                  (aignet-refcounts . aignet-refcounts)
                                  (use-muxes . 'nil)
                                  (top . 't)))
                     (CNF/AIGNET-EVALS-AGREE
                      0 IN-VALS REG-VALS ORIG-SAT-LITS CNF-EVAL AIGNET)
                     (SAT-LITS-WFP ORIG-SAT-LITS AIGNET)
                     (AIGNET-WELL-FORMEDP AIGNET)
                     (AIGNET-LITP LIT AIGNET)
                     (EQUAL (ID->TYPE (LIT-ID LIT) AIGNET)
                            (GATE-TYPE))
                     (AIGNET-LITS-HAVE-SAT-VARS SUPERGATE ORIG-SAT-LITS)
                     (force (EQUAL (SATLINK::EVAL-FORMULA CNF CNF-EVAL) 1)))
                (CNF/AIGNET-EVALS-AGREE N IN-VALS REG-VALS SAT-LITS CNF-EVAL AIGNET)))
             :hints (("goal" :use supergate-add-clauses-cnf->aignet-eval-agrees))))

    (local (defthm supergate-add-clauses-cnf->aignet-eval-agrees-special2
             (B*
                 ((SUPERGATE (LIT-COLLECT-SUPERGATE
                              LIT
                              TOP USE-MUXES NIL AIGNET-REFCOUNTS AIGNET))
                  (SAT-LITS (SAT-ADD-AIGNET-LIT LIT ORIG-SAT-LITS AIGNET))
                  (CNF (SUPERGATE-ADD-CLAUSES
                        LIT SUPERGATE SAT-LITS ORIG-CNF)))
               (IMPLIES
                (AND (bind-free '((orig-cnf . cnf)
                                  (aignet-refcounts . aignet-refcounts)
                                  (use-muxes . use-muxes)
                                  (top . 't)))
                     (CNF/AIGNET-EVALS-AGREE
                      0 IN-VALS REG-VALS ORIG-SAT-LITS CNF-EVAL AIGNET)
                     (SAT-LITS-WFP ORIG-SAT-LITS AIGNET)
                     (AIGNET-WELL-FORMEDP AIGNET)
                     (AIGNET-LITP LIT AIGNET)
                     (EQUAL (ID->TYPE (LIT-ID LIT) AIGNET)
                            (GATE-TYPE))
                     (AIGNET-LITS-HAVE-SAT-VARS SUPERGATE ORIG-SAT-LITS)
                     (force (EQUAL (SATLINK::EVAL-FORMULA CNF CNF-EVAL) 1)))
                (CNF/AIGNET-EVALS-AGREE N IN-VALS REG-VALS SAT-LITS CNF-EVAL AIGNET)))
             :hints (("goal" :use supergate-add-clauses-cnf->aignet-eval-agrees))))

    (local (defthm mux-add-clauses-cnf->aignet-eval-agrees-special
             (b* (((mv is-mux c tb fb) (id-is-mux id aignet))
                  (lit (mk-lit id 0))
                  (sat-lits
                   (sat-add-aignet-lit lit orig-sat-lits aignet))
                  (cnf (mux-add-clauses id c tb fb sat-lits orig-cnf)))
               (implies (and (bind-free '((orig-cnf . cnf)))
                             (cnf/aignet-evals-agree
                              0 in-vals reg-vals orig-sat-lits cnf-eval aignet)
                             (sat-lits-wfp orig-sat-lits aignet)
                             (aignet-well-formedp aignet)
                             (aignet-idp id aignet)
                             is-mux
                             (aignet-id-has-sat-var (lit-id c) orig-sat-lits)
                             (aignet-id-has-sat-var (lit-id tb) orig-sat-lits)
                             (aignet-id-has-sat-var (lit-id fb) orig-sat-lits)
                             (force (equal (satlink::eval-formula cnf cnf-eval) 1)))
                        (cnf/aignet-evals-agree
                         n in-vals reg-vals sat-lits cnf-eval aignet)))
             :hints (("goal" :use mux-add-clauses-cnf->aignet-eval-agrees))))

    (local (in-theory (disable ; equal-when-bits
                       aignet-lit->sat-lit)))

    ;; *** This is the first big correctness theorem for aignet-lit->cnf.
    ;; It says, basically:
    ;;  aignet-lit->cnf preserves the property that
    ;;    a satisfying assignment of the cnf induces (via cnf->aignet-vals)
    ;;    an assignment to the CIs of the circuit such that the evaluations of
    ;;    the aignet nodes have values corresponding to the values in the
    ;;    satisfying assignment (i.e. satisfying cnf/aignet-evals-agree).
    (defthm-aignet-lit->cnf-flg
      (defthm aignet-lit->cnf-preserves-cnf->aignet-in-vals
        (b* (((mv sat-lits1 cnf1)
              (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf))
             (in-vals0 (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval aignet))
             (in-vals1 (cnf->aignet-in-vals 0 in-vals sat-lits1 cnf-eval aignet))
             (reg-vals0 (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval aignet))
             (reg-vals1 (cnf->aignet-reg-vals 0 reg-vals sat-lits1 cnf-eval aignet)))
          (implies (and (sat-lits-wfp sat-lits aignet)
                        (aignet-well-formedp aignet)
                        (equal (satlink::eval-formula cnf1 cnf-eval) 1)
                        (cnf/aignet-evals-agree
                         0 in-vals0 reg-vals0 sat-lits cnf-eval aignet)
                        (sat-lits-covered sat-lits aignet)
                        (aignet-litp x aignet))
                   (cnf/aignet-evals-agree
                    0 in-vals1 reg-vals1 sat-lits1 cnf-eval aignet)))
        :flag lit)
      (defthm aignet-lit-list->cnf-preserves-cnf->aignet-vals
        (b* (((mv sat-lits1 cnf1)
              (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf))
             (in-vals0 (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval aignet))
             (in-vals1 (cnf->aignet-in-vals 0 in-vals sat-lits1 cnf-eval aignet))
             (reg-vals0 (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval aignet))
             (reg-vals1 (cnf->aignet-reg-vals 0 reg-vals sat-lits1 cnf-eval aignet)))
          (implies (and (sat-lits-wfp sat-lits aignet)
                        (aignet-well-formedp aignet)
                        (equal (satlink::eval-formula cnf1 cnf-eval) 1)
                        (cnf/aignet-evals-agree
                         0 in-vals0 reg-vals0 sat-lits cnf-eval aignet)
                        (sat-lits-covered sat-lits aignet)
                        (aignet-lit-listp x aignet))
                   (cnf/aignet-evals-agree
                    0 in-vals1 reg-vals1 sat-lits1 cnf-eval aignet)))
        :flag list)
      :hints ((expand-aignet-lit->cnf-flg)
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::b-and))))))





  (local (in-theory (disable aignet->cnf-eval
                             aignet->cnf-eval-of-sat-add-aignet-lit
                             satlink::eval-lit)))

  (local (in-theory (enable
                     aignet-id-has-sat-var-preserved-split-of-sat-add-aignet-lit)))


  ;; Technical lemma for the theorem below: we need to know that we don't add
  ;; clauses about some node while processing the children of that node.
  (defthm-aignet-lit->cnf-flg
    (defthm aignet-lit->cnf-preserves-no-sat-var-for-greater-id
      (implies (and (aignet-well-formedp aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (not (aignet-id-has-sat-var id sat-lits))
                    (aignet-litp x aignet)
                    (< (id-val (lit-id x)) (id-val id)))
               (b* (((mv sat-lits ?cnf)
                     (aignet-lit->cnf x use-muxes
                                   aignet-refcounts sat-lits aignet cnf)))
                 (not (aignet-id-has-sat-var id sat-lits))))
      :flag lit)
    (defthm aignet-lit-list->cnf-preserves-no-sat-var-for-greater-id
      (implies (and (aignet-well-formedp aignet)
                    (sat-lits-wfp sat-lits aignet)
                    (not (aignet-id-has-sat-var id sat-lits))
                    (aignet-lit-listp x aignet)
                    (< (lits-max-id-val x) (id-val id)))
               (b* (((mv sat-lits ?cnf)
                     (aignet-lit-list->cnf x use-muxes
                                        aignet-refcounts sat-lits aignet cnf)))
                 (not (aignet-id-has-sat-var id sat-lits))))
      :flag list)
    :hints ((expand-aignet-lit->cnf-flg)))

  (local (in-theory (enable lookup-in-aignet->cnf-eval-special)))

  (local (defun zero-supergate-hint (clause)
           (if (Atom clause)
               nil
             (let ((lit (car clause)))
               (case-match lit
                 (('not ('member-equal ''0 ('lit-collect-supergate
                                            x & use-muxes . &)))
                  `(:use ((:instance collect-supergate-correct
                           (lit ,x) (use-muxes ,use-muxes)
                           (supergate nil) (top t)))))
                 (& (zero-supergate-hint (cdr clause))))))))

  (local (in-theory (disable sat-varp-when-varp
                             aignet-lit->cnf-cnf-satisfied-implies-orig-cnf-satisfied
                             sat-litp
                             sat-lit-listp-of-extension
                             sat-lit-list-listp-of-extension
                             sat-litp-of-extension
                             equal-when-bits-false
                             equal-when-bits-true)))


  ;; *** This is the second major correctness theorem about aignet-lit->cnf.
  ;; It says, basically:
  ;;  aignet-lit->cnf preserves the property that
  ;;    any evaluation of the aignet induces (via aignet->cnf-eval) a satisfying
  ;;    assignment of the CNF.
  ;;  (We have separately proven (cnf/aignet-evals-agree-of-aignet->cnf-eval)
  ;;   that these sat variable values correspond to the node values.)
  (defthm-aignet-lit->cnf-flg
    (defthm aignet-lit->cnf-satisfiable
      (b* (((mv sat-lits1 cnf1)
            (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf))
           (cnf-eval0 (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet))
           (cnf-eval1 (aignet->cnf-eval 0 in-vals reg-vals sat-lits1 cnf-eval aignet)))
        (implies (and (sat-lits-wfp sat-lits aignet)
                      (sat-lit-list-listp cnf sat-lits)
                      (aignet-well-formedp aignet)
                      (aignet-litp x aignet)
                      (equal (satlink::eval-formula cnf cnf-eval0) 1))
                 (equal (satlink::eval-formula cnf1 cnf-eval1) 1)))
      :hints ((and stable-under-simplificationp
                   (append
                    (zero-supergate-hint clause)
                    '(:in-theory (e/d (lit-eval aignet-litp)
                                      (id-eval-in-terms-of-lit-eval
                                       collect-supergate-correct))))))
      :flag lit)
    (defthm aignet-lit-list->cnf-satisfiable
      (b* (((mv sat-lits1 cnf1)
            (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf))
           (cnf-eval0 (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet))
           (cnf-eval1 (aignet->cnf-eval 0 in-vals reg-vals sat-lits1 cnf-eval aignet)))
        (implies (and (sat-lits-wfp sat-lits aignet)
                      (sat-lit-list-listp cnf sat-lits)
                      (aignet-well-formedp aignet)
                      (aignet-lit-listp x aignet)
                      (equal (satlink::eval-formula cnf cnf-eval0) 1))
                 (equal (satlink::eval-formula cnf1 cnf-eval1) 1)))
      :flag list)
    :hints ((expand-aignet-lit->cnf-flg))))



(defsection aignet-lit->cnf-correct
  (in-theory (disable aignet-lit->cnf aignet-lit-list->cnf))

  (defun-sk cnf-assign-induces-aignet-vals (cnf sat-lits aignet)
    (forall (cnf-eval in-vals reg-vals)
            (implies (equal (satlink::eval-formula cnf cnf-eval) 1)
                     (cnf/aignet-evals-agree
                      0
                      (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval aignet)
                      (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval aignet)
                      sat-lits cnf-eval aignet))))

  (defthm cnf/aignet-evals-agree-when-past-num-nodes
    (implies (<= (nfix (nth *num-nodes* aignet)) (nfix n))
             (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet)))

  (defthm cnf/aignet-evals-agree-of-cnf->aignet-eval-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (cnf/aignet-evals-agree
                   n
                   (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval
                                        orig-aignet)
                   (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval
                                         orig-aignet)
                   sat-lits cnf-eval orig-aignet))
             (cnf/aignet-evals-agree
              n
              (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval
                                   new-aignet)
              (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval
                                    new-aignet)
              sat-lits cnf-eval new-aignet))
    :hints (("goal" :induct (cnf/aignet-evals-agree
                             n
                             (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval
                                                  orig-aignet)
                             (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval
                                                   orig-aignet)
                             sat-lits cnf-eval orig-aignet)
             :expand ((:free (aignet in-vals reg-vals)
                       (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet))))
            (and stable-under-simplificationp
                 '(:cases ((aignet-idp (to-id n) orig-aignet))
                   :in-theory (enable sat-lits-wfp-implies-no-sat-var-when-not-aignet-idp)))))


  (defthm cnf-assign-induces-aignet-vals-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (cnf-assign-induces-aignet-vals cnf sat-lits orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (cnf-assign-induces-aignet-vals cnf sat-lits new-aignet))
    :hints(("Goal" :in-theory (disable cnf-assign-induces-aignet-vals
                                       cnf-assign-induces-aignet-vals-necc
                                       cnf/aignet-evals-agree))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance cnf-assign-induces-aignet-vals-necc
                           (cnf-eval (mv-nth 0
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                            (cnf-assign-induces-aignet-vals-witness
                                             . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl))))
                           (aignet orig-aignet))))))))



  (defthm cnf/aignet-evals-agree-on-new-cnf/sat-lits
    (implies (and (aignet-well-formedp aignet)
                  (equal (satlink::eval-var 0 cnf-eval) 0))
             (let ((sat-lits (resize-aignet->sat sz (create-sat-lits))))
               (cnf/aignet-evals-agree
                n
                (cnf->aignet-in-vals 0 in-vals sat-lits cnf-eval aignet)
                (cnf->aignet-reg-vals 0 reg-vals sat-lits cnf-eval aignet)
                sat-lits cnf-eval aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-id-has-sat-var
                                    aignet-id->sat-lit
                                    satlink::eval-lit
                                    nth-lit nth)
                                   ((aignet-id->sat-lit)
                                    resize-list)))))

  (defthm cnf-assign-induces-aignet-vals-of-new-cnf/sat-lits
    (implies (aignet-well-formedp aignet)
             (cnf-assign-induces-aignet-vals '((1))
                                          (resize-aignet->sat sz (create-sat-lits))
                                          aignet))
    :hints(("Goal" :in-theory (e/d* (satlink::eval-lit acl2::b-not)
                                    (cnf/aignet-evals-agree))
            :do-not-induct t)))

  (defthm aignet-lit->cnf-preserves-cnf-assign-induces-aignet-vals
    (implies (and (cnf-assign-induces-aignet-vals cnf sat-lits aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-well-formedp aignet)
                  (sat-lits-covered sat-lits aignet)
                  (aignet-litp x aignet))
             (b* (((mv sat-lits1 cnf1)
                   (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet
                                 cnf)))
               (cnf-assign-induces-aignet-vals cnf1 sat-lits1 aignet)))
    :hints(("Goal" :in-theory (disable cnf-assign-induces-aignet-vals
                                       cnf-assign-induces-aignet-vals-necc))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance cnf-assign-induces-aignet-vals-necc
                           (cnf-eval (mv-nth 0
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                            (cnf-assign-induces-aignet-vals-witness
                                             . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                            (cnf-assign-induces-aignet-vals-witness
                                             . ,(cdr concl)))))))))))

  (defthm aignet-lit-list->cnf-preserves-cnf-assign-induces-aignet-vals
    (implies (and (cnf-assign-induces-aignet-vals cnf sat-lits aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-well-formedp aignet)
                  (sat-lits-covered sat-lits aignet)
                  (aignet-lit-listp x aignet))
             (b* (((mv sat-lits1 cnf1)
                   (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet
                                      cnf)))
               (cnf-assign-induces-aignet-vals cnf1 sat-lits1 aignet)))
    :hints(("Goal" :in-theory (disable cnf-assign-induces-aignet-vals
                                       cnf-assign-induces-aignet-vals-necc))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance cnf-assign-induces-aignet-vals-necc
                           (cnf-eval (mv-nth 0
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                             (cnf-assign-induces-aignet-vals-witness
                                              . ,(cdr concl)))))))))))

  (defun-sk aignet-eval-induces-cnf-assign (cnf sat-lits aignet)
    (forall (cnf-eval in-vals reg-vals)
            (equal (satlink::eval-formula cnf (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval
                                                    aignet))
                   1)))

  (defthm aignet-eval-induces-cnf-assign-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-eval-induces-cnf-assign cnf sat-lits orig-aignet)
                  (sat-lits-wfp sat-lits orig-aignet)
                  (aignet-well-formedp orig-aignet))
             (aignet-eval-induces-cnf-assign cnf sat-lits new-aignet))
    :hints(("Goal" :in-theory (disable aignet-eval-induces-cnf-assign
                                       aignet-eval-induces-cnf-assign-necc
                                       cnf/aignet-evals-agree))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance aignet-eval-induces-cnf-assign-necc
                           (cnf-eval (mv-nth 0
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (aignet orig-aignet))))))))

  (defthm aignet-lit->cnf-preserves-aignet-eval-induces-cnf-assign
    (implies (and (aignet-eval-induces-cnf-assign cnf sat-lits aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-well-formedp aignet)
                  (sat-lit-list-listp cnf sat-lits)
                  (aignet-litp x aignet))
             (b* (((mv sat-lits1 cnf1)
                   (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
               (aignet-eval-induces-cnf-assign cnf1 sat-lits1 aignet)))
    :hints(("Goal" :in-theory (disable aignet-eval-induces-cnf-assign
                                       aignet-eval-induces-cnf-assign-necc))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance aignet-eval-induces-cnf-assign-necc
                           (cnf-eval (mv-nth 0
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl)))))))))))

  (defthm aignet-lit-list->cnf-preserves-aignet-eval-induces-cnf-assign
    (implies (and (aignet-eval-induces-cnf-assign cnf sat-lits aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-well-formedp aignet)
                  (sat-lit-list-listp cnf sat-lits)
                  (aignet-lit-listp x aignet))
             (b* (((mv sat-lits1 cnf1)
                   (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf)))
               (aignet-eval-induces-cnf-assign cnf1 sat-lits1 aignet)))
    :hints(("Goal" :in-theory (disable aignet-eval-induces-cnf-assign
                                       aignet-eval-induces-cnf-assign-necc))
           (and stable-under-simplificationp
                (let ((concl (car (last clause))))
                  `(:expand (,concl)
                    :use ((:instance aignet-eval-induces-cnf-assign-necc
                           (cnf-eval (mv-nth 0
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (in-vals (mv-nth 1
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl))))
                           (reg-vals (mv-nth 2
                                             (aignet-eval-induces-cnf-assign-witness
                                              . ,(cdr concl)))))))))))

  (local
   (progn
     (defthm nth-special
       (and (equal (lit-id (nth n '(0))) 0)
            (equal (lit-neg (nth n '(0))) 0)
            (equal (lit-fix (nth n '(0))) 0))
       :hints(("Goal" :in-theory (enable nth))))

     (defthm cnf-eval-0-of-aignet->cnf-eval
       (implies (and (aignet-well-formedp aignet)
                     (equal (nth 0 cnf-eval) 0))
                (equal (satlink::eval-var 0 (aignet->cnf-eval n in-vals reg-vals
                                                      (update-nth 1 (resize-list
                                                                     '(0) sz 0)
                                                                  '(1 (0) (0)))
                                                      cnf-eval aignet))
                       0))
       :hints(("Goal" :in-theory (e/d (aignet-id-has-sat-var
                                       aignet-id->sat-lit
                                       satlink::eval-var
                                       nth-lit
                                       acl2::nth-of-resize-list-split)
                                      (resize-list
                                       acl2::resize-list-when-empty)))))

     (defthm cnf-eval-0-of-aignet->cnf-eval-0
       (implies (and (aignet-well-formedp aignet)
                     (not (zp sz)))
                (equal (satlink::eval-var 0 (aignet->cnf-eval 0 in-vals reg-vals
                                                      (resize-aignet->sat sz (create-sat-lits))
                                                      cnf-eval aignet))
                       0))
       :hints(("Goal"
               :in-theory (e/d (aignet-id->sat-lit resize-aignet->sat
                                                   create-sat-lits
                                                   nth-lit)
                               (acl2::resize-list-when-empty))
               :expand ((:free (sat-lits)
                         (aignet->cnf-eval 0 in-vals reg-vals
                                        sat-lits cnf-eval aignet))))))))

  (defthm aignet-eval-induces-cnf-assign-of-new-cnf/sat-lits
    (implies (and (aignet-well-formedp aignet)
                  (not (zp sz)))
             (aignet-eval-induces-cnf-assign '((1))
                                             (resize-aignet->sat sz (create-sat-lits))
                                             aignet))
    :hints(("Goal" :in-theory (e/d* (satlink::eval-lit))))))
