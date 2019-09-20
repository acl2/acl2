; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
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

(include-book "centaur/aignet/cnf" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "eval")
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

;; ;; BOZO skipping node-list-fix congruence proofs here
;; (local (table fty::fixtypes 'fty::fixtype-alist
;;               (b* ((fixtype-alist (cdr (assoc 'fty::fixtype-alist (table-alist 'fty::fixtypes world)))))
;;                 (remove-equal (assoc 'aignet fixtype-alist)
;;                               fixtype-alist))))


(acl2::Def-universal-equiv eval-formula-equiv
  :qvars (env)
  :equiv-terms ((equal (eval-formula x env))))

(defcong eval-formula-equiv equal (eval-formula x env) 1
  :hints(("Goal" :in-theory (enable eval-formula-equiv-necc))))

(defcong eval-formula-equiv eval-formula-equiv (cons a b) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong eval-formula-equiv eval-formula-equiv (append a b) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong eval-formula-equiv eval-formula-equiv (append a b) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defxdoc aignet-ipasir
  :parents (aignet-cnf)
  :short "Using the @(see ipasir::ipasir) interface to run SAT checks on aignet nodes") 


#!ipasir
(define mux-add-clauses-ipasir ((res-id natp)
                                (c litp)
                                (tb litp)
                                (fb litp)
                                aignet::sat-lits
                                ipasir)
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns (new-ipasir)
  :hooks nil ;; mux-add-clauses doesn't currently satisfy fixtype convention
  (b* ((rl (aignet::aignet-id->sat-lit res-id aignet::sat-lits))
       (cl (aignet::aignet-lit->sat-lit c aignet::sat-lits))
       (tl (aignet::aignet-lit->sat-lit tb aignet::sat-lits))
       (fl (aignet::aignet-lit->sat-lit fb aignet::sat-lits))
       (rlb (satlink::lit-negate rl))
       (clb (satlink::lit-negate cl))
       (tlb (satlink::lit-negate tl))
       (flb (satlink::lit-negate fl))
       (ipasir (ipasir-cancel-new-clause ipasir)))
    (if (int= tb fb)          ;; fanins are equal
        ;; (list* (list tl rlb)  ;;  tb <-> res
        ;;        (list tlb rl)
        ;;        cnf-acc)
        (b* ((ipasir (ipasir-add-binary ipasir rl tlb)))
          (ipasir-add-binary ipasir rlb tl))
      ;; (list* (list clb tlb rl)     ;;   c &  tb ->  res
      ;;        (list cl  flb rl)     ;;  ~c &  fb ->  res
      ;;        (list clb tl  rlb)    ;;   c & ~tb -> ~res
      ;;        (list cl  fl  rlb)    ;;  ~c & ~fb -> ~res
      ;;        (if (int= tb (lit-negate fb))
      ;;            ;; xor, omit last two since they are always satisfied
      ;;            cnf-acc
      ;;          (list* (list tlb flb rl)  ;;  tb &  fb ->  res
      ;;                 (list tl  fl  rlb) ;; ~tb & ~fb -> ~res
      ;;                 cnf-acc)))
      (b* ((ipasir (if (int= tb (lit-negate fb))
                       ipasir
                     (b* ((ipasir (ipasir-add-ternary ipasir rlb fl tl)))
                       (ipasir-add-ternary ipasir rl flb tlb))))
           (ipasir (ipasir-add-ternary ipasir rlb fl cl))
           (ipasir (ipasir-add-ternary ipasir rlb tl clb))
           (ipasir (ipasir-add-ternary ipasir rl flb cl)))
        (ipasir-add-ternary ipasir rl tlb clb))))
  ///
  (defret ipasir-status-of-<fn>
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-<fn>
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-assumption-of-<fn>
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir)))

  (defret ipasir-formula-of-<fn>
    (equal (ipasir$a->formula new-ipasir)
           (aignet::mux-add-clauses res-id c tb fb aignet::sat-lits (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable aignet::mux-add-clauses
                                      ipasir-add-ternary
                                      ipasir-add-binary)))))


#!ipasir
(define supergate-add-clauses1-ipasir ((lit litp)
                                       (supergate lit-listp)
                                       aignet::sat-lits
                                       ipasir)
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :returns new-ipasir
  (if (atom supergate)
      (b* ((ipasir (ipasir-cancel-new-clause ipasir)))
        (ipasir-input ipasir))
    (b* ((ipasir (ipasir-add-binary ipasir
                                    (lit-negate (aignet::aignet-lit->sat-lit lit aignet::sat-lits))
                                    (aignet::aignet-lit->sat-lit (car supergate) aignet::sat-lits))))
      (supergate-add-clauses1-ipasir lit (cdr supergate) aignet::sat-lits ipasir)))
  ///
  (defret ipasir-status-of-<fn>
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-<fn>
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-assumption-of-<fn>
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir)))

  (defret ipasir-formula-of-<fn>
    (equal (ipasir$a->formula new-ipasir)
           (aignet::supergate-add-clauses1 lit (rev supergate) aignet::sat-lits (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable aignet::supergate-add-clauses1
                                      ipasir-add-binary)))))

#!ipasir
(define supergate-add-neg-fanins-ipasir ((supergate lit-listp)
                                         aignet::sat-lits
                                         ipasir)
  :guard (not (eq (ipasir-get-status ipasir) :undef))
  :returns new-ipasir
  (if (atom supergate)
      (ipasir-input ipasir)
    (b* ((ipasir (ipasir-add-lit ipasir
                                 (lit-negate
                                  (aignet::aignet-lit->sat-lit (car supergate) aignet::sat-lits)))))
      (supergate-add-neg-fanins-ipasir (cdr supergate) aignet::sat-lits ipasir)))
  ///
  (defret ipasir-status-of-<fn>
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-<fn>
    (equal (ipasir$a->new-clause new-ipasir)
           (append (rev (aignet::supergate-collect-neg-fanins supergate aignet::sat-lits))
                   (ipasir$a->new-clause ipasir)))
    :hints(("Goal" :in-theory (enable aignet::supergate-collect-neg-fanins))))

  (defret ipasir-assumption-of-<fn>
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir)))

  (defret ipasir-formula-of-<fn>
    (equal (ipasir$a->formula new-ipasir)
           (ipasir$a->formula ipasir))))

#!ipasir
(define supergate-add-clauses-ipasir ((res litp)
                                      (supergate lit-listp)
                                      aignet::sat-lits
                                      ipasir)
  :guard (and (not (eq (ipasir-get-status ipasir) :undef))
              (ipasir-empty-new-clause ipasir))
  :prepwork ((local (defthm lit-listp-of-rev
                      (implies (lit-listp x)
                               (lit-listp (rev x)))
                      :hints(("Goal" :in-theory (enable rev)))))
             (local (fty::deffixcong satlink::lit-list-equiv satlink::lit-list-equiv (rev x) x
                      :hints(("Goal" :in-theory (enable rev))))))
  :returns new-ipasir
  (b* ((supergate (rev supergate))
       (ipasir (supergate-add-clauses1-ipasir res supergate aignet::sat-lits ipasir))
       (ipasir (supergate-add-neg-fanins-ipasir supergate aignet::sat-lits ipasir))
       (ipasir (ipasir-add-lit ipasir (aignet::aignet-lit->sat-lit res aignet::sat-lits))))
    (ipasir-finalize-clause ipasir))
  ///
  (defret ipasir-status-of-<fn>
    (equal (ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-<fn>
    (equal (ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-assumption-of-<fn>
    (equal (ipasir$a->assumption new-ipasir)
           (ipasir$a->assumption ipasir)))

  (local (defthm append-of-supergate-collect-neg-fanins
           (equal (aignet::supergate-collect-neg-fanins (append x y) sat-lits)
                  (append (aignet::supergate-collect-neg-fanins x sat-lits)
                          (aignet::supergate-collect-neg-fanins y sat-lits)))
           :hints(("Goal" :in-theory (enable aignet::supergate-collect-neg-fanins)))))

  (local (defthm rev-of-supergate-collect-neg-fanins
           (equal (rev (aignet::supergate-collect-neg-fanins x sat-lits))
                  (aignet::supergate-collect-neg-fanins (rev x) sat-lits))
           :hints(("Goal" :in-theory (enable aignet::supergate-collect-neg-fanins)))))

  (local (defthm supergate-collect-neg-fanins-of-true-list-fix
           (equal (aignet::supergate-collect-neg-fanins (true-list-fix x) sat-lits)
                  (aignet::supergate-collect-neg-fanins x sat-lits))
           :hints(("Goal" :in-theory (enable aignet::supergate-collect-neg-fanins)))))

  (local (defthm supergate-add-clauses1-of-true-list-fix
           (equal (aignet::supergate-add-clauses1 lit (true-list-fix x) sat-lits cnf)
                  (aignet::supergate-add-clauses1 lit x sat-lits cnf))
           :hints(("Goal" :in-theory (enable aignet::supergate-add-clauses1)))))

  (defret ipasir-formula-of-<fn>
    (equal (ipasir$a->formula new-ipasir)
           (aignet::supergate-add-clauses res supergate aignet::sat-lits (ipasir$a->formula ipasir)))
    :hints(("Goal" :in-theory (enable aignet::supergate-add-clauses)))))
  


(defsection eval-formula-equiv-of-aignet-lit->cnf
  (local (defthm eval-formula-equiv-of-ipasir-add-unary
           (eval-formula-equiv (ipasir::ipasir$a->formula (ipasir::ipasir-add-unary ipasir lit))
                               (cons (list lit) (ipasir::ipasir$a->formula ipasir)))
           :hints(("Goal" :in-theory (enable eval-formula-equiv)))))

  (local (defthm eval-formula-equiv-of-ipasir-add-clauses
           (eval-formula-equiv (ipasir::ipasir$a->formula (ipasir::ipasir-add-clauses ipasir clauses))
                               (append clauses (ipasir::ipasir$a->formula ipasir)))
           :hints(("Goal" :in-theory (enable eval-formula-equiv)))))

  (defthm eval-formula-equiv-congruence-on-aignet-lit->cnf
    (implies (eval-formula-equiv cnf1 cnf2)
             (eval-formula-equiv (mv-nth 1 (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf1))
                                 (mv-nth 1 (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet cnf2))))
    :hints(("Goal" :in-theory (enable aignet-lit->cnf-normalize-cnf)))
    :rule-classes :congruence)

  (defthm eval-formula-equiv-congruence-on-aignet-lit-list->cnf
    (implies (eval-formula-equiv cnf1 cnf2)
             (eval-formula-equiv (mv-nth 1 (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf1))
                                 (mv-nth 1 (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet cnf2))))
    :hints(("Goal" :in-theory (enable aignet-lit-list->cnf-normalize-cnf)))
    :rule-classes :congruence)

  
  (defcong eval-formula-equiv equal (cnf-for-aignet aignet cnf sat-lits) 2
    :hints (("goal" :cases ((cnf-for-aignet aignet cnf sat-lits)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'cnf-for-aignet clause))
                      (other-cnf (if (eq (third lit) 'cnf) 'cnf-equiv 'cnf)))
                   `(:expand (,lit)
                     :use ((:instance cnf-for-aignet-necc
                            (cnf ,other-cnf)
                            (invals (mv-nth 0 (cnf-for-aignet-witness . ,(cdr lit))))
                            (regvals (mv-nth 1 (cnf-for-aignet-witness . ,(cdr lit))))
                            (cnf-vals (mv-nth 2 (cnf-for-aignet-witness . ,(cdr lit))))))
                     :in-theory (disable cnf-for-aignet-necc)))))
    :otf-flg t))




(defines aignet-lit->ipasir
  (define aignet-lit->ipasir ((x litp           "Literal to encode in the CNF")
                              (use-muxes        "Flag saying whether to recognize muxes and encode them specially")
                              (aignet-refcounts "Reference counts of aignet nodes")
                              (sat-lits         "Records assignment of SAT variables to aignet nodes")
                              (aignet           "AIG network")
                              (ipasir           "Incremental solver instance containing the accumulated formula"))
    :guard (and (< (lit-id x) (u32-length aignet-refcounts))
                (fanin-litp x aignet)
                (sat-lits-wfp sat-lits aignet)
                (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                               (not (ipasir::ipasir$a->new-clause ipasir)))))
    :returns (mv (new-sat-lits (implies (sat-lits-wfp sat-lits aignet)
                                        (sat-lits-wfp new-sat-lits aignet))
                               "Updated assignment of SAT variables to aignet nodes")
                 (new-ipasir   "Incremental solver instance, updated with additional
                                clauses for the fanin cone of @('x')."))
    :verify-guards nil
    :flag lit
    :measure (acl2::two-nats-measure (lit-id x) 0)
    :parents (aignet-ipasir)
    :short "Add clauses encoding the fanin cone of literal @('x') of the aignet to the incremental solver."
    :long "<p>Assumes that aignet nodes that have SAT variables assigned in
@('sat-lits') already have their fanin cones encoded, and maintains that invariant.</p>

<p>See @(see ipasir::ipasir) for information on the incremental solver interface.</p>"
    (b* ((id (lit-id x))
         (ipasir (ipasir::ipasir-cancel-new-clause ipasir))
         (ipasir (ipasir::ipasir-input ipasir))
         ((when (aignet-id-has-sat-var id sat-lits))
          ;; already added, so done
          (mv sat-lits ipasir))
         ((when (int= (id->type id aignet) (in-type)))
          ;; input: add variable but no clauses, so it's free
          (b* ((sat-lits
                (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet)))
            (mv sat-lits ipasir)))
         ((unless (int= (id->type id aignet) (gate-type)))
          ;; constant, add variable and a unary clause setting the ID to false
          (b* ((sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits
                                             aignet))
               (sat-lit (aignet-id->sat-lit id sat-lits))
               (ipasir (ipasir::ipasir-add-unary ipasir (satlink::lit-negate sat-lit))))
            (mv sat-lits ipasir)))
         ;; now we have a gate node -- check first for a mux if we're doing that
         ;; if it's an xor, we say it's a mux regardless
         ((mv muxp c tb fb) (if (or use-muxes (eql 1 (id->regp id aignet)))
                                (id-is-mux id aignet)
                              (mv nil nil nil nil)))
         ((when muxp)
          ;; recur on the three children, add the node, add the mux clauses
          (b* (((mv sat-lits ipasir)
                (aignet-lit->ipasir c use-muxes aignet-refcounts sat-lits aignet ipasir))
               ((mv sat-lits ipasir)
                (aignet-lit->ipasir tb use-muxes aignet-refcounts sat-lits aignet ipasir))
               ((mv sat-lits ipasir)
                (aignet-lit->ipasir fb use-muxes aignet-refcounts sat-lits aignet ipasir))
               (sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet))
               (ipasir (ipasir::mux-add-clauses-ipasir id c tb fb sat-lits ipasir)))
            (mv sat-lits ipasir)))
         (lit (mk-lit id 0))
         ((mv supergate &)
          (lit-collect-supergate
           lit t use-muxes 1000 nil aignet-refcounts aignet))
         ((when (member 0 supergate))
          ;; one of the fanins is const 0, so the node is const 0
          (b* ((sat-lits (sat-add-aignet-lit lit sat-lits aignet))
               (sat-lit (aignet-id->sat-lit id sat-lits))
               (ipasir (ipasir::ipasir-add-unary ipasir (lit-negate sat-lit))))
            (mv sat-lits ipasir)))
         ;; recur on the children of the supergate, add the parent literal,
         ;; add the supergate clauses.
         ((mv sat-lits ipasir)
          (aignet-lit-list->ipasir supergate use-muxes aignet-refcounts sat-lits aignet ipasir))
         (sat-lits (sat-add-aignet-lit lit sat-lits aignet))
         (ipasir (ipasir::supergate-add-clauses-ipasir
                  lit supergate sat-lits ipasir)))
      (mv sat-lits ipasir)))

  (define aignet-lit-list->ipasir ((x lit-listp)
                                   (use-muxes)
                                   (aignet-refcounts)
                                   (sat-lits)
                                   (aignet)
                                   (ipasir))
    :guard (and (< (lits-max-id-val x) (u32-length aignet-refcounts))
                (aignet-lit-listp x aignet)
                (sat-lits-wfp sat-lits aignet)
                (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                               (not (ipasir::ipasir$a->new-clause ipasir)))))
    :returns (mv (new-sat-lits (implies (sat-lits-wfp sat-lits aignet)
                                        (sat-lits-wfp new-sat-lits aignet)))
                 (new-ipasir))
    :measure (acl2::two-nats-measure (lits-max-id-val x) (+ 1 (len x)))
    :flag list
    (if (atom x)
        (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
             (ipasir (ipasir::ipasir-input ipasir)))
          (mv sat-lits ipasir))
      (b* (((mv sat-lits ipasir)
            (aignet-lit->ipasir (car x) use-muxes aignet-refcounts sat-lits aignet ipasir)))
        (aignet-lit-list->ipasir (cdr x) use-muxes aignet-refcounts sat-lits aignet
                                 ipasir))))
  ///

  (local (in-theory (disable aignet-lit->ipasir
                             aignet-lit-list->ipasir)))

  (std::defret-mutual ipasir-status-of-aignet-lit->ipasir
    (defret ipasir-status-of-aignet-lit->ipasir
      (equal (ipasir::ipasir$a->status new-ipasir) :input)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir)
    (defret ipasir-status-of-aignet-lit-list->ipasir
      (equal (ipasir::ipasir$a->status new-ipasir) :input)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir))

  (std::defret-mutual ipasir-new-clause-of-aignet-lit->ipasir
    (defret ipasir-new-clause-of-aignet-lit->ipasir
      (equal (ipasir::ipasir$a->new-clause new-ipasir) nil)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir)
    (defret ipasir-new-clause-of-aignet-lit-list->ipasir
      (equal (ipasir::ipasir$a->new-clause new-ipasir) nil)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir))

  (std::defret-mutual ipasir-assumption-of-aignet-lit->ipasir
    (defret ipasir-assumption-of-aignet-lit->ipasir
      (equal (ipasir::ipasir$a->assumption new-ipasir)
             (ipasir::ipasir$a->assumption ipasir))
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir)
    (defret ipasir-assumption-of-aignet-lit-list->ipasir
      (equal (ipasir::ipasir$a->assumption new-ipasir)
             (ipasir::ipasir$a->assumption ipasir))
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir))

  (local (defthm lit-listp-implies-true-listp
           (implies (lit-listp x) (true-listp x)))) 

  (verify-guards aignet-lit->ipasir)

  

  (local (defthm supergate-add-clauses1-normalize
           (implies (syntaxp (not (equal cnf ''nil)))
                    (equal (supergate-add-clauses1 lit supergate sat-lits cnf)
                           (append (supergate-add-clauses1 lit supergate sat-lits nil)
                                   cnf)))
           :hints(("Goal" :in-theory (enable supergate-add-clauses1)))))

  (local (defthm mux-add-clauses-normalize
           (implies (syntaxp (not (equal cnf ''nil)))
                    (equal (mux-add-clauses res-id c tb fb sat-lits cnf)
                           (append (mux-add-clauses res-id c tb fb sat-lits nil)
                                   cnf)))
           :hints(("Goal" :in-theory (enable mux-add-clauses)))))

  (encapsulate nil
    (local (defun concl-formula (fn)
             `(implies (syntaxp (not (equal ipasir ''nil)))
                       (b* (((mv new-sat-lits new-ipasir)
                             (,fn x use-muxes aignet-refcounts sat-lits aignet ipasir))
                            ((mv new-sat-lits2 new-ipasir2)
                             (,fn x use-muxes aignet-refcounts sat-lits aignet nil)))
                         (and (equal new-sat-lits new-sat-lits2)
                              (equal (ipasir::ipasir$a->formula new-ipasir)
                                     (append (ipasir::ipasir$a->formula new-ipasir2)
                                             (ipasir::ipasir$a->formula ipasir))))))))
    (local
     (make-event
      `(defun-sk aignet-lit->ipasir-normalize-req
         (x use-muxes aignet-refcounts sat-lits aignet)
         (forall (ipasir)
                 ,(concl-formula 'aignet-lit->ipasir))
         :rewrite :direct)))
    (local
     (make-event
      `(defun-sk aignet-lit-list->ipasir-normalize-req
         (x use-muxes aignet-refcounts sat-lits aignet)
         (forall (ipasir)
                 ,(concl-formula 'aignet-lit-list->ipasir))
         :rewrite :direct)))

    (local (in-theory (disable aignet-lit->ipasir-normalize-req
                               aignet-lit-list->ipasir-normalize-req)))

    (local
     (std::defret-mutual aignet-lit->ipasir-normalize-lemma
       (defret aignet-lit->ipasir-normalize-lemma
         (aignet-lit->ipasir-normalize-req x use-muxes aignet-refcounts sat-lits aignet)
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))
                                 (:free (use-muxes ipasir) <call>))
                        :in-theory (enable ipasir::ipasir-add-unary-formula
                                           ipasir::ipasir-add-clauses-ordered-formula)
                        ;; :in-theory (enable supergate-add-clauses-normalize-cnf-acc
                        ;;                    mux-add-clauses-normalize-cnf-acc)
                        )))
         :fn aignet-lit->ipasir)
       (defret aignet-lit-list->ipasir-normalize-lemma
         (aignet-lit-list->ipasir-normalize-req x use-muxes aignet-refcounts sat-lits aignet)
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))
                                 (:free (use-muxes ipasir) <call>)))))
         :fn aignet-lit-list->ipasir)))

    (make-event
     `(defthm aignet-lit->ipasir-normalize
        ,(concl-formula 'aignet-lit->ipasir)))

    (make-event
     `(defthm aignet-lit-list->ipasir-normalize
        ,(concl-formula 'aignet-lit-list->ipasir))))

  (std::defret-mutual sat-lits-of-aignet-lit->ipasir-reduce-to-aignet-lit->cnf
    (defret sat-lits-of-aignet-lit->ipasir-reduce-to-aignet-lit->cnf
      (b* (((mv ?new-sat-lits ?new-ipasir)
            (aignet-lit->ipasir x use-muxes aignet-refcounts sat-lits aignet nil))
           ((mv ?new-sat-lits-spec ?new-cnf)
            (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet nil)))
        (equal new-sat-lits new-sat-lits-spec))
      :hints (`(:expand ((:free (use-muxes ipasir) <call>)
                         (:free (use-muxes ipasir) (aignet-lit->cnf . ,(cdr '<call>))))
                :in-theory (enable aignet-lit->ipasir-normalize
                                   aignet-lit-list->ipasir-normalize
                                   aignet-lit->cnf-normalize-cnf
                                   aignet-lit-list->cnf-normalize-cnf)))
      :fn aignet-lit->ipasir)

    (defret sat-lits-of-aignet-lit-list->ipasir-reduce-to-aignet-lit-list->cnf
      (b* (((mv ?new-sat-lits ?new-ipasir)
            (aignet-lit-list->ipasir x use-muxes aignet-refcounts sat-lits aignet nil))
           ((mv ?new-sat-lits-spec ?new-cnf)
            (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet nil)))
        (equal new-sat-lits new-sat-lits-spec))
      :hints (`(:expand ((:free (use-muxes ipasir) <call>)
                         (:free (use-muxes ipasir) (aignet-lit-list->cnf . ,(cdr '<call>))))
                :in-theory (enable aignet-lit->ipasir-normalize
                                   aignet-lit-list->ipasir-normalize
                                   aignet-lit->cnf-normalize-cnf
                                   aignet-lit-list->cnf-normalize-cnf)))
      :fn aignet-lit-list->ipasir))

  (std::defret-mutual formula-of-aignet-lit->ipasir-reduce-to-aignet-lit->cnf
    (defret formula-of-aignet-lit->ipasir-reduce-to-aignet-lit->cnf
      (b* (((mv ?new-sat-lits ?new-ipasir)
            (aignet-lit->ipasir x use-muxes aignet-refcounts sat-lits aignet nil))
           ((mv ?new-sat-lits-spec new-cnf-spec)
            (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet nil)))
        (equal (ipasir$a->formula new-ipasir)
               new-cnf-spec))
      :hints (`(:expand ((:free (use-muxes ipasir) <call>)
                         (:free (use-muxes ipasir) (aignet-lit->cnf . ,(cdr '<call>))))
                :in-theory (enable aignet-lit->ipasir-normalize
                                   aignet-lit-list->ipasir-normalize
                                   aignet-lit->cnf-normalize-cnf
                                   aignet-lit-list->cnf-normalize-cnf
                                   ipasir::ipasir-add-clauses-ordered-formula
                                   IPASIR::IPASIR-ADD-UNARY-FORMULA)))
      :fn aignet-lit->ipasir)

    (defret formula-of-aignet-lit-list->ipasir-reduce-to-aignet-lit-list->cnf
      (b* (((mv ?new-sat-lits ?new-ipasir)
            (aignet-lit-list->ipasir x use-muxes aignet-refcounts sat-lits aignet nil))
           ((mv ?new-sat-lits-spec ?new-cnf-spec)
            (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet nil)))
        (equal (ipasir$a->formula new-ipasir)
               new-cnf-spec))
      :hints (`(:expand ((:free (use-muxes ipasir) <call>)
                         (:free (use-muxes ipasir) (aignet-lit-list->cnf . ,(cdr '<call>))))
                :in-theory (enable aignet-lit->ipasir-normalize
                                   aignet-lit-list->ipasir-normalize
                                   aignet-lit->cnf-normalize-cnf
                                   aignet-lit-list->cnf-normalize-cnf)))
      :fn aignet-lit-list->ipasir))

  
  ;; (local (DEFTHM SAT-LITS-WFP-IMPLIES-LOOKUP-AIGNET-ID-bind-free
  ;;          (IMPLIES (AND (bind-free '((aignet . aignet)))
  ;;                        (SAT-LITS-WFP SAT-LITS AIGNET)
  ;;                        (AIGNET-IDP N AIGNET)
  ;;                        (AIGNET-ID-HAS-SAT-VAR N SAT-LITS))
  ;;                   (AND
  ;;                    (EQUAL (SAT-VAR->AIGNET-LIT
  ;;                            (satlink::lit->var (AIGNET-ID->SAT-LIT N SAT-LITS))
  ;;                            SAT-LITS)
  ;;                           (MK-LIT
  ;;                            N
  ;;                            (satlink::LIT->NEG (AIGNET-ID->SAT-LIT N SAT-LITS))))
  ;;                    (SAT-VARP (satlink::lit->var (AIGNET-ID->SAT-LIT N SAT-LITS))
  ;;                              SAT-LITS)))))

  ;; (local (in-theory (enable AIGNET-ID-HAS-SAT-VAR-PRESERVED-SPLIT-OF-SAT-ADD-AIGNET-LIT)))


  ;; (defthm sat-lit-list-listp-of-rev
  ;;   (implies (sat-lit-list-listp x sat-lits)
  ;;            (sat-lit-list-listp (acl2::rev x) sat-lits))
  ;;   :hints(("Goal" :in-theory (enable acl2::rev))))

  ;; (defthm sat-lit-listp-of-rev
  ;;   (implies (sat-lit-listp x sat-lits)
  ;;            (sat-lit-listp (acl2::rev x) sat-lits))
  ;;   :hints(("Goal" :in-theory (enable acl2::rev))))

  ;; (defthm sat-lit-list-listp-of-rev-each
  ;;   (implies (sat-lit-list-listp x sat-lits)
  ;;            (sat-lit-list-listp (ipasir::rev-each x) sat-lits))
  ;;   :hints(("Goal" :in-theory (enable ipasir::rev-each))))

  ;; (defthm sat-lit-list-litp-of-cons
  ;;   (equal (sat-lit-list-listp (cons a b) sat-lits)
  ;;          (and (sat-lit-listp a sat-lits)
  ;;               (sat-lit-list-listp b sat-lits))))

  ;; (defthm sat-lit-litp-of-cons
  ;;   (equal (sat-lit-listp (cons a b) sat-lits)
  ;;          (and (sat-litp a sat-lits)
  ;;               (sat-lit-listp b sat-lits))))

  ;; (defthm sat-lit-listp-of-nil
  ;;   (sat-lit-listp nil sat-lits))

  ;; (local (in-theory (disable sat-lit-list-listp sat-lit-listp)))

  ;; (std::defret-mutual good-cnf-of-aignet-lit->ipasir
  ;;   (defret good-cnf-of-aignet-lit->ipasir
  ;;     (b* ((new-sat-lits (mv-nth 0 (aignet-lit->cnf x use-muxes aignet-refcounts sat-lits aignet nil))))
  ;;       (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                     (aignet-litp x aignet))
  ;;                (implies (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
  ;;                         (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits))))
  ;;     :hints (`(:expand ((:free (use-muxes ipasir) <call>)
  ;;                        (:free (use-muxes ipasir) (aignet-lit->cnf . ,(cdr '<call>))))
  ;;               :in-theory (enable ipasir::ipasir-add-unary-formula
  ;;                                  ipasir::ipasir-add-clauses-formula)))
  ;;     :fn aignet-lit->ipasir)
  ;;   (defret good-cnf-of-aignet-lit-list->ipasir
  ;;     (b* ((new-sat-lits (mv-nth 0 (aignet-lit-list->cnf x use-muxes aignet-refcounts sat-lits aignet nil))))
  ;;       (implies (and (sat-lits-wfp sat-lits aignet)
  ;;                     (aignet-lit-listp x aignet))
  ;;                (implies (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
  ;;                         (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits))))
  ;;     :hints (`(:expand ((:free (use-muxes ipasir) <call>)
  ;;                        (:free (use-muxes ipasir) (aignet-lit-list->cnf . ,(cdr '<call>))))))
  ;;     :fn aignet-lit-list->ipasir))

  (fty::deffixequiv-mutual aignet-lit->ipasir))





(define aignet-get-ipasir-ctrex-invals
  ((n natp   "Iterator -- should start at 0")
   (invals   "Bit array stobj which will be overwritten with the input values")
   (sat-lits "Records assignment of SAT variables to aignet nodes")
   (aignet   "AIG network")
   (ipasir   "Incremental solver -- must be in @(':sat') state"))
  :guard (and (sat-lits-wfp sat-lits aignet)
              (<= n (num-ins aignet))
              (<= (num-ins aignet) (bits-length invals))
              (non-exec (equal (ipasir::ipasir$a->status ipasir) :sat)))
  :returns (new-invals "Updated bit array stobj containing the input values")
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :verify-guards nil
  :parents (aignet-ipasir)
  :short "Records the input values for a satisfying assignment from an ipasir SAT check."
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        invals)
       (id (innum->id n aignet))
       (sat-lit (aignet-id->sat-lit id sat-lits))
       ((when (eql 0 sat-lit))
        (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
       (val (ipasir::ipasir-val ipasir sat-lit))
       ((unless val)
        (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
       (invals (set-bit n val invals)))
    (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
  ///
  (defret invals-length-of-aignet-get-ipasir-ctrex-invals
    (implies (<= (num-ins aignet) (len invals))
             (equal (len new-invals) (len invals))))
  (verify-guards aignet-get-ipasir-ctrex-invals))


(define aignet-get-ipasir-ctrex-regvals
  ((n natp   "Iterator -- should start at 0")
   (regvals   "Bit array stobj which will be overwritten with the register values")
   (sat-lits "Records assignment of SAT variables to aignet nodes")
   (aignet   "AIG network")
   (ipasir   "Incremental solver -- must be in @(':sat') state"))
  :guard (and (sat-lits-wfp sat-lits aignet)
              (<= n (num-regs aignet))
              (<= (num-regs aignet) (bits-length regvals))
              (non-exec (equal (ipasir::ipasir$a->status ipasir) :sat)))
  :returns (new-regvals "Updated bit array stobj containing the input values")
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :verify-guards nil
  :parents (aignet-ipasir)
  :short "Records the register values for a satisfying assignment from an ipasir SAT check."
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        regvals)
       (id (regnum->id n aignet))
       (sat-lit (aignet-id->sat-lit id sat-lits))
       ((when (eql 0 sat-lit))
        (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
       (val (ipasir::ipasir-val ipasir sat-lit))
       ((unless val)
        (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
       (regvals (set-bit n val regvals)))
    (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
  ///
  (defret regvals-length-of-aignet-get-ipasir-ctrex-regvals
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len new-regvals) (len regvals))))
  (verify-guards aignet-get-ipasir-ctrex-regvals))

(local (in-theory (enable aignet-idp)))

(local (in-theory (disable w)))

(local (defthm w-of-read-acl2-oracle
         (equal (w (mv-nth 2 (read-acl2-oracle state)))
                (w state))
         :hints(("Goal" :in-theory (enable read-acl2-oracle w update-acl2-oracle)))))

(local (defthm w-of-random$
         (equal (w (mv-nth 1 (random$ n state)))
                (w state))
         :hints(("Goal" :in-theory (enable random$)))))

(define aignet-lit-ipasir-sat-check-aux ((x litp)
                                         sat-lits ipasir
                                         aignet state)
  ;; Returns ipasir ready to solve
  :guard (and (fanin-litp x aignet)
              (non-exec (and (equal sat-lits (create-sat-lits))
                             (equal ipasir (create-ipasir)))))
  :returns (mv new-ipasir
               new-sat-lits
               new-state)
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((acl2::local-stobjs aignet-refcounts)
        (mv aignet-refcounts ipasir sat-lits state))
       (sat-lits (mbe :logic (non-exec (create-sat-lits)) :exec sat-lits))
       (ipasir (mbe :logic (non-exec (create-ipasir)) :exec ipasir))
       ((mv ipasir state) (ipasir::ipasir-init ipasir state))
       (sat-lits (resize-aignet->sat (ash (num-fanins aignet) -1) sat-lits)) 
       (aignet-refcounts (resize-u32 (num-fanins aignet) aignet-refcounts))
       (aignet-refcounts (aignet-count-refs aignet-refcounts aignet))
       ((mv sat-lits ipasir) (aignet-lit->ipasir (lit-fix x) t aignet-refcounts sat-lits aignet ipasir))
       (sat-lit (aignet-lit->sat-lit x sat-lits))
       (ipasir (ipasir::ipasir-assume ipasir sat-lit)))
    (mv aignet-refcounts ipasir sat-lits state))
  ///
  (defret ipasir-status-of-aignet-lit-ipasir-sat-check-aux
    (equal (ipasir::ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-aignet-lit-ipasir-sat-check-aux
    (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  ;; (defret cnf-for-aignet-of-aignet-lit-ipasir-sat-check-aux
  ;;   (implies (aignet-litp x aignet)
  ;;            (cnf-for-aignet aignet (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret sat-lits-wfp-of-aignet-lit-ipasir-sat-check-aux
    (implies (aignet-litp x aignet)
             (sat-lits-wfp new-sat-lits aignet)))

  (defthm normalize-inputs-of-aignet-lit-ipasir-sat-check-aux
    (implies (syntaxp (not (and (equal sat-lits ''nil)
                                (equal ipasir ''nil))))
             (equal (aignet-lit-ipasir-sat-check-aux x sat-lits ipasir aignet state)
                    (aignet-lit-ipasir-sat-check-aux x nil nil aignet state))))

  (local (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id-bind
           (implies (and (bind-free '((aignet . aignet)))
                         (sat-lits-wfp sat-lits aignet)
                         (aignet-id-has-sat-var n sat-lits))
                    (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                              sat-lits))))

  (local (defthm sat-lits-wfp-implies-lookup-aignet-id-bind
           (implies (and (bind-free '((aignet . aignet)) (aignet))
                         (sat-lits-wfp sat-lits aignet)
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
           :hints (("goal" :by sat-lits-wfp-implies-lookup-aignet-id))))

  (defret aignet-lit-ipasir-sat-check-aux-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (b* (((mv status &) (ipasir::ipasir-solve$a new-ipasir)))
               (not (equal status :unsat))))
    :hints (("goal" :use ((:instance ipasir::ipasir-solve$a-unsat-implies-unsat
                           (env$ (aignet->cnf-vals some-invals some-regvals nil new-sat-lits aignet))
                           (formula (ipasir::ipasir$a->formula new-ipasir))
                           (solver new-ipasir)))
             :expand ((aignet-eval-conjunction nil some-invals some-regvals aignet))
             :in-theory (disable ipasir::ipasir-solve$a-unsat-implies-unsat))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))
               

(acl2::defstobj-clone inmasks bitarr :prefix "INMASKS-")
(acl2::defstobj-clone regmasks bitarr :prefix "REGMASKS-")
(acl2::defstobj-clone mark bitarr :suffix "-MARK")

(define aignet-vals-sat-care-masks-rec
  ((id natp "ID to traverse")
   (inmasks  "Bit array accumulating the care set for the inputs")
   (regmasks "Bit array accumulating the care set for the registers")
   (invals   "Bit array recording the satisfying assignment for the inputs")
   (regvals  "Bit array recording the satisfying assignment for the registers")
   (vals     "Bit array recording the values of all nodes under the satisfying assignment")
   (mark     "Bit array marking nodes known to be in the care set")
   (aignet   "AIG network")
   (state    "ACL2 state, used for random number generation (coin flips)"))
  :guard (and (id-existsp id aignet)
              (non-exec (equal vals (aignet-record-vals nil invals regvals aignet)))
              (not (Equal (id->type id aignet) (out-type)))
              (<= (num-ins aignet) (bits-length inmasks))
              (<= (num-regs aignet) (bits-length regmasks))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (< id (bits-length vals))
              (< id (bits-length mark)))
  :verify-guards nil
  :returns (mv (new-inmasks  "Updated care set of inputs")
               (new-regmasks "Updated care set of registers")
               (new-mark     "Updated care set of all nodes")
               (new-state    "Updated state"))

  :parents (aignet-ipasir)
  :short "Mark a subset of inputs and registers that, when assigned the same values
          as in the input assignment, produce the same value on the given
          @('id')."
  (b* (((when (eql 1 (get-bit id mark)))
        (mv inmasks regmasks mark state))
       (mark (set-bit id 1 mark)))
    (aignet-case (id->type id aignet)
      :in (if (eql 1 (id->regp id aignet))
              (b* ((regmasks (set-bit (ci-id->ionum id aignet) 1 regmasks)))
                (mv inmasks regmasks mark state))
            (b* ((inmasks (set-bit (ci-id->ionum id aignet) 1 inmasks)))
              (mv inmasks regmasks mark state)))
      :out (mv inmasks regmasks mark state)
      :const (mv inmasks regmasks mark state)
      :gate (b* ((val (mbe :logic (id-eval id invals regvals aignet)
                           :exec (get-bit id vals)))
                 (f0 (gate-id->fanin0 id aignet))
                 (f1 (gate-id->fanin1 id aignet))
                 ((when (or (eql val 1)
                            (eql (id->regp id aignet) 1)))
                  ;; both needed
                  (b* (((mv inmasks regmasks mark state)
                        (aignet-vals-sat-care-masks-rec
                         (lit-id f0) inmasks regmasks invals regvals vals mark aignet state)))
                    (aignet-vals-sat-care-masks-rec
                     (lit-id f1) inmasks regmasks invals regvals vals mark aignet state)))
                 ((when (eql (mbe :logic (lit-eval f0 invals regvals aignet)
                                  :exec (aignet-eval-lit f0 vals)) 1))
                  ;; f1 only needed
                  (aignet-vals-sat-care-masks-rec
                   (lit-id f1) inmasks regmasks invals regvals vals mark aignet state))
                 ((when (eql (mbe :logic (lit-eval f1 invals regvals aignet)
                                  :exec (aignet-eval-lit f1 vals))
                             1))
                  ;; f0 only needed
                  (aignet-vals-sat-care-masks-rec
                   (lit-id f0) inmasks regmasks invals regvals vals mark aignet state))
                 ;; either one will do, check if one is already marked
                 ((when (or (eql 1 (get-bit (lit-id f0) mark))
                            (eql 1 (get-bit (lit-id f1) mark))))
                  (mv inmasks regmasks mark state))
                 ((mv coinflip state) (random$ 2 state)))
              (if (eql 1 coinflip)
                  (aignet-vals-sat-care-masks-rec
                   (lit-id f1) inmasks regmasks invals regvals vals mark aignet state)
                (aignet-vals-sat-care-masks-rec
                 (lit-id f0) inmasks regmasks invals regvals vals mark aignet state)))))
  ///
  (local (in-theory (disable (:d aignet-vals-sat-care-masks-rec))))

  (defthm aignet-vals-sat-care-masks-normalize-input
    (implies (syntaxp (not (equal vals ''nil)))
             (equal (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)
                    (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals nil mark aignet state)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)
             :expand-others ((:free (vals)
                              (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state))))
            (and stable-under-simplificationp
                 '(:do-not-induct t))))

  (defret aignet-vals-sat-care-masks-preserve-marks
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-preserve-inmasks
    (implies (equal (nth n inmasks) 1)
             (equal (nth n new-inmasks) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-preserve-regmasks
    (implies (equal (nth n regmasks) 1)
             (equal (nth n new-regmasks) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret inmasks-length-of-aignet-vals-sat-care-masks
    (implies (<= (num-ins aignet) (len inmasks))
             (equal (len new-inmasks) (len inmasks)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret regmasks-length-of-aignet-vals-sat-care-masks
    (implies (<= (num-regs aignet) (len regmasks))
             (equal (len new-regmasks) (len regmasks)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret mark-length-of-aignet-vals-sat-care-masks
    (implies (< (nfix id) (len mark))
             (equal (len new-mark) (len mark)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (defthm lit-id-of-fanin-mark-lemma
           (implies (< (nfix id) (len mark))
                    (< (lit-id (fanin ftype (lookup-id id aignet))) (len mark)))
           :hints (("goal" :cases ((<= (nfix id) (fanin-count aignet)))))))

  (verify-guards aignet-vals-sat-care-masks-rec
    :hints(("Goal" :in-theory (enable lit-eval))))

  (defun-nx aignet-vals-sat-care-masks-mark-ok (node mark invals regvals aignet)
    (implies (equal (nth node mark) 1)
             (and (implies (equal (stype (car (lookup-id node aignet))) (and-stype))
                           (and (implies (equal (id-eval node invals regvals aignet) 1)
                                         (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                              (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                                (implies (and (equal (id-eval node invals regvals aignet) 0)
                                              (not (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                                         invals regvals aignet)
                                                               0)
                                                        (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1))))
                                         (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     0)
                                              (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))))
                  (implies (equal (stype (car (lookup-id node aignet))) (xor-stype))
                           (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1))))))

  (defun-sk aignet-vals-sat-care-masks-mark-invar (id mark invals regvals aignet)
    (forall node
            (implies (<= (nfix node) (nfix id))
                     (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)))
    :rewrite :direct)

  (in-theory (disable aignet-vals-sat-care-masks-mark-invar))

  (defthmd aignet-vals-sat-care-masks-mark-invar-rw
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (<= (nfix node) (nfix id))
                  (equal (nth node mark) 1))
             (and (implies (equal (stype (car (lookup-id node aignet))) (and-stype))
                           (and (implies (equal (id-eval node invals regvals aignet) 1)
                                         (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                              (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                                (implies (and (equal (id-eval node invals regvals aignet) 0)
                                              (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     1))
                                         (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     0)
                                              (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                                
                                (implies (and (equal (id-eval node invals regvals aignet) 0)
                                              (not (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))
                                         (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     0)
                                              (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))

                                (implies (and (equal (id-eval node invals regvals aignet) 0)
                                              (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     1))
                                         (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     0)
                                              (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))
                                
                                (implies (and (equal (id-eval node invals regvals aignet) 0)
                                              (not (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                                         (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                               invals regvals aignet)
                                                     0)
                                              (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))))
                  (implies (equal (stype (car (lookup-id node aignet))) (xor-stype))
                           (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))))
    :hints (("goal" :use aignet-vals-sat-care-masks-mark-invar-necc
             :in-theory (disable aignet-vals-sat-care-masks-mark-invar-necc))))
             


  (defthm aignet-vals-sat-care-masks-mark-invar-when-lesser-id
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (<= (nfix id2) (nfix id)))
             (aignet-vals-sat-care-masks-mark-invar id2 mark invals regvals aignet))
    :hints (("goal" :expand ((aignet-vals-sat-care-masks-mark-invar id2 mark invals regvals aignet))
             :in-theory (enable aignet-vals-sat-care-masks-mark-ok
                                aignet-vals-sat-care-masks-mark-invar-rw))))

  (defthm aignet-vals-sat-care-masks-mark-invar-of-mark-greater-id
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (< (nfix id) (nfix id2)))
             (aignet-vals-sat-care-masks-mark-invar id (update-nth id2 1 mark) invals regvals aignet))
    :hints (("goal" :expand ((aignet-vals-sat-care-masks-mark-invar id (update-nth id2 1 mark) invals regvals aignet))
             :in-theory (enable aignet-vals-sat-care-masks-mark-ok
                                aignet-vals-sat-care-masks-mark-invar-rw))))

  (defret aignet-vals-sat-care-masks-preserves-marks-above-id
    (implies (< (nfix id) (nfix node))
             (equal (nth node new-mark)
                    (nth node mark)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-marks-id
    (equal (nth id new-mark) 1)
    :hints (("goal" :expand ((:free (vals) <call>)))))

  ;; (local (defretd aignet-vals-sat-care-masks-preserves-marks-above-id-split
  ;;          (implies (case-split (< (nfix id) (nfix node)))
  ;;                   (equal (nth node new-mark)
  ;;                          (if (equal (nth node mark) 1) 1 (nth node mark) )))
  ;;          :hints ((acl2::just-induct-and-expand <call>))))

  ;; (local (defretd aignet-vals-sat-care-masks-preserve-marks-split
  ;;          (implies (case-split (equal (nth n mark) 1))
  ;;                   (equal (nth n new-mark) 1))
  ;;          :hints ((acl2::just-induct-and-expand <call>))))

  (local (defthm id-eval-of-gate-fanins-when-false
           (implies (And (equal (id-eval id invals regvals aignet) 0)
                         (equal (stype (car (lookup-id id aignet))) (and-stype)))
                    (and (implies (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         1)
                                  (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         0))
                         (implies (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         1)
                                  (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         0))))
           :hints (("goal" :expand ((id-eval id invals regvals aignet))
                    :in-theory (enable eval-and-of-lits)))))

  (local (defthm id-eval-of-gate-fanins-when-true
           (implies (and (equal (id-eval id invals regvals aignet) 1)
                         (equal (stype (car (lookup-id id aignet))) (and-stype)))
                    (and (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                          invals regvals aignet)
                                1)
                         (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                          invals regvals aignet)
                                1)))
           :hints (("goal" :expand ((id-eval id invals regvals aignet))
                    :in-theory (enable eval-and-of-lits)))))

  (local (in-theory (disable aignet-vals-sat-care-masks-mark-ok
                             lookup-id-out-of-bounds)))

  (defthm aignet-vals-sat-care-masks-mark-ok-of-update-mark
    (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
                  (not (equal (nfix id) (nfix node))))
             (aignet-vals-sat-care-masks-mark-ok node (update-nth id 1 mark) invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))
  
  ;; (defthm aignet-vals-sat-care-masks-mark-ok-of-update-non-gate
  ;;   (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
  ;;                 (not (equal (stype (car (lookup-id id aignet))) :gate)))
  ;;            (aignet-vals-sat-care-masks-mark-ok node (update-nth id 1 mark) invals regvals aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))

  ;; (defthm aignet-vals-sat-care-masks-mark-ok-of-non-marked
  ;;   (implies (not (equal (nth node mark) 1))
  ;;            (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))

  ;; To prove this we need to show that the invariant still holds afterward of
  ;; an arbitrary witness node NODE.

  ;; - If node is <= than the ID of the recursive call(s), then it is fully
  ;; covered by the inductive invariant.
  ;; - If the node's mark was already set, then the original hyp implies
  ;; sufficient conditions about its fanins.
  ;; - Otherwise, node is ID and we ensure that its fanins are set correctly.

  ;; (defret aignet-vals-sat-care-masks-mark-invar-of-marked-node-preserved
  ;;   (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
  ;;                 (equal (nth node mark) 1))
  ;;            (aignet-vals-sat-care-masks-mark-ok node new-mark invals regvals aignet))
  ;;   :hints ((acl2::just-induct-and-expand <call>)
  ;;           (and stable-under-simplificationp
  ;;                '(:cases ((equal (nfix node) (nfix id)))
  ;;                  :in-theory (enable* acl2::arith-equiv-forwarding)))))

  ;; (local (defthm not-gate-by-ctype
  ;;          (implies (not (equal (ctype (stype x)) :gate))
  ;;                   (not (equal (stype x) :gate)))
  ;;          :hints(("Goal" :in-theory (enable ctype)))))

  (defret aignet-vals-sat-care-masks-mark-ok-preserved
    (implies (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
             (aignet-vals-sat-care-masks-mark-ok node new-mark invals regvals aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix node) (nfix id)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))
  
  (defret aignet-vals-sat-care-masks-mark-invar-preserved
    (implies (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
             (aignet-vals-sat-care-masks-mark-invar id new-mark invals regvals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(Car (last clause)))))))

  ;; When the invariant holds, marked nodes depend only on marked inputs
  (defun-sk aignet-marked-inputs-are-masked (mark inmasks aignet)
    (forall n
            (implies (and (< (nfix n) (num-ins aignet))
                          (equal 1 (nth (fanin-count (lookup-stype n :pi aignet)) mark)))
                     (equal (nth n inmasks) 1)))
    :rewrite :direct)
  
  (in-theory (disable aignet-marked-inputs-are-masked
                      aignet-marked-inputs-are-masked-necc))
  (local (in-theory (enable aignet-marked-inputs-are-masked-necc)))

  (defthm aignet-marked-inputs-are-masked-of-update-non-input
    (implies (and (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (not (equal (stype (car (lookup-id id aignet))) :pi)))
             (aignet-marked-inputs-are-masked (update-nth id 1 mark) inmasks aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-vals-sat-care-masks-preserves-marked-inputs-masked
    (implies (aignet-marked-inputs-are-masked mark inmasks aignet)
             (aignet-marked-inputs-are-masked new-mark new-inmasks aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                 'aignet-marked-inputs-are-masked-witness
                                 clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . n))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))))

  (defun-sk aignet-marked-regs-are-masked (mark regmasks aignet)
    (forall n
            (implies (and (< (nfix n) (num-regs aignet))
                          (equal 1 (nth (fanin-count (lookup-stype n :reg aignet)) mark)))
                     (equal (nth n regmasks) 1)))
    :rewrite :direct)
  
  (in-theory (disable aignet-marked-regs-are-masked
                      aignet-marked-regs-are-masked-necc))
  (local (in-theory (enable aignet-marked-regs-are-masked-necc)))

  (defthm aignet-marked-regs-are-masked-of-update-non-input
    (implies (and (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (stype (car (lookup-id id aignet))) :reg)))
             (aignet-marked-regs-are-masked (update-nth id 1 mark) regmasks aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-vals-sat-care-masks-preserves-marked-regs-masked
    (implies (aignet-marked-regs-are-masked mark regmasks aignet)
             (aignet-marked-regs-are-masked new-mark new-regmasks aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                 'aignet-marked-regs-are-masked-witness
                                 clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . n))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))))


  (defun-sk vals-equiv-under-masks (masks invals1 invals2)
    (forall n
            (implies (equal (nth n masks) 1)
                     (equal (nth n invals1) (nth n invals2))))
    :rewrite :direct)

  (in-theory (disable vals-equiv-under-masks))

  (defthmd aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
    (implies (and (aignet-vals-sat-care-masks-mark-invar max-id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (vals-equiv-under-masks inmasks invals invals1)
                  (vals-equiv-under-masks regmasks regvals regvals1)
                  (equal (nth id mark) 1)
                  (not (equal (id->type id aignet) (out-type)))
                  (<= (nfix id) (nfix max-id)))
             (equal (id-eval id invals regvals aignet)
                    (id-eval id invals1 regvals1 aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-vals-sat-care-masks-mark-invar-rw
                          (id max-id) (node id)))
                   :in-theory (e/d (ctype) (aignet-vals-sat-care-masks-mark-invar-rw))
                   :expand ((:free (invals regvals)
                             (id-eval id invals regvals aignet))
                            (:free (lit0 lit1 invals regvals ) (eval-and-of-lits lit0 lit1 invals regvals aignet))
                            (:free (lit0 lit1 invals regvals ) (eval-xor-of-lits lit0 lit1 invals regvals aignet))
                            (:free (lit invals regvals) (lit-eval lit invals regvals aignet)))))))

  (defretd aignet-vals-sat-care-masks-rec-counterexample-under-masks
    (implies (and (vals-equiv-under-masks new-inmasks invals invals1)
                  (vals-equiv-under-masks new-regmasks regvals regvals1)
                  (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (id->type id aignet) (out-type))))
             (equal (id-eval id invals1 regvals1 aignet)
                    (id-eval id invals regvals aignet)))
    :hints (("goal" :use ((:instance aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
                           (id id) (max-id id)
                           (inmasks new-inmasks)
                           (regmasks new-regmasks)
                           (mark new-mark))))))

  (defretd aignet-vals-sat-care-masks-rec-counterexample-under-masks-lit-eval
    (implies (and (vals-equiv-under-masks new-inmasks invals invals1)
                  (vals-equiv-under-masks new-regmasks regvals regvals1)
                  (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (id->type id aignet) (out-type)))
                  (equal (lit-id x) (nfix id)))
             (equal (lit-eval x invals1 regvals1 aignet)
                    (lit-eval x invals regvals aignet)))
    :hints (("goal" :use ((:instance aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
                           (id id) (max-id id)
                           (inmasks new-inmasks)
                           (regmasks new-regmasks)
                           (mark new-mark)))
             :expand ((:free (invals regvals)
                       (lit-eval x invals regvals aignet))))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)
             :expand-others ((:free (vals)
                              (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)))))))

       
                                                  


(define aignet-lit-ipasir-sat-check
  ((x litp  "Literal to check for satisfiability")
   (invals  "Bit array, overwritten with the input values of the satisfying assignment")
   (regvals "Bit array, overwritten with the register values of the satisfying assignment")
   (vals    "Bit array, overwritten with the values of the satisfying assignment for all aignet nodes")
   (aignet  "AIG network")
   (state   "ACL2 state, used to initialize the incremental solver and generate random numbers"))
  :guard (fanin-litp x aignet)
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status)))
                       "Status of the satisfiability check")
               (sat-invals (equal (len sat-invals) (num-ins aignet))
                           "If satisfiable, input values of the satisfying assignment")
               (sat-regvals (equal (len sat-regvals) (num-regs aignet))
                            "If satisfiable, register values of the satisfying assignment")
               (eval-vals
                (implies (equal status :sat)
                         (equal eval-vals (aignet-record-vals vals sat-invals sat-regvals aignet)))
                "If satisfiable, values for all aignet nodes of the satisfying assignment")
               (new-state "Updated ACL2 state"))
  :Guard-debug t
  :parents (aignet-ipasir)
  :short "Performs a single SAT check to determine whether the input AIGNET literal can have the value 1."
  :long "<p>This uses the ipasir incremental solver interface to perform a SAT
check on the given literal.  This isn't really the intended use of an
incremental solver, but it at least illustrates how to use it.</p>"
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((acl2::local-stobjs ipasir sat-lits)
        (mv ipasir sat-lits status invals regvals vals state))
       ((mv ipasir sat-lits state)
        (aignet-lit-ipasir-sat-check-aux x sat-lits ipasir aignet state))
       ((mv status ipasir) (ipasir::ipasir-solve ipasir))
       (invals (resize-bits (num-ins aignet) invals))
       (regvals (resize-bits (num-regs aignet) regvals))
       ((unless (eq status :sat))
        (b* ((ipasir (ipasir-release ipasir)))
          (mv ipasir sat-lits status invals regvals vals state)))
       (invals (aignet-get-ipasir-ctrex-invals 0 invals sat-lits aignet ipasir))
       (regvals (aignet-get-ipasir-ctrex-regvals 0 regvals sat-lits aignet ipasir))
       (ipasir (ipasir-release ipasir))
       (vals (aignet-record-vals vals invals regvals aignet))
       ((unless (eql (aignet-eval-lit x vals) 1))
        (raise "Supposed satisfying assignment didn't work!")
        (mv ipasir sat-lits :failed invals regvals vals state)))
    (mv ipasir sat-lits :sat invals regvals vals state))
  ///
  (defret satisfying-assign-of-aignet-lit-ipasir-sat-check
    (implies (and (equal status :sat)
                  (aignet-litp x aignet))
             (equal (lit-eval x sat-invals sat-regvals aignet) 1))
    :hints (("goal" :expand ((:free (invals regvals) (lit-eval x invals regvals aignet)))
             :in-theory (enable aignet-idp))))

  (defret aignet-lit-ipasir-sat-check-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (not (equal status :unsat))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))




(define aignet-lit-ipasir-sat-minimize
  ((x litp   "Literal to check for satisfiability")
   (invals   "Bit array, overwritten with the input values of the satisfying assignment")
   (regvals  "Bit array, overwritten with the register values of the satisfying assignment")
   (inmasks  "Bit array, overwritten with the input care set of the satisfying assignment")
   (regmasks "Bit array, overwritten with the register care set of the satisfying assignment")
   (aignet   "AIG network")
   (state    "ACL2 state, used to initialize the incremental solver and generate random numbers"))
  :guard (fanin-litp x aignet)
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status)))
                       "Status of the satisfiability check")
               (sat-invals (equal (len sat-invals) (num-ins aignet))
                           "If satisfiable, input values of the satisfying assignment")
               (sat-regvals (equal (len sat-regvals) (num-regs aignet))
                            "If satisfiable, register values of the satisfying assignment")
               (sat-inmasks (equal (len sat-inmasks) (num-ins aignet))
                            "If satisfiable, input care set of the satisfying assignment")
               (sat-regmasks (equal (len sat-regmasks) (num-regs aignet))
                             "If satisfiable, register care set of the satisfying assignment")
               (new-state "Updated ACL2 state"))
  :Guard-debug t
  :parents (aignet-ipasir)
  :short "Check satisfiability of a literal, and minimize the satisfying assignment if satisfiable."
  (b* (((acl2::local-stobjs vals mark)
        (mv vals mark status invals regvals inmasks regmasks state))
       ((mv status invals regvals vals state)
        (aignet-lit-ipasir-sat-check x invals regvals vals aignet state))
       (inmasks (resize-bits 0 inmasks))
       (inmasks (resize-bits (num-ins aignet) inmasks))
       (regmasks (resize-bits 0 regmasks))
       (regmasks (resize-bits (num-regs aignet) regmasks))
       ((unless (eql status :sat))
        (mv vals mark status invals regvals inmasks regmasks state))
       (mark (resize-bits (+ 1 (lit-id x)) mark))
       ((mv inmasks regmasks mark state)
        (aignet-vals-sat-care-masks-rec (lit-id x) inmasks regmasks invals regvals vals mark aignet state)))
    (mv vals mark :sat invals regvals inmasks regmasks state))
  ///
  (local (defthm aignet-vals-sat-care-masks-mark-invar-of-empty
           (aignet-vals-sat-care-masks-mark-invar id (resize-list nil n 0) invals regvals aignet)
           :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-invar
                                             aignet-vals-sat-care-masks-mark-ok)))))

  (local (defthm aignet-marked-inputs-are-masked-of-empty
           (aignet-marked-inputs-are-masked (resize-list nil n 0) invals aignet)
           :hints(("Goal" :in-theory (enable aignet-marked-inputs-are-masked)))))

  (local (defthm aignet-marked-regs-are-masked-of-empty
           (aignet-marked-regs-are-masked (resize-list nil n 0) regvals aignet)
           :hints(("Goal" :in-theory (enable aignet-marked-regs-are-masked)))))

  (defret satisfying-assign-of-aignet-lit-ipasir-sat-minimize
    (implies (and (equal status :sat)
                  (aignet-litp x aignet)
                  (vals-equiv-under-masks sat-inmasks sat-invals invals1)
                  (vals-equiv-under-masks sat-regmasks sat-regvals regvals1))
             (equal (lit-eval x invals1 regvals1 aignet) 1))
    :hints (("goal" 
             :in-theory (enable aignet-vals-sat-care-masks-rec-counterexample-under-masks-lit-eval))))

  (defret satisfying-assign-of-aignet-lit-ipasir-sat-minimize-basic
    (implies (and (equal status :sat)
                  (aignet-litp x aignet))
             (equal (lit-eval x sat-invals sat-regvals aignet) 1)))

  (defret aignet-lit-ipasir-sat-minimize-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (not (equal status :unsat))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))
