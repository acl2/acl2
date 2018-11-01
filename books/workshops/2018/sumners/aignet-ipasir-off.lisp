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
(include-book "ipasir-tools-off")
(include-book "centaur/aignet/ipasir" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

(defines aignet-lit->ipasir+off
  (define aignet-lit->ipasir+off ((x litp           "Literal to encode in the CNF")
                                  (off litp         "offset to add to clauses in CNF")
                                  (use-muxes        "Flag saying whether to recognize muxes and encode them specially")
                                  (aignet-refcounts "Reference counts of aignet nodes")
                                  (sat-lits         "Records assignment of SAT variables to aignet nodes")
                                  (aignet           "AIG network")
                                  (ipasir           "Incremental solver instance containing the accumulated formula"))
    :guard (and (< (lit-id x) (u32-length aignet-refcounts))
                (fanin-litp x aignet)
                (sat-lits-wfp sat-lits aignet)
                (not (eq (ipasir::ipasir-get-status ipasir) :undef))
                (ipasir::ipasir-empty-new-clause ipasir))
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
               (ipasir (ipasir::ipasir-add-unary+off ipasir (satlink::lit-negate sat-lit) off)))
            (mv sat-lits ipasir)))
         ;; now we have a gate node -- check first for a mux if we're doing that
         ;; if it's an xor, we say it's a mux regardless
         ((mv muxp c tb fb) (if (or use-muxes (eql 1 (id->regp id aignet)))
                                (id-is-mux id aignet)
                              (mv nil nil nil nil)))
         ((when muxp)
          ;; recur on the three children, add the node, add the mux clauses
          (b* (((mv sat-lits ipasir)
                (aignet-lit->ipasir+off c off use-muxes aignet-refcounts sat-lits aignet ipasir))
               ((mv sat-lits ipasir)
                (aignet-lit->ipasir+off tb off use-muxes aignet-refcounts sat-lits aignet ipasir))
               ((mv sat-lits ipasir)
                (aignet-lit->ipasir+off fb off use-muxes aignet-refcounts sat-lits aignet ipasir))
               (sat-lits (sat-add-aignet-lit (mk-lit id 0) sat-lits aignet))
               (new-clauses (mux-add-clauses id c tb fb sat-lits nil))
               (ipasir (ipasir::ipasir-add-clauses+off ipasir new-clauses off)))
            (mv sat-lits ipasir)))
         (lit (mk-lit id 0))
         ((mv supergate &)
          (lit-collect-supergate
           lit t use-muxes 1000 nil aignet-refcounts aignet))
         ((when (member 0 supergate))
          ;; one of the fanins is const 0, so the node is const 0
          (b* ((sat-lits (sat-add-aignet-lit lit sat-lits aignet))
               (sat-lit (aignet-id->sat-lit id sat-lits))
               (ipasir (ipasir::ipasir-add-unary+off ipasir (lit-negate sat-lit) off)))
            (mv sat-lits ipasir)))
         ;; recur on the children of the supergate, add the parent literal,
         ;; add the supergate clauses.
         ((mv sat-lits ipasir)
          (aignet-lit-list->ipasir+off supergate off use-muxes aignet-refcounts sat-lits aignet ipasir))
         (sat-lits (sat-add-aignet-lit lit sat-lits aignet))
         (new-clauses (supergate-add-clauses
                       lit supergate sat-lits nil))
         (ipasir (ipasir::ipasir-add-clauses+off ipasir new-clauses off)))
      (mv sat-lits ipasir)))

  (define aignet-lit-list->ipasir+off ((x lit-listp)
                                       (off litp)
                                       (use-muxes)
                                       (aignet-refcounts)
                                       (sat-lits)
                                       (aignet)
                                       (ipasir))
    :guard (and (< (lits-max-id-val x) (u32-length aignet-refcounts))
                (aignet-lit-listp x aignet)
                (sat-lits-wfp sat-lits aignet)
                (not (eq (ipasir::ipasir-get-status ipasir) :undef))
                (ipasir::ipasir-empty-new-clause ipasir))
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
            (aignet-lit->ipasir+off (car x) off use-muxes aignet-refcounts sat-lits aignet ipasir)))
        (aignet-lit-list->ipasir+off (cdr x) off use-muxes aignet-refcounts sat-lits aignet
                                     ipasir))))
  ///

  (local (in-theory (disable aignet-lit->ipasir+off
                             aignet-lit-list->ipasir+off)))

  (std::defret-mutual ipasir-status-of-aignet-lit->ipasir+off
    (defret ipasir-status-of-aignet-lit->ipasir+off
      (equal (ipasir::ipasir$a->status new-ipasir) :input)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir+off)
    (defret ipasir-status-of-aignet-lit-list->ipasir+off
      (equal (ipasir::ipasir$a->status new-ipasir) :input)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir+off))

  (std::defret-mutual ipasir-new-clause-of-aignet-lit->ipasir+off
    (defret ipasir-new-clause-of-aignet-lit->ipasir+off
      (equal (ipasir::ipasir$a->new-clause new-ipasir) nil)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir+off)
    (defret ipasir-new-clause-of-aignet-lit-list->ipasir+off
      (equal (ipasir::ipasir$a->new-clause new-ipasir) nil)
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir+off))

  (std::defret-mutual ipasir-assumption-of-aignet-lit->ipasir+off
    (defret ipasir-assumption-of-aignet-lit->ipasir+off
      (equal (ipasir::ipasir$a->assumption new-ipasir)
             (ipasir::ipasir$a->assumption ipasir))
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit->ipasir+off)
    (defret ipasir-assumption-of-aignet-lit-list->ipasir+off
      (equal (ipasir::ipasir$a->assumption new-ipasir)
             (ipasir::ipasir$a->assumption ipasir))
      :hints ('(:expand ((:free (use-muxes) <call>))))
      :fn aignet-lit-list->ipasir+off))

  (local (defthm lit-listp-implies-true-listp
           (implies (lit-listp x) (true-listp x))))

  (verify-guards aignet-lit->ipasir+off)
  )


