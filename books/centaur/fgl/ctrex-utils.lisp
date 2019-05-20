; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")
(include-book "interp-st")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable resize-list)))
(local (std::add-default-post-define-hook :fix))
(set-state-ok t)


(acl2::defstobj-clone bitarr acl2::bitarr :pkg fgl-pkg)

(stobjs::defnicestobj env$
  (alist :initially nil)
  (bitarr :type bitarr)
  (obj-alist :type (satisfies obj-alist-p) :fix obj-alist-fix))

(define env->env$ ((x gl-env-p) logicman)
  :guard (stobj-let ((aignet (logicman->aignet logicman)))
                    (ok)
                    (eql (aignet::num-regs aignet) 0)
                    ok)
  (b* ((bfrstate (logicman->bfrstate))
       ((gl-env x))
       ((acl2::local-stobjs env$)
        (mv env$ returned-env$))
       (env$ (update-env$->obj-alist x.obj-alist env$)))
    (bfrstate-case
      :bdd (stobj-let ((bitarr (env$->bitarr env$)))
                      (bitarr)
                      (non-exec (bools->bits x.bfr-vals))
                      (non-exec (mv env$ env$)))
      :aig (b* ((env$ (update-env$->alist x.bfr-vals env$)))
             (non-exec (mv env$ env$)))
      :aignet (stobj-let ((aignet (logicman->aignet logicman)))
                         (env$)
                         (stobj-let ((bitarr (env$->bitarr env$)))
                                    (bitarr)
                                    (b* (((acl2::local-stobjs aignet::invals aignet::regvals)
                                          (mv bitarr aignet::invals aignet::regvals))
                                         (aignet::invals (alist-to-bitarr (aignet::num-ins aignet) x.bfr-vals aignet::invals))
                                         (bitarr
                                          (aignet::aignet-record-vals bitarr aignet::invals aignet::regvals aignet)))
                                      (mv bitarr aignet::invals aignet::regvals))
                                    env$)
                         (non-exec (mv env$ env$))))))

(define bfr-env$-p (env$ logicman)
  (b* ((bfrstate (logicman->bfrstate)))
    (bfrstate-case
      :bdd (stobj-let ((bitarr (env$->bitarr env$)))
                      (ok)
                      (<= (bfrstate->bound bfrstate) (bits-length bitarr))
                      ok)
      :aig t
      :aignet (stobj-let ((bitarr (env$->bitarr env$)))
                         (ok)
                         (< (bfrstate->bound bfrstate) (bits-length bitarr))
                         ok))))
                   

(define eval-bdd-fast ((x acl2::ubddp) (level natp) bitarr)
  :guard (<= (+ level (max-depth x)) (bits-length bitarr))
  :guard-hints (("goal" :expand ((max-depth x) (acl2::ubddp x))))
  (if (atom x)
      (mbe :logic (bool-fix x) :exec x)
    (eval-bdd-fast (if (eql 1 (get-bit level bitarr)) (car x) (cdr x))
                   (1+ (lnfix level)) bitarr))
  ///
  (local (defthm nth-is-car-nthcdr
           (equal (nth n x)
                  (car (nthcdr n x)))
           :hints(("Goal" :in-theory (enable nth nthcdr)))))
  (local (defthm nthcdr-of-nil
           (equal (nthcdr n nil) nil)))
  (local (defthm consp-nthcdr
           (equal (consp (nthcdr n x))
                  (< (nfix n) (len x)))
           :hints(("Goal" :in-theory (enable nthcdr)))))
  (local (defthm bits->bools-when-not-consp
           (implies (not (consp x))
                    (equal (bits->bools x) nil))
           :hints(("Goal" :in-theory (enable bits->bools)))))
  (local (defthm cdr-of-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr n (cdr x)))))
  (defthm eval-bdd-fast-elim
    (equal (eval-bdd-fast x level bitarr)
           (acl2::eval-bdd x (bits->bools (nthcdr level bitarr))))
    :hints(("Goal" :expand ((bits->bools (nthcdr level bitarr))
                            (:free (env) (acl2::eval-bdd x env)))
            :induct (eval-bdd-fast x level bitarr)))))


(define bfr-eval-fast ((x lbfr-p) env$ &optional (logicman 'logicman))
  :guard (bfr-env$-p env$ logicman)
  :guard-hints (("goal" :in-theory (enable bfr-env$-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable bfr-p bfr-fix ubddp))))
  (b* ((bfrstate (logicman->bfrstate)))
    (bfrstate-case
      :bdd (stobj-let ((bitarr (env$->bitarr env$)))
                      (val)
                      (eval-bdd-fast (bfr-fix x) 0 bitarr)
                      val)
      :aig (acl2::aig-eval (bfr-fix x) (env$->alist env$))
      :aignet (b* ((lit (bfr->aignet-lit x)))
                (stobj-let ((bitarr (env$->bitarr env$)))
                           (val)
                           (eql 1 (aignet::aignet-eval-lit lit bitarr))
                           val))))
  ///
  (local (defthm eval-bdd-of-bits->bools-bools->bits
           (equal (acl2::eval-bdd x (bits->bools (bools->bits env)))
                  (acl2::eval-bdd x env))
           :hints(("Goal" :in-theory (enable acl2::eval-bdd bits->bools bools->bits)))))


  (defthm bfr-eval-fast-of-env->env$
    (equal (bfr-eval-fast x (env->env$ env logicman) logicman)
           (gobj-bfr-eval x env logicman))
    :hints(("Goal" :in-theory (enable gobj-bfr-eval bfr-eval env->env$ bfr-eval-fast aignet::lit-eval)
            :do-not-induct t))
    :otf-flg t))

(define bfr-list-eval-fast ((x lbfr-listp) env$ &optional (logicman 'logicman))
  :guard (bfr-env$-p env$ logicman)
  :returns (vals boolean-listp)
  (if (atom x)
      nil
    (cons (bfr-eval-fast (car x) env$)
          (bfr-list-eval-fast (cdr x) env$))))





;; NOTE: This preserves any values in bitarr that are not set in the ipasir's
;; solution.  So if we wanted to add some randomization and the ipasir solver
;; that we used ever produced a partial satisfying assignment, we could seed
;; the bitarr with random values first.
(define ipasir-assignment->cnf-vals ((n natp) ipasir bitarr)
  :guard (and (<= n (bits-length bitarr))
              (equal (ipasir-get-status ipasir) :sat))
  :guard-debug t
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  :returns (new-bitarr)
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
                   :exec (eql n (bits-length bitarr))))
        bitarr)
       (val (ipasir-val ipasir (satlink::make-lit n 0)))
       (bitarr (if val
                   (set-bit n val bitarr)
                 bitarr)))
    (ipasir-assignment->cnf-vals (1+ (lnfix n)) ipasir bitarr))
  ///
  (defret len-of-<fn>
    (equal (len new-bitarr) (len bitarr))))
    

#!aignet  
(defsection cnf->aignet-vals
  ;; BOZO this is probably a good logical definition for this but it might be
  ;; nice to have an exec that iterates over the sat-lits/cnf-vals instead of
  ;; having to skip all the IDs with no sat-vars in vals
  (defiteration cnf->aignet-vals (vals cnf-vals sat-lits aignet)
    (declare (xargs :stobjs (vals cnf-vals sat-lits aignet)
                    :guard (and (sat-lits-wfp sat-lits aignet)
                                (<= (num-fanins aignet) (bits-length vals)))))
    (b* ((id n)
         ((unless (aignet-id-has-sat-var id sat-lits))
          vals)
         (lit (aignet-id->sat-lit id sat-lits))
         (val (satlink::eval-lit lit cnf-vals)))
      (set-bit n val vals))
    :returns vals
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
  

(define logicman-ipasir->env$ (logicman env$)
  :guard (and (lbfr-mode-is :aignet)
              (logicman-invar logicman)
              (stobj-let ((ipasir (logicman->ipasir logicman)))
                         (ok)
                         (equal (ipasir::ipasir-get-status ipasir) :sat)
                         ok))
  :returns (new-env$)
  (stobj-let ((ipasir (logicman->ipasir logicman))
              (aignet (logicman->aignet logicman))
              (sat-lits (logicman->sat-lits logicman)))
             (env$)
             (stobj-let ((bitarr (env$->bitarr env$)))
                        (bitarr)
                        (b* (((acl2::local-stobjs aignet::cnf-vals)
                              (mv bitarr aignet::cnf-vals))
                             (aignet::cnf-vals (resize-bits (aignet::sat-next-var sat-lits) aignet::cnf-vals))
                             (aignet::cnf-vals (ipasir-assignment->cnf-vals 0 ipasir aignet::cnf-vals))
                             (bitarr (resize-bits (aignet::num-fanins aignet) bitarr))
                             (bitarr (aignet::cnf->aignet-vals bitarr aignet::cnf-vals sat-lits aignet))
                             (bitarr (aignet::aignet-eval bitarr aignet)))
                          (mv bitarr aignet::cnf-vals))
                        env$)
             env$)
  ///
  (defret bfr-env$-p-of-<fn>
    (implies (lbfr-mode-is :aignet)
             (bfr-env$-p new-env$ logicman))
    :hints(("Goal" :in-theory (enable bfr-env$-p)))))











;; FGL counterexample translation.

;;   When we do a SAT check we get back results in terms of Boolean variables.
;;   We want to derive from this an assignment to the term-level variables.  We
;;   start with the correspondences between Boolean variables and terms stored
;;   in the bvar-db.  Typically each variable occurs in several entries.  To
;;   recover assignments for variables we use an algorithm that computes a
;;   candidate value for each subterm of each term in the bvar-db.  When we are
;;   done, we have values for all variables used in the bvar-db; any other
;;   variables we assign NIL.

;;   The simple version of the algorithm:

;;   Start with the Boolean-level counterexample.  This gives us an assignment
;;   of Boolean values to each of the terms assigned a correspondence in the
;;   bvar-db.  Then run this to a fixpoint: for each immediate subterm of a
;;   term that currently has an assignment, try to recover a value by applying
;;   counterexample translation rules, discussed below.

;;   The "smarter" version: we create a "cgraph" with an edge A->B whenever
;;   obtaining a value for A might help derive a value for B (via one of the
;;   counterexample translation rules). Edges are labeled with the rule and
;;   substitution that gives rise to that derivation.  Often B is an immediate
;;   subterm of A, but this isn't always the case.  To get a variable-level
;;   counterexample, we then traverse the cgraph in topological order trying to
;;   find a value for each term encountered.  Or, if we want a value for some
;;   particular set of terms, restrict the cgraph to just those terms and their
;;   ancestors and similarly traverse that.  If there are any SCCs containing
;;   multiple terms in the graph, then we try to recover a value for each term
;;   in arbitrary order and check whether we get to a fixpoint.  Implementation
;;   note: the graph we'll actually create is the reverse cgraph, where we can
;;   look up a term B to obtain all in-edges of B, since this will make it
;;   easier to traverse in the way we need to.

;;   Rule types.

;;   We consider a few different types of rules for computing variable values
;;   from bit-level counterexamples.  Note that none of these require proof;
;;   all of this is a purely heuristic process.
;;  
;;  - Elimination rules.  These are basically destructor elimination rules, of the form
;;      (implies (pred x) (equiv (ctor (acc1 x) ... (accn x)) x))
;;    These produce edges (acci x) -> x as well as (pred x) -> x in the cgraph.
;;    Note we expect to sometimes see an incomplete set of such edges
;;    (e.g. (acc1 x) exists but (acc2 x) doesn't, accessors exist but pred
;;    doesn't) and we'll need to choose a default value for the missing terms.
;;    Hypotheses in these rules will be ignored unless two or more rules seem
;;    to apply to x (that is, there are two in-edges of x that are labeled with
;;    different rules).  In that case, if the hyp (under the substitution) is a
;;    term in the cgraph and it has an assigned value, then it is used to
;;    choose which rule will be used.  E.g. suppose we have two elimination
;;    rules
;;      (implies (integerp x) (equal (intcons (intcar x) (intcdr x)) x))
;;      (implies (consp x) (equal (cons (car x) (cdr x)) x))
;;    both of which label in-edges of (foo y), and we also have
;;    (integerp (foo y)) assigned to T, then we will use the integerp elim rule,
;;    whereas if (integerp (foo y)) is assigned NIL then we'll use the consp rule.

;;  - Property rules.  These are somewhat similar to elimination rules but allow
;;    for constructs like maps, alists, etc.  For example:
;;      (equal (s key (g key x) x) x)
;;    Such a rule produces edges (g key x) -> x for every occurrence of (g key
;;    x) in the cgraph.  Note it might sometimes make sense to add non-theorems
;;    like:  (equal (cons (cons key (cdr (assoc key x))) x) x)

;;  - Equivalence rules (implicit): anytime we see an equivalence (equiv a b)
;;    we'll add two edges a->b and b->a.  Whichever of a or b we're able to
;;    resolve first will determine the value of the other, provided the
;;    equivalence is assigned T.

(defenum ctrex-ruletype-p (:elim :property nil))

(defprod ctrex-rule
  ((name symbolp :rule-classes :type-prescription)
   (match pseudo-term-subst-p)
   (assign pseudo-termp)
   (assigned-var pseudo-var-p :rule-classes :type-prescription)
   (hyp pseudo-termp)
   (equiv pseudo-fnsym-p)
   (ruletype ctrex-ruletype-p))
  :layout :tree)



(fty::deflist ctrex-rulelist :elt-type ctrex-rule :true-listp t)

(fty::defmap ctrex-ruletable :key-type pseudo-fnsym :val-type ctrex-rulelist :true-listp t)

(define ctrex-rule-matches-to-ruletable ((matches pseudo-term-subst-p)
                                         (rule ctrex-rule-p)
                                         (ruletable ctrex-ruletable-p))
  :prepwork ((local (defthm true-listp-when-ctrex-rulelist-p-rw
                      (implies (ctrex-rulelist-p x)
                               (true-listp x)))))
  :returns (new-ruletable ctrex-ruletable-p)
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-term-subst-fix)))))
  (b* ((ruletable (ctrex-ruletable-fix ruletable))
       ((when (atom matches)) ruletable)
       ((unless (mbt (and (consp (car matches))
                          (pseudo-var-p (caar matches)))))
        (ctrex-rule-matches-to-ruletable (cdr matches) rule ruletable))
       (x (cdar matches))
       ((unless (pseudo-term-case x :fncall))
        (ctrex-rule-matches-to-ruletable (cdr matches) rule ruletable))
       ((pseudo-term-fncall x))
       (ruletable (hons-acons x.fn (add-to-set-equal (ctrex-rule-fix rule)
                                                     (cdr (hons-get x.fn ruletable)))
                              ruletable)))
    (ctrex-rule-matches-to-ruletable (cdr matches) rule ruletable)))




(defconst *def-ctrex-rule-keys*
  '(:match
    :assigned-var
    :assign
    :hyp
    :equiv
    :ruletype))

(make-event
 (std::da-make-binder-gen
  'ctrex-rule-keys
  (stobjs::kwd-alist-field-accessor-alist *def-ctrex-rule-keys*)))

(defun ctrex-rule-translate (x wrld)
  (declare (xargs :mode :program))
  (acl2::translate-cmp x t t t 'def-ctrex-rule wrld (default-state-vars nil)))

(defun ctrex-rule-translate-matches (x wrld)
  (declare (xargs :mode :program))
  (b* (((When (atom x)) (mv nil nil))
       ((unless (eql (len (car x)) 2))
        (mv 'def-ctrex-rule (msg "bad entry in match: ~x0" x)))
       (term (cadar x))
       ((mv erp trans-term)
        (ctrex-rule-translate term wrld))
       ((when erp) (mv erp trans-term))
       ((mv erp rest)
        (ctrex-rule-translate-matches (cdr x) wrld))
       ((when erp) (mv erp rest)))
    (mv nil (cons (cons (caar x) trans-term) rest))))

(defun def-ctrex-rule-fn (name keys wrld)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard? 'def-ctrex-rule "Bad name -- must be a symbol"))
       ((mv keys rest)
        (std::extract-keywords 'def-ctrex-rule
                               *def-ctrex-rule-keys*
                               keys nil))
       ((when rest)
        (er hard? 'def-ctrex-rule "Bad args: ~x0~%" rest))
       (keys (if (assoc :ruletype keys)
                 keys
               (cons (cons :ruletype :property) keys)))
       ((ctrex-rule-keys keys))
       ((mv erp match) (ctrex-rule-translate-matches keys.match wrld))
       ((when erp) (er hard? erp "~@0" match))
       ((mv erp assign) (ctrex-rule-translate keys.assign wrld))
       ((when erp) (er hard? erp "~@0" assign))
       ((mv erp hyp) (ctrex-rule-translate keys.hyp wrld))
       ((when erp) (er hard? erp "~@0" hyp))
       ((unless (pseudo-var-p keys.assigned-var))
        (er hard? 'def-ctrex-rule "Bad ASSIGNED-VAR: must be a variable"))
       ((unless (ctrex-ruletype-p keys.ruletype))
        (er hard? 'def-ctrex-rule "Bad ruletype: must satisfy ~x0" 'ctrex-ruletype-p))
       ((unless (pseudo-fnsym-p keys.equiv))
        (er hard? 'def-ctrex-rule "Bad equiv: must be a function symbol"))
       (rule (make-ctrex-rule :name name
                              :match match
                              :assign assign
                              :assigned-var keys.assigned-var
                              :hyp hyp
                              :equiv keys.equiv
                              :ruletype keys.ruletype)))
    `(table fgl-ctrex-rules nil (ctrex-rule-matches-to-ruletable
                                 ',match ',rule
                                 (make-fast-alist
                                  (table-alist 'fgl-ctrex-rules world)))
            :clear)))

(defmacro def-ctrex-rule (name &rest args)
  `(make-event
    (def-ctrex-rule-fn ',name ',args (w state))))


(def-ctrex-rule intcar-intcdr-ctrex-elim
  :match ((car (intcar x))
          (cdr (intcdr x)))
  :assign (intcons car cdr)
  :assigned-var x
  :hyp (integerp x)
  :ruletype :elim)

(def-ctrex-rule car-cdr-ctrex-elim
  :match ((car (car x))
          (cdr (cdr x)))
  :assign (cons car cdr)
  :assigned-var x
  :hyp (consp x)
  :ruletype :elim)

(def-ctrex-rule assoc-equal-ctrex-rule
  :match ((pair (assoc-equal k x)))
  :assign (put-assoc-equal k (cdr pair) x)
  :assigned-var x
  :hyp (alistp x)
  :ruletype :property)

(defun redundant-hons-acons (key val x)
  (if (hons-equal val (cdr (hons-get key x)))
      x
    (hons-acons key val x)))

(def-ctrex-rule hons-get-ctrex-rule
  :match ((val (cdr (hons-get k x))))
  :assign (redundant-hons-acons k val x)
  :assigned-var x
  :ruletype :property)



(defprod cgraph-edge
  ((match-vars pseudo-var-list-p :rule-classes :type-prescription)
   (rule ctrex-rule-p)
   (subst gl-object-bindings))
  :layout :tree)

(fty::deflist cgraph-edgelist :elt-type cgraph-edge :true-listp t)



(fty::defmap cgraph :key-type gl-object :val-type cgraph-edgelist :true-listp t)


(define cgraph-edge-bfrlist ((x cgraph-edge-p))
  :enabled t
  (gl-object-bindings-bfrlist (cgraph-edge->subst x)))

(define cgraph-edgelist-bfrlist ((x cgraph-edgelist-p))
  (if (atom x)
      nil
    (append (cgraph-edge-bfrlist (car x))
            (cgraph-edgelist-bfrlist (cdr x)))))

(define cgraph-bfrlist ((x cgraph-p))
  (if (atom x)
      nil
    (append (and (mbt (And (consp (car x))
                           (gl-object-p (caar x))))
                 (cgraph-edgelist-bfrlist (cdar x)))
            (cgraph-bfrlist (cdr x))))
  ///
  (defthm lookup-in-cgraph-bfrlist
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (gl-object-p k))
             (not (member v (cgraph-edgelist-bfrlist (cdr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm cgraph-bfrlist-of-fast-alist-fork
    (implies (and (not (member v (cgraph-bfrlist x)))
                  (not (member v (cgraph-bfrlist y))))
             (not (member v (cgraph-bfrlist (fast-alist-fork x y))))))

  (local (defthm cgraph-fix-of-bad-car
           (implies (not (And (consp (car x))
                              (gl-object-p (caar x))))
                    (equal (cgraph-fix x)
                           (cgraph-fix (cdr x))))
           :hints(("Goal" :in-theory (enable cgraph-fix))))))


(defconst *fake-ctrex-rule-for-equivs*
  (make-ctrex-rule :name 'fake-ctrex-rule-for-equivs
                   :match '((y . y))
                   :assign 'y
                   :assigned-var 'x
                   :hyp 't
                   :ruletype nil))

(include-book "glcp-unify-thms")

(defthm glcp-unify-create-produces-concrete-objs
  (b* (((mv ?flag new-alist) (glcp-unify-concrete pat x alist)))
    (implies (and flag (not (hons-assoc-equal k alist)))
             (equal (gl-object-kind (cdr (hons-assoc-equal k new-alist)))
                    :g-concrete)))
  :hints(("Goal" :in-theory (e/d ((:i glcp-unify-concrete))
                                 (logcar logcdr))
          :induct (glcp-unify-concrete pat x alist))
         (acl2::use-termhint
          `(:expand ((glcp-unify-concrete ,(acl2::hq pat)
                                          ,(acl2::hq x)
                                          ,(acl2::hq alist)))))))

(encapsulate nil
  (flag::make-flag glcp-unify-term/gobj-flg glcp-unify-term/gobj :local t)

  (local (defthm gl-object-count-of-mk-g-boolean
           (equal (gl-object-count (mk-g-boolean x)) 1)
           :hints(("Goal" :in-theory (enable mk-g-boolean gl-object-count)))))

  (local (defthm gl-object-count-of-mk-g-integer
           (equal (gl-object-count (mk-g-integer x)) 1)
           :hints(("Goal" :in-theory (enable mk-g-integer gl-object-count)))))

  (local (defthm gl-object-count-when-g-concrete
           (implies (gl-object-case x :g-concrete)
                    (equal (gl-object-count x) 1))
           :hints(("Goal" :in-theory (enable gl-object-count)))))

  (local (in-theory (disable len acl2::member-of-cons member-equal)))

  (defthm-glcp-unify-term/gobj-flg
    (defthm gl-object-count-of-glcp-unify-term/gobj
      (b* (((mv flag new-alist)
            (glcp-unify-term/gobj pat x alist)))
        (implies (and flag
                      (not (hons-assoc-equal k alist))
                      (hons-assoc-equal k new-alist))
                 (<= (gl-object-count (cdr (hons-assoc-equal k new-alist)))
                     (gl-object-count x))))
      :hints ((acl2::use-termhint
               `(:expand ((glcp-unify-term/gobj ,(acl2::hq pat)
                                                ,(acl2::hq x)
                                                ,(acl2::hq alist))))))
      :flag glcp-unify-term/gobj
      :rule-classes :linear)
    (defthm gl-object-count-of-glcp-unify-term/gobj-list
      (b* (((mv flag new-alist)
            (glcp-unify-term/gobj-list pat x alist)))
        (implies (and flag
                      (not (hons-assoc-equal k alist))
                      (hons-assoc-equal k new-alist))
                 (< (gl-object-count (cdr (hons-assoc-equal k new-alist)))
                    (gl-objectlist-count x))))
      :hints ((acl2::use-termhint
               `(:expand ((glcp-unify-term/gobj-list ,(acl2::hq pat)
                                                     ,(acl2::hq x)
                                                     ,(acl2::hq alist))))))
      :flag glcp-unify-term/gobj-list
      :rule-classes :linear))

  (defthmd gl-object-count-of-glcp-unify-term/gobj-casesplit
    (b* (((mv flag new-alist)
          (glcp-unify-term/gobj pat x alist)))
      (implies (and flag
                    (case-split (not (hons-assoc-equal k alist)))
                    (hons-assoc-equal k new-alist))
               (<= (gl-object-count (cdr (hons-assoc-equal k new-alist)))
                   (gl-object-count x))))
    :rule-classes :linear)

  (local (in-theory (enable gl-object-count-of-glcp-unify-term/gobj-casesplit)))

  (defthm gl-object-count-of-glcp-unify-term/gobj-strict
    (b* (((mv flag new-alist)
          (glcp-unify-term/gobj pat x alist)))
      (implies (and flag (not (hons-assoc-equal k alist))
                    (hons-assoc-equal k new-alist)
                    (not (pseudo-term-case pat :var))
                    (not (gl-object-case x '(:g-concrete :g-boolean :g-integer))))
               (< (gl-object-count (cdr (hons-assoc-equal k new-alist)))
                  (gl-object-count x))))
    :hints (("goal" :expand ((glcp-unify-term/gobj pat x alist)
                             (gl-object-count x))))
    :rule-classes :linear))


(define my-alists-compatible ((rest-x alistp)
                       (full-x alistp)
                       (y alistp))
  (if (atom rest-x)
      t
    (and (or (not (mbt (consp (car rest-x))))
             (let* ((key (caar rest-x))
                    (x-look (hons-assoc-equal key full-x))
                    (y-look (hons-assoc-equal key y)))
               (or (not y-look) (not x-look)
                   (equal x-look y-look))))
         (my-alists-compatible (cdr rest-x) full-x y)))
  ///
  (defthm my-alists-compatible-is-alists-compatible-on-keys
    (equal (my-alists-compatible rest-x full-x y)
           (acl2::alists-compatible-on-keys (alist-keys rest-x) full-x y))
    :hints(("Goal" :in-theory (enable acl2::alists-compatible-on-keys alist-keys))))

  (defthm my-alists-compatible-is-alists-compatible
    (equal (my-alists-compatible x x y)
           (acl2::alists-compatible x y))
    :hints(("Goal" :in-theory (enable acl2::alists-compatible)))))

(define my-join-alists ((x alistp) (y alistp))
  (if (atom x)
      y
    (if (mbt (consp (car x)))
        (if (hons-assoc-equal (caar x) y)
            (my-join-alists (cdr x) y)
          (my-join-alists (cdr x) (cons (car x) y)))
      (my-join-alists (cdr x) y)))
  ///
  (defthm my-join-alists-is-fast-alist-fork
    (equal (my-join-alists x y)
           (fast-alist-fork x y))))


(define add-cgraph-edge-join1 ((x cgraph-edge-p)
                               (y cgraph-edge-p))
  :returns (mv ok (new-edge (implies ok (cgraph-edge-p new-edge))))
  :prepwork ((defthm symbol-listp-when-pseudo-var-list-p
               (implies (pseudo-var-list-p x)
                        (symbol-listp x)))
             (defthm pseudo-var-list-p-of-union
               (implies (and (pseudo-var-list-p x)
                             (pseudo-var-list-p y))
                        (pseudo-var-list-p (union$ x y)))))
  (b* (((cgraph-edge x))
       ((cgraph-edge y))
       ((unless (and (equal x.rule y.rule)
                     (my-alists-compatible x.subst x.subst y.subst)))
        (mv nil nil)))
    (mv t
        (change-cgraph-edge x :match-vars (acl2::union-eq x.match-vars y.match-vars)
                            :subst (my-join-alists x.subst y.subst))))

  ///
  (local (defthm gl-object-bindings-bfrlist-of-fast-alist-fork
           (implies (and (not (member v (gl-object-bindings-bfrlist x)))
                         (not (member v (gl-object-bindings-bfrlist y))))
                    (not (member v (gl-object-bindings-bfrlist (fast-alist-fork x y)))))
           :hints(("Goal" :in-theory (enable gl-object-bindings-bfrlist fast-alist-fork)))))

  (defret cgraph-edge-bfrlist-of-<fn>
    (implies (and (not (member v (cgraph-edge-bfrlist x)))
                  (not (member v (cgraph-edge-bfrlist y))))
             (not (member v (cgraph-edge-bfrlist new-edge))))))
  
(define add-cgraph-edge-join ((edge cgraph-edge-p)
                              (edges cgraph-edgelist-p))
  :returns (mv foundp
               (new-edges cgraph-edgelist-p))
  (b* (((when (atom edges)) (mv nil nil))
       ((mv ok new-edge) (add-cgraph-edge-join1 edge (car edges)))
       ((when ok)
        (mv t (cons new-edge (cgraph-edgelist-fix (cdr edges)))))
       ((mv found rest) (add-cgraph-edge-join edge (cdr edges)))
       ((when found) (mv t (cons (cgraph-edge-fix (car edges)) rest))))
    (mv nil nil))
  ///
  (defret cgraph-edgelist-bfrlist-of-<fn>
    (implies (and (not (member v (cgraph-edge-bfrlist edge)))
                  (not (member v (cgraph-edgelist-bfrlist edges))))
             (not (member v (cgraph-edgelist-bfrlist new-edges))))
    :hints(("Goal" :in-theory (e/d (cgraph-edgelist-bfrlist)
                                   (cgraph-edge-bfrlist))))))
                     
  
                  

(define add-cgraph-edge ((matchvar pseudo-var-p)
                         (subst gl-object-bindings-p)
                         (rule ctrex-rule-p)
                         (cgraph cgraph-p))
  :returns (new-cgraph cgraph-p)
  (b* (((ctrex-rule rule))
       (to (cdr (hons-assoc-equal rule.assigned-var (gl-object-bindings-fix subst))))
       (edge (make-cgraph-edge :match-vars (list matchvar) :rule rule :subst subst))
       (cgraph (cgraph-fix cgraph))
       (edges (cdr (hons-get to cgraph)))
       ((mv found new-edges) (add-cgraph-edge-join edge edges))
       (new-edges (if found new-edges (cons edge edges))))
    (hons-acons to new-edges cgraph))
  ///
  (defret cgraph-edgelist-bfrlist-of-<fn>
    (implies (and (not (member v (gl-object-bindings-bfrlist subst)))
                  (not (member v (cgraph-bfrlist cgraph))))
             (not (member v (cgraph-bfrlist new-cgraph))))
    :hints(("Goal" :in-theory (e/d (cgraph-bfrlist
                                    cgraph-edgelist-bfrlist))))))
       
(local (defthm equal-const-of-plus-const
         (implies (and (syntaxp (and (quotep a) (quotep c)))
                       (acl2-numberp a) (acl2-numberp c))
                  (equal (equal (+ a b) c)
                         (equal (fix b) (- c a))))))











(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (defthm len-of-cons
         (equal (len (cons a b))
                (+ 1 (len b)))))

(local (defun len-is (x n)
         (if (zp n)
             (and (eql n 0) (atom x))
           (and (consp x)
                (len-is (cdr x) (1- n))))))

(local (defthm open-len-is
         (implies (syntaxp (quotep n))
                  (equal (len-is x n)
                         (if (zp n)
                             (and (eql n 0) (atom x))
                           (and (consp x)
                                (len-is (cdr x) (1- n))))))))
                         

(local (defthm equal-len-hyp
         (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
                                    (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
                                (quotep n)))
                  (equal (equal (len x) n)
                         (len-is x n)))))                  

(defines gl-object-add-to-cgraph
  (define gl-object-add-to-cgraph ((x gl-object-p)
                                   (cgraph cgraph-p)
                                   (ruletable ctrex-ruletable-p)
                                   (wrld plist-worldp))
    :well-founded-relation acl2::nat-list-<
    :measure (list (gl-object-count x) 10 0 0)
    :returns (new-cgraph cgraph-p)
    :verify-guards nil
    (b* ((fnsym (gl-object-case x
                  (:g-ite 'if)
                  (:g-cons 'cons)
                  (:g-apply x.fn)
                  (otherwise nil)))
         ((unless fnsym)
          (cgraph-fix cgraph))
         ((when (and (gl-object-case x :g-apply)
                     (fgetprop fnsym 'acl2::coarsenings nil wrld)))
          ;; Equivalence relation.  Add edges between two args
          (b* (((g-apply x))
               ((unless (eql (len x.args) 2))
                (cgraph-fix cgraph))
               ((list arg1 arg2) x.args)
               (rule (change-ctrex-rule *fake-ctrex-rule-for-equivs* :equiv x.fn))
               (cgraph (add-cgraph-edge 'y `((x . ,arg2) (y . ,arg1)) rule cgraph))
               (cgraph (add-cgraph-edge 'y `((x . ,arg1) (y . ,arg2)) rule cgraph))
               (cgraph (gl-object-add-to-cgraph arg1 cgraph ruletable wrld)))
            (gl-object-add-to-cgraph arg2 cgraph ruletable wrld)))
         (rules (cdr (hons-get fnsym (ctrex-ruletable-fix ruletable)))))
      (gl-object-add-to-cgraph-rules x rules cgraph ruletable wrld)))

  (define gl-object-add-to-cgraph-rules ((x gl-object-p)
                                         (rules ctrex-rulelist-p)
                                         (cgraph cgraph-p)
                                         (ruletable ctrex-ruletable-p)
                                         (wrld plist-worldp))
    :guard (not (gl-object-case x '(:g-concrete :g-boolean :g-integer)))
    :measure (list (gl-object-count x) 7 (len rules) 0)
    :returns (new-cgraph cgraph-p)
    (b* (((when (atom rules)) (cgraph-fix cgraph))
         (cgraph (gl-object-add-to-cgraph-rule x (car rules) cgraph ruletable wrld)))
      (gl-object-add-to-cgraph-rules x (cdr rules) cgraph ruletable wrld)))

  (define gl-object-add-to-cgraph-rule ((x gl-object-p)
                                        (rule ctrex-rule-p)
                                        (cgraph cgraph-p)
                                        (ruletable ctrex-ruletable-p)
                                        (wrld plist-worldp))
    :guard (not (gl-object-case x '(:g-concrete :g-boolean :g-integer)))
    :measure (list (gl-object-count x) 7 0 0)
    :returns (new-cgraph cgraph-p)
    (b* (((ctrex-rule rule)))
      (gl-object-add-to-cgraph-matches x rule.match rule cgraph ruletable wrld)))

  (define gl-object-add-to-cgraph-matches ((x gl-object-p)
                                           (matches pseudo-term-subst-p)
                                           (rule ctrex-rule-p)
                                           (cgraph cgraph-p)
                                           (ruletable ctrex-ruletable-p)
                                           (wrld plist-worldp))
    :guard (not (gl-object-case x '(:g-concrete :g-boolean :g-integer)))
    :measure (list (gl-object-count x) 5 (len matches) 0)
    :returns (new-cgraph cgraph-p)
    (b* (((when (atom matches)) (cgraph-fix cgraph))
         ((unless (mbt (and (consp (car matches))
                            (pseudo-var-p (caar matches)))))
          (gl-object-add-to-cgraph-matches x (cdr matches) rule cgraph ruletable wrld))
         (cgraph (gl-object-add-to-cgraph-match x (caar matches) (cdar matches) rule cgraph ruletable wrld)))
      (gl-object-add-to-cgraph-matches x (cdr matches) rule cgraph ruletable wrld)))

  (define gl-object-add-to-cgraph-match ((x gl-object-p)
                                         (matchvar pseudo-var-p)
                                         (match pseudo-termp)
                                         (rule ctrex-rule-p)
                                         (cgraph cgraph-p)
                                         (ruletable ctrex-ruletable-p)
                                         (wrld plist-worldp))
    :guard (not (gl-object-case x '(:g-concrete :g-boolean :g-integer)))
    :measure (list (gl-object-count x) 5 0 0)
    :returns (new-cgraph cgraph-p)
    (b* (((when (pseudo-term-case match :var))
          (cw "Bad ctrex rule? Match is a variable: ~x0" (ctrex-rule->name rule))
          (cgraph-fix cgraph))
         ((unless (mbt (not (gl-object-case x '(:g-concrete :g-boolean :g-integer)))))
          (cgraph-fix cgraph))
         ((mv ok subst) (glcp-unify-term/gobj match x nil))
         ((unless ok) (cgraph-fix cgraph))
         ((ctrex-rule rule))
         (to-look (hons-assoc-equal rule.assigned-var subst))
         ((unless to-look)
          (cw "Bad ctrex rule? ASSIGNED-VAR wasn't bound by match: ~x0" rule.name)
          (cgraph-fix cgraph))
         (to (cdr to-look))
         (cgraph (add-cgraph-edge matchvar subst rule cgraph)))
      (gl-object-add-to-cgraph to cgraph ruletable wrld)))
  ///
  (verify-guards gl-object-add-to-cgraph)
  (local (in-theory (disable gl-object-add-to-cgraph
                             gl-object-add-to-cgraph-rules
                             gl-object-add-to-cgraph-rule
                             gl-object-add-to-cgraph-matches
                             gl-object-add-to-cgraph-match)))

  (local (defthm pseudo-term-subst-fix-when-bad-car
           (implies (not (and (consp (car x))
                              (pseudo-var-p (caar x))))
                    (equal (pseudo-term-subst-fix x)
                           (pseudo-term-subst-fix (cdr x))))
           :hints(("Goal" :in-theory (enable pseudo-term-subst-fix)))))

  (defret-mutual cgraph-bfrlist-of-gl-object-add-to-cgraph
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (not (member v (gl-object-bfrlist x)))
                    (not (member v (cgraph-bfrlist cgraph))))
               (not (member v (cgraph-bfrlist new-cgraph))))
      :hints ('(:expand (<call>)))
      :fn gl-object-add-to-cgraph)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (not (member v (gl-object-bfrlist x)))
                    (not (member v (cgraph-bfrlist cgraph))))
               (not (member v (cgraph-bfrlist new-cgraph))))
      :hints ('(:expand (<call>)))
      :fn gl-object-add-to-cgraph-rules)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (not (member v (gl-object-bfrlist x)))
                    (not (member v (cgraph-bfrlist cgraph))))
               (not (member v (cgraph-bfrlist new-cgraph))))
      :hints ('(:expand (<call>)))
      :fn gl-object-add-to-cgraph-rule)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (not (member v (gl-object-bfrlist x)))
                    (not (member v (cgraph-bfrlist cgraph))))
               (not (member v (cgraph-bfrlist new-cgraph))))
      :hints ('(:expand (<call>)))
      :fn gl-object-add-to-cgraph-matches)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (not (member v (gl-object-bfrlist x)))
                    (not (member v (cgraph-bfrlist cgraph))))
               (not (member v (cgraph-bfrlist new-cgraph))))
      :hints ('(:expand (<call>)))
      :fn gl-object-add-to-cgraph-match))

  (fty::deffixequiv-mutual gl-object-add-to-cgraph))

(define bvar-db-add-to-cgraph-aux ((n natp)
                                   (bvar-db)
                                   (cgraph cgraph-p)
                                   (ruletable ctrex-ruletable-p)
                                   (wrld plist-worldp))
  :returns (new-cgraph cgraph-p)
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql n (next-bvar bvar-db))))
        (cgraph-fix cgraph))
       (cgraph (gl-object-add-to-cgraph (get-bvar->term n bvar-db)
                                        cgraph ruletable wrld)))
    (bvar-db-add-to-cgraph-aux (1+ (lnfix n))
                               bvar-db cgraph ruletable wrld))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (not (member v (cgraph-bfrlist cgraph)))
                  (<= (base-bvar$a bvar-db) (nfix n)))
             (not (member v (cgraph-bfrlist new-cgraph))))))

(define bvar-db-create-cgraph (bvar-db
                               (ruletable ctrex-ruletable-p)
                               (wrld plist-worldp))
  :returns (cgraph cgraph-p)
  (fast-alist-clean
   (bvar-db-add-to-cgraph-aux (base-bvar bvar-db) bvar-db nil ruletable wrld))
  ///
  (local (defthm cgraph-bfrlist-of-cdr-last
           (equal (cgraph-bfrlist (cdr (last x))) nil)
           :hints(("Goal" :in-theory (enable last cgraph-bfrlist)))))

  (defret cgraph-bfrlist-of-<fn>
    (implies (not (member v (bvar-db-bfrlist bvar-db)))
             (not (member v (cgraph-bfrlist cgraph))))))

(fty::defmap cgraph-alist :key-type gl-object :true-listp t)


;; (define cgraph-edges-invert ((from gl-object-p)
;;                              (edges cgraph-edgelist-p)
;;                              (acc cgraph-p))
;;   :returns (new-acc cgraph-p)
;;   (b* ((acc (cgraph-fix acc))
;;        ((when (atom edges)) acc)
;;        ((cgraph-edge edge1) (car edges))
;;        (new-edge (change-cgraph-edge edge1 :trigger from))
;;        (acc (hons-acons edge1.trigger (cons new-edge (cdr (hons-get edge1.trigger acc))) acc)))
;;     (cgraph-edges-invert from (cdr edges) acc)))

;; (define cgraph-invert ((cgraph cgraph-p)
;;                        (acc cgraph-p))
;;   :returns (new-acc cgraph-p)
;;   (if (atom cgraph)
;;       (cgraph-fix acc)
;;     (if (mbt (and (consp (car cgraph))
;;                   (gl-object-p (caar cgraph))))
;;         (b* ((acc (cgraph-edges-invert (caar cgraph) (cdar cgraph) acc)))
;;           (cgraph-invert (cdr cgraph) acc))
;;       (cgraph-invert (cdr cgraph) acc))))

;; (fty::defmap cgraph-indexmap :key-type gl-object :val-type natp :true-listp t)


;; (fty::deflist gl-objectlistlist :elt-type gl-objectlist :true-listp t)


;; (define cgraph-stack-pop-n ((n natp)
;;                             (stk cgraph-alist-p))
;;   :guard (and (no-duplicatesp-equal (alist-keys stk))
;;               (<= n (len stk)))
;;   :guard-hints (("goal" :in-theory (enable cgraph-alist-p)))
;;   :measure (len stk)
;;   :returns (mv (popped gl-objectlist-p)
;;                (new-stk cgraph-alist-p))
;;   (if (zp n)
;;       (mv nil (cgraph-alist-fix stk))
;;     (if (mbt (and (consp stk)
;;                   (consp (car stk))
;;                   (gl-object-p (caar stk))))
;;         (b* ((obj (caar stk))
;;              (stk (acl2::fast-alist-pop stk))
;;              ((mv rest stk) (cgraph-stack-pop-n (1- n) stk)))
;;           (mv (cons obj rest) stk))
;;       (if (consp stk)
;;           (cgraph-stack-pop-n n (cdr stk))
;;         (mv nil nil))))
;;   ///
;;   (defret len-of-cgraph-stack-pop-n-new-stk
;;     (implies (<= (nfix n) (len (cgraph-alist-fix stk)))
;;              (equal (len new-stk)
;;                     (- (len (cgraph-alist-fix stk)) (nfix n))))
;;     :hints(("Goal" :in-theory (enable cgraph-alist-fix))))

;;   (defret len-of-cgraph-stack-pop-n-popped
;;     (implies (<= (nfix n) (len (cgraph-alist-fix stk)))
;;              (equal (len popped) (nfix n)))
;;     :hints(("Goal" :in-theory (enable cgraph-alist-fix))))

;;   (defret hons-assoc-equal-of-<fn>
;;     (implies (not (hons-assoc-equal k (cgraph-alist-fix stk)))
;;              (not (hons-assoc-equal k new-stk))))

;;   (defret no-dups-of-<fn>
;;     (implies (no-duplicatesp (alist-keys (cgraph-alist-fix stk)))
;;              (no-duplicatesp (alist-keys new-stk)))
;;     :hints(("Goal" :in-theory (enable alist-keys cgraph-alist-fix)))))

;; (define cgraph-edgelist->triggers ((x cgraph-edgelist-p))
;;   :returns (triggers gl-objectlist-p)
;;   (if (Atom x)
;;       nil
;;     (cons (cgraph-edge->trigger (car x))
;;           (cgraph-edgelist->triggers (cdr x)))))

;; (local
;;  (defprojection cgraph-edgelist->triggers ((x cgraph-edgelist-p))
;;    :returns (triggers gl-objectlist-p)
;;    (cgraph-edge->trigger x)
;;    :already-definedp t))



;; (local (defthm len-set-difference-of-cons
;;          (<= (len (set-difference$ a (cons x b)))
;;              (len (set-difference$ a b)))
;;          :hints(("Goal" :in-theory (enable set-difference$)))
;;          :rule-classes :linear))

;; (local (defthm len-set-difference-of-cons-when-not-member
;;          (implies (and (member x a)
;;                        (not (member x b)))
;;                   (< (len (set-difference$ a (cons x b)))
;;                      (len (set-difference$ a b))))
;;          :hints(("Goal" :in-theory (enable set-difference$)))
;;          :rule-classes :linear))

;; (local (in-theory (disable min len acl2::consp-when-member-equal-of-atom-listp
;;                            cgraph-indexmap-p-when-subsetp-equal)))

;; (defines cgraph-tarjan-sccs
;;   (define cgraph-tarjan-sccs ((x gl-object-p)
;;                               (cgraph cgraph-p)
;;                               (preorder cgraph-indexmap-p)
;;                               (preorder-next)
;;                               (stk cgraph-alist-p)
;;                               (stack-size)
;;                               (sccs-acc gl-objectlistlist-p))
;;     :guard (and (no-duplicatesp-equal (alist-keys stk))
;;                 (equal stack-size (len stk))
;;                 (equal preorder-next (len preorder))
;;                 (subsetp-equal (alist-keys stk) (alist-keys preorder)))
;;     :returns (mv (lowlink natp :rule-classes :type-prescription)
;;                  (new-preorder cgraph-indexmap-p)
;;                  (new-preorder-next (equal new-preorder-next (len new-preorder)))
;;                  (new-stk cgraph-alist-p)
;;                  (new-stack-size
;;                   ;; need to prove this later
;;                   ;; (equal new-stack-size (len new-stk))
;;                   )
;;                  (sccs gl-objectlistlist-p))
;;     :well-founded-relation acl2::nat-list-<
;;     :measure (list (let ((rem (len (set-difference$ (alist-keys (cgraph-fix cgraph))
;;                                                     (alist-keys (cgraph-indexmap-fix preorder))))))
;;                      (+ rem ;; (if (hons-assoc-equal (gl-object-fix x) (cgraph-fix cgraph)) 0 1)
;;                         ))
;;                    0 1)
;;     :verify-guards nil
;;     (b* ((preorder (cgraph-indexmap-fix preorder))
;;          (stk (cgraph-alist-fix stk))
;;          (preorder-next (mbe :logic (len preorder) :exec preorder-next))
;;          (stack-size (mbe :logic (len stk) :exec stack-size))
;;          (sccs-acc (gl-objectlistlist-fix sccs-acc))
;;          (x (gl-object-fix x))
;;          (index (cdr (hons-get x preorder)))
;;          ((when index)
;;           (mv (if (hons-get x stk)
;;                   index
;;                 preorder-next)
;;               preorder
;;               preorder-next
;;               stk
;;               stack-size
;;               sccs-acc))
;;          (index preorder-next)
;;          (preorder (hons-acons x preorder-next preorder))
;;          (preorder-next (1+ preorder-next))
;;          (stk (hons-acons x nil stk))
;;          (prev-stack-size stack-size)
;;          (stack-size (1+ stack-size))
;;          (edges (cdr (hons-get x (cgraph-fix cgraph))))
;;          ((mv lowlink preorder preorder-next stk stack-size sccs-acc)
;;           (cgraph-tarjan-sccs-edges edges cgraph preorder preorder-next stk stack-size sccs-acc))
;;          (lowlink (min lowlink index))
;;          ((unless (eql lowlink index))
;;           (mv lowlink preorder preorder-next stk stack-size sccs-acc))
;;          ((mv new-scc stk) (cgraph-stack-pop-n (- stack-size prev-stack-size) stk)))
;;       (mv index preorder preorder-next stk prev-stack-size (cons new-scc sccs-acc))))

;;   (define cgraph-tarjan-sccs-edges ((x cgraph-edgelist-p)
;;                                     (cgraph cgraph-p)
;;                                     (preorder cgraph-indexmap-p)
;;                                     (preorder-next)
;;                                     (stk cgraph-alist-p)
;;                                     (stack-size)
;;                                     (sccs-acc gl-objectlistlist-p))
;;     :guard (and (no-duplicatesp-equal (alist-keys stk))
;;                 (equal stack-size (len stk))
;;                 (equal preorder-next (len preorder))
;;                 (subsetp-equal (alist-keys stk) (alist-keys preorder)))
;;     :returns (mv (lowlink natp :rule-classes :type-prescription)
;;                  (new-preorder cgraph-indexmap-p)
;;                  (new-preorder-next (equal new-preorder-next (len new-preorder)))
;;                  (new-stk cgraph-alist-p)
;;                  (new-stack-size
;;                   ;; need to prove this later
;;                   ;; (equal new-stack-size (len new-stk))
;;                   )
;;                  (sccs gl-objectlistlist-p))
;;     :measure (list (let ((rem (len (set-difference$ (alist-keys (cgraph-fix cgraph))
;;                                                     (alist-keys (cgraph-indexmap-fix preorder))))))
;;                      (+ rem ;; (if (subsetp (cgraph-edgelist->triggers x)
;;                             ;;              (alist-keys (cgraph-fix cgraph)))
;;                             ;;     0 1)
;;                         ))
;;                    (len x) 0)
;;     (b* ((preorder (cgraph-indexmap-fix preorder))
;;          (stk (cgraph-alist-fix stk))
;;          (preorder-next (mbe :logic (len preorder) :exec preorder-next))
;;          (stack-size (mbe :logic (len stk) :exec stack-size))
;;          (sccs-acc (gl-objectlistlist-fix sccs-acc))

;;          ((when (atom x))
;;           (mv preorder-next preorder preorder-next stk stack-size sccs-acc))

;;          ((mv lowlink1 preorder preorder-next stk stack-size sccs-acc)
;;           (b* (((mv lowlink1 new-preorder new-preorder-next new-stk new-stack-size new-sccs-acc)
;;                 (cgraph-tarjan-sccs (cgraph-edge->trigger (car x))
;;                                     cgraph preorder preorder-next stk stack-size sccs-acc))
;;                ((unless (mbt (<= (len (set-difference$ (alist-keys (cgraph-fix cgraph))
;;                                                        (alist-keys (cgraph-indexmap-fix new-preorder))))
;;                                  (len (set-difference$ (alist-keys (cgraph-fix cgraph))
;;                                                        (alist-keys (cgraph-indexmap-fix preorder)))))))
;;                 (mv preorder-next preorder preorder-next stk stack-size sccs-acc)))
;;             (mv lowlink1 new-preorder new-preorder-next new-stk new-stack-size new-sccs-acc)))

;;          ((mv lowlink2 preorder preorder-next stk stack-size sccs-acc)
;;           (cgraph-tarjan-sccs-edges (cdr x) cgraph preorder preorder-next stk stack-size sccs-acc)))
;;       (mv (min lowlink1 lowlink2) preorder preorder-next stk stack-size sccs-acc)))
;;   ///
;;   (local (in-theory (disable cgraph-tarjan-sccs-edges
;;                              cgraph-tarjan-sccs)))
                             
;;   (defret-mutual cgraph-tarjan-sccs-stack-size-correct
;;     (defret <fn>-stack-size-correct
;;       (and (<= (len (cgraph-alist-fix stk)) (len new-stk))
;;            (equal new-stack-size (len new-stk)))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs)
;;     (defret <fn>-stack-size-correct
;;       (and (<= (len (cgraph-alist-fix stk)) (len new-stk))
;;            (equal new-stack-size (len new-stk)))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs-edges))

;;   (defret <fn>-stack-size-decr-linear
;;     (<= (len (cgraph-alist-fix stk)) (len new-stk))
;;     :rule-classes :linear
;;     :fn cgraph-tarjan-sccs)
;;   (defret <fn>-stack-size-decr-linear
;;     (<= (len (cgraph-alist-fix stk)) (len new-stk))
;;     :rule-classes :linear
;;     :fn cgraph-tarjan-sccs-edges)

;;   (defret-mutual cgraph-tarjan-sccs-preorder-preserved
;;     (defret <fn>-preorder-preserved
;;       (implies (hons-assoc-equal k (cgraph-indexmap-fix preorder))
;;                (hons-assoc-equal k preorder))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs)
;;     (defret <fn>-preorder-preserved
;;       (implies (hons-assoc-equal k (cgraph-indexmap-fix preorder))
;;                (hons-assoc-equal k preorder))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs-edges))

;;   (defret-mutual cgraph-tarjan-sccs-stack-subsetp
;;     (defret <fn>-stack-subsetp-lemma
;;       (implies (and (or (not (hons-assoc-equal k (cgraph-alist-fix stk)))
;;                         (hons-assoc-equal k (cgraph-indexmap-fix preorder)))
;;                     (hons-assoc-equal k new-stk))
;;                (hons-assoc-equal k new-preorder))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs)
;;     (defret <fn>-stack-subsetp-lemma
;;       (implies (and (or (not (hons-assoc-equal k (cgraph-alist-fix stk)))
;;                         (hons-assoc-equal k (cgraph-indexmap-fix preorder)))
;;                     (hons-assoc-equal k new-stk))
;;                (hons-assoc-equal k new-preorder))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs-edges))

  
;;   (local (defthm subsetp-alist-keys-implies-hons-assoc-equal
;;            (implies (and (subsetp (alist-keys a) (alist-keys b))
;;                          (hons-assoc-equal k a))
;;                     (hons-assoc-equal k b))
;;            :hints (("goal" :use ((:instance acl2::subsetp-member
;;                                   (a k) (x (alist-keys a)) (y (alist-keys b))))
;;                     :in-theory (disable acl2::subsetp-member)))))

;;   (defret <fn>-stack-subsetp
;;     (implies (subsetp (alist-keys (cgraph-alist-fix stk))
;;                       (alist-keys (cgraph-indexmap-fix preorder)))
;;              (subsetp (alist-keys new-stk)
;;                       (alist-keys new-preorder)))
;;     :hints(("Goal" :in-theory (e/d (ACL2::SUBSETP-WITNESS-RW)
;;                                    (acl2::subsetp-member))
;;             ;; :use ((:instance acl2::subsetp-member
;;             ;;        (a (acl2::subsetp-witness (alist-keys (cgraph-alist-fix new-stk))
;;             ;;                                  (alist-keys (cgraph-indexmap-fix new-preorder))))
;;             ;;        (x (alist-keys (cgraph-alist-fix stk)))
;;             ;;        (y (alist-keys (cgraph-indexmap-fix preorder)))))
;;             ))
;;     :fn cgraph-tarjan-sccs)
;;   (defret <fn>-stack-subsetp
;;     (implies (subsetp (alist-keys (cgraph-alist-fix stk))
;;                       (alist-keys (cgraph-indexmap-fix preorder)))
;;              (subsetp (alist-keys new-stk)
;;                       (alist-keys new-preorder)))
;;     :hints(("Goal" :in-theory (e/d (ACL2::SUBSETP-WITNESS-RW)
;;                                    (acl2::subsetp-member))
;;             ;; :use ((:instance acl2::subsetp-member
;;             ;;        (a (acl2::subsetp-witness (alist-keys (cgraph-alist-fix new-stk))
;;             ;;                                  (alist-keys (cgraph-indexmap-fix new-preorder))))
;;             ;;        (x (alist-keys (cgraph-alist-fix stk)))
;;             ;;        (y (alist-keys (cgraph-indexmap-fix preorder)))))
;;             ))
;;     :fn cgraph-tarjan-sccs-edges)

;;   (local (defthm cdr-hons-assoc-under-iff-when-cgraph-indexmap-p
;;            (implies (cgraph-indexmap-p x)
;;                     (iff (cdr (hons-assoc-equal k x))
;;                          (hons-assoc-equal k x)))
;;            :hints(("Goal" :in-theory (enable cgraph-indexmap-p)))))


;;   (defret-mutual cgraph-tarjan-sccs-stack-no-dups
;;     (defret <fn>-stack-no-dups
;;       (implies (and (no-duplicatesp (alist-keys (cgraph-alist-fix stk)))
;;                     (subsetp (alist-keys (cgraph-alist-fix stk))
;;                              (alist-keys (cgraph-indexmap-fix preorder))))
;;                (no-duplicatesp (alist-keys new-stk)))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs)
;;     (defret <fn>-stack-no-dups
;;       (implies (and (no-duplicatesp (alist-keys (cgraph-alist-fix stk)))
;;                     (subsetp (alist-keys (cgraph-alist-fix stk))
;;                              (alist-keys (cgraph-indexmap-fix preorder))))
;;                (no-duplicatesp (alist-keys new-stk)))
;;       :hints ('(:expand (<call>)))
;;       :fn cgraph-tarjan-sccs-edges))

;;   (defret-mutual cgraph-tarjan-sccs-measure-decr
;;     (defret <fn>-measure-decr
;;       (<= (len (set-difference$
;;                 (alist-keys (cgraph-fix cgraph))
;;                 (alist-keys new-preorder)))
;;           (len (set-difference$
;;                 (alist-keys (cgraph-fix cgraph))
;;                 (alist-keys (cgraph-indexmap-fix preorder)))))
;;       :hints ('(:expand (<call>)))
;;       :rule-classes :linear
;;       :fn cgraph-tarjan-sccs)
;;     (defret <fn>-measure-decr
;;       (<= (len (set-difference$
;;                 (alist-keys (cgraph-fix cgraph))
;;                 (alist-keys new-preorder)))
;;           (len (set-difference$
;;                 (alist-keys (cgraph-fix cgraph))
;;                 (alist-keys (cgraph-indexmap-fix preorder)))))
;;       :hints ('(:expand (<call>)))
;;       :rule-classes :linear
;;       :fn cgraph-tarjan-sccs-edges))

;;   (defret <fn>-measure-decr-no-fix
;;     (implies (cgraph-p cgraph)
;;              (<= (len (set-difference$
;;                        (alist-keys cgraph)
;;                        (alist-keys new-preorder)))
;;                  (len (set-difference$
;;                        (alist-keys cgraph)
;;                        (alist-keys (cgraph-indexmap-fix preorder))))))
;;       :hints (("goal" :use cgraph-tarjan-sccs-measure-decr
;;                :in-theory (disable cgraph-tarjan-sccs-measure-decr)))
;;       :rule-classes :linear
;;       :fn cgraph-tarjan-sccs)

;;   (verify-guards cgraph-tarjan-sccs))

;; (local (in-theory (disable cgraph-tarjan-sccs-preorder-preserved
;;                            cgraph-tarjan-sccs-edges-preorder-preserved)))

;; (define cgraph-tarjan-sccs-iter ((x cgraph-p) ;; tail
;;                                  (cgraph cgraph-p)
;;                                  (preorder cgraph-indexmap-p)
;;                                  (preorder-next)
;;                                  (stk cgraph-alist-p)
;;                                  (stack-size)
;;                                  (sccs-acc gl-objectlistlist-p))
;;   :guard (and (no-duplicatesp-equal (alist-keys stk))
;;               (equal stack-size (len stk))
;;               (equal preorder-next (len preorder))
;;               (subsetp-equal (alist-keys stk) (alist-keys preorder)))
;;   :returns (sccs gl-objectlistlist-p)
;;   :verify-guards nil
;;   (b* (;; (preorder (cgraph-indexmap-fix preorder))
;;        ;; (stk (cgraph-alist-fix stk))
;;        ;; (preorder-next (mbe :logic (len preorder) :exec preorder-next))
;;        ;; (stack-size (mbe :logic (len stk) :exec stack-size))
;;        (sccs-acc (gl-objectlistlist-fix sccs-acc))
       
;;        ((when (atom x))
;;         ;; (mv preorder
;;         ;;     preorder-next
;;         ;;     stk
;;         ;;     stack-size
;;             sccs-acc)
;;        ((unless (mbt (and (consp (car x))
;;                           (gl-object-p (caar x)))))
;;         (cgraph-tarjan-sccs-iter (cdr x) cgraph preorder preorder-next stk stack-size sccs-acc))
;;        ((mv ?lowlink
;;             preorder
;;             preorder-next
;;             stk
;;             stack-size
;;             sccs-acc)
;;         (cgraph-tarjan-sccs (caar x) cgraph preorder preorder-next stk stack-size sccs-acc)))
;;     (cgraph-tarjan-sccs-iter (cdr x) cgraph preorder preorder-next stk stack-size sccs-acc))
;;   ///
;;   (verify-guards cgraph-tarjan-sccs-iter))

;; (define cgraph-tarjan-sccs-top ((cgraph cgraph-p))
;;   :returns (sccs gl-objectlistlist-p)
;;   (cgraph-tarjan-sccs-iter cgraph cgraph nil 0 nil 0 nil))
 

;; ;; This is very similar to gl-objectlistlist-p...
;; (fty::defmap cgraph-scc-map :key-type gl-object :val-type gl-objectlist :true-listp t)

;; (define cgraph-map-one-scc ((objs gl-objectlist-p)
;;                             (scc gl-objectlist-p)
;;                             (scc-map cgraph-scc-map-p))
;;   :returns (new-scc-map cgraph-scc-map-p)
;;   (if (atom objs)
;;       (cgraph-scc-map-fix scc-map)
;;     (cgraph-map-one-scc
;;      (cdr objs) scc (hons-acons (gl-object-fix (car objs))
;;                                 (gl-objectlist-fix scc)
;;                                 scc-map))))

;; (define cgraph-map-sccs ((sccs gl-objectlistlist-p)
;;                          (scc-map cgraph-scc-map-p))
;;   :returns (new-scc-map cgraph-scc-map-p)
;;   (if (atom sccs)
;;       (cgraph-scc-map-fix scc-map)
;;     (cgraph-map-sccs (cdr sccs)
;;                      (cgraph-map-one-scc (car sccs) (car sccs) scc-map))))


;; (defprod scc-cgraph-edges
;;   ((tree-edges cgraph-edgelist-p)
;;    (scc-edges cgraph-edgelist-p)
;;    (scc gl-objectlist-p))
;;   :layout :tree)

;; (fty::defmap scc-cgraph :key-type gl-object :val-type scc-cgraph-edges :true-listp t)


;; (define cgraph-edges-scc-split ((edges cgraph-edgelist-p)
;;                                 (scc gl-objectlist-p))
;;   :returns (mv (tree-edges cgraph-edgelist-p)
;;                (scc-edges cgraph-edgelist-p))
;;   (b* (((when (atom edges))
;;         (mv nil nil))
;;        ((mv tree-edges scc-edges) (cgraph-edges-scc-split (cdr edges) scc))
;;        ((cgraph-edge x1) (cgraph-edge-fix (car edges)))
;;        ((when (acl2::hons-member-equal x1.trigger scc))
;;         (mv tree-edges (cons x1 scc-edges))))
;;     (mv (cons x1 tree-edges) scc-edges)))


;; (define scc-to-scc-cgraph ((rest gl-objectlist-p)
;;                            (scc gl-objectlist-p)
;;                            (cgraph cgraph-p)
;;                            (scc-cgraph scc-cgraph-p))
;;   :returns (new-scc-cgraph scc-cgraph-p)
;;   (b* (((when (atom rest)) (scc-cgraph-fix scc-cgraph))
;;        (first (gl-object-fix (car rest)))
;;        (edges (cdr (hons-get first (cgraph-fix cgraph))))
;;        ((unless edges)
;;         ;; must be a singleton, leaf scc
;;         (scc-to-scc-cgraph (cdr rest) scc cgraph scc-cgraph))
;;        ((mv tree-edges scc-edges) (cgraph-edges-scc-split edges scc))
;;        (scc-cgraph (hons-acons first (make-scc-cgraph-edges
;;                                       :tree-edges tree-edges
;;                                       :scc-edges scc-edges
;;                                       :scc scc)
;;                                scc-cgraph)))
;;     (scc-to-scc-cgraph (cdr rest) scc cgraph scc-cgraph)))

;; (define cgraph-to-scc-cgraph ((sccs gl-objectlistlist-p)
;;                               (cgraph cgraph-p)
;;                               (scc-cgraph scc-cgraph-p))
;;   :returns (new-scc-cgraph scc-cgraph-p)
;;   (if (atom sccs)
;;       (scc-cgraph-fix scc-cgraph)
;;     (cgraph-to-scc-cgraph
;;      (cdr sccs)
;;      cgraph
;;      (scc-to-scc-cgraph (car sccs) (car sccs) cgraph scc-cgraph))))


    



(defines gl-object-variable-free-p
  (define gl-object-variable-free-p ((x gl-object-p))
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    (gl-object-case x
      :g-var nil
      :g-apply (gl-objectlist-variable-free-p x.args)
      :g-cons (and (gl-object-variable-free-p x.car)
                   (gl-object-variable-free-p x.cdr))
      :g-map (gl-object-alist-variable-free-p x.alist)
      :g-ite (and (gl-object-variable-free-p x.test)
                  (gl-object-variable-free-p x.then)
                  (gl-object-variable-free-p x.else))
      :otherwise t))

  (define gl-objectlist-variable-free-p ((x gl-objectlist-p))
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    (if (atom x)
        t
      (and (gl-object-variable-free-p (car x))
           (gl-objectlist-variable-free-p (cdr x)))))

  (define gl-object-alist-variable-free-p ((x gl-object-alist-p))
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    (if (atom x)
        t
      (and (or (not (mbt (consp (car x))))
               (gl-object-variable-free-p (cdar x)))
           (gl-object-alist-variable-free-p (cdr x)))))
  ///
  (memoize 'gl-object-variable-free-p))


(define magitastic-ev-definition ((fn pseudo-fnsym-p) state)
  :returns (mv ok
               (formals symbol-listp)
               (body pseudo-termp))
  :prepwork ((local (in-theory (disable pseudo-termp symbol-listp pseudo-term-listp
                                        acl2::pseudo-termp-opener))))
  (b* ((tab (table-alist 'magitastic-ev-definitions (w state)))
       (fn (pseudo-fnsym-fix fn))
       (look (cdr (hons-assoc-equal fn tab)))
       ((when (and (eql (len look) 2)
                   (symbol-listp (first look))
                   (pseudo-termp (second look))))
        (mv t (first look) (second look)))
       ((mv ok formals body) (acl2::fn-get-def fn state))
       ((unless (and ok (pseudo-termp body)))
        (mv nil nil nil)))
    (mv t formals body)))


(defines magitastic-ev
  (define magitastic-ev ((x pseudo-termp)
                         (alist symbol-alistp)
                         (reclimit natp)
                         state hard-errp aokp)
    :well-founded-relation acl2::nat-list-<
    :measure (list reclimit (pseudo-term-count x))
    :returns (mv errmsg val)
    :verify-guards nil
    (pseudo-term-case x
      :const (mv nil x.val)
      :var (mv nil (cdr (hons-assoc-equal x.name alist)))
      :lambda (b* (((mv err args)
                    (magitastic-ev-list x.args alist reclimit state hard-errp aokp))
                   ((when err) (mv err nil)))
                (magitastic-ev x.body
                               (pairlis$ x.formals args)
                               reclimit state hard-errp aokp))
      :fncall (b* (((when (and** (eq x.fn 'if) (eql (len x.args) 3)))
                    (b* (((mv err test) (magitastic-ev (first x.args) alist reclimit state hard-errp aokp))
                         ((when err) (mv err nil)))
                      (if test
                          (magitastic-ev (second x.args) alist reclimit state hard-errp aokp)
                        (magitastic-ev (third x.args) alist reclimit state hard-errp aokp))))
                   ((when (and** (eq x.fn 'return-last) (eql (len x.args) 3)))
                    (b* ((arg1 (first x.args)))
                      (prog2$
                       (pseudo-term-case arg1
                         :const (and (eq arg1.val 'progn)
                                     (b* (((mv ?err ?arg1)
                                           (magitastic-ev (second x.args) alist reclimit state hard-errp aokp)))
                                       nil))
                         :otherwise nil)
                       (magitastic-ev (third x.args) alist reclimit state hard-errp aokp))))
                   ((mv err args) (magitastic-ev-list x.args alist reclimit state hard-errp aokp))
                   ((when err) (mv err nil)))
                (magitastic-ev-fncall x.fn args reclimit state hard-errp aokp))))

  (define magitastic-ev-fncall ((fn pseudo-fnsym-p)
                                (args true-listp)
                                (reclimit natp)
                                state hard-errp aokp)
    :measure (list reclimit 0)
    :returns (mv errmsg val)
    (b* (((mv ev-err val)
          (acl2::magic-ev-fncall (pseudo-fnsym-fix fn)
                                 (mbe :logic (true-list-fix args)
                                      :exec args)
                                 state hard-errp aokp))
         ((unless ev-err) (mv nil val))
         ((when (zp reclimit))
          (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil))
         ((mv def-ok formals body) (magitastic-ev-definition fn state))
         ((unless def-ok)
          (mv (msg "No definition for ~x0" (pseudo-fnsym-fix fn)) nil))
         ((unless (eql (len formals) (len args)))
          (mv (msg "Wrong arity for ~x0 call" (pseudo-fnsym-fix fn)) nil)))
      (magitastic-ev body (pairlis$ formals args) (1- reclimit) state hard-errp aokp)))

  (define magitastic-ev-list ((x pseudo-term-listp)
                              (alist symbol-alistp)
                              (reclimit natp)
                              state hard-errp aokp)
    :measure (list reclimit (pseudo-term-list-count x))
    :returns (mv errmsg (vals true-listp))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv err first) (magitastic-ev (car x) alist reclimit state hard-errp aokp))
         ((when err) (mv err nil))
         ((mv err rest) (magitastic-ev-list (cdr x) alist reclimit state hard-errp aokp))
         ((when err) (mv err nil)))
      (mv nil (cons first rest))))
  ///
  (verify-guards magitastic-ev)

  (local (in-theory (disable magitastic-ev magitastic-ev-list magitastic-ev-fncall
                             pseudo-term-listp pseudo-termp)))

  (fty::deffixequiv-mutual magitastic-ev))


(local (defthm assoc-is-hons-assoc-equal
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(defines magic-gl-object-eval
  (define magic-gl-object-eval ((x gl-object-p)
                                (env$)
                                &optional
                                (logicman 'logicman)
                                (state 'state))
    :guard (and (bfr-env$-p env$ logicman)
                (lbfr-listp (gl-object-bfrlist x)))
    :returns (mv err val)
    :verify-guards nil
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    (gl-object-case x
      :g-concrete (mv nil x.val)
      :g-boolean (mv nil (bfr-eval-fast x.bool env$))
      :g-integer (mv nil (bools->int (bfr-list-eval-fast x.bits env$)))
      :g-ite (b* (((mv err test) (magic-gl-object-eval x.test env$))
                  ((when err) (mv err nil)))
               (if test
                   (magic-gl-object-eval x.then env$)
                 (magic-gl-object-eval x.else env$)))
      :g-cons (b* (((mv err car) (magic-gl-object-eval x.car env$))
                   ((when err) (mv err nil))
                   ((mv err cdr) (magic-gl-object-eval x.cdr env$))
                   ((when err) (mv err nil)))
                (mv nil (cons car cdr)))
      :g-map (magic-gl-object-alist-eval x.alist env$)
      :g-var (mv nil (cdr (assoc-eq x.name (env$->obj-alist env$))))
      :g-apply (b* (((mv err args) (magic-gl-objectlist-eval x.args env$))
                    ((when err) (mv err nil)))
                 (magitastic-ev-fncall x.fn args 1000 state t t))))

  (define magic-gl-objectlist-eval ((x gl-objectlist-p)
                                    (env$)
                                    &optional
                                    (logicman 'logicman)
                                    (state 'state))
    :guard (and (bfr-env$-p env$ logicman)
                (lbfr-listp (gl-objectlist-bfrlist x)))
    :returns (mv err (val true-listp))
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    (b* (((when (atom x)) (mv nil nil))
         ((mv err car) (magic-gl-object-eval (car x) env$))
         ((when err) (mv err nil))
         ((mv err cdr) (magic-gl-objectlist-eval (cdr x) env$))
         ((when err) (mv err nil)))
      (mv nil (cons car cdr))))

  (define magic-gl-object-alist-eval ((x gl-object-alist-p)
                                      (env$)
                                      &optional
                                      (logicman 'logicman)
                                      (state 'state))
    :guard (and (bfr-env$-p env$ logicman)
                (lbfr-listp (gl-object-alist-bfrlist x)))
    :returns (mv err val)
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    (b* (((when (atom x)) (mv nil x))
         ((unless (mbt (consp (car x))))
          (magic-gl-object-alist-eval (cdr x) env$))
         ((mv err val1) (magic-gl-object-eval (cdar x) env$))
         ((when err) (mv err nil))
         ((mv err rest) (magic-gl-object-alist-eval (cdr x) env$))
         ((when err) (mv err nil)))
      (mv nil (cons (cons (caar x) val1) rest))))
  ///
  (verify-guards magic-gl-object-eval-fn
    :hints (("goal" :expand (gl-object-bfrlist x)
             :in-theory (disable magic-gl-object-eval-fn
                                 magic-gl-objectlist-eval
                                 magic-gl-object-alist-eval))))

  (local (defthm gl-object-alist-fix-when-bad-car
           (implies (and (consp X)
                         (not (consp (car x))))
                    (equal (gl-object-alist-fix x)
                           (gl-object-alist-fix (cdr x))))
           :hints(("Goal" :in-theory (enable gl-object-alist-fix)))))

  (fty::deffixequiv-mutual magic-gl-object-eval))


(define pairlis-vars ((x symbol-listp)
                      (args))
  :guard (equal (len x) (len args))
  (if (atom x)
      nil
    (b* ((x1 (mbe :logic (acl2::symbol-fix (car x)) :exec (car x))))
      (if x1
          (cons (cons x1 (car args))
                (pairlis-vars (cdr x) (cdr args)))
        (pairlis-vars (cdr x) (cdr args)))))
  ///
  (defthm gl-object-bindings-p-of-pairlis-vars
    (implies (gl-objectlist-p args)
             (gl-object-bindings-p (pairlis-vars x args))))

  (local (in-theory (disable symbol-listp symbol-listp-when-pseudo-var-list-p)))

  (defthm gl-object-bindings-bfrlist-of-pairlis-vars
    (implies (not (member v (gl-objectlist-bfrlist args)))
             (not (member v (gl-object-bindings-bfrlist (pairlis-vars x args)))))))


(defines pseudo-term-subst-gl-objects
  (define pseudo-term-subst-gl-objects ((x pseudo-termp)
                                        (alist gl-object-bindings-p))
    :returns (new-x gl-object-p)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :const (g-concrete x.val)
      :var (cdr (assoc x.name (gl-object-bindings-fix alist)))
      :fncall (g-apply x.fn (pseudo-term-list-subst-gl-objects x.args alist))
      :lambda (pseudo-term-subst-gl-objects
               x.body
               (pairlis-vars x.formals
                             (pseudo-term-list-subst-gl-objects x.args alist)))))
  (define pseudo-term-list-subst-gl-objects ((x pseudo-term-listp)
                                             (alist gl-object-bindings-p))
    :returns (new-x gl-objectlist-p)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (hons (pseudo-term-subst-gl-objects (car x) alist)
            (pseudo-term-list-subst-gl-objects (cdr x) alist))))
  ///
  (defthm len-of-pseudo-term-list-subst-gl-objects
    (equal (len (pseudo-term-list-subst-gl-objects x alist))
           (len x))
    :hints(("Goal" :in-theory (enable len))))

  (defret-mutual gl-object-bfrlist-of-pseudo-term-subst-gl-objects
    (defret gl-object-bfrlist-of-<fn>
      (implies (not (member v (gl-object-bindings-bfrlist alist)))
               (not (member v (gl-object-bfrlist new-x))))
      :hints ('(:expand (<call>)))
      :fn pseudo-term-subst-gl-objects)
    (defret gl-objectlist-bfrlist-of-<fn>
      (implies (not (member v (gl-object-bindings-bfrlist alist)))
               (not (member v (gl-objectlist-bfrlist new-x))))
      :hints ('(:expand (<call>)))
      :fn pseudo-term-list-subst-gl-objects))

  (verify-guards pseudo-term-subst-gl-objects))





 


(fty::defprod cgraph-derivstate
  ((times-seen natp :rule-classes :type-prescription)
   (result-msg))
  :layout :tree)

(fty::defmap cgraph-derivstates :key-type gl-object :val-type cgraph-derivstate :true-listp t)

(define cgraph-derive-assigns-measure ((cgraph cgraph-p)
                                       (assigns cgraph-alist-p)
                                       (sts cgraph-derivstates-p)
                                       (replimit posp))
  :returns (count natp :rule-classes :type-prescription)
  :measure (len cgraph)
  (b* (((when (atom cgraph)) 0)
       ((unless (mbt (and (consp (car cgraph))
                          (gl-object-p (caar cgraph)))))
        (cgraph-derive-assigns-measure (cdr cgraph) assigns sts replimit))
       (obj (caar cgraph))
       (assignedp (hons-get obj (cgraph-alist-fix assigns)))
       ((when assignedp)
        (cgraph-derive-assigns-measure (cdr cgraph) assigns sts replimit))
       (derivstate (cdr (hons-get obj (cgraph-derivstates-fix sts))))
       ((unless derivstate)
        (+ (acl2::pos-fix replimit)
           (cgraph-derive-assigns-measure (cdr cgraph) assigns sts replimit))))
    (+ (nfix (- (acl2::pos-fix replimit)
                (cgraph-derivstate->times-seen derivstate)))
       (cgraph-derive-assigns-measure (cdr cgraph) assigns sts replimit)))
  ///
  (local (in-theory (disable (:d cgraph-derive-assigns-measure))))

  (defthm cgraph-derive-assigns-measure-of-add-assign-weak
    (<= (cgraph-derive-assigns-measure cgraph (cons (cons obj val) assigns) sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (assigns) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t))
    :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-add-assign-unseen
    (implies (and (gl-object-p obj)
                  (not (hons-assoc-equal obj assigns))
                  (not (hons-assoc-equal obj sts))
                  (hons-assoc-equal obj cgraph))
             (<= (+ (acl2::pos-fix replimit)
                    (cgraph-derive-assigns-measure cgraph (cons (cons obj val) assigns) sts replimit))
                 (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (assigns) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t))
    :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-add-assign-seen
    (implies (and (gl-object-p obj)
                  (not (hons-assoc-equal obj assigns))
                  (hons-assoc-equal obj sts)
                  (b* ((st (cdr (hons-assoc-equal obj sts))))
                    (< (cgraph-derivstate->times-seen st) (acl2::pos-fix replimit)))
                  (hons-assoc-equal obj cgraph))
             (<= (+ (acl2::pos-fix replimit)
                    (- (cgraph-derivstate->times-seen (cdr (hons-assoc-equal obj sts))))
                    (cgraph-derive-assigns-measure cgraph (cons (cons obj val) assigns) sts replimit))
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (assigns) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t))
    :rule-classes :linear)

  ;; (defthm cgraph-derive-assigns-measure-of-add-derivstate-weak
  ;;   (implies (not (cgraph-derivstate-case st :seen))
  ;;            (<= (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit)
  ;;                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;   :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
  ;;            :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;            :do-not-induct t))
  ;;   :rule-classes :linear)

  ;; (defthm cgraph-derive-assigns-measure-of-add-derivstate-unseen
  ;;   (implies (and (not (cgraph-derivstate-case st :seen))
  ;;                 (not (hons-assoc-equal obj assigns))
  ;;                 (not (hons-assoc-equal obj sts))
  ;;                 (hons-assoc-equal obj cgraph)
  ;;                 (gl-object-p obj))
  ;;            (<= (+ (acl2::pos-fix replimit)
  ;;                   (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit))
  ;;                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;   :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
  ;;            :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;            :do-not-induct t))
  ;;   :rule-classes :linear)

  ;; (defthm cgraph-derive-assigns-measure-of-add-derivstate-seen
  ;;   (implies (and (not (cgraph-derivstate-case st :seen))
  ;;                 (not (hons-assoc-equal obj assigns))
  ;;                 (hons-assoc-equal obj sts)
  ;;                 (b* ((st (cdr (hons-assoc-equal obj sts))))
  ;;                   (and (cgraph-derivstate-case st :seen)
  ;;                        (< (cgraph-derivstate->times-seen st) (acl2::pos-fix replimit))))
  ;;                 (hons-assoc-equal obj cgraph)
  ;;                 (gl-object-p obj))
  ;;            (<= (+ (acl2::pos-fix replimit)
  ;;                   (- (cgraph-derivstate->times-seen (cdr (hons-assoc-equal obj sts))))
  ;;                   (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit))
  ;;                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;   :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
  ;;            :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
  ;;            :do-not-induct t))
  ;;   :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-set-seen-weak
    (implies (not (hons-assoc-equal obj sts))
             (<= (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit)
                 (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable nfix))))
    :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-set-seen
    (implies (and (<= (cgraph-derivstate->times-seen st) (acl2::pos-fix replimit))
                  (not (hons-assoc-equal obj assigns))
                  (not (hons-assoc-equal obj sts))
                  (hons-assoc-equal obj cgraph)
                  (gl-object-p obj))
             (<= (+ (cgraph-derivstate->times-seen st)
                    (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit))
                 (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable nfix))))
    :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-update-seen-weak
    (implies (and (hons-assoc-equal obj sts)
                  (b* ((st1 (cdr (hons-assoc-equal obj sts))))
                    (<= (cgraph-derivstate->times-seen st1)
                        (cgraph-derivstate->times-seen st))))
             (<= (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit)
                 (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable nfix))))
    :rule-classes :linear)

  (defthm cgraph-derive-assigns-measure-of-update-seen
    (implies (and (<= (cgraph-derivstate->times-seen st) (acl2::pos-fix replimit))
                  (not (hons-assoc-equal obj assigns))
                  (hons-assoc-equal obj sts)
                  (b* ((st1 (cdr (hons-assoc-equal obj sts))))
                    (and (< (cgraph-derivstate->times-seen st1)
                            (acl2::pos-fix replimit))
                         (<= (cgraph-derivstate->times-seen st1)
                             (cgraph-derivstate->times-seen st))))
                  (hons-assoc-equal obj cgraph)
                  (gl-object-p obj))
             (<= (+ (cgraph-derivstate->times-seen st)
                    (- (cgraph-derivstate->times-seen (cdr (hons-assoc-equal obj sts))))
                    (cgraph-derive-assigns-measure cgraph assigns (cons (cons obj st) sts) replimit))
                 (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :hints (("goal" :induct (cgraph-derive-assigns-measure cgraph assigns sts replimit)
             :expand ((:free (sts) (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
             :do-not-induct t))
    :rule-classes :linear)

  (local (defthm cgraph-fix-when-bad-car
           (implies (not (and (consp (car x))
                              (gl-object-p (caar x))))
                    (equal (cgraph-fix x)
                           (cgraph-fix (cdr x))))
           :hints(("Goal" :in-theory (enable cgraph-fix))))))

(fty::defprod candidate-assign
  ((edge cgraph-edge-p)
   (val))
  :layout :tree)

(fty::deflist candidate-assigns :elt-type candidate-assign :true-listp t)

;; (fty::defprod edge-errmsg
;;   ((edge cgraph-edge-p)
;;    (msg))
;;   :layout :tree)

;; (fty::deflist edge-errors :elt-type edge-errmsg :true-listp t)

(define candidate-assigns->vals ((x candidate-assigns-p))
  (if (atom x)
      nil
    (cons (candidate-assign->val (car x))
          (candidate-assigns->vals (cdr x)))))

(define combine-error-messages1 ((errors consp))
  (cond ((atom (cdr errors)) (msg "~@0~%" (car errors)))
        (t (msg "~@0~% * ~@1" (car errors)
                (combine-error-messages1 (cdr errors))))))

(define combine-error-messages (errors)
  (cond ((atom errors) nil)
        ((atom (cdr errors)) (msg "~@0~%" (car errors)))
        (t (msg "~% * ~@0" (combine-error-messages1 errors)))))


(define cgraph-set-error ((x gl-object-p)
                          (msg)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (gl-object-fix x))
       (sts (cgraph-derivstates-fix sts))
       (st (cdr (hons-get x sts)))
       ((unless st)
        (hons-acons x (make-cgraph-derivstate :times-seen 0 :result-msg msg) sts)))
    (hons-acons x (change-cgraph-derivstate st :result-msg msg) sts))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear))

(define cgraph-incr-seen ((x gl-object-p)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (gl-object-fix x))
       (sts (cgraph-derivstates-fix sts))
       (st (cdr (hons-get x sts)))
       ((unless st)
        (hons-acons x (make-cgraph-derivstate :times-seen 1) sts)))
    (hons-acons x (change-cgraph-derivstate st :times-seen (+ 1 (cgraph-derivstate->times-seen st)))
                sts))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>-weak
    (<= (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear)

  (defret cgraph-derive-assigns-measure-of-<fn>-unseen
    (implies (and (not (hons-assoc-equal (gl-object-fix x) sts))
                  (hons-assoc-equal (gl-object-fix x) cgraph)
                  (not (hons-assoc-equal (gl-object-fix x) assigns)))
             (< (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :rule-classes :linear)

  (defret cgraph-derive-assigns-measure-of-<fn>-seen
    (implies (and (< (cgraph-derivstate->times-seen (cdr (hons-assoc-equal (gl-object-fix x) sts)))
                     (acl2::pos-fix replimit))
                  (hons-assoc-equal (gl-object-fix x) cgraph)
                  (not (hons-assoc-equal (gl-object-fix x) assigns)))
             (< (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :rule-classes :linear))
    


(define cgraph-summarize-errors-and-assign ((x gl-object-p)
                                            errors
                                            (cands candidate-assigns-p)
                                            (assigns cgraph-alist-p)
                                            (sts cgraph-derivstates-p))
  :returns (mv (new-assigns cgraph-alist-p)
               (new-sts cgraph-derivstates-p))
  (b* ((vals (remove-duplicates-equal (candidate-assigns->vals cands)))
       (cand-summary (cond ((atom vals) "No assignment succeeded")
                           ((atom (cdr vals)) nil)
                           (t "Multiple conflicting assignments")))
       (error-summary (combine-error-messages errors))
       (summary (if cand-summary
                    (if error-summary
                        (msg "~@0: ~@1" cand-summary error-summary)
                      cand-summary)
                  error-summary))
       (assigns (cgraph-alist-fix assigns))
       (assigns (if (consp vals)
                    (hons-acons (gl-object-fix x) (car vals) assigns)
                  assigns))
       (sts (cgraph-set-error x summary sts)))
    (mv assigns sts))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear))





(local (defthm bfr-varname-p-of-get-term->bvar$a
         (implies (and (equal (bfr-nvars) (next-bvar$a bvar-db))
                       (get-term->bvar$a x bvar-db))
                  (bfr-varname-p (get-term->bvar$a x bvar-db)))
         :hints(("Goal" :in-theory (enable bfr-varname-p)))))

(defines cgraph-derive-assignments
  (define cgraph-derive-assignments-obj ((x gl-object-p)
                                         (assigns cgraph-alist-p)
                                         (sts cgraph-derivstates-p)
                                         (env$)
                                         (cgraph cgraph-p)
                                         (replimit posp)
                                         &optional
                                         (logicman 'logicman)
                                         (bvar-db 'bvar-db)
                                         (state 'state))
    :guard (and (lbfr-listp (gl-object-bfrlist x))
                (bfr-env$-p env$ logicman)
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    :returns (mv (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :well-founded-relation acl2::nat-list-<
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   0
                   0)
    :verify-guards nil
    (b* ((x (gl-object-fix x))
         (assigns (cgraph-alist-fix assigns))
         (sts (cgraph-derivstates-fix sts))
         (cgraph (cgraph-fix cgraph))
         (assigns-look (hons-get x assigns))
         ((when assigns-look)
          (mv assigns sts))
         ((cgraph-derivstate st)
          (or (cdr (hons-get x sts)) '(0)))
         ((when (<= (lposfix replimit) st.times-seen))
          (mv assigns sts))
         ((when (gl-object-variable-free-p x))
          (b* (((mv err val) (magic-gl-object-eval x env$))
               ((when err)
                (b* ((sts (cgraph-set-error x
                                            (msg "Failed to evaluate the object: ~@0"
                                                 (if* (eq err t) "(no msg)" err))
                                            sts)))
                  (mv assigns sts)))
               (assigns (hons-acons x val assigns)))
            (mv assigns sts)))
         (bvar (get-term->bvar x bvar-db))
         ((when bvar)
          (b* ((val (bfr-eval-fast (bfr-var bvar) env$ logicman))
               (assigns (hons-acons x val assigns)))
            (mv assigns sts)))

         (edges (cdr (hons-get x cgraph)))
         ((unless edges)
          (b* ((sts (cgraph-set-error x
                                      "No rules for deriving the value of the object"
                                      sts)))
            (mv assigns sts)))
         (sts (cgraph-incr-seen x sts))

         ((mv errors candidate-assigns assigns sts)
          (cgraph-derive-assignments-edges edges assigns sts env$ cgraph replimit)))

      (cgraph-summarize-errors-and-assign x errors candidate-assigns assigns sts)))

  (define cgraph-derive-assignments-edges ((x cgraph-edgelist-p)
                                           (assigns cgraph-alist-p)
                                           (sts cgraph-derivstates-p)
                                           (env$)
                                           (cgraph cgraph-p)
                                           (replimit posp)
                                           &optional
                                           (logicman 'logicman)
                                           (bvar-db 'bvar-db)
                                           (state 'state))
    :guard (and (lbfr-listp (cgraph-edgelist-bfrlist x))
                (bfr-env$-p env$ logicman)
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))

    :returns (mv errors
                 (cands candidate-assigns-p)
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   9
                   (len x))
    (b* (((when (atom x)) (mv nil nil
                              (cgraph-alist-fix assigns)
                              (cgraph-derivstates-fix sts)))
         ((mv err cand1 new-assigns new-sts)
          (cgraph-derive-assignments-edge (car x) assigns sts env$ cgraph replimit))
         ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                           (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
          (mv nil nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ((mv rest-errs rest-cands assigns sts)
          (cgraph-derive-assignments-edges (cdr x) new-assigns new-sts env$ cgraph replimit)))
      (if err
          (mv (cons err rest-errs) rest-cands assigns sts)
        (mv rest-errs
            (cons cand1 rest-cands) assigns sts))))

  (define cgraph-derive-assignments-edge ((x cgraph-edge-p)
                                          (assigns cgraph-alist-p)
                                          (sts cgraph-derivstates-p)
                                          (env$)
                                          (cgraph cgraph-p)
                                          (replimit posp)
                                          &optional
                                          (logicman 'logicman)
                                          (bvar-db 'bvar-db)
                                          (state 'state))
    :returns (mv errmsg
                 (cand (implies (not errmsg)
                                (candidate-assign-p cand)))
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   8
                   0)
    :guard (and (lbfr-listp (cgraph-edge-bfrlist x))
                (bfr-env$-p env$ logicman)
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* (((cgraph-edge x))
         ((mv match-subst assigns sts)
          (cgraph-derive-assignments-matches x.match-vars x.rule x.subst
                                              assigns sts env$ cgraph replimit))
         ((unless match-subst)
          ;; BOZO It would kind of make sense to produce a real error message
          ;; here, but then we'd get not just the root cause of a given error,
          ;; but tons of messages about its various consequences.
          (mv t nil assigns sts))
         ((ctrex-rule x.rule))
         ((mv err val)
          (magitastic-ev x.rule.assign match-subst 1000 state t t))
         ((when err)
          (mv (msg "Failed to evaluate assignment ~x0 from rule ~x1"
                   x.rule.assign x.rule.name)
              nil assigns sts)))
      (mv nil (make-candidate-assign :edge x :val val) assigns sts)))
               
  (define cgraph-derive-assignments-matches ((x pseudo-var-list-p)
                                             (rule ctrex-rule-p)
                                             (subst gl-object-bindings-p)
                                             (assigns cgraph-alist-p)
                                             (sts cgraph-derivstates-p)
                                             (env$)
                                             (cgraph cgraph-p)
                                             (replimit posp)
                                             &optional
                                             (logicman 'logicman)
                                             (bvar-db 'bvar-db)
                                             (state 'state))
    :returns (mv (match-subst symbol-alistp)
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   7
                   (len x))
    :guard (and (lbfr-listp (gl-object-bindings-bfrlist subst))
                (bfr-env$-p env$ logicman)
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* (((when (atom x))
          (mv nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ((mv ok val new-assigns new-sts)
          (cgraph-derive-assignments-match (car x) rule subst
                                           assigns sts env$ cgraph replimit))
         ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                           (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
          (mv nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ((mv rest assigns sts)
          (cgraph-derive-assignments-matches (cdr x) rule subst
                                             new-assigns new-sts env$ cgraph replimit)))
      (mv (if ok
              (cons (cons (pseudo-var-fix (car x)) val) rest)
            rest)
          assigns sts)))

  (define cgraph-derive-assignments-match ((x pseudo-var-p)
                                           (rule ctrex-rule-p)
                                           (subst gl-object-bindings-p)
                                           (assigns cgraph-alist-p)
                                           (sts cgraph-derivstates-p)
                                           (env$)
                                           (cgraph cgraph-p)
                                           (replimit posp)
                                           &optional
                                           (logicman 'logicman)
                                           (bvar-db 'bvar-db)
                                           (state 'state))
    :returns (mv ok val
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   6
                   0)
    :guard (and (lbfr-listp (gl-object-bindings-bfrlist subst))
                (bfr-env$-p env$ logicman)
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* (((ctrex-rule rule))
         (term (cdr (assoc (pseudo-var-fix x) rule.match)))
         (obj (pseudo-term-subst-gl-objects term subst))
         ((mv assigns sts)
          (cgraph-derive-assignments-obj obj assigns sts env$ cgraph replimit))
         (assigns-look (hons-get obj assigns)))
      (if assigns-look
          (mv t (cdr assigns-look) assigns sts)
        (mv nil nil assigns sts))))

  ///
  (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (defret-mutual measure-decr-of-cgraph-derive-assigns
    (defret measure-decr-of-<fn>
      (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
          (cgraph-derive-assigns-measure cgraph assigns sts replimit))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn cgraph-derive-assignments-obj)
    (defret measure-decr-of-<fn>
      (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
          (cgraph-derive-assigns-measure cgraph assigns sts replimit))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn cgraph-derive-assignments-edges)
    (defret measure-decr-of-<fn>
      (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
          (cgraph-derive-assigns-measure cgraph assigns sts replimit))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn cgraph-derive-assignments-edge)
    (defret measure-decr-of-<fn>
      (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
          (cgraph-derive-assigns-measure cgraph assigns sts replimit))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn cgraph-derive-assignments-matches)
    (defret measure-decr-of-<fn>
      (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
          (cgraph-derive-assigns-measure cgraph assigns sts replimit))
      :hints ('(:expand (<call>)))
      :rule-classes :linear
      :fn cgraph-derive-assignments-match))

  (verify-guards cgraph-derive-assignments-obj-fn
    :hints (("goal" :Expand ((cgraph-edgelist-bfrlist x))))))


(defines gl-object-vars
  (define gl-object-vars ((x gl-object-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    :verify-guards nil
    (gl-object-case x
      :g-var (add-to-set-eq x.name (pseudo-var-list-fix acc))
      :g-apply (gl-objectlist-vars x.args acc)
      :g-ite (gl-object-vars x.test (gl-object-vars x.then (gl-object-vars x.else acc)))
      :g-cons (gl-object-vars x.car (gl-object-vars x.cdr acc))
      :g-map (gl-object-alist-vars x.alist acc)
      :otherwise (pseudo-var-list-fix acc)))

  (define gl-objectlist-vars ((x gl-objectlist-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    (if (atom x)
        (pseudo-var-list-fix acc)
      (gl-objectlist-vars (cdr x) (gl-object-vars (car x) acc))))

  (define gl-object-alist-vars ((x gl-object-alist-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    (if (atom x)
        (pseudo-var-list-fix acc)
      (gl-object-alist-vars (cdr x)
                            (if (mbt (consp (car x)))
                                (gl-object-vars (cdar x) acc)
                              acc))))
  ///
  (verify-guards gl-object-vars)

  (local (defthm gl-object-alist-fix-when-bad-car
           (implies (and (consp x) (not (Consp (car x))))
                    (equal (gl-object-alist-fix x)
                           (gl-object-alist-fix (cdr x))))
           :hints(("Goal" :in-theory (enable gl-object-alist-fix)))))

  (fty::deffixequiv-mutual gl-object-vars))

