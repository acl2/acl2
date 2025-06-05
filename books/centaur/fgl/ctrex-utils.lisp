; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "sat-stub")
(include-book "interp-st-bfrs-ok")
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "magitastic-ev")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "unify-thms"))
(local (in-theory (disable resize-list)))
(local (std::add-default-post-define-hook :fix))
(set-state-ok t)


;; ------------------------------------------------------------------------
;; Miscellaneous helper functions
;; ------------------------------------------------------------------------

(define env->env$ ((x fgl-env-p) logicman)
  :guard (stobj-let ((aignet (logicman->aignet logicman)))
                    (ok)
                    (eql (aignet::num-regs aignet) 0)
                    ok)
  (b* ((bfrstate (logicman->bfrstate))
       ((fgl-env x))
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
  :guard (bfr-env$-p env$ (logicman->bfrstate))
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
  :guard (bfr-env$-p env$ (logicman->bfrstate))
  :returns (vals boolean-listp)
  (if (atom x)
      nil
    (cons (bfr-eval-fast (car x) env$)
          (bfr-list-eval-fast (cdr x) env$))))










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

;;   The "smarter" version: we create a "cgraph" with an "edge" B->{A0..AN}
;;   whenever obtaining values for Ai might help derive a value for B (via one
;;   of the counterexample translation rules). Edges are labeled with the rule
;;   and substitution that gives rise to that derivation.  Often B is an
;;   immediate subterm of the Ai (as in elimination rules, below), but this
;;   isn't always the case.  To get a variable-level counterexample, we then
;;   traverse the cgraph depth-first starting from the variables, trying to
;;   find a value for each term after finding values for all of its
;;   descendants.

;;   If there are any SCCs containing
;;   multiple terms in the graph, then we try to recover a value for each term
;;   in arbitrary order and check whether we get to a fixpoint.

;; Cgraph representation -- see also cgraph.lisp, particularly the xdoc for cgraph.

;; The cgraph maps nodes to formulas, each of which has other nodes as
;; dependencies.  A formula says how to compute a value for the target node in
;; terms of the dependency values, and how to determine whether it was
;; successful and how "good" (priority) the value was.

;;   Rule types.

;;   We consider a few different types of rules for computing variable values
;;   from bit-level counterexamples.  Note that none of these require proof;
;;   all of this is a purely heuristic process.

;;   The basic idea for any rule is that it should add certain nodes and
;;   multiedges, or perhaps update existing multiedges, in the graph based on
;;   nodes that already exist (starting with a node for each term bound in the
;;   bvar-db). For each multiedge B -> {Ai}, we can either derive a complete
;;   value for B from the values for Ai, or an update to the value of B. That
;;   means when we evaluate the counterexample, we'll try to derive values for
;;   Ai and then use them to update/derive B. Each node (FGL object) can be
;;   mapped to multiple multiedges; these can either be compatible updates or
;;   conflicting derivations. Each multiedge needs to say what its destination
;;   nodes are and how to assign a value to the source object given some or all
;;   of those values.

;;  - Implicit rule: A function call (foo x0..xn) can be considered to have a
;;    multiedge (foo x0..xn) -> {x0..xn}, such that if we can derive the xi, we
;;    can derive the function call.  However, these should be considered lower
;;    priority and we need to take care that we don't get confused by loops --
;;    e.g. elimination rules (below) will go in the opposite direction and
;;    should be considered higher priority.

;;
;;  - Elimination rules.  These are basically destructor elimination rules, of the form
;;      (implies (pred x) (equiv (ctor (acc1 x) ... (accn x)) x))
;;    Whenever a node (acci y) is found in the graph, we add a multiedge y -> {(acci y)}, or
;;    if there already exists such a multiedge based on the same rule with a compatible substitution, add the (acci y) destination
;;    to that multiedge.
;;    Note we expect to sometimes see an incomplete set of such edges
;;    (e.g. (acc1 x) exists but (acc2 x) doesn't) and we'll need to choose a default value for the missing terms.
;;    Hypotheses in these rules are currently ignored.

;;  - Property rules.  These are somewhat similar to elimination rules but
;;    allow for constructs like maps, alists, etc.  For example: (equal (s key
;;    (g key x) x) x) Such a rule produces edges x -> {(g key x)} for every
;;    occurrence of (g key x) in the cgraph.  Note it might sometimes make
;;    sense to add non-theorems like: (equal (cons (cons key (cdr (assoc key
;;    x))) x) x). It is expected that several property rule edges can be
;;    applied in any order to update the value of their source node and still
;;    yield a sensible value.

;;  - Equivalence rules (implicit): anytime we see an equivalence (equiv a b)
;;    we'll add two edges a->b and b->a.  Whichever of a or b we're able to
;;    resolve first will determine the value of the other, provided the
;;    equivalence is assigned T.

;;  - Fixup rules: these are intended to patch the assigned value of some object after
;;    it has been assigned something by other rules.

;; A counterexample rule has two functions: it is used to make the cgraph from
;; the bvar-db, without reference to any particular Boolean assignment, and
;; then it is used as part of the cgraph when trying to derive values for a
;; particular assignment.

;; When creating the cgraph, we start with an object stored in the Boolean
;; variable database and find any counterexample rules that have a match for
;; that object.  E.g., perhaps the object is (intcar (intcdr a)) and we match
;; it against the rule intcar-intcdr-ctrex-elim, below.  This means we'll make
;; an edge
;;   (intcdr a) -> (intcar (intcdr a))
;; where the edge is labelled with the rule, the match variable CAR (the var of
;; the rule corresponding to the term that matched) and the substitution
;;  ((x . (intcdr a))).

;; If we also find (intcdr (intcdr a)), then we'll match on the other matchvar
;; (cdr) of the same rule.  When this happens, we'll end up joining the two
;; compatible applications of the rule on the same edge structure, essentially
;; making two edges with the same label.

;; More generally, we can have rules that are hung on some relation between
;; subterms.  Suppose we have a rule of this form:

;; (def-ctrex-rule foo-ctrex-rule
;;   :match ((v (foo a b)))
;;   :assign (bar b)
;;   :assigned-var a
;;   :ruletype :property)

;; If we come across a term (foo (g d) (h e)) while creating the counterexample graph,
;; we'll add an edge (g d) -> (foo (g d) (h e)) labeled with
;;  (v, foo-ctrex-rule, ((a . (g d)) (b . (h e)))).

;; Problem: By doing this, we're saying "derive a value for (foo (g d) (h e))
;; in order to derive a value for (g d)".  But we're also going to need a value
;; for (h e) in order to apply this rule.  So when we traverse the graph, we'll
;; implicitly end up looking for a value for (h e) when we try and apply this
;; rule -- sort of an edge for an edge.




(defxdoc fgl-counterexample-implementation-details
  :short "Parent topic for implementation specifics of FGL counterexample generation"
  :parents (fgl-counterexamples))



;; ------------------------------------------------------------------------
;; Creating a cgraph from rules.
;; See main function FGL-OBJECT-ADD-TO-CGRAPH, below
;; ------------------------------------------------------------------------

(fty::deflist ctrex-rulelist :elt-type ctrex-rule :true-listp t)

(fty::defmap ctrex-ruletable :key-type pseudo-fnsym :val-type ctrex-rulelist :true-listp t)

(define ctrex-rulelist-bfr-free ((x ctrex-rulelist-p))
  (if (atom x)
      t
    (and (not (fgl-object-bindings-bfrlist (ctrex-rule->unify-subst (car x))))
         (ctrex-rulelist-bfr-free (cdr x))))
  ///
  (defthm ctrex-rulelist-bfr-free-implies
    (implies (ctrex-rulelist-bfr-free x)
             (and (equal (fgl-object-bindings-bfrlist (ctrex-rule->unify-subst (car x))) nil)
                  (ctrex-rulelist-bfr-free (cdr x))))))

(define ctrex-ruletable-bfr-free ((x ctrex-ruletable-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (pseudo-fnsym-p (caar x)))))
             (ctrex-rulelist-bfr-free (cdar x)))
         (ctrex-ruletable-bfr-free (cdr x))))
  ///
  (defthm ctrex-ruletable-bfr-free-implies
    (implies (ctrex-ruletable-bfr-free x)
             (and (implies (pseudo-fnsym-p (caar x))
                           (ctrex-rulelist-bfr-free (cdar x)))
                  (ctrex-ruletable-bfr-free (cdr x)))))

  (defthm ctrex-ruletable-bfr-free-implies-lookup
    (implies (and (ctrex-ruletable-bfr-free x)
                  (pseudo-fnsym-p fn))
             (ctrex-rulelist-bfr-free (cdr (hons-assoc-equal fn x)))))

  (local (in-theory (enable ctrex-ruletable-fix))))







;; (defconst *cgraph-equiv-edge-template*
;;   (make-cgraph-edge
;;    :deps nil ;; filled in per instance -- key name should be EQUIV for the equivalence itself, X for the candidate equivalent object
;;    :name 'fake-cgraph-formula-for-equiv
;;    :dep-success-vars nil ;; not used for equivalences
;;    :success 'equiv ;; different for equivalences
;;    :value nil ;; different for equivalences
;;    :priority ''0 ;; different for equivalences
;;    :order *ctrex-order-first*
;;    :ruletype :equiv))

(defconst *cgraph-implicit-edge-template*
  (make-cgraph-formula
   :deps nil ;; filled in per instance
   :name 'fake-cgraph-formula-for-implicit
   :dep-success-vars nil ;; filled in per instance
   :success nil ;; filled in per instance
   :value nil ;; filled in per instance
   :priority ''0 ;; lowest
   :order (1- *ctrex-order-last*) ;; late but not as late as fixups
   :ruletype :implicit))


(local (defthm true-listp-when-cgraph-formulalist-p-rw
         (implies (cgraph-formulalist-p x)
                  (true-listp x))))

(local (defthm cgraph-formulalist-p-of-cgraph-formula-insert
         (implies (and (cgraph-formula-p x)
                       (cgraph-formulalist-p lst))
                  (cgraph-formulalist-p (cgraph-formula-insert x lst)))
         :hints(("Goal" :in-theory (enable cgraph-formula-insert)))))

(local (defthm cgraph-formulalist-bfrlist-of-cgraph-formula-insert
         (implies (and (not (member v (cgraph-formula-bfrlist x)))
                       (not (member v (cgraph-formulalist-bfrlist lst))))
                  (not (member v (cgraph-formulalist-bfrlist (cgraph-formula-insert x lst)))))
         :hints(("Goal" :in-theory (enable cgraph-formula-insert
                                           cgraph-formulalist-bfrlist)))))

(define add-cgraph-formula ((target fgl-object-p)
                            (formula cgraph-formula-p)
                            (cgraph cgraph-p))
  :returns (new-cgraph cgraph-p)
  (b* ((target (fgl-object-fix target))
       (formula (cgraph-formula-fix formula))
       (cgraph (cgraph-fix cgraph))
       (outedges (cdr (hons-get target cgraph)))
       ((unless outedges)
        (hons-acons target (cgraph-outedges (list formula) nil) cgraph))
       ((cgraph-outedges outedges))
       ((when (member-equal formula outedges.formulas)) cgraph))
    (hons-acons target (cgraph-outedges (cgraph-formula-insert formula outedges.formulas) outedges.equivs) cgraph))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (not (member v (cgraph-formula-bfrlist formula)))
                  (not (member v (cgraph-bfrlist cgraph))))
             (not (member v (cgraph-bfrlist new-cgraph))))
    :hints(("Goal" :in-theory (e/d (cgraph-bfrlist
                                    cgraph-formulalist-bfrlist))))))

(define add-cgraph-equiv1 ((target fgl-object-p)
                           (equiv fgl-object-p)
                           (other fgl-object-p)
                           (cgraph cgraph-p))
  :returns (new-cgraph cgraph-p)
  (b* ((cgraph (cgraph-fix cgraph))
       ((when (fgl-object-variable-free-p target))
        cgraph)
       (target (fgl-object-fix target))
       (node (cgraph-equivnode equiv other))
       (outedges (cdr (hons-get target (cgraph-fix cgraph))))
       (new-outedges (if outedges
                         (change-cgraph-outedges
                          outedges
                          :equivs (cons node (cgraph-outedges->equivs outedges)))
                       (cgraph-outedges nil (list node)))))
    (hons-acons target new-outedges cgraph))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bfrlist equiv)))
                  (not (member v (fgl-object-bfrlist other)))
                  (not (member v (cgraph-bfrlist cgraph))))
             (not (member v (cgraph-bfrlist new-cgraph))))))

(define add-cgraph-equiv ((equiv fgl-object-p)
                          (a fgl-object-p)
                          (b fgl-object-p)
                          (cgraph cgraph-p))
  :returns (new-cgraph cgraph-p)
  (add-cgraph-equiv1 a equiv b (add-cgraph-equiv1 b equiv a cgraph))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bfrlist equiv)))
                  (not (member v (fgl-object-bfrlist a)))
                  (not (member v (fgl-object-bfrlist b)))
                  (not (member v (cgraph-bfrlist cgraph))))
             (not (member v (cgraph-bfrlist new-cgraph))))))


(local (defthm character-listp-of-explode-nonneg
         (implies (character-listp acc)
                  (character-listp (explode-nonnegative-integer n 10 acc)))))


(local
 (encapsulate nil
   (local (in-theory (disable floor mod)))
   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (defthm has-digit-p-of-explode-nonneg
     (implies (or (intersectp-equal '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9) acc)
                  (not acc))
              (intersectp-equal '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                (explode-nonnegative-integer n 10 acc))))

   (defthmd pseudo-var-p-by-has-digit
     (implies (and (symbolp x)
                   (intersectp-equal '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9) (coerce (symbol-name x) 'list)))
              (pseudo-var-p x)))))


(define make-argvars ((stem stringp) (n natp) (acc pseudo-var-list-p))
  :returns (vars pseudo-var-list-p)
  :prepwork ((local (in-theory (e/d (pseudo-var-p-by-has-digit)
                                    (explode-nonnegative-integer)))))
  (if (zp n)
      (pseudo-var-list-fix acc)
    (make-argvars stem (1- n) (cons (intern-in-package-of-symbol
                                     (concatenate 'string stem (coerce (explode-atom (1- n) 10) 'string)) 'fgl-pkg)
                                    acc)))
  ///
  (defret len-of-<fn>
    (equal (len vars) (+ (nfix n) (len acc)))))




(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

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
  (defthm fgl-object-bindings-p-of-pairlis-vars
    (implies (fgl-objectlist-p args)
             (fgl-object-bindings-p (pairlis-vars x args))))

  (local (in-theory (disable symbol-listp symbol-listp-when-pseudo-var-list-p)))

  (defthm fgl-object-bindings-bfrlist-of-pairlis-vars
    (implies (not (member v (fgl-objectlist-bfrlist args)))
             (not (member v (fgl-object-bindings-bfrlist (pairlis-vars x args)))))))



(local (defthm assoc-is-hons-assoc-equal
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(defines pseudo-term-subst-fgl-objects
  (define pseudo-term-subst-fgl-objects ((x pseudo-termp)
                                        (alist fgl-object-bindings-p))
    :returns (new-x fgl-object-p)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :const (g-concrete x.val)
      :var (cdr (assoc x.name (fgl-object-bindings-fix alist)))
      :fncall (g-apply x.fn (pseudo-term-list-subst-fgl-objects x.args alist))
      :lambda (pseudo-term-subst-fgl-objects
               x.body
               (pairlis-vars x.formals
                             (pseudo-term-list-subst-fgl-objects x.args alist)))))
  (define pseudo-term-list-subst-fgl-objects ((x pseudo-term-listp)
                                             (alist fgl-object-bindings-p))
    :returns (new-x fgl-objectlist-p)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (hons (pseudo-term-subst-fgl-objects (car x) alist)
            (pseudo-term-list-subst-fgl-objects (cdr x) alist))))
  ///
  (defthm len-of-pseudo-term-list-subst-fgl-objects
    (equal (len (pseudo-term-list-subst-fgl-objects x alist))
           (len x))
    :hints(("Goal" :in-theory (enable len))))

  (defret-mutual fgl-object-bfrlist-of-pseudo-term-subst-fgl-objects
    (defret fgl-object-bfrlist-of-<fn>
      (implies (not (member v (fgl-object-bindings-bfrlist alist)))
               (not (member v (fgl-object-bfrlist new-x))))
      :hints ('(:expand (<call>)))
      :fn pseudo-term-subst-fgl-objects)
    (defret fgl-objectlist-bfrlist-of-<fn>
      (implies (not (member v (fgl-object-bindings-bfrlist alist)))
               (not (member v (fgl-objectlist-bfrlist new-x))))
      :hints ('(:expand (<call>)))
      :fn pseudo-term-list-subst-fgl-objects))

  (verify-guards pseudo-term-subst-fgl-objects)

  (fty::deffixequiv-mutual pseudo-term-subst-fgl-objects))


(define pseudo-term-subst-subst-fgl-objects ((x pseudo-term-subst-p)
                                             (alist fgl-object-bindings-p))
  :returns (new-x fgl-object-bindings-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (pseudo-term-subst-fgl-objects (cdar x) alist))
              (pseudo-term-subst-subst-fgl-objects (cdr x) alist))
      (pseudo-term-subst-subst-fgl-objects (cdr x) alist)))
  ///
  (defret fgl-object-bindings-bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bindings-bfrlist alist)))
             (not (member v (fgl-object-bindings-bfrlist new-x)))))
  (local (in-theory (enable pseudo-term-subst-fix))))



;; (encapsulate nil
;;   (make-event
;;    (let ((wrld (w state))
;;          (fn 'fgl-unify-term/gobj-fn))
;;      `(flag::make-flag ,(flag::flag-fn-name fn wrld) ,fn
;;                        :defthm-macro-name ,(flag::flag-defthm-macro fn wrld)
;;                        :flag-mapping ,(acl2::alist-to-doublets (flag::flag-alist fn wrld))
;;                        :local t
;;                        :hints ((and stable-under-simplificationp
;;                                     '(:expand ((pseudo-term-count pat)
;;                                                (pseudo-term-list-count (pseudo-term-call->args pat))
;;                                                (pseudo-term-list-count (cdr (pseudo-term-call->args pat))))))))))

;;   (local (defthm fgl-object-bfrlist-of-mk-g-boolean
;;            (equal (fgl-object-bfrlist (mk-g-boolean bit))
;;                   (if (booleanp bit) nil (list bit)))
;;            :hints(("Goal" :in-theory (enable mk-g-boolean)))))

;;   (local (defthm fgl-object-bfrlist-of-gobj-syntactic-boolean-negate
;;            (implies (not (member v (fgl-object-bfrlist x)))
;;                     (not (member v (fgl-object-bfrlist (gobj-syntactic-boolean-negate x)))))
;;            :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-negate bfr-negate)))))

;;   (local (defthm fgl-object-bfrlist-of-gobj-syntactic-boolean-fix
;;            (implies (not (member v (fgl-object-bfrlist x)))
;;                     (not (member v (fgl-object-bfrlist (gobj-syntactic-boolean-fix x)))))
;;            :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix)))))
  
;;   (std::defretgen bfr-vars-of-<fn>
;;     :formal-hyps
;;     (((fgl-object-bindings-p alist)    (not (member v (fgl-object-bindings-bfrlist alist))))
;;      ((fgl-object-p x)                 (not (member v (fgl-object-bfrlist x))))
;;      ((fgl-objectlist-p x)             (not (member v (fgl-objectlist-bfrlist x))))
;;      ((fgl-object-alist-p x)           (not (member v (fgl-object-alist-bfrlist x)))))
;;     :rules ((t (:add-concl (not (member v (fgl-object-bindings-bfrlist new-alist)))))
;;             (:mutrec
;;              (:add-keyword
;;               :hints ('(:expand ((:free (x-key) <call>))))))
;;             (:recursive
;;              (:add-keyword
;;               :hints (("goal" :induct <call>
;;                        :in-theory (enable (:i <fn>))
;;                        :expand ((:free (x) <call>)))))))
;;     :functions fgl-unify-fnset))



(define ctrex-rule-to-formula ((match-obj fgl-object-p)
                            (rule ctrex-rule-p)
                            (bfrstate bfrstate-p))
  :guard (bfr-listp (fgl-object-bfrlist match-obj))
  :returns (mv ok (target fgl-object-p) (formula (implies ok (cgraph-formula-p formula))))
  (b* (((ctrex-rule rule))
       ((mv ok bindings) (fgl-unify-term/gobj rule.match match-obj rule.unify-subst))
       ((unless ok) (mv nil nil nil))
       (target (pseudo-term-subst-fgl-objects rule.target bindings))
       (deps (pseudo-term-subst-subst-fgl-objects rule.deps bindings)))
    (mv t
        target
        (make-cgraph-formula
         :deps deps
         :name rule.name
         :dep-success-vars rule.dep-success-vars
         :success          rule.success
         :priority         rule.priority
         :value            rule.value
         :order            rule.order
         :ruletype         rule.ruletype)))
  ///
  (defret bfr-listp-cgraph-formula-bfrlist-of-<fn>
    (implies (and (bfr-listp (fgl-object-bfrlist match-obj))
                  (bfr-listp (fgl-object-bindings-bfrlist (ctrex-rule->unify-subst rule))))
             (and (bfr-listp (fgl-object-bfrlist target))
                  (implies ok
                           (and (bfr-listp (fgl-object-bindings-bfrlist (cgraph-formula->deps formula)))
                                (bfr-listp (cgraph-formula-bfrlist formula))))))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))

;; (local (defthm bfrs-of-cgraph-formula->deps
;;          (implies (not (member v (cgraph-formula-bfrlist x)))
;;                   (not (member v (fgl-object-bindings-bfrlist (cgraph-formula->deps x)))))
;;          :hints(("Goal" :in-theory (enable cgraph-formula-bfrlist)))))


(define fgl-object-bindings-count ((x fgl-object-bindings-p))
  :returns (count posp :rule-classes :type-prescription)
  (if (atom x)
      1
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (+ 1 (fgl-object-count (cdar x))
           (fgl-object-bindings-count (cdr x)))
      (fgl-object-bindings-count (cdr x))))
  ///
  (defret fgl-object-bindings-count-of-pairlis$
    (implies (and (pseudo-var-list-p keys)
                  (equal (len keys) (len vals)))
             (equal (fgl-object-bindings-count (pairlis$ keys vals))
                    (fgl-objectlist-count vals)))
    :hints(("Goal" :in-theory (enable pairlis$ fgl-objectlist-count))))

  (defret fgl-object-bindings-count-linear
    (implies (and (consp (car x))
                  (pseudo-var-p (caar x)))
             (= (fgl-object-bindings-count x)
                (+ 1 (fgl-object-count (cdar x))
                   (fgl-object-bindings-count (cdr x)))))
    :rule-classes :linear)

  (defret fgl-object-bindings-count-cdr
    (<= (fgl-object-bindings-count (cdr x)) (fgl-object-bindings-count x))
    :rule-classes :linear)

  ;; (defret fgl-object-bindings-count-cdr-strong
  ;;   (implies (consp x)
  ;;   (<= (fgl-object-bindings-count (cdr x)) (fgl-object-bindings-count x))
  ;;   :rule-classes :linear)

  (local (in-theory (enable fgl-object-bindings-fix))))

(local (defthm fgl-object-bindings-count-of-g-ite
         (implies (fgl-object-case x :g-ite)
                  (equal (fgl-object-bindings-count (list (cons 'arg0 (g-ite->test x))
                                                          (cons 'arg1 (g-ite->then x))
                                                          (cons 'arg2 (g-ite->else x))))
                         (fgl-object-count x)))
         :hints (("goal" :in-theory (enable fgl-object-count
                                            fgl-object-bindings-count)))))

(local (defthm fgl-object-bindings-count-of-g-cons
         (implies (fgl-object-case x :g-cons)
                  (equal (fgl-object-bindings-count (list (cons 'arg0 (g-cons->car x))
                                                          (cons 'arg1 (g-cons->cdr x))))
                         (fgl-object-count x)))
         :hints (("goal" :in-theory (enable fgl-object-count
                                            fgl-object-bindings-count)))))



(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

;; (local (defthm len-of-cons
;;          (equal (len (cons a b))
;;                 (+ 1 (len b)))))

;; (local (defun len-is (x n)
;;          (if (zp n)
;;              (and (eql n 0) (atom x))
;;            (and (consp x)
;;                 (len-is (cdr x) (1- n))))))

;; (local (defthm open-len-is
;;          (implies (syntaxp (quotep n))
;;                   (equal (len-is x n)
;;                          (if (zp n)
;;                              (and (eql n 0) (atom x))
;;                            (and (consp x)
;;                                 (len-is (cdr x) (1- n))))))))


;; (local (defthm equal-len-hyp
;;          (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
;;                                     (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
;;                                 (quotep n)))
;;                   (equal (equal (len x) n)
;;                          (len-is x n)))))


(local (defthm equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (if (zp n)
                             (and (atom x) (equal n 0))
                           (and (consp x)
                                (equal (len (cdr x)) (1- n))))))))

(local (defthm len-cdr
         (implies (consp x)
                  (< (len (cdr x)) (len x)))
         :rule-classes :linear))

(local (defthm len-of-cons
         (Equal (len (cons x y))
                (+ 1 (len y)))))

(local (in-theory (disable len)))


(local
 (defthm fgl-object-bindings-p-of-pairlis$
   (implies (and (pseudo-var-list-p keys)
                 (fgl-objectlist-p vals)
                 (equal (len keys) (len vals)))
            (fgl-object-bindings-p (pairlis$ keys vals)))
   :hints(("Goal" :in-theory (enable pairlis$)))))

(local (defthm fgl-object-bindings-bfrlist-of-pairlis$
         (implies (and (pseudo-var-list-p keys)
                       (equal (len keys) (len vals)))
                  (equal (fgl-object-bindings-bfrlist
                          (pairlis$ keys vals))
                         (fgl-objectlist-bfrlist vals)))
         :hints(("Goal" :in-theory (enable pairlis$)))))


(local (defthm fgl-object-bindings-bfrlist-of-cdr
         (implies (not (member v (fgl-object-bindings-bfrlist x)))
                  (not (member v (fgl-object-bindings-bfrlist (cdr x)))))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist)))))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 5 7 nil nil))
  (defines fgl-object-add-to-cgraph
    (define fgl-object-add-to-cgraph ((x fgl-object-p)
                                      (cgraph cgraph-p)
                                      (memo cgraph-memo-p)
                                      (ruletable ctrex-ruletable-p)
                                      (bfrstate bfrstate-p)
                                      (wrld plist-worldp)
                                      (clk natp))
      :well-founded-relation acl2::nat-list-<
      :measure (list (nfix clk) (fgl-object-count x) 10 0 0)
      :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
      :guard (and (bfr-listp (fgl-object-bfrlist x))
                  (ctrex-ruletable-bfr-free ruletable))
      :verify-guards nil
      (b* ((fnsym (fgl-object-case x
                    (:g-ite 'if)
                    (:g-cons 'cons)
                    (:g-apply x.fn)
                    (otherwise nil)))
           ((unless fnsym)
            (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           ((when (fgl-object-variable-free-p x)) ;; ???
            (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           ((when (hons-get (fgl-object-fix x) (cgraph-memo-fix memo)))
            (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           (memo (hons-acons (fgl-object-fix x) t (cgraph-memo-fix memo)))
           ((when (and (fgl-object-case x :g-apply)
                       (fgetprop fnsym 'acl2::coarsenings nil wrld)))
            ;; Equivalence relation.  Add edges between two args
            (b* (((g-apply x))
                 ((unless (eql (len x.args) 2))
                  (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
                 ((list arg1 arg2) x.args)
                 ((mv cgraph memo) (fgl-object-add-to-cgraph arg1 cgraph memo ruletable bfrstate wrld clk))
                 ((mv cgraph memo) (fgl-object-add-to-cgraph arg2 cgraph memo ruletable bfrstate wrld clk)))
              (mv (add-cgraph-equiv x arg1 arg2 cgraph) memo)))
           ((mv cgraph memo)
            (fgl-object-add-to-cgraph-implicit x cgraph memo ruletable bfrstate wrld clk))
           (rules (cdr (hons-get fnsym (ctrex-ruletable-fix ruletable)))))
        (fgl-object-add-to-cgraph-rules x rules cgraph memo ruletable bfrstate wrld clk)))

    (define fgl-object-add-to-cgraph-implicit ((x fgl-object-p)
                                               (cgraph cgraph-p)
                                               (memo cgraph-memo-p)
                                               (ruletable ctrex-ruletable-p)
                                               (bfrstate bfrstate-p)
                                               (wrld plist-worldp)
                                               (clk natp))
      :measure (list (nfix clk) (fgl-object-count x) 7 0 0)
      :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
      :guard (and (bfr-listp (fgl-object-bfrlist x))
                  (ctrex-ruletable-bfr-free ruletable))
      (b* ((x (fgl-object-fix x))
           ((mv fnsym args)
            (fgl-object-case x
              :g-ite (mv 'if (list x.test x.then x.else))
              :g-cons (mv 'cons (list x.car x.cdr))
              :g-apply (mv x.fn x.args)
              :otherwise (mv nil nil)))
           ((unless fnsym)
            (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           (arg-vars (make-argvars "ARG" (len args) nil))
           (success-vars (make-argvars "ARG-SUCCESS" (len args) nil))
           (deps (pairlis$ arg-vars args))
           ((mv cgraph memo)
            (fgl-object-add-to-cgraph-bindings deps cgraph memo ruletable bfrstate wrld clk))
           (template *cgraph-implicit-edge-template*)
           (edge (change-cgraph-formula template
                                     :deps deps
                                     :dep-success-vars (pairlis$ success-vars arg-vars)
                                     :success (disjoin success-vars)
                                     :value (pseudo-term-fncall fnsym arg-vars))))
        (mv (add-cgraph-formula x edge cgraph) memo)))

    (define fgl-object-add-to-cgraph-bindings ((x fgl-object-bindings-p)
                                               (cgraph cgraph-p)
                                               (memo cgraph-memo-p)
                                               (ruletable ctrex-ruletable-p)
                                               (bfrstate bfrstate-p)
                                               (wrld plist-worldp)
                                               (clk natp))
      :measure (list (nfix clk) (fgl-object-bindings-count x) 5 (len x) 0)
      :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
      :guard (And (bfr-listp (fgl-object-bindings-bfrlist x))
                  (ctrex-ruletable-bfr-free ruletable))
      (if (atom x)
          (mv (cgraph-fix cgraph) (cgraph-memo-fix memo))
        (if (mbt (and (consp (car x))
                      (pseudo-var-p (caar x))))
            (b* (((mv cgraph memo) (fgl-object-add-to-cgraph (cdar x) cgraph memo ruletable bfrstate wrld clk)))
              (fgl-object-add-to-cgraph-bindings (cdr x) cgraph memo ruletable bfrstate wrld clk))
          (fgl-object-add-to-cgraph-bindings (cdr x) cgraph memo ruletable bfrstate wrld clk))))


    (define fgl-object-add-to-cgraph-rules ((x fgl-object-p)
                                            (rules ctrex-rulelist-p)
                                            (cgraph cgraph-p)
                                            (memo cgraph-memo-p)
                                            (ruletable ctrex-ruletable-p)
                                            (bfrstate bfrstate-p)
                                            (wrld plist-worldp)
                                            (clk natp))
      :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                  (bfr-listp (fgl-object-bfrlist x))
                  (ctrex-rulelist-bfr-free rules)
                  (ctrex-ruletable-bfr-free ruletable))
      :measure (list (nfix clk) (fgl-object-count x) 7 (len rules) 0)
      :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
      (b* (((when (atom rules)) (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           ((mv cgraph memo) (fgl-object-add-to-cgraph-rule x (car rules) cgraph memo ruletable bfrstate wrld clk)))
        (fgl-object-add-to-cgraph-rules x (cdr rules) cgraph memo ruletable bfrstate wrld clk)))

    (define fgl-object-add-to-cgraph-rule ((x fgl-object-p)
                                           (rule ctrex-rule-p)
                                           (cgraph cgraph-p)
                                           (memo cgraph-memo-p)
                                           (ruletable ctrex-ruletable-p)
                                           (bfrstate bfrstate-p)
                                           (wrld plist-worldp)
                                           (clk natp))
      :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                  (bfr-listp (fgl-object-bfrlist x))
                  (not (fgl-object-bindings-bfrlist (ctrex-rule->unify-subst rule)))
                  (ctrex-ruletable-bfr-free ruletable))
      :measure (list (nfix clk) (fgl-object-count x) 7 0 0)
      :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
      (b* (((mv ok target edge) (ctrex-rule-to-formula x rule bfrstate))
           ((unless ok) (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           ((when (zp clk))
            (raise "Loop in cgraph generation rules? Clock ran out")
            (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
           (clk (1- clk))
           ((mv cgraph memo) (fgl-object-add-to-cgraph target cgraph memo ruletable bfrstate wrld clk))
           ((mv cgraph memo) (fgl-object-add-to-cgraph-bindings (cgraph-formula->deps edge) cgraph memo ruletable bfrstate wrld clk)))
        (mv (add-cgraph-formula target edge cgraph) memo)))
    ///
    (local (include-book "tools/trivial-ancestors-check" :dir :system))
    (local (acl2::use-trivial-ancestors-check))
    (verify-guards fgl-object-add-to-cgraph
      ;; :guard-debug t
      :hints (("goal" :do-not-induct t
               :in-theory (enable bfr-listp-when-not-member-witness))))
    (local (in-theory (disable fgl-object-add-to-cgraph
                               fgl-object-add-to-cgraph-implicit
                               fgl-object-add-to-cgraph-bindings
                               fgl-object-add-to-cgraph-rules
                               fgl-object-add-to-cgraph-rule)))

    (local (defthm pseudo-term-subst-fix-when-bad-car
             (implies (not (and (consp (car x))
                                (pseudo-var-p (caar x))))
                      (equal (pseudo-term-subst-fix x)
                             (pseudo-term-subst-fix (cdr x))))
             :hints(("Goal" :in-theory (enable pseudo-term-subst-fix)))))

    (local (in-theory (enable bfr-listp-when-not-member-witness)))

    (defret-mutual cgraph-bfrlist-of-fgl-object-add-to-cgraph
      (defret cgraph-bfrlist-of-<fn>
        (implies (and (bfr-listp (fgl-object-bfrlist x))
                      (bfr-listp (cgraph-bfrlist cgraph))
                      (ctrex-ruletable-bfr-free ruletable))
                 (bfr-listp (cgraph-bfrlist new-cgraph)))
        :hints ('(:expand (<call>)))
        :fn fgl-object-add-to-cgraph)
      (defret cgraph-bfrlist-of-<fn>
        (implies (and (bfr-listp (fgl-object-bindings-bfrlist x))
                      (bfr-listp (cgraph-bfrlist cgraph))
                      (ctrex-ruletable-bfr-free ruletable))
                 (bfr-listp (cgraph-bfrlist new-cgraph)))
        :hints ('(:expand (<call>)))
        :fn fgl-object-add-to-cgraph-bindings)
      (defret cgraph-bfrlist-of-<fn>
        (implies (and (bfr-listp (fgl-object-bfrlist x))
                      (bfr-listp (cgraph-bfrlist cgraph))
                      (ctrex-rulelist-bfr-free rules)
                      (ctrex-ruletable-bfr-free ruletable))
                 (bfr-listp (cgraph-bfrlist new-cgraph)))
        :hints ('(:expand (<call>)))
        :fn fgl-object-add-to-cgraph-rules)
      (defret cgraph-bfrlist-of-<fn>
        (implies (and (bfr-listp (fgl-object-bfrlist x))
                      (bfr-listp (cgraph-bfrlist cgraph))
                      (ctrex-ruletable-bfr-free ruletable))
                 (bfr-listp (cgraph-bfrlist new-cgraph)))
        :hints ('(:expand (<call>
                           (:free (a b) (cgraph-bfrlist (cons a b)))
                           (:free (a b) (cgraph-formulalist-bfrlist (cons a b))))
                  :in-theory (enable cgraph-formula-bfrlist)))
        :fn fgl-object-add-to-cgraph-implicit)
      (defret cgraph-bfrlist-of-<fn>
        (implies (and (bfr-listp (fgl-object-bfrlist x))
                      (bfr-listp (cgraph-bfrlist cgraph))
                      (not (fgl-object-bindings-bfrlist (ctrex-rule->unify-subst rule)))
                      (ctrex-ruletable-bfr-free ruletable))
                 (bfr-listp (cgraph-bfrlist new-cgraph)))
        :hints ('(:expand (<call>)))
        :fn fgl-object-add-to-cgraph-rule))

    (local (in-theory (enable fgl-object-bindings-fix)))
    (fty::deffixequiv-mutual fgl-object-add-to-cgraph)))





;; ------------------------------------------------------------------------
;; Creating a cgraph from a bvar-db and set of rules, using
;; fgl-object-add-to-cgraph -- main function bvar-db-update-cgraph
;; ------------------------------------------------------------------------


(define bvar-db-add-to-cgraph-aux ((n natp)
                                   (bvar-db)
                                   (cgraph cgraph-p)
                                   (memo cgraph-memo-p)
                                   (ruletable ctrex-ruletable-p)
                                   (bfrstate bfrstate-p)
                                   (wrld plist-worldp))
  :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n)
              (bfr-listp (bvar-db-bfrlist bvar-db))
              (ctrex-ruletable-bfr-free ruletable))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql n (next-bvar bvar-db))))
        (mv (cgraph-fix cgraph) (cgraph-memo-fix memo)))
       ((mv cgraph memo) (fgl-object-add-to-cgraph (get-bvar->term n bvar-db)
                                                  cgraph memo ruletable bfrstate wrld 1000)))
    (bvar-db-add-to-cgraph-aux (1+ (lnfix n))
                               bvar-db cgraph memo ruletable bfrstate wrld))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (bfr-listp (bvar-db-bfrlist bvar-db))
                  (bfr-listp (cgraph-bfrlist cgraph))
                  (<= (base-bvar$c bvar-db) (nfix n))
                  (ctrex-ruletable-bfr-free ruletable))
             (bfr-listp (cgraph-bfrlist new-cgraph)))))

(define bvar-db-update-cgraph ((cgraph cgraph-p)
                               (memo cgraph-memo-p)
                               (cgraph-index natp)
                               bvar-db
                               (ruletable ctrex-ruletable-p)
                               (bfrstate bfrstate-p)
                               (wrld plist-worldp))
  :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-memo-p))
  :guard (and (bfr-listp (bvar-db-bfrlist bvar-db))
              (ctrex-ruletable-bfr-free ruletable))
  ;; BOZO this never shrinks the cgraph -- probably not necessary
  (b* (((when (<= (next-bvar bvar-db) (lnfix cgraph-index)))
        (mv (cgraph-fix cgraph) (cgraph-memo-fix memo))))
    (bvar-db-add-to-cgraph-aux (max (lnfix cgraph-index)
                                    (base-bvar bvar-db))
                               bvar-db cgraph memo ruletable bfrstate wrld))
  ///

  (defret cgraph-bfrlist-of-<fn>
    (implies (and (bfr-listp (bvar-db-bfrlist bvar-db))
                  (bfr-listp (cgraph-bfrlist cgraph))
                  (ctrex-ruletable-bfr-free ruletable))
             (bfr-listp (cgraph-bfrlist new-cgraph)))))





;; ------------------------------------------------------------------------
;; Deriving counterexample values from a cgraph.
;; See main function cgraph-derive-assignments-obj, below
;; ------------------------------------------------------------------------




(fty::defprod cgraph-derivstate
  ((times-seen natp :rule-classes :type-prescription)
   (result-msg))
  :layout :tree)

(fty::defmap cgraph-derivstates :key-type fgl-object :val-type cgraph-derivstate :true-listp t)

(make-event
 `(define cgraph-derivstate-start ()
    :returns (st cgraph-derivstate-p)
    ',(make-cgraph-derivstate :times-seen 0)))

(make-event
 `(define cgraph-derivstate-1 ()
    :returns (st cgraph-derivstate-p)
    ',(make-cgraph-derivstate :times-seen 1)))

(define cgraph-derive-assigns-measure ((cgraph cgraph-p)
                                       (assigns cgraph-alist-p)
                                       (sts cgraph-derivstates-p)
                                       (replimit posp))
  :returns (count natp :rule-classes :type-prescription)
  :measure (len cgraph)
  (b* (((when (atom cgraph)) 0)
       ((unless (mbt (and (consp (car cgraph))
                          (fgl-object-p (caar cgraph)))))
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
    (implies (and (fgl-object-p obj)
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
    (implies (and (fgl-object-p obj)
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
  ;;                 (fgl-object-p obj))
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
  ;;                 (fgl-object-p obj))
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
                  (fgl-object-p obj))
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
                  (fgl-object-p obj))
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
                              (fgl-object-p (caar x))))
                    (equal (cgraph-fix x)
                           (cgraph-fix (cdr x))))
           :hints(("Goal" :in-theory (enable cgraph-fix))))))



(define cgraph-incr-seen ((x fgl-object-p)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (fgl-object-fix x))
       (sts (cgraph-derivstates-fix sts))
       (st (cdr (hons-get x sts)))
       ((unless st)
        (hons-acons x (cgraph-derivstate-1) sts)))
    (hons-acons x (change-cgraph-derivstate st :times-seen (+ 1 (cgraph-derivstate->times-seen st)))
                sts))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>-weak
    (<= (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear)

  (defret cgraph-derive-assigns-measure-of-<fn>-unseen
    (implies (and (not (hons-assoc-equal (fgl-object-fix x) sts))
                  (hons-assoc-equal (fgl-object-fix x) cgraph)
                  (not (hons-assoc-equal (fgl-object-fix x) assigns)))
             (< (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :rule-classes :linear)

  (defret cgraph-derive-assigns-measure-of-<fn>-seen
    (implies (and (< (cgraph-derivstate->times-seen (cdr (hons-assoc-equal (fgl-object-fix x) sts)))
                     (acl2::pos-fix replimit))
                  (hons-assoc-equal (fgl-object-fix x) cgraph)
                  (not (hons-assoc-equal (fgl-object-fix x) assigns)))
             (< (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :rule-classes :linear))


(defines magic-fgl-object-eval
  (define magic-fgl-object-eval ((x fgl-object-p)
                                (env$)
                                &optional
                                (logicman 'logicman)
                                (state 'state))
    :guard (and (bfr-env$-p env$ (logicman->bfrstate))
                (lbfr-listp (fgl-object-bfrlist x)))
    :returns (mv err val)
    :verify-guards nil
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    (fgl-object-case x
      :g-concrete (mv nil x.val)
      :g-boolean (mv nil (bfr-eval-fast x.bool env$))
      :g-integer (mv nil (bools->int (bfr-list-eval-fast x.bits env$)))
      :g-ite (b* (((mv err test) (magic-fgl-object-eval x.test env$))
                  ((when err) (mv err nil)))
               (if test
                   (magic-fgl-object-eval x.then env$)
                 (magic-fgl-object-eval x.else env$)))
      :g-cons (b* (((mv err car) (magic-fgl-object-eval x.car env$))
                   ((when err) (mv err nil))
                   ((mv err cdr) (magic-fgl-object-eval x.cdr env$))
                   ((when err) (mv err nil)))
                (mv nil (cons car cdr)))
      :g-map (magic-fgl-object-alist-eval x.alist env$)
      :g-var (mv nil (cdr (assoc-eq x.name (env$->obj-alist env$))))
      :g-apply (b* (((mv err args) (magic-fgl-objectlist-eval x.args env$))
                    ((when err) (mv err nil)))
                 (magitastic-ev-fncall x.fn args 1000 state t t))))

  (define magic-fgl-objectlist-eval ((x fgl-objectlist-p)
                                    (env$)
                                    &optional
                                    (logicman 'logicman)
                                    (state 'state))
    :guard (and (bfr-env$-p env$ (logicman->bfrstate))
                (lbfr-listp (fgl-objectlist-bfrlist x)))
    :returns (mv err (val true-listp))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (b* (((when (atom x)) (mv nil nil))
         ((mv err car) (magic-fgl-object-eval (car x) env$))
         ((when err) (mv err nil))
         ((mv err cdr) (magic-fgl-objectlist-eval (cdr x) env$))
         ((when err) (mv err nil)))
      (mv nil (cons car cdr))))

  (define magic-fgl-object-alist-eval ((x fgl-object-alist-p)
                                      (env$)
                                      &optional
                                      (logicman 'logicman)
                                      (state 'state))
    :guard (and (bfr-env$-p env$ (logicman->bfrstate))
                (lbfr-listp (fgl-object-alist-bfrlist x)))
    :returns (mv err val)
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    (b* (((when (atom x)) (mv nil x))
         ((unless (mbt (consp (car x))))
          (magic-fgl-object-alist-eval (cdr x) env$))
         ((mv err val1) (magic-fgl-object-eval (cdar x) env$))
         ((when err) (mv err nil))
         ((mv err rest) (magic-fgl-object-alist-eval (cdr x) env$))
         ((when err) (mv err nil)))
      (mv nil (cons (cons (caar x) val1) rest))))
  ///
  (verify-guards magic-fgl-object-eval-fn
    :hints (("goal" :expand (fgl-object-bfrlist x)
             :in-theory (disable magic-fgl-object-eval-fn
                                 magic-fgl-objectlist-eval
                                 magic-fgl-object-alist-eval))))

  (local (defthm fgl-object-alist-fix-when-bad-car
           (implies (and (consp X)
                         (not (consp (car x))))
                    (equal (fgl-object-alist-fix x)
                           (fgl-object-alist-fix (cdr x))))
           :hints(("Goal" :in-theory (enable fgl-object-alist-fix)))))

  (fty::deffixequiv-mutual magic-fgl-object-eval))


(define cgraph-set-error ((x fgl-object-p)
                          (msg)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (fgl-object-fix x))
       (sts (cgraph-derivstates-fix sts))
       (st (cdr (hons-get x sts)))
       ((unless st)
        (hons-acons x (make-cgraph-derivstate :times-seen 0 :result-msg msg) sts))
       ((cgraph-derivstate st))
       (new-msg (if st.result-msg
                    (msg "~@0~%~@1" msg st.result-msg)
                  msg)))
    (hons-acons x (change-cgraph-derivstate st :result-msg new-msg) sts))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear)

  (defret times-seen-of-<fn>
    (equal (cgraph-derivstate->times-seen (cdr (hons-assoc-equal k new-sts)))
           (cgraph-derivstate->times-seen (cdr (hons-assoc-equal k (cgraph-derivstates-fix sts)))))))

(define cgraph-set-errors ((x fgl-objectlist-p)
                          (msg)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (if (atom x)
      (cgraph-derivstates-fix sts)
    (cgraph-set-errors (cdr x) msg (cgraph-set-error (car x) msg sts)))
  ///
  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear)

  (defret times-seen-of-<fn>
    (equal (cgraph-derivstate->times-seen (cdr (hons-assoc-equal k new-sts)))
           (cgraph-derivstate->times-seen (cdr (hons-assoc-equal k (cgraph-derivstates-fix sts)))))))

(local (defthm bfr-varname-p-of-get-term->bvar$c
         (implies (and (equal (bfr-nvars) (next-bvar$c bvar-db))
                       (get-term->bvar$c x bvar-db))
                  (bfr-varname-p (get-term->bvar$c x bvar-db)))
         :hints(("Goal" :in-theory (enable bfr-varname-p)))))


(define cgraph-derive-assignments-end ((x fgl-object-p)
                                        (assigns cgraph-alist-p)
                                        (sts cgraph-derivstates-p)
                                        (replimit posp))
  :returns (done)
  (b* ((x (fgl-object-fix x))
       (assigns (cgraph-alist-fix assigns))
       (sts (cgraph-derivstates-fix sts))
       (assigns-look (hons-get x assigns))
       ((when assigns-look) t)
       ((cgraph-derivstate st)
        (or (cdr (hons-get x sts))
            (cgraph-derivstate-start))))
    (<= (lposfix replimit) st.times-seen))
  ///

  (defret cgraph-derive-assigns-measure-of-incr-seen-when-<fn>
    (implies (and (not done)
                  (hons-assoc-equal (fgl-object-fix x) cgraph))
             (< (cgraph-derive-assigns-measure cgraph assigns
                                               (cgraph-incr-seen x sts)
                                               replimit)
                (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
    :rule-classes :linear))

(define cgraph-derive-assignments-base ((x fgl-object-p)
                                        (assigns cgraph-alist-p)
                                        (sts cgraph-derivstates-p)
                                        env$
                                        &optional
                                        (logicman 'logicman)
                                        (bvar-db 'bvar-db)
                                        (state 'state))
  :returns (mv donep
               (new-assigns cgraph-alist-p)
               (new-sts cgraph-derivstates-p))
    :guard (and (lbfr-listp (fgl-object-bfrlist x))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db)))
  (b* ((x (fgl-object-fix x))
       (assigns (cgraph-alist-fix assigns))
       (sts (cgraph-derivstates-fix sts))
       (bvar (get-term->bvar x bvar-db))
       ((when bvar)
        (b* ((val (bfr-eval-fast (bfr-var bvar) env$ logicman))
             (assigns (hons-acons x (cgraph-value val *ctrex-eval-default-priority* :boolean) assigns)))
          (mv t assigns sts)))
       ((when (fgl-object-variable-free-p x))
        (b* (((mv err val) (magic-fgl-object-eval x env$))
             ((when err)
              (b* ((sts (cgraph-set-error x
                                          (msg "Failed to evaluate the object: ~@0"
                                               (if* (eq err t) "(no msg)" err))
                                          sts)))
                (mv nil assigns sts)))
             (assigns (hons-acons x (cgraph-value val *ctrex-eval-default-priority* :evaluation) assigns)))
          (mv t assigns sts))))
    (mv nil assigns sts))
  ///

  (defret cgraph-derive-assigns-measure-when-<fn>
    (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear)

  (defret cgraph-derive-assignments-end-of-base-when-not-done
    (implies (not donep)
             (equal (cgraph-derive-assignments-end y new-assigns new-sts replimit)
                    (cgraph-derive-assignments-end y assigns sts replimit)))
    :hints(("Goal" :in-theory (enable cgraph-derive-assignments-end
                                      cgraph-set-error))))

  (defret cgraph-derive-assignments-base-bound-when-done
    (implies (and donep
                  (fgl-object-p x))
             (hons-assoc-equal x new-assigns))))

(define cgraph-assign-all ((x fgl-objectlist-p)
                           (val cgraph-value-p)
                           (assigns cgraph-alist-p)
                           (sts cgraph-derivstates-p))
  :returns (mv (new-assigns cgraph-alist-p)
               (new-sts cgraph-derivstates-p))
  (b* ((assigns (cgraph-alist-fix assigns))
       (sts (cgraph-derivstates-fix sts))
       ((when (atom x)) (mv assigns sts))
       (x1 (fgl-object-fix (car x)))
       (look (hons-get x1 assigns))
       (sts (if (and look
                     (equal (cgraph-value->priority (cdr look)) (cgraph-value->priority val))
                     (not (equal (cgraph-value->val (cdr look)) (cgraph-value->val val))))
                (cgraph-set-error x1 (msg "Conflicting assignment: ~x0, ~x1" (cdr look) (cgraph-value-fix val)) sts)
              sts))
       (assigns (if (or (not look)
                        (> (cgraph-value->priority val) (cgraph-value->priority (cdr look))))
                    (hons-acons x1 (cgraph-value-fix val) assigns)
                  assigns)))
    (cgraph-assign-all (cdr x) val assigns sts))
  ///
  

  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear))

(define cgraph-derive-assignments-base-equivclass ((x fgl-objectlist-p)
                                                   (equivclass fgl-objectlist-p)
                                                   (assigns cgraph-alist-p)
                                                   (sts cgraph-derivstates-p)
                                                   env$
                                                   &optional
                                                   (logicman 'logicman)
                                                   (bvar-db 'bvar-db)
                                                   (state 'state))
  ;; This is done for an equivalence class of objects where we want to derive a
  ;; value for any of them and conclude that they're all the same.
  :returns (mv donep
               (new-assigns cgraph-alist-p)
               (new-sts cgraph-derivstates-p))
    :guard (and (lbfr-listp (fgl-objectlist-bfrlist x))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db)))
    (b* (((when (atom x))
          (mv nil (cgraph-alist-fix assigns) (cgraph-derivstates-fix sts)))
         (x1 (fgl-object-fix (car x)))
         (look (hons-get x1 (cgraph-alist-fix assigns)))
         ((when look)
          (b* (((mv assigns sts)
                (cgraph-assign-all equivclass (cdr look) assigns sts)))
            (mv t assigns sts)))
         ((mv done assigns sts)
          (cgraph-derive-assignments-base x1 assigns sts env$))
         ((when done)
          (b* (((mv assigns sts)
                (cgraph-assign-all equivclass (cdr (hons-get x1 assigns)) assigns sts)))
            (mv t assigns sts))))
      (cgraph-derive-assignments-base-equivclass (cdr x) equivclass assigns sts env$))
    ///
    
  

  (defret cgraph-derive-assigns-measure-of-<fn>
    (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
        (cgraph-derive-assigns-measure cgraph assigns sts replimit))
    :rule-classes :linear))


;; (define cgraph-formulalist-sortedp ((x cgraph-formulalist-p))
;;   (if (or (atom x)
;;           (atom (cdr x)))
;;       t
;;     (and (not (cgraph-formula-order< (cadr x) (car x)))
;;          (cgraph-formulalist-sortedp (cdr x)))))


(define cgraph-formulalist-member-by-order ((x cgraph-formula-p)
                                            (lst cgraph-formulalist-p))
  (cond ((atom lst) nil)
        ((cgraph-formula-order< x (car lst)) nil)
        ((equal (cgraph-formula-fix x)
                (cgraph-formula-fix (car lst))) t)
        (t (cgraph-formulalist-member-by-order x (cdr lst))))
  ///
  (local (defthm cgraph-formula-order-irreflexive
           (not (cgraph-formula-order< x x))
           :hints(("Goal" :in-theory (enable cgraph-formula-order<)))))
  (local (defthm cgraph-formula-order-trans-lemma
           (implies (and (cgraph-formula-order< x y)
                         (not (cgraph-formula-order< z y)))
                    (cgraph-formula-order< x z))
           :hints(("Goal" :in-theory (enable cgraph-formula-order<)))))
  (local (defthm cgraph-formula-order-trans
           (implies (and (cgraph-formula-order< x y)
                         (cgraph-formula-order< y z))
                    (cgraph-formula-order< x z))
           :hints(("Goal" :in-theory (enable cgraph-formula-order<)))))
  
  (local (defthm not-member-when-sorted
           (implies (and (cgraph-formula-ordered-p lst)
                         (cgraph-formula-order< x (car lst)))
                    (not (member-equal (cgraph-formula-fix x)
                                       (cgraph-formulalist-fix lst))))
           :hints(("Goal" :in-theory (enable cgraph-formula-ordered-p
                                             cgraph-formulalist-fix)))))
  (defthm <fn>-correct-when-sorted
    (implies (cgraph-formula-ordered-p lst)
             (iff (cgraph-formulalist-member-by-order x lst)
                  (member-equal (cgraph-formula-fix x)
                                (cgraph-formulalist-fix lst))))
    :hints(("Goal" :in-theory (enable cgraph-formula-ordered-p
                                      cgraph-formulalist-fix)))))
    

(fty::deffixequiv cgraph-formula-ordered-p :args ((x cgraph-formulalist-p))
  :hints(("Goal" :in-theory (enable cgraph-formula-ordered-p))))

(define cgraph-formulalist-sortedp ((x cgraph-formulalist-p))
  (if (or (atom x)
          (atom (cdr x)))
      t
    (and (not (cgraph-formulalist-member-by-order (car x) (cdr x)))
         (not (cgraph-formula-order< (cadr x) (car x)))
         (cgraph-formulalist-sortedp (cdr x))))
  ///
  (defthm cgraph-formulalist-sortedp-implies-orderd-p
    (implies (cgraph-formulalist-sortedp x)
             (cgraph-formula-ordered-p x))
    :hints(("Goal" :in-theory (enable cgraph-formula-ordered-p))))

  
  (local (defthm cgraph-formula-order-irreflexive
           (not (cgraph-formula-order< x x))
           :hints(("Goal" :in-theory (enable cgraph-formula-order<)))))

  (local (defthm cgraph-formula-order-asymm
           (implies (cgraph-formula-order< x y)
                    (not (cgraph-formula-order< y x)))
           :hints(("Goal" :in-theory (enable cgraph-formula-order<)))))
  
  (defthm cgraph-formulalist-sortedp-iff-ordered-and-dup-free
    (iff (cgraph-formulalist-sortedp x)
         (and (no-duplicatesp-equal (cgraph-formulalist-fix x))
              (cgraph-formula-ordered-p x)))
    :hints(("Goal" :in-theory (enable cgraph-formula-ordered-p
                                      cgraph-formulalist-fix)))))

(define cgraph-formulalist-uniqsort ((x cgraph-formulalist-p))
  :returns (new-x cgraph-formulalist-p)
  (if (cgraph-formulalist-sortedp x)
      (cgraph-formulalist-fix x)
    (cgraph-formula-sort (set::mergesort (cgraph-formulalist-fix x))))
  ///
  (defthm cgraph-formulalist-bfrlist-of-insert
    (implies (and (not (member v (cgraph-formula-bfrlist x)))
                  (not (member v (cgraph-formulalist-bfrlist y))))
             (not (member v (cgraph-formulalist-bfrlist (set::insert x y)))))
    :hints(("Goal" :in-theory (enable set::insert set::head set::emptyp set::tail))))

  (defthm cgraph-formulalist-bfrlist-of-mergesort
    (implies (not (member v (cgraph-formulalist-bfrlist x)))
             (not (member v (cgraph-formulalist-bfrlist (set::mergesort x)))))
    :hints(("Goal" :in-theory (enable set::mergesort))))

  (defthm cgraph-formulalist-bfrlist-of-cgraph-formula-insertsort
    (implies (not (member v (cgraph-formulalist-bfrlist x)))
             (not (member v (cgraph-formulalist-bfrlist (cgraph-formula-insertsort x)))))
    :hints(("Goal" :in-theory (enable cgraph-formula-insertsort))))

  (defret cgraph-formulalist-bfrlist-of-uniqsort
    (implies (not (member v (cgraph-formulalist-bfrlist x)))
             (not (member v (cgraph-formulalist-bfrlist new-x))))))


(define cgraph-extract-dep-values ((deps fgl-object-bindings-p)
                                   (assigns cgraph-alist-p))
  :returns (values symbol-alistp)
  (if (atom deps)
      nil
    (if (mbt (and (consp (car deps))
                  (pseudo-var-p (caar deps))))
        (b* ((obj (fgl-object-fix (cdar deps)))
             (look (hons-get obj assigns)))
          (if look
              (cons (cons (caar deps) (cgraph-value->val (cdr look)))
                    (cgraph-extract-dep-values (cdr deps) assigns))
            (cgraph-extract-dep-values (cdr deps) assigns)))
      (cgraph-extract-dep-values (cdr deps) assigns)))
  ///
  (local (in-theory (enable fgl-object-bindings-fix))))

(define cgraph-extract-dep-success-values ((dep-success-vars pseudo-term-subst-p)
                                           (values symbol-alistp))
  :returns (succ-values symbol-alistp)
  (if (atom dep-success-vars)
      nil
    (if (and (mbt (and (consp (car dep-success-vars))
                       (pseudo-var-p (caar dep-success-vars))))
             (pseudo-term-case (cdar dep-success-vars) :var))
        (b* ((var (pseudo-term-var->name (cdar dep-success-vars)))
             (look (hons-assoc-equal var values)))
          (if look
              (cons (cons (caar dep-success-vars) t)
                    (cgraph-extract-dep-success-values (cdr dep-success-vars) values))
            (cgraph-extract-dep-success-values (cdr dep-success-vars) values)))
      (cgraph-extract-dep-success-values (cdr dep-success-vars) values)))
  ///
  (local (in-theory (enable pseudo-term-subst-fix))))

;; in case this needs tracing
(define magitastic-ev-wrap ((x pseudo-termp)
                            (alist symbol-alistp)
                            (reclimit natp)
                            state hard-errp aokp)
  (magitastic-ev x alist (lnfix reclimit) state hard-errp aokp))

(define cgraph-formulas-some-non-implicit ((x cgraph-formulalist-p))
  (if (atom x)
      nil
    (or (not (eq (cgraph-formula->ruletype (car x)) :implicit))
        (cgraph-formulas-some-non-implicit (cdr x)))))


(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 5 7 nil nil))

  (defines cgraph-derive-assignments
    (define cgraph-derive-assignments-obj ((x fgl-object-p
                                              "object to try and derive an assignment for")
                                           (assigns cgraph-alist-p
                                                    "accumulator of object assignments")
                                           (sts cgraph-derivstates-p)
                                           (env$)
                                           (cgraph cgraph-p)
                                           (replimit posp)
                                           &optional
                                           (logicman 'logicman)
                                           (bvar-db 'bvar-db)
                                           (state 'state))
      :parents (fgl-counterexample-implementation-details)
      :guard (and (lbfr-listp (fgl-object-bfrlist x))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))
      :returns (mv (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :well-founded-relation acl2::nat-list-<
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     10
                     0)
      :verify-guards nil
      ;; Tries to derive an assignment for object X by looking it up in the
      ;; cgraph and seeing what rules (edges) are available that might help
      ;; determine its value.
      ;; If x is already bound in assigns, then we're done with it already and we don't add an assignment.
      ;; If x is variable free, then it just assigns its evaluation under the Boolean env.
      ;; If x is term for which there is a Boolean variable in the bvar-db, we assign its Boolean value.
      ;; Otherwise, we derive candidate values for x by looking at its edges in the cgraph.
      ;; If any edge successfully (?) derives a value, we choose the first one.
      (b* ((x (fgl-object-fix x))
           (assigns (cgraph-alist-fix assigns))
           (sts (cgraph-derivstates-fix sts))
           (cgraph (cgraph-fix cgraph))
           (donep (cgraph-derive-assignments-end x assigns sts replimit))
           ((when donep) (mv assigns sts))
           ((mv donep assigns sts)
            (cgraph-derive-assignments-base x assigns sts env$))
           ((when donep) (mv assigns sts))

           (outedges (cdr (hons-get x cgraph)))
           ((unless outedges)
            (b* ((sts (cgraph-set-error x
                                        "No rules for deriving the value of the object"
                                        sts)))
              (mv assigns sts)))
           ((cgraph-outedges outedges))

           (sts (cgraph-incr-seen x sts))

           ((mv equiv-objects equiv-obj-formulas new-assigns new-sts)
            (cgraph-derive-assignments-collect-equiv-class outedges.equivs (list x) outedges.formulas assigns sts env$ cgraph replimit))
           ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                             (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
            (mv new-assigns new-sts))
           (assigns new-assigns)
           (sts new-sts)
           ((mv donep assigns sts)
            (cgraph-derive-assignments-base-equivclass equiv-objects equiv-objects assigns sts env$))
           ((when donep)
            (mv assigns sts))

           (formulas (cgraph-formulalist-uniqsort equiv-obj-formulas))
           ((mv successp value assigns sts)
            (cgraph-derive-assignments-formulas equiv-objects formulas
                                                nil ;; successp
                                                nil ;; current cgraph-value
                                                assigns sts env$ cgraph replimit))
      
           ;; if successful, assign the value; otherwise store the error
           ((unless successp)
            (mv (cgraph-alist-fix assigns)
                ;; Do we always set an error here? We get a lot of messages about (intcdr (intcdr ...))
                ;; when it has really just reached the end of the vector. Heuristically, let's only produce the error if there is anon-implicit rule.
                (if (cgraph-formulas-some-non-implicit formulas)
                    (cgraph-set-errors equiv-objects (msg "No formula succeeded in computing a value") sts)
                  sts))))
        (cgraph-assign-all equiv-objects value assigns sts)))
    
    (define cgraph-derive-assignments-collect-equiv-class ((equivs cgraph-equivlist-p)
                                                           (class fgl-objectlist-p)
                                                           (edges cgraph-formulalist-p)
                                                           (assigns cgraph-alist-p)
                                                           (sts cgraph-derivstates-p)
                                                           (env$)
                                                           (cgraph cgraph-p)
                                                           (replimit posp)
                                                           &optional
                                                           (logicman 'logicman)
                                                           (bvar-db 'bvar-db)
                                                           (state 'state))
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     20
                     (len equivs))
      :returns (mv (equiv-objects fgl-objectlist-p)
                   (equiv-obj-edges cgraph-formulalist-p)
                   (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :guard (and (lbfr-listp (fgl-objectlist-bfrlist class))
                  (lbfr-listp (cgraph-equivlist-bfrlist equivs))
                  (lbfr-listp (cgraph-formulalist-bfrlist edges))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))
      (b* ((class (fgl-objectlist-fix class))
           (edges (cgraph-formulalist-fix edges))
           (assigns (cgraph-alist-fix assigns))
           (sts (cgraph-derivstates-fix sts))
           ((when (atom equivs))
            (mv class edges assigns sts))
           ((mv class edges new-assigns new-sts)
            (cgraph-derive-assignments-collect-equiv (car equivs) class edges assigns sts env$ cgraph replimit))
           ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                             (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
            (mv class edges new-assigns new-sts))
           (assigns new-assigns)
           (sts new-sts))
        (cgraph-derive-assignments-collect-equiv-class (cdr equivs) class edges assigns sts env$ cgraph replimit)))


    (define cgraph-derive-assignments-collect-equiv ((equiv cgraph-equivnode-p)
                                                     (class fgl-objectlist-p)
                                                     (edges cgraph-formulalist-p)
                                                     (assigns cgraph-alist-p)
                                                     (sts cgraph-derivstates-p)
                                                     (env$)
                                                     (cgraph cgraph-p)
                                                     (replimit posp)
                                                     &optional
                                                     (logicman 'logicman)
                                                     (bvar-db 'bvar-db)
                                                     (state 'state))
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     20
                     0)
      :returns (mv (equiv-objects fgl-objectlist-p)
                   (equiv-obj-edges cgraph-formulalist-p)
                   (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :guard (and (lbfr-listp (fgl-objectlist-bfrlist class))
                  (lbfr-listp (cgraph-equivnode-bfrlist equiv))
                  (lbfr-listp (cgraph-formulalist-bfrlist edges))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))
      (b* (((cgraph-equivnode equiv))
           (class (fgl-objectlist-fix class))
           (edges (cgraph-formulalist-fix edges))
           (assigns (cgraph-alist-fix assigns))
           (sts (cgraph-derivstates-fix sts))
           ((when (member-equal equiv.other class))
            (mv class edges assigns sts))
           ((mv new-assigns new-sts)
            (cgraph-derive-assignments-obj equiv.equivalence assigns sts env$ cgraph replimit))
           ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                             (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
            (mv class edges new-assigns new-sts))
           (assigns new-assigns)
           (sts new-sts)
           (look (hons-get equiv.equivalence assigns))
           ((unless (and look (cgraph-value->val (cdr look))))
            (mv class edges assigns sts))
           (class (cons equiv.other class))
           (outedges (cdr (hons-get equiv.other (cgraph-fix cgraph))))
           ((unless outedges)
            (mv class edges assigns sts))
           ((cgraph-outedges outedges))
           (edges (append outedges.formulas edges))
           (done (cgraph-derive-assignments-end equiv.other assigns sts replimit))
           ((when done)
            (mv class edges assigns sts))
           (sts (cgraph-incr-seen equiv.other sts)))
        (cgraph-derive-assignments-collect-equiv-class outedges.equivs class edges assigns sts env$ cgraph replimit)))
    

    (define cgraph-derive-assignments-formulas ((targets fgl-objectlist-p)
                                                (formulas cgraph-formulalist-p)
                                                (successp)
                                                (curr-value (implies successp (cgraph-value-p curr-value)))
                                                (assigns cgraph-alist-p)
                                                (sts cgraph-derivstates-p)
                                                (env$)
                                                (cgraph cgraph-p)
                                                (replimit posp)
                                                &optional
                                                (logicman 'logicman)
                                                (bvar-db 'bvar-db)
                                                (state 'state))
      :guard (and (lbfr-listp (cgraph-formulalist-bfrlist formulas))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))

      :returns (mv (new-successp)
                   (new-value (implies new-successp (cgraph-value-p new-value)))
                   (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     12
                     (len formulas))
      ;; Just iterates over the list of edges applying cgraph-derive-assignments-edge to each.
      (b* (((when (atom formulas)) (mv successp
                                       (mbe :logic (if successp (cgraph-value-fix curr-value) curr-value)
                                            :exec curr-value)
                                       (cgraph-alist-fix assigns) (cgraph-derivstates-fix sts)))
           ((mv successp curr-value new-assigns new-sts)
            (cgraph-derive-assignments-formula targets (car formulas) successp curr-value assigns sts env$ cgraph replimit))
           ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                             (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
            (mv successp curr-value new-assigns new-sts))
           (assigns new-assigns)
           (sts new-sts))
        (cgraph-derive-assignments-formulas targets (cdr formulas) successp curr-value assigns sts env$ cgraph replimit)))

    (define cgraph-derive-assignments-formula ((targets fgl-objectlist-p)
                                               (x cgraph-formula-p)
                                               (successp)
                                               (curr-value (implies successp (cgraph-value-p curr-value)))
                                               (assigns cgraph-alist-p)
                                               (sts cgraph-derivstates-p)
                                               (env$)
                                               (cgraph cgraph-p)
                                               (replimit posp)
                                               &optional
                                               (logicman 'logicman)
                                               (bvar-db 'bvar-db)
                                               (state 'state))
      (declare (ignorable targets))
      :returns (mv (new-successp)
                   (new-value (implies new-successp (cgraph-value-p new-value)))
                   (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     12
                     0)
      :guard (and (lbfr-listp (cgraph-formula-bfrlist x))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))
      (b* (((cgraph-formula x))
           (curr-value (mbe :logic (if successp (cgraph-value-fix curr-value) curr-value)
                            :exec curr-value))
           (curr-val (and successp (cgraph-value->val curr-value)))
           (curr-prio (and successp (cgraph-value->priority curr-value)))
           ;; Optimization
           ((when (and (pseudo-term-case x.priority :quote)
                       successp
                       (< (nfix (pseudo-term-quote->val x.priority))
                          curr-prio)))
            (mv successp curr-value (cgraph-alist-fix assigns) (cgraph-derivstates-fix sts)))
           ((mv new-assigns new-sts)
            (cgraph-derive-assignments-bindings x.deps assigns sts env$ cgraph replimit))
           ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                             (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
            (mv successp curr-value new-assigns new-sts))
           (assigns new-assigns)
           (sts new-sts)
           (dep-values (cgraph-extract-dep-values x.deps assigns))
           (dep-success-values (cgraph-extract-dep-success-values x.dep-success-vars dep-values))
           (alist (append `((prev-successp . ,successp)
                            (prev-value . ,curr-val)
                            (prev-priority . ,curr-prio))
                          dep-values dep-success-values))
           ((mv err successp1) (magitastic-ev-wrap x.success alist 1000 state t t))
           ((when err)
            (raise "Failed to evaluate success condition ~x0, derived from rule ~x1: ~@2~%" x.success x.name
                   (if (eq err t) "(no msg)" err))
            (mv successp curr-value assigns sts))
           ((unless successp1)
            (mv successp curr-value assigns sts))
           ((mv err priority1) (magitastic-ev-wrap x.priority alist 1000 state t t))
           ((when err)
            (raise "Failed to evaluate priority expression ~x0, derived from rule ~x1: ~@2~%" x.priority x.name
                   (if (eq err t) "(no msg)" err))
            (mv successp curr-value assigns sts))
           ((unless (natp priority1))
            (raise "Priority ~x0 derived from rule ~x1 evalued to non-natp ~x2~%" x.priority x.name priority1)
            (mv successp curr-value assigns sts))
           ((when (and successp (< priority1 curr-prio)))
            (mv successp curr-value assigns sts))
           ((mv err value1) (magitastic-ev-wrap x.value alist 1000 state t t))
           ((when err)
            (raise "Failed to evaluate value expression ~x0, derived from rule ~x1: ~@2~%" x.value x.name
                   (if (eq err t) "(no msg)" err))
            (mv successp curr-value assigns sts))
           ;; (sts (if (and (eql (lnfix curr-priority) priority1)
           ;;               (not (equal curr-value value1)))
           ;;          (cgraph-set-errors targets (msg "Conflicting values from equal priority formulas (latest rule name: ~x0)" x.name)
           ;;                             stas)
           ;;        sts))
           )
        (mv t (cgraph-value value1 priority1 x.name) assigns sts)))

    (define cgraph-derive-assignments-bindings ((x fgl-object-bindings-p)
                                                (assigns cgraph-alist-p)
                                                (sts cgraph-derivstates-p)
                                                (env$)
                                                (cgraph cgraph-p)
                                                (replimit posp)
                                                &optional
                                                (logicman 'logicman)
                                                (bvar-db 'bvar-db)
                                                (state 'state))
      :parents (fgl-counterexample-implementation-details)
      :guard (and (lbfr-listp (fgl-object-bindings-bfrlist x))
                  (bfr-env$-p env$ (logicman->bfrstate))
                  (equal (bfr-nvars) (next-bvar bvar-db))
                  (lbfr-listp (cgraph-bfrlist cgraph)))
      :returns (mv (new-assigns cgraph-alist-p)
                   (new-sts cgraph-derivstates-p))
      :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                     10
                     (len x))
      (if (atom x)
          (mv (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts))
        (if (mbt (and (consp (car x))
                      (pseudo-var-p (caar x))))
            (b* (((mv new-assigns new-sts) (cgraph-derive-assignments-obj (cdar x) assigns sts env$ cgraph replimit))
                 ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                                   (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
                  (mv new-assigns new-sts))
                 (assigns new-assigns)
                 (sts new-sts))
              (cgraph-derive-assignments-bindings (cdr x) assigns sts env$ cgraph replimit))
          (cgraph-derive-assignments-bindings (cdr x) assigns sts env$ cgraph replimit))))
    ///

    (std::defret-mutual-generate measure-decr-of-<fn>
      :rules ((t
               (:add-concl (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                               (cgraph-derive-assigns-measure cgraph assigns sts replimit)))
               (:add-keyword :rule-classes :linear)
               (:add-keyword :hints ('(:expand (<call>)))))))

    (std::defret-mutual-generate bfr-listp-of-<fn>
      :rules ((t
               (:add-hyp (lbfr-listp (cgraph-bfrlist cgraph)))
               (:each-formal :type fgl-object-p :var x :action (:add-hyp (lbfr-listp (fgl-object-bfrlist x))))
               (:each-formal :type fgl-object-bindings-p :var x :action (:add-hyp (lbfr-listp (fgl-object-bindings-bfrlist x))))
               (:each-formal :type fgl-objectlist-p :var x :action (:add-hyp (lbfr-listp (fgl-objectlist-bfrlist x))))
               (:each-formal :type cgraph-equivlist-p :var x :action (:add-hyp (lbfr-listp (cgraph-equivlist-bfrlist x))))
               (:each-formal :type cgraph-equivnode-p :var x :action (:add-hyp (lbfr-listp (cgraph-equivnode-bfrlist x))))
               (:each-formal :type cgraph-formulalist-p :var x :action (:add-hyp (lbfr-listp (cgraph-formulalist-bfrlist x))))
               (:each-formal :type cgraph-formula-p :var x :action (:add-hyp (lbfr-listp (cgraph-formula-bfrlist x))))
               (:each-return :type cgraph-formulalist-p :var x :action (:add-concl (lbfr-listp (cgraph-formulalist-bfrlist x))))
               (:each-return :type fgl-objectlist-p :var x :action (:add-concl (lbfr-listp (fgl-objectlist-bfrlist x))))
               (:add-keyword :hints ('(:expand (<call>)
                                       :in-theory (enable bfr-listp-when-not-member-witness))))))
      :mutual-recursion cgraph-derive-assignments)

    (local (defthm symbol-alistp-of-append
             (implies (and (symbol-alistp x)
                           (symbol-alistp y))
                      (symbol-alistp (append x y)))))
    
    (verify-guards cgraph-derive-assignments-obj-fn
      :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness))))
    
    (local (in-theory (enable fgl-object-bindings-fix)))
    (fty::deffixequiv-mutual cgraph-derive-assignments)))















;; ------------------------------------------------------------------------
;; Creating rules from user def-cgraph-rule forms.
;; ------------------------------------------------------------------------





(defconst *def-ctrex-rule-keys*
  '(:match
    :assigned-var
    :assign
    :assign-cond
    :match-conds
    ;; :hyp
    ;; :equiv
    :ruletype

    :unify-subst
    :target
    :deps
    :dep-success-vars
    :success
    :priority
    :value
    :order
    ))






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
       (ruletable (hons-acons x.fn (add-to-set-equal (change-ctrex-rule rule :match x)
                                                     (cdr (hons-get x.fn ruletable)))
                              ruletable)))
    (ctrex-rule-matches-to-ruletable (cdr matches) rule ruletable)))




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
       ((when erp) (er hard? erp "Failed to translate match pairs: ~@0" match))
       (value (or keys.assign keys.value))
       ((mv erp value) (ctrex-rule-translate value wrld))
       ((when erp) (er hard? erp "failed to translate value term: ~@0" value))
       (success (or keys.assign-cond keys.success t))
       ((mv erp success) (ctrex-rule-translate success wrld))
       ((when erp) (er hard? erp "failed to translate success term: ~@0" success))
       (priority (or keys.priority
                     (case keys.ruletype
                       (:elim *ctrex-elim-default-priority*)
                       (:property *ctrex-property-default-priority*)
                       (:fixup *ctrex-fixup-default-priority*)
                       (otherwise *ctrex-other-default-priority*))))
       ((mv erp priority) (ctrex-rule-translate priority wrld))
       ((when erp) (er hard? erp "failed to translate priority term: ~@0" priority))
       (target (or keys.assigned-var keys.target))
       ((mv erp target) (ctrex-rule-translate target wrld))
       ((when erp) (er hard? erp "failed to translate target term: ~@0" target))
       ((unless (ctrex-ruletype-p keys.ruletype))
        (er hard? 'def-ctrex-rule "Bad ruletype: must satisfy ~x0" 'ctrex-ruletype-p))
       ;; ((unless (pseudo-fnsym-p keys.equiv))
       ;;  (er hard? 'def-ctrex-rule "Bad equiv: must be a function symbol"))
       ((unless (acl2::doublet-listp keys.match-conds))
        (er hard? 'def-ctrex-rule "Bad match-conds: must be a doublet-list"))

       (dep-vars (remove-eq target (cmr::termlist-vars (strip-cdrs match))))
       (deps (append (pairlis$ dep-vars dep-vars) match))
       (dep-success-vars (or keys.dep-success-vars (acl2::doublets-to-alist keys.match-conds)))

       ((mv success value priority)
        (if (pseudo-term-case target :var)
            ;; If target is a variable and it is used in any of the formulas,
            ;; replace it with prev-value in those formulas.  If it has an
            ;; entry in dep-success-vars, replace that entry with
            ;; 'prev-successp in the formulas.
            (b* ((target-var (pseudo-term-var->name target))
                 (alist (list (cons target-var 'prev-value)))
                 (success-look (rassoc-eq target-var dep-success-vars))
                 (alist (if success-look (cons (cons (car success-look) 'prev-successp) alist) alist)))
              (mv (acl2::sublis-var alist success)
                  (acl2::sublis-var alist value)
                  (acl2::sublis-var alist priority)))
          (mv success value priority)))
       
       
       (rule (make-ctrex-rule :name name
                              :match nil
                              :unify-subst keys.unify-subst
                              :target target
                              :deps deps
                              :dep-success-vars dep-success-vars
                              :success success
                              :priority priority
                              :value value
                              :order (or keys.order
                                         (case keys.ruletype
                                           (:elim (1+ *ctrex-order-first*))
                                           (:property *ctrex-order-mid*)
                                           (:fixup *ctrex-order-last*)
                                           (otherwise *ctrex-order-mid*)))
                              :ruletype keys.ruletype)))
    `(table fgl-ctrex-rules nil (ctrex-rule-matches-to-ruletable
                                 ',match ',rule
                                 (make-fast-alist
                                  (table-alist 'fgl-ctrex-rules world)))
            :clear)))

(defmacro def-ctrex-rule (name &rest args)
  `(make-event
    (def-ctrex-rule-fn ',name ',args (w state))))

(defxdoc def-ctrex-rule
  :parents (fgl-counterexamples)
  :short "Define a rule that helps FGL derive term-level counterexamples from Boolean assignments."
  :long "<p>This form defines an informal rule that FGL may use to help derive
assignments for theorem variables from the Boolean assignments returned by SAT
solvers.  During this process (see @(see fgl-counterexamples)), various FGL objects
are assigned concrete values, and we use these values to derive further assignments.</p>

<p>A counterexample rule tells how to derive a new assignment from some
existing assignments.  An example:</p>

@({
 (def-ctrex-rule intcar-intcdr-ctrex-elim
   :match ((car (intcar x))
           (cdr (intcdr x)))
   :match-conds ((cdr-match cdr)
                 (car-match car))
   :assign (let ((cdr (if cdr-match cdr (intcdr x)))
                 (car (if car-match car (intcar x))))
             (intcons car cdr))
   :assigned-var x
   :ruletype :elim)
 })

<p>The rule is stored under an arbitrary name, the first argument.  The rest of the arguments:</p>
<ul>

<li>@(':match') gives a list of bindings @('(var expr)').  When applying the
rule, one or more of the @('expr') entries must be matched against an object
with an existing assignment.  For example, to apply the above rule we must have
an assignment of a value to some term matching @('(intcar x)'), @('(intcdr
x)'), or both.  These assignments may come from three origins -- 1. the term
may be one that is assigned a Boolean variable in the Boolean variable
database (see @(see fgl-getting-bits-from-objects)); 2. the term may be contain
no variables and thus be evaluated under the Boolean assignment; 3. the term
may be given an assignment by applying other counterexample rules.</li>

<li>@(':assigned-var') and @(':assign') respectively give the term to be
assigned the value and the value.  In the above case, the subterm @('x') from
that matched expressions is assigned the value @('(intcons car cdr)'), where
@('car') and @('cdr') are the values assigned for the respective expressions,
if they were assigned.  If not, @('x') may have been tentatively assigned a
value by a previous rule and its @('intcar') or @('intcdr') may be
preserved.</li>

<li>@(':match-conds') provide variables that say whether a value was determined
for the given variable.  In this case, @('cdr-match') will be true if
@('(intcdr x)') (the binding of @('cdr') in the @(':match') field)) was
successfully assigned a value.</li>

<li>@(':ruletype') may be @(':elim'), @(':property'), or @(':fixup'), signifying how the rule
is intended to be used.  An @(':elim') rule should be applied once when as many
of the match expressions as possible have been assigned values; at that point,
we apply the rule and compute the final value for the subexpression.  A
@(':property') rule may be applied to several different matching expressions in
order to compute a value for the same subexpression. A @(':fixup') rule is placed
last in the order and is intended to fix up a previously assigned value.</li>

<li>An additional keyword @(':assign-cond') must (if provided) be a term, which
will be evaluated in the same way as @(':assign').  If it evaluates to a
non-@('nil') value, then the value is assigned; if not, the rule does not
provide an assignment.</li>

</ul>

<p>An example of a property rule:</p>

@({
 (def-ctrex-rule assoc-equal-ctrex-rule
   :match ((pair (assoc-equal k x)))
   :assign (put-assoc-equal k (cdr pair) x)
   :assigned-var x
   :ruletype :property)
 })

<p>This is a suitable property rule, but not an elim rule, because it may match
many assignments to @('(assoc-equal k x)') for different @('k') in order to
compute a value for @('x').</p>
")


(def-ctrex-rule intcar-intcdr-ctrex-elim
  :match ((car (intcar x))
          (cdr (intcdr x)))
  :match-conds ((cdr-match cdr)
                (car-match car)
                (x-match x))
  :assign (let ((cdr (if cdr-match cdr (intcdr x)))
                (car (if car-match car (intcar x))))
            (intcons car cdr))
  :assigned-var x
  ;; :hyp (integerp x)
  :ruletype :elim)

(def-ctrex-rule car-cdr-ctrex-elim
  :match ((car (car x))
          (cdr (cdr x)))
  :match-conds ((cdr-match cdr)
                (car-match car))
  :assign (let ((cdr (if cdr-match cdr (cdr x)))
                (car (if car-match car (car x))))
            (cons car cdr))
  :assigned-var x
  ;; :hyp (consp x)
  :ruletype :elim)

(def-ctrex-rule assoc-equal-ctrex-rule
  :match ((pair (assoc-equal k x)))
  :assign (put-assoc-equal k (cdr pair) x)
  :assigned-var x
  ;; :hyp (alistp x)
  :ruletype :property)

;; (defconst *implicit-subterm-ctrex-rule-template*
;;   (make-ctrex-rule :name 'implicit-subterm-ctrex-rule
;;                    :assigned-var 'x
;;                    :ruletype :implicit))

(defun redundant-hons-acons (key val x)
  (if (hons-equal val (cdr (hons-get key x)))
      x
    (hons-acons key val x)))

(def-ctrex-rule hons-get-ctrex-rule
  :match ((val (cdr (hons-get k x))))
  :assign (redundant-hons-acons k val x)
  :assigned-var x
  :ruletype :property)




;; ------------------------------------------------------------------------
;; Deriving a cgraph and set of variable assignments for a counterexample
;; Top function: interp-st-infer-ctrex-var-assignments
;; ------------------------------------------------------------------------

(define cgraph-derive-assignments-for-vars ((x pseudo-var-list-p
                                               "list of variables to derive values for")
                                            (vals obj-alist-p
                                                  "accumulator of variable values")
                                            (assigns cgraph-alist-p
                                                     "accumulator of object values")
                                            (sts cgraph-derivstates-p
                                                 "accumulator of object derivstates")
                                            (env$ "Boolean assignment environment")
                                            (cgraph cgraph-p)
                                            (replimit posp)
                                            &optional
                                            (logicman 'logicman)
                                            (bvar-db 'bvar-db)
                                            (state 'state))
  :parents (fgl-counterexample-implementation-details)
  :returns (mv (new-vals obj-alist-p)
               (new-assigns cgraph-alist-p)
               (new-sts cgraph-derivstates-p))
  :guard (and (bfr-env$-p env$ (logicman->bfrstate))
              (equal (bfr-nvars) (next-bvar bvar-db))
              (lbfr-listp (cgraph-bfrlist cgraph)))
  (b* (((when (atom x))
        (mv (obj-alist-fix vals)
            (cgraph-alist-fix assigns)
            (cgraph-derivstates-fix sts)))
       (obj (g-var (car x)))
       ((mv assigns sts)
        (cgraph-derive-assignments-obj
         obj assigns sts env$ cgraph replimit))
       (pair (hons-get obj assigns))
       (vals (if pair
                 (cons (cons (pseudo-var-fix (car x))
                             (cgraph-value->val (cdr pair))) vals)
               vals)))
    (cgraph-derive-assignments-for-vars
     (cdr x) vals assigns sts env$ cgraph replimit)))

(define cgraph-derivstates-summarize-errors ((x cgraph-derivstates-p))
  :returns (errmsg-or-nil)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (fgl-object-p (caar x)))))
        (cgraph-derivstates-summarize-errors (cdr x)))
       (err1 (cgraph-derivstate->result-msg (cdar x))))
    (if err1
        (let ((rest (cgraph-derivstates-summarize-errors (cdr x))))
          (if rest
              (msg "~x0: ~@1~%~@2" (caar x) err1 rest)
            (msg "~x0: ~@1~%" (caar x) err1)))
      (cgraph-derivstates-summarize-errors (cdr x))))
  ///
  (local (in-theory (enable cgraph-derivstates-fix))))


(define ctrex-summarize-errors ((vars pseudo-var-list-p)
                                (vals obj-alist-p)
                                (errors))
  (b* ((diff (set-difference-eq (pseudo-var-list-fix vars)
                                (alist-keys (obj-alist-fix vals)))))
    (if diff
        (if errors
            (msg "Some variables were left unbound: ~x0.  Errors: ~@1"
                 diff
                 errors)
          (msg "Some variables were left unbound: ~x0. But there were no ~
                errors to help explain this!~%"
               diff))
      (if errors
          (msg "All variables were bound, but some errors occurred in the ~
                process: ~@0"
               errors)
        nil))))


(local (in-theory (disable w)))

(define bfr-env$-fix (env$ (bfrstate bfrstate-p))
  :prepwork ((local (in-theory (enable bfr-env$-p))))
  :returns (new-env$ (bfr-env$-p new-env$ bfrstate))
  (bfrstate-case
    :bdd (stobj-let ((bitarr (env$->bitarr env$)))
                    (bitarr)
                    (if (<= (bfrstate->bound bfrstate) (bits-length bitarr))
                        bitarr
                      (resize-bits (max (bfrstate->bound bfrstate) (* 2 (bits-length bitarr)))
                                   bitarr))
                    env$)
    :aig env$
    :aignet (stobj-let ((bitarr (env$->bitarr env$)))
                    (bitarr)
                    (if (< (bfrstate->bound bfrstate) (bits-length bitarr))
                        bitarr
                      (resize-bits (max (+ 1 (bfrstate->bound bfrstate)) (* 2 (bits-length bitarr)))
                                   bitarr))
                    env$))
  ///
  (defthm bfr-env$-fix-when-bfr-env$-p
    (implies (and (bfr-env$-p env$ bfrstate)
                  (env$p env$))
             (equal (bfr-env$-fix env$ bfrstate) env$))))

(define interp-st-infer-ctrex-var-assignments ((vars pseudo-var-list-p)
                                               (interp-st interp-st-bfrs-ok)
                                               (state))
  :returns (mv (errmsg)
               (new-interp-st))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-listp-when-not-member-witness))))
  (b* ((cgraph (interp-st->cgraph interp-st))
       (memo (interp-st->cgraph-memo interp-st))
       (cgraph-index (interp-st->cgraph-index interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (bvar-db (interp-st->bvar-db interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (errmsg cgraph memo cgraph-index env$ assigns)
               (b* ((env$ (bfr-env$-fix env$ (logicman->bfrstate)))
                    (ruletable (make-fast-alist (table-alist 'fgl-ctrex-rules (w state))))
                    ((unless (and (ctrex-ruletable-p ruletable)
                                  (ctrex-ruletable-bfr-free ruletable)))
                     (mv "bad ctrex-ruletable~%" cgraph memo cgraph-index env$ nil))
                    ((mv cgraph memo) ;; (bvar-db-update-cgraph cgraph cgraph-index bvar-db ruletable (w state))
                     (bvar-db-update-cgraph cgraph memo cgraph-index bvar-db ruletable
                                            (logicman->bfrstate)
                                            (w state)))
                    ((mv var-vals assigns sts)
                     (cgraph-derive-assignments-for-vars vars nil nil nil env$ cgraph 2))
                    (- (fast-alist-free assigns))
                    (sts (fast-alist-free (fast-alist-clean sts)))
                    (deriv-errors (cgraph-derivstates-summarize-errors sts))
                    (env$ (update-env$->obj-alist var-vals env$))
                    (full-deriv-errors (ctrex-summarize-errors vars var-vals deriv-errors)))
                 (mv full-deriv-errors cgraph memo (next-bvar bvar-db) env$ assigns))
               (b* ((interp-st (update-interp-st->cgraph cgraph interp-st))
                    (interp-st (update-interp-st->cgraph-memo memo interp-st))
                    (interp-st (update-interp-st->cgraph-index cgraph-index interp-st))
                    (interp-st (interp-st-put-user-scratch :ctrex-assigns assigns interp-st) ))
                 (mv errmsg interp-st))))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness))))

  (defret bfr-env$-p-of-<fn>
    (implies (and ;; (not errmsg)
                  (equal bfrstate (logicman->bfrstate (interp-st->logicman interp-st))))
             (bfr-env$-p (interp-st->ctrex-env new-interp-st) bfrstate))))





;; ------------------------------------------------------------------------
;; Checking consistency of a counterexample with bvar-db assignments
;; ------------------------------------------------------------------------


(fty::deftagsum bvar-db-consistency-error
  (:eval-error ((obj fgl-object-p)
                (msg)))
  (:inconsistency ((obj fgl-object-p)
                   (var-val)
                   (obj-val)))
  :layout :tree)

(fty::deflist bvar-db-consistency-errorlist :elt-type bvar-db-consistency-error :true-listp t)


(define summarize-bvar-db-consistency-errorlist ((x bvar-db-consistency-errorlist-p))
  (if (atom x)
      nil
    (cons (b* ((x1 (car x)))
            (bvar-db-consistency-error-case x1
              :eval-error
              (list :eval-error (summarize-fgl-object x1.obj) x1.msg)
              :inconsistency
              (list :inconsistency (summarize-fgl-object x1.obj)
                    :var-val x1.var-val
                    :obj-val x1.obj-val)))
          (summarize-bvar-db-consistency-errorlist (cdr x)))))


(define bvar-db-check-ctrex-consistency ((n natp)
                                         bvar-db logicman env$ state
                                         (acc bvar-db-consistency-errorlist-p))
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (next-bvar bvar-db))
              (equal (next-bvar bvar-db) (bfr-nvars))
              (lbfr-listp (bvar-db-bfrlist bvar-db))
              (bfr-env$-p env$ (logicman->bfrstate)))
  :guard-hints (("goal" :in-theory (enable bfr-varname-p)))

  :returns (errs bvar-db-consistency-errorlist-p)
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* ((acc (bvar-db-consistency-errorlist-fix acc))
       ((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql n (next-bvar bvar-db))))
        acc)
       (var (bfr-var n logicman))
       (obj (get-bvar->term n bvar-db))
       (var-val (bfr-eval-fast var env$))
       ((mv eval-err obj-val) (magic-fgl-object-eval obj env$))
       (acc (cond (eval-err (cons (make-bvar-db-consistency-error-eval-error :obj obj :msg eval-err)
                                  acc))
                  ((xor var-val obj-val)
                   (cons (make-bvar-db-consistency-error-inconsistency :obj obj :var-val var-val :obj-val obj-val)
                         acc))
                  (t acc))))
    (bvar-db-check-ctrex-consistency (1+ (lnfix n)) bvar-db logicman env$ state acc)))


(define interp-st-check-bvar-db-ctrex-consistency ((interp-st interp-st-bfrs-ok)
                                                   (state))
  :returns (new-interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st))
              (env$ (interp-st->ctrex-env interp-st)))
             (err consistency-result)
             (b* (((unless (bfr-env$-p env$ (logicman->bfrstate)))
                   (mv "Bad counterexample env" nil)))
               (mv nil
                   (bvar-db-check-ctrex-consistency
                    (base-bvar bvar-db) bvar-db logicman env$ state nil)))
             (b* (((when err)
                   (cw "Error checking bvar-db consistency: ~@0" err)
                   interp-st)
                  (interp-st
                   (interp-st-put-user-scratch :bvar-db-ctrex-consistency-errors consistency-result interp-st)))
               (and consistency-result
                    (cw "Inconsistencies in bvar-db counterexample (~x0 total). See error list: ~x1.~%"
                        (len consistency-result)
                        '(cdr (hons-get :bvar-db-ctrex-consistency-errors (@ :fgl-user-scratch)))))
               interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :user-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))








;; ------------------------------------------------------------------------
;; Interp-st-counterex-bindings: get the counterexample's values for a
;; set of fgl-object bindings
;; ------------------------------------------------------------------------


(defines fgl-object-vars
  (define fgl-object-vars ((x fgl-object-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :verify-guards nil
    (fgl-object-case x
      :g-var (add-to-set-eq x.name (pseudo-var-list-fix acc))
      :g-apply (fgl-objectlist-vars x.args acc)
      :g-ite (fgl-object-vars x.test (fgl-object-vars x.then (fgl-object-vars x.else acc)))
      :g-cons (fgl-object-vars x.car (fgl-object-vars x.cdr acc))
      :g-map (fgl-object-alist-vars x.alist acc)
      :otherwise (pseudo-var-list-fix acc)))

  (define fgl-objectlist-vars ((x fgl-objectlist-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (if (atom x)
        (pseudo-var-list-fix acc)
      (fgl-objectlist-vars (cdr x) (fgl-object-vars (car x) acc))))

  (define fgl-object-alist-vars ((x fgl-object-alist-p) (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    (if (atom x)
        (pseudo-var-list-fix acc)
      (fgl-object-alist-vars (cdr x)
                            (if (mbt (consp (car x)))
                                (fgl-object-vars (cdar x) acc)
                              acc))))
  ///
  (verify-guards fgl-object-vars)

  (local (defthm fgl-object-alist-fix-when-bad-car
           (implies (and (consp x) (not (Consp (car x))))
                    (equal (fgl-object-alist-fix x)
                           (fgl-object-alist-fix (cdr x))))
           :hints(("Goal" :in-theory (enable fgl-object-alist-fix)))))

  (fty::deffixequiv-mutual fgl-object-vars))

(define counterex-bindings-summarize-errors (infer-errors eval-errors)
  (if infer-errors
      (if eval-errors
          (msg "~@0~%~@1" infer-errors eval-errors)
        (msg "~@0" infer-errors))
    (and eval-errors (msg "~@0" eval-errors))))


(local (defthm fgl-objectlist-p-alist-vals-of-fgl-object-bindings
         (implies (fgl-object-bindings-p x)
                  (fgl-objectlist-p (alist-vals x)))
         :hints(("Goal" :in-theory (enable alist-vals)))))

(local (defthm fgl-objectlist-bfrlist-alist-vals-of-fgl-object-bindings
         (implies (fgl-object-bindings-p x)
                  (equal (fgl-objectlist-bfrlist (alist-vals x))
                         (fgl-object-bindings-bfrlist x)))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist
                                           alist-vals)))))

(local (defthm symbol-listp-keys-of-fgl-object-bindings
         (implies (fgl-object-bindings-p x)
                  (symbol-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(define interp-st-counterex-bindings ((x fgl-object-bindings-p)
                                      (interp-st)
                                      (state))
  :returns (mv (errmsg)
               (bindings-vals symbol-alistp)
               (var-vals obj-alist-p)
               (new-interp-st))
  :guard (and (interp-st-bfrs-ok interp-st)
              (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable interp-st-bfrs-ok
                                          bfr-listp-when-not-member-witness))))
  :prepwork ((local (defthm fgl-object-alist-p-when-fgl-object-bindings-p
                      (implies (fgl-object-bindings-p x)
                               (fgl-object-alist-p x))
                      :hints(("Goal" :in-theory (enable fgl-object-alist-p
                                                        fgl-object-bindings-p))))))
  (b* ((x (fgl-object-bindings-fix x))
       (vars (fgl-object-alist-vars x nil))
       ((mv infer-err interp-st)
        (interp-st-infer-ctrex-var-assignments vars interp-st state))
       ;; ((when err)
       ;;  (mv (msg "Error inferring counterexample term-level variable assignments: ~@0" err)
       ;;      nil nil interp-st))
       )
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (eval-err binding-vals var-vals)
               (b* (((mv eval-err objs) (magic-fgl-objectlist-eval (alist-vals x) env$))
                    ;; (errmsg (ctrex-eval-summarize-errors eval-err full-deriv-errors))
                    (binding-vals (pairlis$ (alist-keys x) objs))
                    (var-vals (env$->obj-alist env$)))
                 (mv eval-err binding-vals var-vals))
               (mv (counterex-bindings-summarize-errors infer-err eval-err)
                   binding-vals  var-vals interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))



;; ------------------------------------------------------------------------
;; Utilities for computing/accessing counterexamples in rewrite rules
;; interp-st-counterex-value, interp-st-counterex-stack-bindings,
;; interp-st-counterex-prev-bindings,
;; and /print-errors variants
;; ------------------------------------------------------------------------

(define interp-st-counterex-value ((x fgl-object-p)
                                   (interp-st)
                                   (state))
  :returns (mv (errmsg)
               (x-val)
               (new-interp-st))
  :guard (and (interp-st-bfrs-ok interp-st)
              (interp-st-bfr-listp (fgl-object-bfrlist x)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable interp-st-bfrs-ok
                                          bfr-listp-when-not-member-witness))))
  :prepwork ((local (defthm fgl-object-alist-p-when-fgl-object-bindings-p
                      (implies (fgl-object-bindings-p x)
                               (fgl-object-alist-p x))
                      :hints(("Goal" :in-theory (enable fgl-object-alist-p
                                                        fgl-object-bindings-p))))))
  (b* ((x (fgl-object-fix x))
       (vars (fgl-object-vars x nil))
       ((mv infer-err interp-st)
        (interp-st-infer-ctrex-var-assignments vars interp-st state))
       ;; ((when err)
       ;;  (mv (msg "Error inferring counterexample term-level variable assignments: ~@0" err)
       ;;      nil nil interp-st))
       )
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (eval-err x-val)
               (magic-fgl-object-eval x env$)
               (mv (counterex-bindings-summarize-errors infer-err eval-err)
                   x-val interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))




(define interp-st-counterex-stack-bindings ((interp-st interp-st-bfrs-ok)
                                            (state))
  :returns (mv errmsg
               (bindings-vals symbol-alistp)
               (var-vals obj-alist-p)
               (new-interp-st))
  :guard-hints ('(:in-theory (enable interp-st-bfrs-ok
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     stack$a-bindings
                                     stack$a-minor-bindings
                                     bfr-listp-when-not-member-witness)
                  :expand ((major-stack-bfrlist (interp-st->stack interp-st))
                           (minor-stack-bfrlist (major-frame->minor-stack (car (interp-st->stack interp-st)))))))
  (b* ((bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st))))
    (interp-st-counterex-bindings bindings interp-st state))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))


;; (verify-termination evisc-tuple)
;; (verify-guards evisc-tuple)

(define interp-st-counterex-stack-bindings/print-errors ((interp-st interp-st-bfrs-ok)
                                                                (state))
  :returns (mv (bindings-vals symbol-alistp)
               (var-vals obj-alist-p)
               (new-interp-st))
  (b* (((mv errmsg bindings-vals var-vals interp-st)
        (interp-st-counterex-stack-bindings interp-st state)))
    (and errmsg
         (acl2::fmt-to-comment-window
          "~@0" `((#\0 . ,errmsg)) 0
          (evisc-tuple 8 20 nil nil)
          nil))
    (mv bindings-vals var-vals interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))

(define interp-st-counterex-bindings/print-errors ((x fgl-object-bindings-p)
                                                          (interp-st)
                                                          (state))
  :returns (mv (bindings-vals symbol-alistp)
               (var-vals obj-alist-p)
               (new-interp-st))
  :guard (and (interp-st-bfrs-ok interp-st)
              (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
  (b* (((mv errmsg bindings-vals var-vals interp-st)
        (interp-st-counterex-bindings x interp-st state)))
    (and errmsg
         (acl2::fmt-to-comment-window
          "~@0" `((#\0 . ,errmsg)) 0
          (evisc-tuple 8 20 nil nil)
          nil))
    (mv bindings-vals var-vals interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))




(define interp-st-prev-bindings ((interp-st))
  :guard (< 1 (interp-st-stack-frames interp-st))
  :guard-hints (("Goal" :in-theory (enable interp-st-stack-frames
                                           stack$a-nth-frame-minor-frames)))
  :returns (bindings fgl-object-bindings-p)
  :prepwork ((local (defthm len-when-minor-stack-p
                      (implies (minor-stack-p x)
                               (< 0 (len x)))
                      :hints(("Goal" :in-theory (enable len minor-stack-p)))
                      :rule-classes :linear)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (append (stack-nth-frame-minor-bindings 1 0 stack)
                     (stack-nth-frame-bindings 1 stack))
             bindings))

(local (defthm major-frame-bfrlist-of-nth
         (implies (not (member v (major-stack-bfrlist x)))
                  (not (member v (major-frame-bfrlist (nth n x)))))
         :hints(("Goal" :in-theory (enable major-stack-bfrlist nth)))))


(define interp-st-counterex-stack-prev-bindings/print-errors ((interp-st interp-st-bfrs-ok)
                                                                state)
  :guard (< 1 (interp-st-stack-frames interp-st))
  :guard-hints (("goal" :in-theory (enable interp-st-prev-bindings
                                           stack$a-nth-frame-bindings
                                           stack$a-nth-frame-minor-bindings
                                           BFR-LISTP-WHEN-NOT-MEMBER-WITNESS)))
  :returns (mv (bindings-vals symbol-alistp)
               (var-vals obj-alist-p)
               (new-interp-st))
  (b* ((bindings (interp-st-prev-bindings interp-st)))
    (interp-st-counterex-bindings/print-errors bindings interp-st state))
  ///
  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
                       :equiv-contexts :reclimit :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))



;; ------------------------------------------------------------------------
;; Top level function for computing/runnign a counterexample after a SAT check:
;; interp-st-run-ctrex
;; ------------------------------------------------------------------------


(define interp-st-run-ctrex (sat-config
                             (interp-st interp-st-bfrs-ok)
                             state)
  :returns (mv errmsg new-interp-st)
  (b* ((goal (cdr (hons-get :goal-term (interp-st->user-scratch interp-st))))
       ((unless (pseudo-termp goal))
        (mv (msg "Goal term malformed: ~x0~%" goal) interp-st))
       (bindings (variable-g-bindings (term-vars goal)))
       ((mv sat-ctrex-err interp-st)
        (interp-st-sat-counterexample sat-config interp-st state))
       ((when sat-ctrex-err)
        (mv (msg "Error retrieving SAT counterexample: ~@0~%" sat-ctrex-err) interp-st))
       ((mv ctrex-errmsg ctrex-bindings ?var-vals interp-st)
        (interp-st-counterex-bindings bindings interp-st state))
       (- (and ctrex-errmsg
               (fmt-to-comment-window
                "Warnings/errors from deriving counterexample: ~@0~%"
                (list (cons #\0 ctrex-errmsg))
                0 '(nil 7 10 nil) 10)))
       ;; ((when ctrex-errmsg)
       ;;  (mv (msg "Error extending counterexample: ~@0~%" ctrex-errmsg) interp-st state))
       (- (cw "~%*** Counterexample assignment: ***~%~x0~%~%" ctrex-bindings))
       (- (cw "Running counterexample on top-level goal:~%"))
       ((mv err ans) (magitastic-ev goal ctrex-bindings 1000 state t t))
       (- (cond (err (cw "Error running goal on counterexample: ~@0~%" err))
                (ans (cw "False counterexample -- returned: ~x0.  See ~
                          warnings/errors from counterexample derivation ~
                          above.~%" ans))
                (t   (cw "Counterexample verified!~%"))))
       (interp-st (interp-st-check-bvar-db-ctrex-consistency interp-st state))
       (scratch (interp-st->user-scratch interp-st))
       ;; Collect counterexamples in the user scratch for later extraction
       (interp-st (update-interp-st->user-scratch
                   (hons-acons ':counterexamples
                               (cons ctrex-bindings
                                     (cdr (hons-get ':counterexamples scratch)))
                               scratch)
                   interp-st))
       (interp-st (update-interp-st->debug-info (cons "Counterexample." ctrex-bindings) interp-st)))
    (mv nil interp-st)))

