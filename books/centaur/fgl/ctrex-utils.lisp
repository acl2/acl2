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
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable resize-list)))
(local (std::add-default-post-define-hook :fix))
(set-state-ok t)

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

;;   The "smarter" version: we create a "cgraph" with an edge A->B whenever
;;   obtaining a value for B might help derive a value for A (via one of the
;;   counterexample translation rules). Edges are labeled with the rule and
;;   substitution that gives rise to that derivation.  Often A is an immediate
;;   subterm of B, but this isn't always the case.  To get a variable-level
;;   counterexample, we then traverse the cgraph depth-first starting from the
;;   variables, trying to find a value for each term after finding values for
;;   all of its descendants.

;;   If there are any SCCs containing
;;   multiple terms in the graph, then we try to recover a value for each term
;;   in arbitrary order and check whether we get to a fixpoint.

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
   :assign (intcons car cdr)
   :assigned-var x
   :ruletype :elim)
 })

<p>The rule is stored under an arbitrary name, the first argument.  The rest of the arguments:</p>
<ul>

<li>@(':match') gives a list of bindings @('(var expr)').  When applying the
rule, one or more of the @('expr') entries must be matched against an object
with an existing assignment.  For example, to apply the above rule we must have
an assignment of a value to some term matching @('(intcar x)'), @('(intcdr
x)'), or both.</li>

<li>@(':assigned-var') and @(':assign') respectively give the term to be
assigned the value and the value.  In the above case, the subterm @('x') from
that matched expressions is assigned the value @('(intcons car cdr)'), where
@('car') and @('cdr') are the values assigned for the respective expressions.</li>

<li>@(':ruletype') may be @(':elim') or @(':property'), signifying how the rule
is intended to be used.  An @(':elim') rule should be applied once when as many
of the match expressions as possible have been assigned values; at that point,
we apply the rule and compute the final value for the subexpression.  A
@(':property') rule may be applied to several different matching expressions in
order to compute a value for the same subexpression.</li>

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


(defconst *fake-ctrex-rule-for-equivs*
  (make-ctrex-rule :name 'fake-ctrex-rule-for-equivs
                   :match '((val . (equiv x y)))
                   :assign '(if val y x)
                   :assigned-var 'x
                   :hyp 't
                   :ruletype nil))

(include-book "unify-thms")

(defthm fgl-unify-concrete-produces-concrete-objs
  (b* (((mv ?flag new-alist) (fgl-unify-concrete pat x alist)))
    (implies (and flag (not (hons-assoc-equal k alist)))
             (equal (fgl-object-kind (cdr (hons-assoc-equal k new-alist)))
                    :g-concrete)))
  :hints(("Goal" :in-theory (e/d ((:i fgl-unify-concrete))
                                 (logcar logcdr))
          :induct (fgl-unify-concrete pat x alist))
         (acl2::use-termhint
          `(:expand ((fgl-unify-concrete ,(acl2::hq pat)
                                          ,(acl2::hq x)
                                          ,(acl2::hq alist)))))))

(encapsulate nil
  (make-event
   (let ((wrld (w state))
         (fn 'fgl-unify-term/gobj-fn))
     `(flag::make-flag ,(flag::flag-fn-name fn wrld) ,fn
                       :defthm-macro-name ,(flag::flag-defthm-macro fn wrld)
                       :flag-mapping ,(acl2::alist-to-doublets (flag::flag-alist fn wrld))
                       :local t
                       :hints ((and stable-under-simplificationp
                                    '(:expand ((pseudo-term-count pat)
                                               (pseudo-term-list-count (pseudo-term-call->args pat))
                                               (pseudo-term-list-count (cdr (pseudo-term-call->args pat))))))))))

  (local (defthm fgl-object-count-of-mk-g-boolean
           (equal (fgl-object-count (mk-g-boolean x)) 1)
           :hints(("Goal" :in-theory (enable mk-g-boolean fgl-object-count)))))

  (local (defthm fgl-object-count-of-mk-g-integer
           (equal (fgl-object-count (mk-g-integer x)) 1)
           :hints(("Goal" :in-theory (enable mk-g-integer fgl-object-count)))))

  (local (defthm fgl-object-count-when-g-concrete
           (implies (fgl-object-case x :g-concrete)
                    (equal (fgl-object-count x) 1))
           :hints(("Goal" :in-theory (enable fgl-object-count)))))

  (local (in-theory (disable len acl2::member-of-cons member-equal)))

  (local (defthm fgl-object-count-of-gobj-syntactic-boolean-fix
           (<= (fgl-object-count (mv-nth 1 (gobj-syntactic-boolean-fix x)))
               (fgl-object-count x))
           :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix
                                             fgl-object-count)))
           :rule-classes :linear))

  (local (defthm fgl-object-count-of-gobj-syntactic-boolean-negate
           (<= (fgl-object-count (gobj-syntactic-boolean-negate x))
               (fgl-object-count x))
           :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-negate
                                             fgl-object-count)))
           :rule-classes :linear))



  (std::defret-mutual-generate fgl-object-count-of-<fn>
    :rules
    ((t (:add-hyp (and flag
                       (not (hons-assoc-equal k alist))
                       (hons-assoc-equal k new-alist)))
        (:add-keyword :hints ('(:expand ((:free (x-key) <call>)))
                              (and stable-under-simplificationp
                                   '(:expand ((:free (x y) (fgl-object-count (g-cons x y)))
                                              (:free (x) (fgl-object-count (g-concrete x)))
                                              (:free (x) (fgl-object-count (g-map '(:g-map) x))))))
                              (and stable-under-simplificationp
                                   '(:expand ((fgl-object-count x)))))))
     ((:fnname fgl-unify-term/gobj)
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (fgl-object-count x))))
     ((:fnname fgl-unify-term/gobj-commutative-args)
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (max (fgl-object-count x1)
                (fgl-object-count x2)))))
     ((or (:fnname fgl-unify-term/gobj-if)
          (:fnname fgl-unify-term/gobj-if1))
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (max (fgl-object-count x-test)
                (max (fgl-object-count x-then)
                     (fgl-object-count x-else))))))
     ((:fnname fgl-unify-term/gobj-fn/args)
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (fgl-objectlist-count x-args))))
     ((:fnname fgl-unify-term/gobj-list)
      (:add-concl
       (< (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
          (fgl-objectlist-count x))))
     ((:fnname fgl-unify-term/gobj-map)
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (+ 3 (fgl-object-alist-count x)))))
     ((:fnname fgl-unify-term/gobj-map-pair)
      (:add-concl
       (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
           (+ 4 (fgl-object-count val-obj))))))
    :mutual-recursion fgl-unify-term/gobj)



  (defthmd fgl-object-count-of-fgl-unify-term/gobj-casesplit
    (b* (((mv flag new-alist)
          (fgl-unify-term/gobj pat x alist)))
      (implies (and flag
                    (case-split (not (hons-assoc-equal k alist)))
                    (hons-assoc-equal k new-alist))
               (<= (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
                   (fgl-object-count x))))
    :rule-classes :linear)

  (local (defthm <=-max-forward-3
           (implies (and (<= x (max y (max z w)))
                         (natp y) (natp z) (natp w))
                    (<= x (+ y z w)))
           :rule-classes :forward-chaining))

  (local (defthm <=-max-forward-2
           (implies (and (<= x (max y z))
                         (natp y) (natp z))
                    (<= x (+ y z)))
           :rule-classes :forward-chaining))

  (local (in-theory (enable fgl-object-count-of-fgl-unify-term/gobj-casesplit)))
  (local (in-theory (disable max)))
  (defthm fgl-object-count-of-fgl-unify-term/gobj-strict
    (b* (((mv flag new-alist)
          (fgl-unify-term/gobj pat x alist)))
      (implies (and flag (not (hons-assoc-equal k alist))
                    (hons-assoc-equal k new-alist)
                    (not (pseudo-term-case pat :var))
                    (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map))))
               (< (fgl-object-count (cdr (hons-assoc-equal k new-alist)))
                  (fgl-object-count x))))
    :hints (("goal" :expand ((fgl-unify-term/gobj pat x alist)
                             (fgl-object-count x)))
            (and stable-under-simplificationp
                 '(:expand ((fgl-objectlist-count (g-apply->args x))
                            (fgl-objectlist-count (cdr (g-apply->args x))))
                   :use ((:instance fgl-object-count-of-fgl-unify-term/gobj-commutative-args
                          (pat1 (car (pseudo-term-call->args pat)))
                          (pat2 (cadr (pseudo-term-call->args pat)))
                          (x1 (car (g-apply->args x)))
                          (x2 (cadr (g-apply->args x))))
                         (:instance fgl-object-count-of-fgl-unify-term/gobj-commutative-args
                          (pat1 (car (pseudo-term-call->args pat)))
                          (pat2 (cadr (pseudo-term-call->args pat)))
                          (x2 (car (g-apply->args x)))
                          (x1 (cadr (g-apply->args x))))
                         (:instance fgl-object-count-of-fgl-unify-term/gobj-if
                          (pat-test (car (pseudo-term-call->args pat)))
                          (pat-then (cadr (pseudo-term-call->args pat)))
                          (pat-else (caddr (pseudo-term-call->args pat)))
                          (x-test (g-ite->test x))
                          (x-then (g-ite->then x))
                          (x-else (g-ite->else x)))
                         (:instance fgl-object-count-of-fgl-unify-term/gobj-if
                          (pat-test (car (pseudo-term-call->args pat)))
                          (pat-then (cadr (pseudo-term-call->args pat)))
                          (pat-else (caddr (pseudo-term-call->args pat)))
                          (x-test (gobj-syntactic-boolean-negate
                                   (mv-nth 1
                                           (gobj-syntactic-boolean-fix (g-ite->test x)))))
                          (x-then (g-ite->else x))
                          (x-else (g-ite->then x)))
                         (:instance fgl-object-count-of-fgl-unify-term/gobj-fn/args
                          (pat-fn (pseudo-term-fncall->fn pat))
                          (pat-args (pseudo-term-call->args pat))
                          (x-fn (g-apply->fn x))
                          (x-args (g-apply->args x)))
                         ;; (:instance fgl-object-count-of-fgl-unify-term/gobj-map
                         ;;  (pat pat)
                         ;;  (x (g-map->alist x)))
                         )
                   :in-theory (disable fgl-object-count-of-fgl-unify-term/gobj-commutative-args
                                       fgl-object-count-of-fgl-unify-term/gobj-if
                                       fgl-object-count-of-fgl-unify-term/gobj-fn/args
                                       ;; fgl-object-count-of-fgl-unify-term/gobj-map
                                       ))))
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
  (local (defthm fgl-object-bindings-bfrlist-of-fast-alist-fork
           (implies (and (not (member v (fgl-object-bindings-bfrlist x)))
                         (not (member v (fgl-object-bindings-bfrlist y))))
                    (not (member v (fgl-object-bindings-bfrlist (fast-alist-fork x y)))))
           :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist fast-alist-fork)))))

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
                         (subst fgl-object-bindings-p)
                         (rule ctrex-rule-p)
                         (cgraph cgraph-p))
  :returns (new-cgraph cgraph-p)
  (b* (((ctrex-rule rule))
       (to (cdr (hons-assoc-equal rule.assigned-var (fgl-object-bindings-fix subst))))
       (edge (make-cgraph-edge :match-vars (list matchvar) :rule rule :subst subst))
       (cgraph (cgraph-fix cgraph))
       (edges (cdr (hons-get to cgraph)))
       ((mv found new-edges) (add-cgraph-edge-join edge edges))
       (new-edges (if found new-edges (cons edge edges))))
    (hons-acons to new-edges cgraph))
  ///
  (defret cgraph-edgelist-bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindings-bfrlist subst)))
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

(defines fgl-object-add-to-cgraph
  (define fgl-object-add-to-cgraph ((x fgl-object-p)
                                   (cgraph cgraph-p)
                                   (memo cgraph-alist-p)
                                   (ruletable ctrex-ruletable-p)
                                   (bfrstate bfrstate-p)
                                   (wrld plist-worldp))
    :well-founded-relation acl2::nat-list-<
    :measure (list (fgl-object-count x) 10 0 0)
    :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
    :guard (bfr-listp (fgl-object-bfrlist x))
    :verify-guards nil
    (b* ((fnsym (fgl-object-case x
                  (:g-ite 'if)
                  (:g-cons 'cons)
                  (:g-apply x.fn)
                  (otherwise nil)))
         ((unless fnsym)
          (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((when (hons-get (fgl-object-fix x) (cgraph-alist-fix memo)))
          (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         (memo (hons-acons (fgl-object-fix x) t (cgraph-alist-fix memo)))
         ((when (and (fgl-object-case x :g-apply)
                     (fgetprop fnsym 'acl2::coarsenings nil wrld)))
          ;; Equivalence relation.  Add edges between two args
          (b* (((g-apply x))
               ((unless (eql (len x.args) 2))
                (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
               ((list arg1 arg2) x.args)
               (rule1 (change-ctrex-rule *fake-ctrex-rule-for-equivs*
                                         :match `((val . ,(pseudo-term-call x.fn '(x y))))
                                         :equiv x.fn))
               (rule2 (change-ctrex-rule *fake-ctrex-rule-for-equivs*
                                         :match `((val . ,(pseudo-term-call x.fn '(y x))))
                                         :equiv x.fn))
               (cgraph (add-cgraph-edge 'val `((x . ,arg2) (y . ,arg1)) rule2 cgraph))
               (cgraph (add-cgraph-edge 'val `((x . ,arg1) (y . ,arg2)) rule1 cgraph))
               ((mv cgraph memo) (fgl-object-add-to-cgraph arg1 cgraph memo ruletable bfrstate wrld)))
            (fgl-object-add-to-cgraph arg2 cgraph memo ruletable bfrstate wrld)))
         (rules (cdr (hons-get fnsym (ctrex-ruletable-fix ruletable)))))
      (fgl-object-add-to-cgraph-rules x rules cgraph memo ruletable bfrstate wrld)))

  (define fgl-object-add-to-cgraph-rules ((x fgl-object-p)
                                         (rules ctrex-rulelist-p)
                                         (cgraph cgraph-p)
                                         (memo cgraph-alist-p)
                                         (ruletable ctrex-ruletable-p)
                                         (bfrstate bfrstate-p)
                                         (wrld plist-worldp))
    :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                (bfr-listp (fgl-object-bfrlist x)))
    :measure (list (fgl-object-count x) 7 (len rules) 0)
    :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
    (b* (((when (atom rules)) (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((mv cgraph memo) (fgl-object-add-to-cgraph-rule x (car rules) cgraph memo ruletable bfrstate wrld)))
      (fgl-object-add-to-cgraph-rules x (cdr rules) cgraph memo ruletable bfrstate wrld)))

  (define fgl-object-add-to-cgraph-rule ((x fgl-object-p)
                                        (rule ctrex-rule-p)
                                        (cgraph cgraph-p)
                                        (memo cgraph-alist-p)
                                        (ruletable ctrex-ruletable-p)
                                        (bfrstate bfrstate-p)
                                        (wrld plist-worldp))
    :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                (bfr-listp (fgl-object-bfrlist x)))
    :measure (list (fgl-object-count x) 7 0 0)
    :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
    (b* (((ctrex-rule rule)))
      (fgl-object-add-to-cgraph-matches x rule.match rule cgraph memo ruletable bfrstate wrld)))

  (define fgl-object-add-to-cgraph-matches ((x fgl-object-p)
                                           (matches pseudo-term-subst-p)
                                           (rule ctrex-rule-p)
                                           (cgraph cgraph-p)
                                           (memo cgraph-alist-p)
                                           (ruletable ctrex-ruletable-p)
                                           (bfrstate bfrstate-p)
                                           (wrld plist-worldp))
    :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                (bfr-listp (fgl-object-bfrlist x)))
    :measure (list (fgl-object-count x) 5 (len matches) 0)
    :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
    (b* (((when (atom matches)) (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((unless (mbt (and (consp (car matches))
                            (pseudo-var-p (caar matches)))))
          (fgl-object-add-to-cgraph-matches x (cdr matches) rule cgraph memo ruletable bfrstate wrld))
         ((mv cgraph memo) (fgl-object-add-to-cgraph-match x (caar matches) (cdar matches) rule cgraph memo ruletable bfrstate wrld)))
      (fgl-object-add-to-cgraph-matches x (cdr matches) rule cgraph memo ruletable bfrstate wrld)))

  (define fgl-object-add-to-cgraph-match ((x fgl-object-p)
                                         (matchvar pseudo-var-p)
                                         (match pseudo-termp)
                                         (rule ctrex-rule-p)
                                         (cgraph cgraph-p)
                                         (memo cgraph-alist-p)
                                         (ruletable ctrex-ruletable-p)
                                         (bfrstate bfrstate-p)
                                         (wrld plist-worldp))
    :guard (and (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))
                (bfr-listp (fgl-object-bfrlist x)))
    :measure (list (fgl-object-count x) 5 0 0)
    :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
    (b* (((when (pseudo-term-case match :var))
          (cw "Bad ctrex rule? Match is a variable: ~x0" (ctrex-rule->name rule))
          (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((unless (mbt (not (fgl-object-case x '(:g-concrete :g-boolean :g-integer :g-map)))))
          (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((mv ok subst) (fgl-unify-term/gobj match x nil))
         ((unless ok) (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         ((ctrex-rule rule))
         (to-look (hons-assoc-equal rule.assigned-var subst))
         ((unless to-look)
          (cw "Bad ctrex rule? ASSIGNED-VAR wasn't bound by match: ~x0" rule.name)
          (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
         (to (cdr to-look))
         (cgraph (add-cgraph-edge matchvar subst rule cgraph)))
      (fgl-object-add-to-cgraph to cgraph memo ruletable bfrstate wrld)))
  ///
  (verify-guards fgl-object-add-to-cgraph
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-listp-when-not-member-witness))))
  (local (in-theory (disable fgl-object-add-to-cgraph
                             fgl-object-add-to-cgraph-rules
                             fgl-object-add-to-cgraph-rule
                             fgl-object-add-to-cgraph-matches
                             fgl-object-add-to-cgraph-match)))

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
                    (bfr-listp (cgraph-bfrlist cgraph)))
               (bfr-listp (cgraph-bfrlist new-cgraph)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-add-to-cgraph)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (bfr-listp (fgl-object-bfrlist x))
                    (bfr-listp (cgraph-bfrlist cgraph)))
               (bfr-listp (cgraph-bfrlist new-cgraph)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-add-to-cgraph-rules)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (bfr-listp (fgl-object-bfrlist x))
                    (bfr-listp (cgraph-bfrlist cgraph)))
               (bfr-listp (cgraph-bfrlist new-cgraph)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-add-to-cgraph-rule)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (bfr-listp (fgl-object-bfrlist x))
                    (bfr-listp (cgraph-bfrlist cgraph)))
               (bfr-listp (cgraph-bfrlist new-cgraph)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-add-to-cgraph-matches)
    (defret cgraph-bfrlist-of-<fn>
      (implies (and (bfr-listp (fgl-object-bfrlist x))
                    (bfr-listp (cgraph-bfrlist cgraph)))
               (bfr-listp (cgraph-bfrlist new-cgraph)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-add-to-cgraph-match))

  (fty::deffixequiv-mutual fgl-object-add-to-cgraph))

(define bvar-db-add-to-cgraph-aux ((n natp)
                                   (bvar-db)
                                   (cgraph cgraph-p)
                                   (memo cgraph-alist-p)
                                   (ruletable ctrex-ruletable-p)
                                   (bfrstate bfrstate-p)
                                   (wrld plist-worldp))
  :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n)
              (bfr-listp (bvar-db-bfrlist bvar-db)))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql n (next-bvar bvar-db))))
        (mv (cgraph-fix cgraph) (cgraph-alist-fix memo)))
       ((mv cgraph memo) (fgl-object-add-to-cgraph (get-bvar->term n bvar-db)
                                                  cgraph memo ruletable bfrstate wrld)))
    (bvar-db-add-to-cgraph-aux (1+ (lnfix n))
                               bvar-db cgraph memo ruletable bfrstate wrld))
  ///
  (defret cgraph-bfrlist-of-<fn>
    (implies (and (bfr-listp (bvar-db-bfrlist bvar-db))
                  (bfr-listp (cgraph-bfrlist cgraph))
                  (<= (base-bvar$a bvar-db) (nfix n)))
             (bfr-listp (cgraph-bfrlist new-cgraph)))))

(define bvar-db-create-cgraph (bvar-db
                               (ruletable ctrex-ruletable-p)
                               (bfrstate bfrstate-p)
                               (wrld plist-worldp))
  :guard (bfr-listp (bvar-db-bfrlist bvar-db))
  :returns (cgraph cgraph-p)
  (b* (((mv cgraph memo)
        (bvar-db-add-to-cgraph-aux (base-bvar bvar-db) bvar-db nil nil ruletable bfrstate wrld)))
    (fast-alist-free memo)
    (fast-alist-clean cgraph))
  ///
  (local (defthm cgraph-bfrlist-of-cdr-last
           (equal (cgraph-bfrlist (cdr (last x))) nil)
           :hints(("Goal" :in-theory (enable last cgraph-bfrlist)))))

  (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (defret cgraph-bfrlist-of-<fn>
    (implies (bfr-listp (bvar-db-bfrlist bvar-db))
             (bfr-listp (cgraph-bfrlist cgraph)))))

(define bvar-db-update-cgraph ((cgraph cgraph-p)
                               (memo cgraph-alist-p)
                               (cgraph-index natp)
                               bvar-db
                               (ruletable ctrex-ruletable-p)
                               (bfrstate bfrstate-p)
                               (wrld plist-worldp))
  :returns (mv (new-cgraph cgraph-p) (new-memo cgraph-alist-p))
  :guard (bfr-listp (bvar-db-bfrlist bvar-db))
  ;; BOZO this never shrinks the cgraph -- probably not necessary
  (b* (((when (<= (next-bvar bvar-db) (lnfix cgraph-index)))
        (mv (cgraph-fix cgraph) (cgraph-alist-fix memo))))
    (bvar-db-add-to-cgraph-aux (max (lnfix cgraph-index)
                                    (base-bvar bvar-db))
                               bvar-db cgraph memo ruletable bfrstate wrld))
  ///

  (defret cgraph-bfrlist-of-<fn>
    (implies (and (bfr-listp (bvar-db-bfrlist bvar-db))
                  (bfr-listp (cgraph-bfrlist cgraph)))
             (bfr-listp (cgraph-bfrlist new-cgraph)))))





;; (define cgraph-edges-invert ((from fgl-object-p)
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
;;                   (fgl-object-p (caar cgraph))))
;;         (b* ((acc (cgraph-edges-invert (caar cgraph) (cdar cgraph) acc)))
;;           (cgraph-invert (cdr cgraph) acc))
;;       (cgraph-invert (cdr cgraph) acc))))

;; (fty::defmap cgraph-indexmap :key-type fgl-object :val-type natp :true-listp t)


;; (fty::deflist fgl-objectlistlist :elt-type fgl-objectlist :true-listp t)


;; (define cgraph-stack-pop-n ((n natp)
;;                             (stk cgraph-alist-p))
;;   :guard (and (no-duplicatesp-equal (alist-keys stk))
;;               (<= n (len stk)))
;;   :guard-hints (("goal" :in-theory (enable cgraph-alist-p)))
;;   :measure (len stk)
;;   :returns (mv (popped fgl-objectlist-p)
;;                (new-stk cgraph-alist-p))
;;   (if (zp n)
;;       (mv nil (cgraph-alist-fix stk))
;;     (if (mbt (and (consp stk)
;;                   (consp (car stk))
;;                   (fgl-object-p (caar stk))))
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
;;   :returns (triggers fgl-objectlist-p)
;;   (if (Atom x)
;;       nil
;;     (cons (cgraph-edge->trigger (car x))
;;           (cgraph-edgelist->triggers (cdr x)))))

;; (local
;;  (defprojection cgraph-edgelist->triggers ((x cgraph-edgelist-p))
;;    :returns (triggers fgl-objectlist-p)
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
;;   (define cgraph-tarjan-sccs ((x fgl-object-p)
;;                               (cgraph cgraph-p)
;;                               (preorder cgraph-indexmap-p)
;;                               (preorder-next)
;;                               (stk cgraph-alist-p)
;;                               (stack-size)
;;                               (sccs-acc fgl-objectlistlist-p))
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
;;                  (sccs fgl-objectlistlist-p))
;;     :well-founded-relation acl2::nat-list-<
;;     :measure (list (let ((rem (len (set-difference$ (alist-keys (cgraph-fix cgraph))
;;                                                     (alist-keys (cgraph-indexmap-fix preorder))))))
;;                      (+ rem ;; (if (hons-assoc-equal (fgl-object-fix x) (cgraph-fix cgraph)) 0 1)
;;                         ))
;;                    0 1)
;;     :verify-guards nil
;;     (b* ((preorder (cgraph-indexmap-fix preorder))
;;          (stk (cgraph-alist-fix stk))
;;          (preorder-next (mbe :logic (len preorder) :exec preorder-next))
;;          (stack-size (mbe :logic (len stk) :exec stack-size))
;;          (sccs-acc (fgl-objectlistlist-fix sccs-acc))
;;          (x (fgl-object-fix x))
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
;;                                     (sccs-acc fgl-objectlistlist-p))
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
;;                  (sccs fgl-objectlistlist-p))
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
;;          (sccs-acc (fgl-objectlistlist-fix sccs-acc))

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
;;                                  (sccs-acc fgl-objectlistlist-p))
;;   :guard (and (no-duplicatesp-equal (alist-keys stk))
;;               (equal stack-size (len stk))
;;               (equal preorder-next (len preorder))
;;               (subsetp-equal (alist-keys stk) (alist-keys preorder)))
;;   :returns (sccs fgl-objectlistlist-p)
;;   :verify-guards nil
;;   (b* (;; (preorder (cgraph-indexmap-fix preorder))
;;        ;; (stk (cgraph-alist-fix stk))
;;        ;; (preorder-next (mbe :logic (len preorder) :exec preorder-next))
;;        ;; (stack-size (mbe :logic (len stk) :exec stack-size))
;;        (sccs-acc (fgl-objectlistlist-fix sccs-acc))

;;        ((when (atom x))
;;         ;; (mv preorder
;;         ;;     preorder-next
;;         ;;     stk
;;         ;;     stack-size
;;             sccs-acc)
;;        ((unless (mbt (and (consp (car x))
;;                           (fgl-object-p (caar x)))))
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
;;   :returns (sccs fgl-objectlistlist-p)
;;   (cgraph-tarjan-sccs-iter cgraph cgraph nil 0 nil 0 nil))


;; ;; This is very similar to fgl-objectlistlist-p...
;; (fty::defmap cgraph-scc-map :key-type fgl-object :val-type fgl-objectlist :true-listp t)

;; (define cgraph-map-one-scc ((objs fgl-objectlist-p)
;;                             (scc fgl-objectlist-p)
;;                             (scc-map cgraph-scc-map-p))
;;   :returns (new-scc-map cgraph-scc-map-p)
;;   (if (atom objs)
;;       (cgraph-scc-map-fix scc-map)
;;     (cgraph-map-one-scc
;;      (cdr objs) scc (hons-acons (fgl-object-fix (car objs))
;;                                 (fgl-objectlist-fix scc)
;;                                 scc-map))))

;; (define cgraph-map-sccs ((sccs fgl-objectlistlist-p)
;;                          (scc-map cgraph-scc-map-p))
;;   :returns (new-scc-map cgraph-scc-map-p)
;;   (if (atom sccs)
;;       (cgraph-scc-map-fix scc-map)
;;     (cgraph-map-sccs (cdr sccs)
;;                      (cgraph-map-one-scc (car sccs) (car sccs) scc-map))))


;; (defprod scc-cgraph-edges
;;   ((tree-edges cgraph-edgelist-p)
;;    (scc-edges cgraph-edgelist-p)
;;    (scc fgl-objectlist-p))
;;   :layout :tree)

;; (fty::defmap scc-cgraph :key-type fgl-object :val-type scc-cgraph-edges :true-listp t)


;; (define cgraph-edges-scc-split ((edges cgraph-edgelist-p)
;;                                 (scc fgl-objectlist-p))
;;   :returns (mv (tree-edges cgraph-edgelist-p)
;;                (scc-edges cgraph-edgelist-p))
;;   (b* (((when (atom edges))
;;         (mv nil nil))
;;        ((mv tree-edges scc-edges) (cgraph-edges-scc-split (cdr edges) scc))
;;        ((cgraph-edge x1) (cgraph-edge-fix (car edges)))
;;        ((when (acl2::hons-member-equal x1.trigger scc))
;;         (mv tree-edges (cons x1 scc-edges))))
;;     (mv (cons x1 tree-edges) scc-edges)))


;; (define scc-to-scc-cgraph ((rest fgl-objectlist-p)
;;                            (scc fgl-objectlist-p)
;;                            (cgraph cgraph-p)
;;                            (scc-cgraph scc-cgraph-p))
;;   :returns (new-scc-cgraph scc-cgraph-p)
;;   (b* (((when (atom rest)) (scc-cgraph-fix scc-cgraph))
;;        (first (fgl-object-fix (car rest)))
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

;; (define cgraph-to-scc-cgraph ((sccs fgl-objectlistlist-p)
;;                               (cgraph cgraph-p)
;;                               (scc-cgraph scc-cgraph-p))
;;   :returns (new-scc-cgraph scc-cgraph-p)
;;   (if (atom sccs)
;;       (scc-cgraph-fix scc-cgraph)
;;     (cgraph-to-scc-cgraph
;;      (cdr sccs)
;;      cgraph
;;      (scc-to-scc-cgraph (car sccs) (car sccs) cgraph scc-cgraph))))







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








(fty::defprod cgraph-derivstate
  ((times-seen natp :rule-classes :type-prescription)
   (result-msg))
  :layout :tree)

(fty::defmap cgraph-derivstates :key-type fgl-object :val-type cgraph-derivstate :true-listp t)

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


(define cgraph-set-error ((x fgl-object-p)
                          (msg)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (fgl-object-fix x))
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

(define cgraph-incr-seen ((x fgl-object-p)
                          (sts cgraph-derivstates-p))
  :returns (new-sts cgraph-derivstates-p)
  (b* ((x (fgl-object-fix x))
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



(define cgraph-summarize-errors-and-assign ((x fgl-object-p)
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
                    (hons-acons (fgl-object-fix x) (car vals) assigns)
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


;; If there is a property rule application among cands, add a binding of that
;; candidate's value to rule's assigned-var and remove that candidate.  Theory
;; being that all applicable property rules should work together to make one
;; value.
(define candidate-assigns-complete-match-subst ((rule ctrex-rule-p)
                                                (cands candidate-assigns-p))
  :returns (mv (new-match-subst symbol-alistp)
               (rest-cands candidate-assigns-p))
  (b* (((when (atom cands)) (mv (list (cons (ctrex-rule->assigned-var rule) nil)) nil))
       ((candidate-assign cand) (candidate-assign-fix (car cands)))
       ((cgraph-edge cand.edge))
       ((ctrex-rule cand.edge.rule))
       ((when (eq cand.edge.rule.ruletype :property))
        (mv (list (cons (ctrex-rule->assigned-var rule) cand.val))
            (candidate-assigns-fix (cdr cands))))
       ((mv subst rest-cands)
        (candidate-assigns-complete-match-subst rule (cdr cands))))
    (mv subst (cons-with-hint cand rest-cands cands))))

(local (defthm symbol-alistp-of-append
         (implies (and (symbol-alistp x)
                       (symbol-alistp y))
                  (symbol-alistp (append x y)))))

;; (local (defthm symbol-alistp-when-fgl-object-bindings-p
;;          (implies (fgl-object-bindings-p x)
;;                   (symbol-alistp x))))

(local (defthm caar-of-fgl-object-bindings-fix-type
         (implies (consp (fgl-object-bindings-fix x))
                  (pseudo-var-p (caar (fgl-object-bindings-fix x))))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-fix)))
         :rule-classes :type-prescription))

(defines cgraph-derive-assignments
  (define cgraph-derive-assignments-obj ((x fgl-object-p)
                                         (assigns cgraph-alist-p)
                                         (sts cgraph-derivstates-p)
                                         (env$)
                                         (cgraph cgraph-p)
                                         (replimit posp)
                                         &optional
                                         (logicman 'logicman)
                                         (bvar-db 'bvar-db)
                                         (state 'state))
    :guard (and (lbfr-listp (fgl-object-bfrlist x))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    :returns (mv (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :well-founded-relation acl2::nat-list-<
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   0
                   0)
    :verify-guards nil
    (b* ((x (fgl-object-fix x))
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
         ((when (fgl-object-variable-free-p x))
          (b* (((mv err val) (magic-fgl-object-eval x env$))
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
          (cgraph-derive-assignments-edges edges nil assigns sts env$ cgraph replimit)))

      (cgraph-summarize-errors-and-assign x errors candidate-assigns assigns sts)))

  (define cgraph-derive-assignments-edges ((x cgraph-edgelist-p)
                                           (cands candidate-assigns-p)
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
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))

    :returns (mv errors
                 (new-cands candidate-assigns-p)
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   9
                   (len x))
    (b* (((when (atom x)) (mv nil (candidate-assigns-fix cands)
                              (cgraph-alist-fix assigns)
                              (cgraph-derivstates-fix sts)))
         ((mv err cands new-assigns new-sts)
          (cgraph-derive-assignments-edge (car x) cands assigns sts env$ cgraph replimit))
         ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                           (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
          (mv nil (candidate-assigns-fix cands)
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ((mv rest-errs cands assigns sts)
          (cgraph-derive-assignments-edges (cdr x) cands new-assigns new-sts env$ cgraph replimit)))
      (if err
          (mv (cons err rest-errs) cands assigns sts)
        (mv rest-errs cands assigns sts))))

  (define cgraph-derive-assignments-edge ((x cgraph-edge-p)
                                          (cands candidate-assigns-p)
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
                 (new-cands candidate-assigns-p)
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   8
                   0)
    :guard (and (lbfr-listp (cgraph-edge-bfrlist x))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* (((cgraph-edge x))
         ((mv match-subst new-assigns new-sts)
          (cgraph-derive-assignments-matches x.match-vars x.rule x.subst
                                              assigns sts env$ cgraph replimit))
         ((unless match-subst)
          ;; BOZO It would kind of make sense to produce a real error message
          ;; here, but then we'd get not just the root cause of a given error,
          ;; but tons of messages about its various consequences.
          (mv t (candidate-assigns-fix cands) new-assigns new-sts))
         ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                           (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
          (mv nil nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ((mv eval-subst assigns sts)
          (cgraph-derive-assignments-eval-subst x.subst new-assigns new-sts env$ cgraph replimit logicman bvar-db state))
         ((ctrex-rule x.rule))
         ((mv new-subst cands)
          (if (eq x.rule.ruletype :property)
              (candidate-assigns-complete-match-subst x.rule cands)
            (mv nil (candidate-assigns-fix cands))))
         (match-subst (append new-subst match-subst eval-subst))
         ((mv err val)
          (magitastic-ev x.rule.assign match-subst 1000 state t t))
         ;; (- (cw "magitastic-ev ~x0: ~x2 ~x3~%" x.rule.assign nil err val))
         ((when err)
          (b* ((msg (msg "Failed to evaluate assignment ~x0 from rule ~x1"
                   x.rule.assign x.rule.name)))
            ;; (cw "~@0~%" msg)
            (mv msg cands assigns sts))))
      (mv nil
          (cons (make-candidate-assign :edge x :val val) cands)
          assigns sts)))

  (define cgraph-derive-assignments-eval-subst ((subst fgl-object-bindings-p)
                                                (assigns cgraph-alist-p)
                                                (sts cgraph-derivstates-p)
                                                (env$)
                                                (cgraph cgraph-p)
                                                (replimit posp)
                                                &optional
                                                (logicman 'logicman)
                                                (bvar-db 'bvar-db)
                                                (state 'state))
    :returns (mv (eval-subst symbol-alistp)
                 (new-assigns cgraph-alist-p)
                 (new-sts cgraph-derivstates-p))
    :measure (list (cgraph-derive-assigns-measure cgraph assigns sts replimit)
                   7
                   (len (fgl-object-bindings-fix subst)))
    :guard (and (lbfr-listp (fgl-object-bindings-bfrlist subst))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* ((subst (fgl-object-bindings-fix subst))
         ((when (atom subst))
          (mv nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         ;; ((unless (mbt (and (consp (car subst))
         ;;                    (pseudo-var-p (caar subst)))))
         ;;  (cgraph-derive-assignments-eval-subst (cdr subst) assigns sts env$ cgraph replimit))
         ((cons var obj) (car subst))
         ((mv new-assigns new-sts) (cgraph-derive-assignments-obj obj assigns sts env$ cgraph replimit))
         ((unless (mbt (<= (cgraph-derive-assigns-measure cgraph new-assigns new-sts replimit)
                           (cgraph-derive-assigns-measure cgraph assigns sts replimit))))
          (mv nil
              (cgraph-alist-fix assigns)
              (cgraph-derivstates-fix sts)))
         (pair (hons-get ;; (fgl-object-fix obj)
                obj new-assigns))
         ((mv rest-subst assigns sts)
          (cgraph-derive-assignments-eval-subst (cdr subst) new-assigns new-sts env$ cgraph replimit)))
      (mv (if pair
              (cons (cons var (cdr pair)) rest-subst)
            rest-subst)
          assigns sts)))


  (define cgraph-derive-assignments-matches ((x pseudo-var-list-p)
                                             (rule ctrex-rule-p)
                                             (subst fgl-object-bindings-p)
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
    :guard (and (lbfr-listp (fgl-object-bindings-bfrlist subst))
                (bfr-env$-p env$ (logicman->bfrstate))
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
                                           (subst fgl-object-bindings-p)
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
    :guard (and (lbfr-listp (fgl-object-bindings-bfrlist subst))
                (bfr-env$-p env$ (logicman->bfrstate))
                (equal (bfr-nvars) (next-bvar bvar-db))
                (lbfr-listp (cgraph-bfrlist cgraph)))
    (b* (((ctrex-rule rule))
         (term (cdr (assoc (pseudo-var-fix x) rule.match)))
         (obj (pseudo-term-subst-fgl-objects term subst))
         ((mv assigns sts)
          (cgraph-derive-assignments-obj obj assigns sts env$ cgraph replimit))
         (assigns-look (hons-get obj assigns)))
      (if assigns-look
          (mv t (cdr assigns-look) assigns sts)
        (mv nil nil assigns sts))))

  ///
  (local (in-theory (enable bfr-listp-when-not-member-witness)))
  (local
   (make-event
    `(in-theory (disable . ,(getpropc 'cgraph-derive-assignments-obj-fn 'recursivep nil (w state))))))

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
      :fn cgraph-derive-assignments-eval-subst)
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
    :hints (("goal" :Expand ((cgraph-edgelist-bfrlist x)
                             (fgl-object-bindings-bfrlist subst)))))

  (local (in-theory (disable cons-equal)))

  ;; (local (defthm fgl-object-bindings-fix-open-when-bad-car
  ;;          (implies (not (and (consp (car subst))
  ;;                             (pseudo-var-p (caar subst))))
  ;;                   (equal (fgl-object-bindings-fix (cdr subst))
  ;;                          (fgl-object-bindings-fix subst)))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-bindings-fix)))))

  ;; (local (defthm cdar-of-fgl-object-bindings-fix
  ;;          (implies (and (consp (car subst))
  ;;                        (pseudo-var-p (caar subst)))
  ;;                   (equal (cdar (fgl-object-bindings-fix subst))
  ;;                          (fgl-object-fix (cdar subst))))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-bindings-fix)))))

  ;; (local (defthm fgl-object-bindings-fix-when-atom
  ;;          (implies (not (consp subst))
  ;;                   (not (fgl-object-bindings-fix subst)))
  ;;          :hints(("Goal" :in-theory (enable fgl-object-bindings-fix)))))

  (fty::deffixequiv-mutual cgraph-derive-assignments))


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

(define cgraph-derive-assignments-for-vars ((x pseudo-var-list-p)
                                            (vals obj-alist-p)
                                            (assigns cgraph-alist-p)
                                            (sts cgraph-derivstates-p)
                                            (env$)
                                            (cgraph cgraph-p)
                                            (replimit posp)
                                            &optional
                                            (logicman 'logicman)
                                            (bvar-db 'bvar-db)
                                            (state 'state))
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
         (g-var (car x)) assigns sts env$ cgraph replimit))
       (pair (hons-get obj assigns))
       (vals (if pair
                 (cons (cons (pseudo-var-fix (car x)) (cdr pair)) vals)
               vals)))
    (cgraph-derive-assignments-for-vars
     (cdr x) vals assigns sts env$ cgraph replimit)))

(define cgraph-derivstates-summarize-errors ((x cgraph-derivstates-p))
  :returns (errmsg-or-nil)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (fgl-object-p (caar x)))))
        (cgraph-derivstates-summarize-errors (cdr x)))
       (err1 (cgraph-derivstate->result-msg (cdar x)))
       (rest (cgraph-derivstates-summarize-errors (cdr x))))
    (if err1
        (if rest
            (msg "~x0: ~@1~%~@2" (caar x) err1 rest)
          (msg "~x0: ~@1~%" (caar x) err1))
      rest))
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

(define ctrex-eval-summarize-errors ((eval-error)
                                     (deriv-errors))
  (if eval-error
      (if deriv-errors
          (msg "Error evaluating the bindings: ~@0~%Additionally, there were ~
                errors deriving the variable assignments:~@1"
               eval-error
               deriv-errors)
        eval-error)
    deriv-errors))


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
               (errmsg cgraph memo cgraph-index env$)
               (b* ((env$ (bfr-env$-fix env$ (logicman->bfrstate)))
                    (ruletable (make-fast-alist (table-alist 'fgl-ctrex-rules (w state))))
                    ((unless (ctrex-ruletable-p ruletable))
                     (mv "bad ctrex-ruletable~%" cgraph memo cgraph-index env$))
                    ((mv cgraph memo) ;; (bvar-db-update-cgraph cgraph cgraph-index bvar-db ruletable (w state))
                     (bvar-db-update-cgraph cgraph memo cgraph-index bvar-db ruletable
                                            (logicman->bfrstate)
                                            (w state)))
                    ((mv var-vals assigns sts)
                     (cgraph-derive-assignments-for-vars vars nil nil nil env$ cgraph 10))
                    (- (fast-alist-free assigns))
                    (sts (fast-alist-free (fast-alist-clean sts)))
                    (deriv-errors (cgraph-derivstates-summarize-errors sts))
                    (env$ (update-env$->obj-alist var-vals env$))
                    (full-deriv-errors (ctrex-summarize-errors vars var-vals deriv-errors)))
                 (mv full-deriv-errors cgraph memo (next-bvar bvar-db) env$))
               (b* ((interp-st (update-interp-st->cgraph cgraph interp-st))
                    (interp-st (update-interp-st->cgraph-memo memo interp-st))
                    (interp-st (update-interp-st->cgraph-index cgraph-index interp-st)))
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


(fty::deftagsum bvar-db-consistency-error
  (:eval-error ((obj fgl-object-p)
                (msg)))
  (:inconsistency ((obj fgl-object-p)
                   (var-val)
                   (obj-val)))
  :layout :tree)

(fty::deflist bvar-db-consistency-errorlist :elt-type bvar-db-consistency-error :true-listp t)


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

(define counterex-bindings-summarize-errors (infer-errors eval-errors)
  (if infer-errors
      (if eval-errors
          (msg "~@0~%~@1" infer-errors eval-errors)
        infer-errors)
    eval-errors))


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


(verify-termination evisc-tuple)
(verify-guards evisc-tuple)

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
