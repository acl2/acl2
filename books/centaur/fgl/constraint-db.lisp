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

(include-book "clause-processors/unify-subst" :dir :system)
(include-book "unify-defs")
(include-book "clause-processors/magic-ev" :dir :system)
(include-book "centaur/meta/term-vars" :dir :system)
(include-book "constraint-inst")

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable pseudo-termp acl2::magic-ev)))

;; (defun fgl-bool-fix (x)
;;   (and x t))

;; A constraint rule is written as follows:

;; (fgl::def-fgl-boolean-constraint thmname
;;        :bindings ((x (logbitp n a))
;;                   (y (logbitp m a)))
;;        :syntaxp (and (<< n m)
;;                      (not (and (atom n) (atom m))))
;;        :body (implies (equal n m)
;;                       (equal x y))
;;        :hints ...)

;; This generates an ACL2 theorem:
;; (defthm thmname
;;    (let ((x (fgl-bool-fix (logbitp n a)))
;;          (y (fgl-bool-fix (logbitp m a))))
;;       (implies (equal n m)
;;                (equal x y)))
;;   :hints ...
;;   :rule-classes nil).

;; The point of this rule is to add a constraint when we have two Boolean
;; variables generated from (logbitp n a) terms.  When we find two such
;; variables, we call their corresponding terms the literals of the
;; constraint.  We generate the constraint by unifying the literals with the
;; bindings from the constraint rule and then symbolically executing the body
;; of the theorem under a Boolean context.  Since it's a theorem, we can assume
;; the symbolic-Boolean result to be true under our bvar-db.



;; To find such literals, we maintain a constraint catalog, a data structure
;; that lets us quickly match a new literal to existing ones.  This uses a
;; several-levels lookup system, as follows.

;; Source of confusion: there are essentially two variable namespaces for each
;; rule.  The "literals" are those that are let-bound in the body of the
;; theorem, (x, y above); these can be used in the :body but not in the terms
;; of the bindings.  The "variables" are those that are used in the terms of
;; the bindings; these can also appear in the body (unless they are shadowed by
;; literals).

;; Let a partial instantiation of a rule be a rule together with a list of
;; matched literal variables and an assignment of fgl-objects to the variables
;; contained in the pattern terms of the matched literals.  A full
;; instantiation is one with all literals matched.

;; A constraint-tuple is a set of non-full partial instantiations with the same
;; set of matched literals and a choice of one distinguished unmatched literal.
;; We index these constraint-tuples by the function symbol of this unmatched
;; literal.  Each partial instantiation can be stored within multiple
;; constraint-tuples in the constraint-db, one for each unmatched literal.

;; Whenever a new term is assigned a Boolean variable, we try to extend as many
;; such partial instantiations as possible by matching one of the unmatched
;; literals to the new term.  The match is allowed if all the variable
;; assignments induced by the matching of the literal to the term agree with
;; existing variable assignments.  To do this, we look up the set of tuples
;; whose unmatched literals have the same leading function symbol as the new
;; term.  For each such tuple, we try to unify the new term with the unmatched
;; literal.  If they unify, then the tuple contains a set of partial
;; instantiations that we might be able to extend with this match.  We can
;; extend such a partial instantiation if the assignments to variables that are
;; in both the newly-matched literal and previously-matched literals (called
;; the common variables) are consistent between the new unify alist and the
;; existing assignments.  To help us do this matching quickly, we store the
;; assignment of each partial instantiation indexed by its signature, which is
;; the list of fgl-objects assigned to the common variables.  (Each signature may
;; have multiple associated substitutions.)  Note that NIL is a (in fact the
;; only) valid signature when there are no common vars, and all partial
;; instantiations will be indexed under NIL in that case.


;; Outermost structure is indexed by the first function symbol of the literal.
;; Inside that is a list of tuples, each corresponding to a partial instantiation of a constraint rule.
;; (rule existing-lits matching-lit common-variables signature-table)

;; Rule is a constraint rule structure

;; Matching-lit is the variable of the lit pattern we'll match against (whose
;; leading function symbol is the symbol under which the tuple is indexed in
;; the constraint catalog).

;; Existing-lits are literals for which matches have already been found.

;; Common-vars are the intersection of the vars of the matching-lit pattern
;; with the vars of the existing-lit patterns.

;; Existing-vars are variables that are already assigned values in the partial
;; substitution.

;; Signature-table maps signatures to partial unifying substitution lists.  A
;; signature is the list of unifying bindings of common-vars.

;; So to find new constraints given a new literal:
;; - look up the tuples for that literal's leading function symbol
;; - for each tuple,
;;      unify the literal with the matching-lit of the rule
;;      extract the bindings of common-vars to make the signature
;;      look up the signature in the signature-table to get the partial substs
;;      for each partial unifying subst, union the unifying subst for the
;;          literal.
;;      If the matching-lit + existing-lits are all the literals of the rule,
;;      then these substitutions are now complete and can be used to generate constraints.
;;      Otherwise, new entries should be added to the constraint-catalog for
;;      each other literal of the rule, as follows:
;;  under the function symbol of the addtl-literal,
;;    find the tuple matching (rule existing-lits+matching-lit addtl-lit ....)
;;    create it if not, computing the common-vars
;;    for each partial-subst:
;;        extract the common-vars to get the signature
;;        add the partial-subst to the list for that signature.

;; As a FGL proof progresses, new literals may be added to the bvar-db and the
;; constraint-table may be extended.  But we start with a base constraint-table
;; at the beginning of any proof; this is stored in an ACL2 table.  In this
;; initial constraing table, each tuple has empty existing-lits, thus empty
;; common-vars and thus the unique signature is NIL, and a single empty
;; partial unifying subst is stored under that signature.


  

;; Heuristic info about a constraint rule.
;; We'll look up the theorem in the world, so it doesn't need to be stored
;; here.
;; Constrained-terms is an alist mapping variables to terms.
(defprod constraint-rule
  ((thmname symbolp)
   (lit-alist pseudo-term-subst-p)
   (syntaxp pseudo-termp))
  :layout :fulltree)

;;(fty::deflist pseudo-term-substlist :elt-type pseudo-term-subst :true-listp t)
(fty::deflist fgl-object-bindingslist :elt-type fgl-object-bindings :true-listp t)
(fty::defmap sig-table :key-type fgl-objectlist :val-type fgl-object-bindingslist :true-listp t)



;; get set theorems
(local (fty::deflist pseudo-var-list :elt-type pseudo-var :true-listp t))

(define pseudo-var-set-p (x)
  (and (pseudo-var-list-p x)
       (set::setp x))
  ///
  (define pseudo-var-set-fix ((x pseudo-var-set-p))
    :returns (new-x pseudo-var-set-p)
    (mbe :logic (set::mergesort (pseudo-var-list-fix x))
         :exec x)
    ///
    (defthm pseudo-var-set-fix-when-pseudo-var-set-p
      (implies (pseudo-var-set-p x)
               (equal (pseudo-var-set-fix x) x)))

    (fty::deffixtype pseudo-var-set :pred pseudo-var-set-p :fix pseudo-var-set-fix
      :equiv pseudo-var-set-equiv :define t))

  (defthm pseudo-var-set-p-when-pseudo-var-list-and-set
    (implies (and (pseudo-var-list-p x)
                  (set::setp x))
             (pseudo-var-set-p x)))

  (defthmd setp-when-pseudo-var-set-p
    (implies (pseudo-var-set-p x)
             (set::setp x)))

  (defthmd pseudo-var-list-p-when-pseudo-var-set-p
    (implies (pseudo-var-set-p x)
             (pseudo-var-list-p x))))

(local (in-theory (enable setp-when-pseudo-var-set-p
                          pseudo-var-list-p-when-pseudo-var-set-p)))

;; this is the tuple referred to above
(defprod constraint-tuple
  ((rule constraint-rule-p)
   (existing-lits pseudo-var-set-p)
   (matching-lit pseudo-var-p)
   (common-vars pseudo-var-set-p)
   (existing-vars pseudo-var-set-p)
   (sig-table sig-table-p))
  :layout :fulltree)

(fty::deflist constraint-tuplelist :elt-type constraint-tuple :true-listp t)

(fty::defmap constraint-db :key-type pseudo-fnsym-p :val-type constraint-tuplelist :true-listp t)


(defthm fgl-object-bindings-bfrlist-of-append
  (equal (fgl-object-bindings-bfrlist (append a b))
         (append (fgl-object-bindings-bfrlist a)
                 (fgl-object-bindings-bfrlist b)))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist))))

(define fgl-object-bindingslist-bfrlist ((x fgl-object-bindingslist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (fgl-object-bindings-bfrlist (car x))
            (fgl-object-bindingslist-bfrlist (cdr x))))
  ///
  (defthm fgl-object-bindingslist-bfrlist-of-append
    (equal (fgl-object-bindingslist-bfrlist (append a b))
           (append (fgl-object-bindingslist-bfrlist a)
                   (fgl-object-bindingslist-bfrlist b)))
    :hints(("Goal" :in-theory (enable fgl-object-bindingslist-bfrlist)))))

(define sig-table-bfrlist ((x sig-table-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (fgl-objectlist-p (caar x))))
        (append (fgl-objectlist-bfrlist (caar x))
                (fgl-object-bindingslist-bfrlist (cdar x))
                (sig-table-bfrlist (cdr x)))
      (sig-table-bfrlist (cdr x))))
  ///
  (defthm sig-table-bfrlist-of-append
    (equal (sig-table-bfrlist (append a b))
           (append (sig-table-bfrlist a)
                   (sig-table-bfrlist b)))
    :hints(("Goal" :in-theory (enable sig-table-bfrlist))))

  (defthm member-bfrlist-of-sig-table-lookup
    (implies (and (fgl-objectlist-p pat)
                  (not (member v (sig-table-bfrlist x))))
             (not (member v (fgl-object-bindingslist-bfrlist
                             (cdr (hons-assoc-equal pat x)))))))

  (local (in-theory (enable sig-table-fix))))

(define constraint-tuple-bfrlist ((x constraint-tuple-p))
  :returns (bfrs)
  (b* (((constraint-tuple x)))
    (sig-table-bfrlist x.sig-table)))

(define constraint-tuplelist-bfrlist ((x constraint-tuplelist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (constraint-tuple-bfrlist (car x))
            (constraint-tuplelist-bfrlist (cdr x))))
  ///
  (defthm constraint-tuplelist-bfrlist-of-append
    (equal (constraint-tuplelist-bfrlist (append a b))
           (append (constraint-tuplelist-bfrlist a)
                   (constraint-tuplelist-bfrlist b)))
    :hints(("Goal" :in-theory (enable constraint-tuplelist-bfrlist)))))

(define constraint-db-bfrlist ((x constraint-db-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-fnsym-p (caar x))))
        (append (constraint-tuplelist-bfrlist (cdar x))
                (constraint-db-bfrlist (cdr x)))
      (constraint-db-bfrlist (cdr x))))
  ///
  (local (in-theory (enable constraint-db-fix)))

  (defthm constraint-tuplelist-bfrlist-of-lookup
    (implies (pseudo-fnsym-p pat)
             (subsetp (constraint-tuplelist-bfrlist
                       (cdr (hons-assoc-equal pat x)))
                      (constraint-db-bfrlist x))))

  (defthm member-constraint-tuplelist-bfrlist-of-lookup
    (implies (and (pseudo-fnsym-p pat)
                  (not (member v (constraint-db-bfrlist x))))
             (not (member v (constraint-tuplelist-bfrlist
                             (cdr (hons-assoc-equal pat x))))))
    :hints (("goal" :use constraint-tuplelist-bfrlist-of-lookup
             :in-theory (disable constraint-tuplelist-bfrlist-of-lookup))))

  (defthm member-constraint-db-bfrlist-of-hons-shrink-alist
    (implies (and (not (member v (constraint-db-bfrlist x)))
                  (not (member v (constraint-db-bfrlist y))))
             (not (member v (constraint-db-bfrlist (hons-shrink-alist x y))))))

  (defthm subsetp-constraint-db-bfrlist-of-hons-shrink-alist
    (subsetp (constraint-db-bfrlist (hons-shrink-alist x nil))
             (constraint-db-bfrlist x))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw))))

  (defthm constraint-db-bfrlist-of-append
    (equal (constraint-db-bfrlist (append a b))
           (append (constraint-db-bfrlist a)
                   (constraint-db-bfrlist b)))
    :hints(("Goal" :in-theory (enable constraint-db-bfrlist)))))


;; Code to add a rule to the initial catalog (with empty existing-lits etc).
(define gbc-rule-lit-add-catalog-entry ((var pseudo-var-p)
                                        (pat pseudo-termp)
                                        (rule constraint-rule-p)
                                        (ccat constraint-db-p))
  :returns (new-ccat constraint-db-p)
  (b* (((unless (pseudo-term-case pat :fncall))
        (cw "Bad constraint rule literal binding: (~x0 ~x1)~%Binding should be a function call.~%"
            var pat)
        (constraint-db-fix ccat))
       ((pseudo-term-fncall pat))
       (tuples (cdr (hons-assoc-equal pat.fn (constraint-db-fix ccat))))
       ;; assume rule is new, so no matching tuple exists -- just cons on a new
       ;; one.
       ;; signature-table contains nil mapped to (list nil) -- list containing
       ;; one empty unifying subst
       (new-tuple (make-constraint-tuple
                   :rule rule
                   :existing-lits nil
                   :matching-lit var
                   :common-vars nil
                   :existing-vars nil
                   :sig-table (hons-acons nil (list nil) nil))))
    (cons (cons pat.fn (cons new-tuple tuples)) (constraint-db-fix ccat)))
  ///
  (defret bfrlist-of-<fn>
    (acl2::set-equiv (constraint-db-bfrlist new-ccat)
                     (constraint-db-bfrlist ccat))
    :hints(("Goal" :in-theory (enable constraint-db-bfrlist
                                      constraint-tuplelist-bfrlist
                                      constraint-tuple-bfrlist)))))

(define gbc-rule-add-catalog-entries ((lit-alist pseudo-term-subst-p)
                                      (rule constraint-rule-p)
                                      (ccat constraint-db-p))
  :returns (new-ccat constraint-db-p)
  (b* (((when (atom lit-alist)) (constraint-db-fix ccat))
       ((unless (mbt (and (consp (car lit-alist))
                          (pseudo-var-p (caar lit-alist)))))
        (gbc-rule-add-catalog-entries (cdr lit-alist) rule ccat))
       ((cons var pat) (car lit-alist))
       (ccat (gbc-rule-lit-add-catalog-entry var pat rule ccat)))
    (gbc-rule-add-catalog-entries (cdr lit-alist) rule ccat))
  ///
  
  (defret bfrlist-of-<fn>
    (acl2::set-equiv (constraint-db-bfrlist new-ccat)
                     (constraint-db-bfrlist ccat))
    :hints(("Goal" :in-theory (enable constraint-db-bfrlist
                                      constraint-tuplelist-bfrlist
                                      constraint-tuple-bfrlist))))
  (local (in-theory (enable pseudo-term-subst-fix)))) ;; for fix hook


;; Optimization: if two constrained terms are isomorphic (they unify with the
;; same terms), and there's no syntaxp, then there's no need to list the rule
;; under both of them.  Note: not true -- could have e.g.
;;  ((x (logbitp n a))
;;   (y (logbitp m a))
;;   (z (< n m)))
;; Or worse
;; ((x (loghead n a))
;;  (y (loghead m a)))
;; body: (if (and (equal x 0) (<= (nfix m) (nfix n)))
;;           (equal y 0)
;;         t)
;; Let's just get rid of this...
;; (define gbc-alist-has-symmetric ((term pseudo-termp)
;;                                  (alist pseudo-term-subst-p))
;;   (b* (((when (atom alist)) nil)
;;        ((unless (mbt (and (consp (car alist))
;;                           (pseudo-var-p (caar alist)))))
;;         (gbc-alist-has-symmetric term (cdr alist)))
;;        (term2 (cdar alist))
;;        ((mv ok1 &) (acl2::simple-one-way-unify term term2 nil))
;;        ((unless ok1)
;;         (gbc-alist-has-symmetric term (cdr alist)))
;;        ((mv ok2 &) (acl2::simple-one-way-unify term2 term nil)))
;;     (or ok2
;;         (gbc-alist-has-symmetric term (cdr alist)))))

;; (defun gbc-alist-remove-symmetric (alist)
;;   (if (atom alist)
;;       nil
;;     (if (gbc-alist-has-symmetric (cdar alist) (cdr alist))
;;         (gbc-alist-remove-symmetric (cdr alist))
;;       (cons (car alist) (gbc-alist-remove-symmetric (cdr alist))))))




(define gbc-rule-add-to-catalog ((rule constraint-rule-p)
                                 (ccat constraint-db-p))
  :returns (new-ccat constraint-db-p)
  ;; Iterate over the constraint-alist.
  (b* (((constraint-rule rule)))
    (hons-shrink-alist
     (gbc-rule-add-catalog-entries rule.lit-alist rule ccat)
     nil))
  ///
  (defret bfrlist-of-<fn>
    (subsetp (constraint-db-bfrlist new-ccat) (constraint-db-bfrlist ccat))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw))))

  (defret member-bfrlist-of-<fn>
    (implies (not (member v (constraint-db-bfrlist ccat)))
             (not (member v (constraint-db-bfrlist new-ccat))))))

(defmacro gbc-add-rule (name lit-alist syntaxp)
  `(table fgl::fgl-bool-constraints
          nil
          (gbc-rule-add-to-catalog
           (constraint-rule ',name ',lit-alist ',syntaxp)
           (table-alist 'fgl::fgl-bool-constraints world))
          :clear))




(define gbc-translate-lit-alist (lit-patterns state)
  :mode :program
  ;; :returns (lit-alist pseudo-term-subst-p)
  (b* (((when (atom lit-patterns)) (value nil))
       ((list var term) (car lit-patterns))
       ((er trans) (acl2::translate term t t nil 'def-fgl-boolean-constraint (w state)
                              state))
       ((er rest) (gbc-translate-lit-alist (cdr lit-patterns) state)))
    (value (cons (cons var trans) rest))))



(define def-fgl-boolean-constraint-fn (name lit-patterns syntaxp body hints state)
  :mode :program
  (b* (((er syntaxp-trans) (acl2::translate syntaxp t t nil 'def-fgl-boolean-constraint
                                      (w state) state))
       ((er alist) (gbc-translate-lit-alist lit-patterns state))
       (body1 `(let ,(pairlis$ (strip-cars lit-patterns)
                               (pairlis$ (pairlis$
                                          (make-list-ac (len lit-patterns) 'fgl-bool-fix nil)
                                          (strip-cdrs lit-patterns))
                                         nil))
                 ,body)))
    (value `(progn (defthm ,name
                     ,body1
                     :hints ,hints
                     :rule-classes nil)
                   (gbc-add-rule ,name ,alist ,syntaxp-trans)))))


(defun fgl-bool-fix (x)
  (and x t))

(defsection def-fgl-boolean-constraint
  :parents (reference term-level-reasoning)
  :short "Define a rule that recognizes constraints among FGL generated Boolean variables"
  :long "
<p>When using FGL in a term-level style FGL
may generate new Boolean variables from terms that appear as IF tests.</p>

<p>Sometimes, the terms from which these variables are generated have
interdependent meanings.  For example, if Boolean variable @('a') represents
@('(logbitp 5 x)') and Boolean variable @('b') represents @('(integerp x)'), it
should be impossible for @('a') to be true when @('b') is false.  However, by
default, the Boolean variables generated this way are unconstrained.  When
this sort of interdependency among variables exists but is not accounted for,
it can cause FGL to find false counterexamples.</p>

<p>@('Def-fgl-boolean-constraint') provides a mechanism to make such constraints
known to FGL.  While symbolically executing a form, FGL maintains a constraint, a
Boolean formula known to always be true (under the evolving assignment of
Boolean variables to terms).  A constraint rule generated by
@('def-fgl-boolean-constraint') is triggered when a Boolean variable is
generated from an IF condition term and can cause the constraint to be updated
with a new conjunct.</p>

<p>A Boolean constraint rule is formulated as follows:</p>
@({
 (def-fgl-boolean-constraint fgl-logbitp-implies-integerp
    :bindings ((bit    (logbitp n x))
               (intp   (integerp x)))
    :body (implies bit intp)
    ;; optional arguments:
    :syntaxp ...
    :hints ...)
 })
<p>This generates a proof obligation:</p>
@({
 (defthm fgl-logbitp-implies-integerp
   (let ((bit    (fgl-bool-fix (logbitp n x)))
         (intp   (fgl-bool-fix (integerp x))))
     (implies bit intp))
  :hints ...
  :rule-classes nil)
 })
<p>(The optional :hints argument to def-fgl-boolean-constraint provides the
hints for the proof obligation.)</p>

<p>Once this rule is established, FGL will generate constraints as follows:</p>
<ul>
<li>When a Boolean variable @('a') is generated from an IF condition matching
@('(logbitp n x)'), FGL will search for an existing generated Boolean variable
@('b') whose IF condition was @('(integerp x)') and, if it exists, add the
constraint @('(implies a b)').</li>

<li>Conversely, when a Boolean variable @('b') is generated from an IF
condition matching @('(integerp x)'), FGL will search for existing generated
Boolean variables @('ai') matching @('(logbitp n x)'), and for each of them,
add the constraint @('(implies ai b)').</li>
</ul>

<p>To show that this rule works, you can verify that the following events fail
prior to introducing the constraint rule above, but succeed after:</p>

@({
 (def-fgl-thm foo1
    :hyp t
    :concl (if (integerp x) t (not (logbitp n x)))
    :g-bindings nil
    :rule-classes nil)

 (def-fgl-thm foo2
    :hyp t
    :concl (if (logbitp n x) (integerp x) t)
    :g-bindings nil
    :rule-classes nil)
 })
"


  (defmacro def-fgl-boolean-constraint (name &key bindings (syntaxp ''t) body
                                            hints)
    `(make-event
      (def-fgl-boolean-constraint-fn
        ',name ',bindings ',syntaxp ',body ',hints state))))


(local (defthm assoc-when-nonnil
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(defthm member-bfrlist-of-lookup-in-fgl-object-bindings
  (implies (and (not (member v (fgl-object-bindings-bfrlist x)))
                (pseudo-var-p k))
           (not (member v (fgl-object-bfrlist (cdr (hons-assoc-equal k x))))))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist hons-assoc-equal))))

(define gbc-signature ((common-vars pseudo-var-list-p)
                       (subst fgl-object-bindings-p))
  :returns (sig fgl-objectlist-p)
  (if (atom common-vars)
      nil
    (hons (cdr (assoc (pseudo-var-fix (car common-vars))
                      (fgl-object-bindings-fix subst)))
          (gbc-signature (cdr common-vars) subst)))
  ///
  (defret bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bindings-bfrlist subst)))
             (not (member v (fgl-objectlist-bfrlist sig))))))

(define gbc-extend-substs ((lit-subst fgl-object-bindings-p)
                           (partial-substs fgl-object-bindingslist-p))
  :returns (new-substs fgl-object-bindingslist-p)
  (if (atom partial-substs)
      nil
    ;; is append good enough? I think so
    (cons (append (fgl-object-bindings-fix lit-subst)
                  (fgl-object-bindings-fix (car partial-substs)))
          (gbc-extend-substs lit-subst (cdr partial-substs))))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindings-bfrlist lit-subst)))
                  (not (member v (fgl-object-bindingslist-bfrlist partial-substs))))
             (not (member v (fgl-object-bindingslist-bfrlist new-substs))))
    :hints(("Goal" :in-theory (enable fgl-object-bindingslist-bfrlist)))))

(local (defthm symbol-alistp-when-fgl-object-bindings-p
         (implies (fgl-object-bindings-p x)
                  (symbol-alistp x))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-p)))))

(local (in-theory (disable symbol-alistp)))



(define gbc-substs-check-syntaxp ((substs fgl-object-bindingslist-p)
                                  (thmname symbolp)
                                  (syntaxp pseudo-termp)
                                  state)
  :returns (insts constraint-instancelist-p)
  (b* (((when (atom substs)) nil)
       (subst (fgl-object-bindings-fix (car substs)))
       ((mv err ok) (acl2::magic-ev (pseudo-term-fix syntaxp) subst state t t))
       ((when (or err (not ok)))
        (gbc-substs-check-syntaxp (cdr substs) thmname syntaxp state)))
    (cons (constraint-instance thmname subst)
          (gbc-substs-check-syntaxp (cdr substs) thmname syntaxp state)))
  ///
  (defret bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bindingslist-bfrlist substs)))
             (not (member v (constraint-instancelist-bfrlist insts))))
    :hints(("Goal" :in-theory (enable fgl-object-bindingslist-bfrlist
                                      constraint-instancelist-bfrlist
                                      constraint-instance-bfrlist)))))


(define gbc-sort-substs-into-sigtable ((substs fgl-object-bindingslist-p)
                                       (common-vars pseudo-var-list-p)
                                       (sigtable sig-table-p))
  :returns (new-sigtable sig-table-p)
  (b* (((when (atom substs)) (sig-table-fix sigtable))
       (subst (fgl-object-bindings-fix (car substs)))
       (sig (gbc-signature common-vars subst))
       (sig-substs (cdr (hons-get sig (sig-table-fix sigtable))))
       (sigtable (hons-acons sig (cons subst sig-substs) sigtable)))
    (gbc-sort-substs-into-sigtable (cdr substs) common-vars sigtable))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindingslist-bfrlist substs)))
                  (not (member v (sig-table-bfrlist sigtable))))
             (not (member v (sig-table-bfrlist new-sigtable))))
    :hints(("Goal" :in-theory (enable sig-table-bfrlist
                                      fgl-object-bindingslist-bfrlist)))))


;; Invariant: for a given rule, existing lit set, and matching lit, there is at
;; most 1 tuple stored in the constraint-db.  Here we are extending some
;; partial substitution with a match for a literal, so we need to find all
;; tuples where we need to store the new substitution.  In this function we
;; have picked a still-unmatched lit to match on and we are looking for the
;; unique tuple that matches.  Below in gbc-add-new-substs-for-unmatched-lit we
;; also add a new one if we did not find it, and we iterate over the unmatched
;; lits for the rule in gbc-add-new-substs-for-unmatched-lits.
(define gbc-add-substs-to-existing-tuple ((rule constraint-rule-p)
                                          (existing-lits pseudo-var-set-p)
                                          (lit pseudo-var-p)
                                          (substs fgl-object-bindingslist-p)
                                          (tuples constraint-tuplelist-p))
  :returns (mv found
               (new-tuples constraint-tuplelist-p))
  :measure (len tuples)
  (b* ((tuples (constraint-tuplelist-fix tuples))
       ((when (atom tuples)) (mv nil tuples))
       ((constraint-tuple x) (car tuples))
       ((unless (and (equal (constraint-rule-fix rule) x.rule)
                     (equal (pseudo-var-set-fix existing-lits) x.existing-lits)
                     (eq (pseudo-var-fix lit) x.matching-lit)))
        (b* (((mv found rest)
              (gbc-add-substs-to-existing-tuple
               rule existing-lits lit substs (cdr tuples)))
             ((when found)
              (mv t (cons x rest))))
          (mv nil tuples)))
       (sigtable (gbc-sort-substs-into-sigtable substs x.common-vars
                                                x.sig-table)))
    (mv t
        (cons (change-constraint-tuple x :sig-table sigtable)
              (cdr tuples))))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindingslist-bfrlist substs)))
                  (not (member v (constraint-tuplelist-bfrlist tuples))))
             (not (member v (constraint-tuplelist-bfrlist new-tuples))))
    :hints(("Goal" :in-theory (e/d (constraint-tuplelist-bfrlist
                                      constraint-tuple-bfrlist)
                                   ((:d gbc-add-substs-to-existing-tuple)))
            :induct <call> :expand (<call>)))))



(define gbc-add-new-substs-for-unmatched-lit ((unmatched-litvar pseudo-var-p)
                                              (rule constraint-rule-p)
                                              (existing-lits pseudo-var-set-p)
                                              (existing-vars pseudo-var-set-p)
                                              (substs fgl-object-bindingslist-p)
                                              (ccat constraint-db-p))
  :returns (new-ccat constraint-db-p)
  (b* ((ccat (constraint-db-fix ccat))
       ((constraint-rule r) rule)
       (lit (cdr (hons-assoc-equal (pseudo-var-fix unmatched-litvar) r.lit-alist)))
       ((unless (pseudo-term-case lit :fncall)) ccat)
       (fnsym (acl2::pseudo-term-fncall->fn lit))
       (tuples (cdr (hons-get fnsym ccat)))
       ((mv found new-tuples)
        (gbc-add-substs-to-existing-tuple
         rule existing-lits unmatched-litvar substs tuples))
       ((when found)
        (hons-acons fnsym new-tuples ccat))
       (lit-vars (set::mergesort (term-vars lit)))
       (common-vars (set::intersect (pseudo-var-set-fix existing-vars) lit-vars))
       (sigtable (gbc-sort-substs-into-sigtable substs common-vars nil))
       (new-tuple (make-constraint-tuple
                   :rule rule
                   :existing-lits existing-lits
                   :matching-lit unmatched-litvar
                   :common-vars common-vars
                   :existing-vars existing-vars
                   :sig-table sigtable)))
    (hons-acons fnsym (cons new-tuple tuples) ccat))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindingslist-bfrlist substs)))
                  (not (member v (constraint-db-bfrlist ccat))))
             (not (member v (constraint-db-bfrlist new-ccat))))
    :hints(("Goal" :in-theory (enable constraint-db-bfrlist
                                      constraint-tuplelist-bfrlist
                                      constraint-tuple-bfrlist)))))

(define gbc-add-new-substs-for-unmatched-lits ((unmatched-litvars pseudo-var-list-p)
                                               (rule constraint-rule-p)
                                               (existing-lits pseudo-var-set-p)
                                               (existing-vars pseudo-var-set-p)
                                               (substs fgl-object-bindingslist-p)
                                               (ccat constraint-db-p))
  :returns (new-ccat constraint-db-p)
  (if (atom unmatched-litvars)
      (constraint-db-fix ccat)
    (gbc-add-new-substs-for-unmatched-lits
     (cdr unmatched-litvars) rule existing-lits existing-vars substs
     (gbc-add-new-substs-for-unmatched-lit
      (car unmatched-litvars) rule existing-lits existing-vars substs ccat)))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (not (member v (fgl-object-bindingslist-bfrlist substs)))
                  (not (member v (constraint-db-bfrlist ccat))))
             (not (member v (constraint-db-bfrlist new-ccat))))))

(local (defthm pseudo-var-list-p-strip-cars-of-fgl-object-bindings
         (implies (fgl-object-bindings-p x)
                  (pseudo-var-list-p (strip-cars x)))
         :hints(("Goal" :in-theory (enable strip-cars
                                           fgl-object-bindings-p)))))

(local (defthm pseudo-var-list-p-strip-cars-of-pseudo-term-subst
         (implies (pseudo-term-subst-p x)
                  (pseudo-var-list-p (strip-cars x)))
         :hints(("Goal" :in-theory (enable strip-cars
                                           fgl-object-bindings-p)))))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(define gbc-process-new-lit-tuple ((lit fgl-object-p)
                                   (tuple constraint-tuple-p)
                                   (ccat constraint-db-p)
                                   (bfrstate bfrstate-p)
                                   state)
  :returns (mv (insts constraint-instancelist-p)
               (new-ccat constraint-db-p))
  :guard (bfr-listp (fgl-object-bfrlist lit))
  (b* ((ccat (constraint-db-fix ccat))
       ((constraint-tuple x) tuple)
       ;; (rule existing-lits matching-lit common-vars existing-vars sig-table)
       ((constraint-rule r) x.rule)
       ;; (thmname lit-alist syntaxp)
       (pat (cdr (hons-assoc-equal x.matching-lit r.lit-alist)))
       ((mv ok lit-subst) (fgl-unify-term/gobj pat lit nil))
       ((unless ok) (mv nil ccat))
       (sig (gbc-signature x.common-vars lit-subst))
       (partial-substs (cdr (hons-get sig x.sig-table)))
       (new-substs (gbc-extend-substs lit-subst partial-substs))
       (rest-litvars (set-difference-eq (strip-cars r.lit-alist)
                                        (cons x.matching-lit x.existing-lits)))
       ;; (- (cw "rest-litvars: ~x0 matching: ~x1 existing: ~x2~%" rest-litvars
       ;;        x.matching-lit x.existing-lits))
       ((unless rest-litvars)
        (b* ((substs (gbc-substs-check-syntaxp new-substs r.thmname r.syntaxp state)))
          (mv substs ccat)))
       (new-existing-vars (set::union (set::mergesort (strip-cars lit-subst))
                                      x.existing-vars))
       ;; unbound lits remaining -- add to ccat
       (ccat (gbc-add-new-substs-for-unmatched-lits
              rest-litvars
              x.rule
              ;; need to keep these canonical
              ;; so that we can find an existing
              ;; tuple if it exists
              (set::insert x.matching-lit x.existing-lits)
              new-existing-vars
              new-substs
              ccat)))
    (mv nil ccat))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (bfr-listp (fgl-object-bfrlist lit))
                  (bfr-listp (constraint-tuple-bfrlist tuple))
                  (bfr-listp (constraint-db-bfrlist ccat)))
             (and (bfr-listp (constraint-instancelist-bfrlist insts))
                  (bfr-listp (constraint-db-bfrlist new-ccat))))
    :hints(("Goal" :in-theory (enable constraint-tuple-bfrlist
                                      bfr-listp-when-not-member-witness)))))




(define gbc-process-new-lit-tuples ((lit fgl-object-p)
                                    (tuples constraint-tuplelist-p)
                                    (ccat constraint-db-p)
                                    (bfrstate bfrstate-p)
                                    state)
  :returns (mv (insts constraint-instancelist-p)
               (new-ccat constraint-db-p))
  :guard (bfr-listp (fgl-object-bfrlist lit))
  (b* (((when (atom tuples)) (mv nil (constraint-db-fix ccat)))
       ((mv substs1 ccat)
        (gbc-process-new-lit-tuple lit (car tuples) ccat bfrstate state))
       ((mv substs-rest ccat)
        (gbc-process-new-lit-tuples lit (cdr tuples) ccat bfrstate state)))
    (mv (append substs1 substs-rest) ccat))
  ///
  
  (defret bfrlist-of-<fn>
    (implies (and (bfr-listp (fgl-object-bfrlist lit))
                  (bfr-listp (constraint-tuplelist-bfrlist tuples))
                  (bfr-listp (constraint-db-bfrlist ccat)))
             (and (bfr-listp (constraint-instancelist-bfrlist insts))
                  (bfr-listp (constraint-db-bfrlist new-ccat))))
    :hints(("Goal" :in-theory (enable constraint-tuplelist-bfrlist)))))


(define gbc-process-new-lit ((lit fgl-object-p)
                             (ccat constraint-db-p)
                             (bfrstate bfrstate-p)
                             state)
  :returns (mv (insts constraint-instancelist-p)
               (new-ccat constraint-db-p))
  :guard (bfr-listp (fgl-object-bfrlist lit))
  (b* ((ccat (constraint-db-fix ccat))
       ((unless (fgl-object-case lit :g-apply))
        (mv nil ccat))
       (tuples (cdr (hons-get (g-apply->fn lit) ccat))))
    (gbc-process-new-lit-tuples lit tuples ccat bfrstate state))
  ///
  (defret bfrlist-of-<fn>
    (implies (and (bfr-listp (fgl-object-bfrlist lit))
                  (bfr-listp (constraint-db-bfrlist ccat)))
             (and (bfr-listp (constraint-instancelist-bfrlist insts))
                  (bfr-listp (constraint-db-bfrlist new-ccat))))
    :hints(("Goal" :in-theory (enable constraint-tuplelist-bfrlist)))))


(define gbc-tuples-make-fast ((x constraint-tuplelist-p))
  :enabled t
  (mbe :logic (constraint-tuplelist-fix X)
       :exec (if (atom x)
                 nil
               (cons (change-constraint-tuple (car x)
                                              :sig-table
                                              (make-fast-alist
                                               (constraint-tuple->sig-table (car x))))
                     (gbc-tuples-make-fast (cdr x))))))

(define gbc-tuples-free ((x constraint-tuplelist-p))
  (if (atom x)
      nil
    (prog2$ (fast-alist-free (constraint-tuple->sig-table (car x)))
            (gbc-tuples-free (cdr x)))))

(define gbc-db-make-fast-rec ((x constraint-db-p)
                              (acc constraint-db-p))
  :returns (new-x constraint-db-p)
  :enabled t
  (mbe :logic (hons-shrink-alist (constraint-db-fix x)
                                 (constraint-db-fix acc))
       :exec (b* ((acc (constraint-db-fix acc))
                  (x (constraint-db-fix x))
                  ((when (atom x)) acc)
                  (acc (if (hons-get (caar x) acc)
                           acc
                         (hons-acons (caar x)
                                     (gbc-tuples-make-fast (cdar x))
                                     acc))))
               (gbc-db-make-fast-rec (cdr x) acc))))

(define gbc-db-make-fast ((x constraint-db-p))
  :returns (new-x constraint-db-p)
  :enabled t
  (gbc-db-make-fast-rec x nil))

(define gbc-db-free-rec ((x constraint-db-p))
  (if (atom x)
      nil
    (prog2$ (gbc-tuples-free (cdar x))
            (gbc-db-free-rec (cdr x)))))

(define gbc-db-free ((x constraint-db-p))
  (gbc-db-free-rec (fast-alist-free x)))






#||

(fgl::def-fgl-boolean-constraint logbitp-n-m
       :bindings ((x (logbitp n a))
                  (y (logbitp m a)))
       :syntaxp (and (acl2::<< n m)
                     (not (and (atom n) (atom m))))
       :body (implies (equal n m)
                      (equal x y)))

(time$ (b* ((ccat (table-alist 'fgl-bool-constraints (w state)))
     ((mv substs ccat)
      (gbc-process-new-lit '(:g-apply logbitp (fff) q) ccat state))
     (- (cw "substs1: ~x0~%" substs))
     (ccat (hons-shrink-alist ccat nil))
     (state (f-put-global 'ccat1 ccat state))
     ((mv substs ccat)
      (gbc-process-new-lit '(:g-apply logbitp (qwr) b) ccat state))
     (- (cw "substs2: ~x0~%" substs))
     (ccat (hons-shrink-alist ccat nil))
     (state (f-put-global 'ccat2 ccat state))
     ((mv substs ccat)
      (gbc-process-new-lit '(:g-apply logbitp (qwf) q) ccat state))
     (- (cw "substs3: ~x0~%" substs))
     (ccat (hons-shrink-alist ccat nil))
     (state (f-put-global 'ccat3 ccat state))
     ((mv substs ccat)
      (gbc-process-new-lit '(:g-apply logbitp (fff) b) ccat state))
     (- (cw "substs4: ~x0~%" substs))
     (ccat (hons-shrink-alist ccat nil))
     (state (f-put-global 'ccat3 ccat state)))
  state))

||#
