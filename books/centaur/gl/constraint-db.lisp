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

(in-package "GL")

(include-book "clause-processors/unify-subst" :dir :system)
(include-book "glcp-unify-defs")
(include-book "clause-processors/magic-ev" :dir :system)


(defun gl-bool-fix (x)
  (and x t))

;; A constraint rule is written as follows:

;; (gl::def-gl-boolean-constraint thmname
;;        :bindings ((x (logbitp n a))
;;                   (y (logbitp m a)))
;;        :syntaxp (and (<< n m)
;;                      (not (and (atom n) (atom m))))
;;        :body (implies (equal n m)
;;                       (equal x y))
;;        :hints ...)

;; This generates an ACL2 theorem:
;; (defthm thmname
;;    (let ((x (gl-bool-fix (logbitp n a)))
;;          (y (gl-bool-fix (logbitp m a))))
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
;;
;; Outermost structure is indexed by the first function symbol of the literal.
;; Inside that is a list of tuples:
;; (rule existing-lits matching-lit common-variables signature-table)
;; rule is a constraint rule structure, matching-lit is the variable of the
;; lit pattern we'll match against, existing-lits are variables of lit
;; patterns for which literals have already been found.
;; Common-vars are the intersection of the vars of the matching-lit pattern
;; with the vars of the existing-lit patterns.
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

;; As a GL proof progresses, new literals may be added to the bvar-db and the
;; constraint-table may be extended.  But we start with a base constraint-table
;; at the beginning of any proof; this is stored in an ACL2 table.  In this
;; initial constraing table, each tuple has empty existing-lits, thus empty
;; common-vars and thus the unique signature is NIL, and a single empty
;; partial unifying subst is stored under that signature.

;; Heuristic info about a constraint rule.
;; We'll look up the theorem in the world, so it doesn't need to be stored
;; here.
;; Constrained-terms is an alist mapping variables to terms.
(std::defaggregate constraint-rule
  (thmname lit-alist syntaxp))

;; this is the tuple referred to above
(std::defaggregate constraint-tuple
  (rule existing-lits matching-lit common-vars existing-vars sig-table))


;; Code to add a rule to the initial catalog (with empty existing-lits etc).
(defun gbc-rule-lit-add-catalog-entry (var pat rule ccat)
  (b* ((fnsym (car pat))
       (tuples (cdr (hons-assoc-equal fnsym ccat)))
       ;; assume rule is new, so no matching tuple exists -- just cons on a new
       ;; one.
       ;; signature-table contains nil mapped to (list nil) -- list containing
       ;; one empty unifying subst
       (new-tuple (constraint-tuple rule nil var nil nil (hons-acons nil (list nil) nil))))
    (cons (cons fnsym (cons new-tuple tuples)) ccat)))

(defun gbc-rule-add-catalog-entries (lit-alist rule ccat)
  (b* (((when (atom lit-alist)) ccat)
       ((cons var pat) (car lit-alist))
       (ccat (gbc-rule-lit-add-catalog-entry var pat rule ccat)))
    (gbc-rule-add-catalog-entries (cdr lit-alist) rule ccat)))


;; Optimization: if two constrained terms are isomorphic (they unify with the
;; same terms), and there's no syntaxp, then there's no need to list the rule
;; under both of them
(defun gbc-alist-has-symmetric (term alist)
  (b* (((when (atom alist)) nil)
       (term2 (cdar alist))
       ((mv ok1 &) (acl2::simple-one-way-unify term term2 nil))
       ((mv ok2 &) (acl2::simple-one-way-unify term2 term nil)))
    (or (and ok1 ok2)
        (gbc-alist-has-symmetric term (cdr alist)))))

(defun gbc-alist-remove-symmetric (alist)
  (if (atom alist)
      nil
    (if (gbc-alist-has-symmetric (cdar alist) (cdr alist))
        (gbc-alist-remove-symmetric (cdr alist))
      (cons (car alist) (gbc-alist-remove-symmetric (cdr alist))))))




(defun gbc-rule-add-to-catalog (rule ccat)
  ;; Iterate over the constraint-alist.
  (b* ((syntaxp (constraint-rule->syntaxp rule))
       (alist (constraint-rule->lit-alist rule))
       (reduced-alist (if (equal syntaxp ''t)
                          (gbc-alist-remove-symmetric alist)
                        alist)))
    (hons-shrink-alist
     (gbc-rule-add-catalog-entries reduced-alist rule ccat)
     nil)))

(defmacro gbc-add-rule (name lit-alist syntaxp)
  `(table gl::gl-bool-constraints
          nil
          (gbc-rule-add-to-catalog
           (constraint-rule ',name ',lit-alist ',syntaxp)
           (table-alist 'gl::gl-bool-constraints world))
          :clear))




(defun gbc-translate-lit-alist (lit-patterns state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (atom lit-patterns)) (value nil))
       ((list var term) (car lit-patterns))
       ((er trans) (acl2::translate term t t nil 'def-gl-boolean-constraint (w state)
                              state))
       ((er rest) (gbc-translate-lit-alist (cdr lit-patterns) state)))
    (value (cons (cons var trans) rest))))



(defun def-gl-boolean-constraint-fn (name lit-patterns syntaxp body hints state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er syntaxp-trans) (acl2::translate syntaxp t t nil 'def-gl-boolean-constraint
                                      (w state) state))
       ((er alist) (gbc-translate-lit-alist lit-patterns state))
       (body1 `(let ,(pairlis$ (strip-cars lit-patterns)
                               (pairlis$ (pairlis$
                                          (make-list-ac (len lit-patterns) 'gl-bool-fix nil)
                                          (strip-cdrs lit-patterns))
                                         nil))
                 ,body)))
    (value `(progn (defthm ,name
                     ,body1
                     :hints ,hints
                     :rule-classes nil)
                   (gbc-add-rule ,name ,alist ,syntaxp-trans)))))

(defsection def-gl-boolean-constraint
  :parents (reference term-level-reasoning)
  :short "Define a rule that recognizes constraints among GL generated Boolean variables"
  :long "
<p>When using GL in a term-level style (see @(see term-level-reasoning)), GL
may generate new Boolean variables from terms that appear as IF tests.</p>

<p>Sometimes, the terms from which these variables are generated have
interdependent meanings.  For example, if Boolean variable @('a') represents
@('(logbitp 5 x)') and Boolean variable @('b') represents @('(integerp x)'), it
should be impossible for @('a') to be true when @('b') is false.  However, by
default, the Boolean variables generated this way are unconstrained.  When
this sort of interdependency among variables exists but is not accounted for,
it can cause GL to find @(see false-counterexamples).</p>

<p>@('Def-gl-boolean-constraint') provides a mechanism to make such constraints
known to GL.  While symbolically executing a form, GL maintains a constraint, a
Boolean formula known to always be true (under the evolving assignment of
Boolean variables to terms).  A constraint rule generated by
@('def-gl-boolean-constraint') is triggered when a Boolean variable is
generated from an IF condition term and can cause the constraint to be updated
with a new conjunct.</p>

<p>A Boolean constraint rule is formulated as follows:</p>
@({
 (def-gl-boolean-constraint gl-logbitp-implies-integerp
    :bindings ((bit    (logbitp n x))
               (intp   (integerp x)))
    :body (implies bit intp)
    ;; optional arguments:
    :syntaxp ...
    :hints ...)
 })
<p>This generates a proof obligation:</p>
@({
 (defthm gl-logbitp-implies-integerp
   (let ((bit    (gl-bool-fix (logbitp n x)))
         (intp   (gl-bool-fix (integerp x))))
     (implies bit intp))
  :hints ...
  :rule-classes nil)
 })
<p>(The optional :hints argument to def-gl-boolean-constraint provides the
hints for the proof obligation.)</p>

<p>Once this rule is established, GL will generate constraints as follows:</p>
<ul>
<li>When a Boolean variable @('a') is generated from an IF condition matching
@('(logbitp n x)'), GL will search for an existing generated Boolean variable
@('b') whose IF condition was @('(integerp x)') and, if it exists, add the
constraint @('(implies a b)').</li>

<li>Conversely, when a Boolean variable @('b') is generated from an IF
condition matching @('(integerp x)'), GL will search for existing generated
Boolean variables @('ai') matching @('(logbitp n x)'), and for each of them,
add the constraint @('(implies ai b)').</li>
</ul>

<p>To show that this rule works, you can verify that the following events fail
prior to introducing the constraint rule above, but succeed after:</p>

@({
 (def-gl-thm foo1
    :hyp t
    :concl (if (integerp x) t (not (logbitp n x)))
    :g-bindings nil
    :rule-classes nil)

 (def-gl-thm foo2
    :hyp t
    :concl (if (logbitp n x) (integerp x) t)
    :g-bindings nil
    :rule-classes nil)
 })
"


  (defmacro def-gl-boolean-constraint (name &key bindings (syntaxp ''t) body
                                            hints)
    `(make-event
      (def-gl-boolean-constraint-fn
        ',name ',bindings ',syntaxp ',body ',hints state))))

(defun gbc-signature (common-vars subst)
  (if (atom common-vars)
      nil
    (hons (cdr (assoc (car common-vars) subst))
          (gbc-signature (cdr common-vars) subst))))

(defun gbc-extend-substs (lit-subst partial-substs)
  (if (atom partial-substs)
      nil
    ;; is append good enough? I think so
    (cons (append lit-subst (car partial-substs))
          (gbc-extend-substs lit-subst (cdr partial-substs)))))

(defun gbc-substs-check-syntaxp (substs thmname syntaxp state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((when (atom substs)) nil)
       ((mv err ok) (acl2::magic-ev syntaxp (car substs) state t t))
       ((when (or err (not ok)))
        (gbc-substs-check-syntaxp (cdr substs) thmname syntaxp state)))
    (cons (cons thmname (car substs))
          (gbc-substs-check-syntaxp (cdr substs) thmname syntaxp state))))


(defun gbc-sort-substs-into-sigtable (substs common-vars sigtable)
  (b* (((when (atom substs)) sigtable)
       (subst (car substs))
       (sig (gbc-signature common-vars subst))
       (sig-substs (cdr (hons-get sig sigtable)))
       (sigtable (hons-acons sig (cons subst sig-substs) sigtable)))
    (gbc-sort-substs-into-sigtable (cdr substs) common-vars sigtable)))

(defun gbc-unbound-lits-add-to-existing-tuple (rule existing-lits lit substs tuples)
  (b* (((when (atom tuples)) (mv nil tuples))
       ((constraint-tuple x) (car tuples))
       ((unless (and (equal rule x.rule)
                     (equal existing-lits x.existing-lits)
                     (equal lit x.matching-lit)))
        (b* (((mv found rest)
              (gbc-unbound-lits-add-to-existing-tuple
               rule existing-lits lit substs (cdr tuples)))
             ((when found)
              (mv t (cons (car tuples) rest))))
          (mv nil tuples)))
       (sigtable (gbc-sort-substs-into-sigtable substs x.common-vars
                                                x.sig-table)))
    (mv t
        (cons (constraint-tuple rule existing-lits lit
                                x.common-vars x.existing-vars sigtable)
              (cdr tuples)))))


(defun gbc-unbound-lits-add-tuples (litvars rule existing-lits existing-vars
                                            substs ccat)
  (b* (((when (atom litvars)) ccat)
       (var (car litvars))
       ((constraint-rule r) rule)
       (lit (cdr (hons-assoc-equal var r.lit-alist)))
       (fnsym (car lit))
       (tuples (cdr (hons-get fnsym ccat)))
       ((mv found tuples)
        (gbc-unbound-lits-add-to-existing-tuple
         rule existing-lits var substs tuples))
       ((when found)
        (hons-acons fnsym tuples ccat))
       (lit-vars (set::mergesort (acl2::simple-term-vars lit)))
       (common-vars (set::intersect existing-vars lit-vars))
       (sigtable (gbc-sort-substs-into-sigtable substs common-vars nil))
       (new-tuple (constraint-tuple rule existing-lits var common-vars
                                    existing-vars sigtable)))
    (hons-acons fnsym (cons new-tuple tuples) ccat)))

(defun gbc-process-new-lit-tuple (lit tuple ccat state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((constraint-tuple x) tuple)
       ;; (rule existing-lits matching-lit common-vars existing-vars sig-table)
       ((constraint-rule r) x.rule)
       ;; (thmname lit-alist syntaxp)
       (pat (cdr (hons-assoc-equal x.matching-lit r.lit-alist)))
       ((mv ok lit-subst) (glcp-unify-term/gobj pat lit nil))
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
       (ccat (gbc-unbound-lits-add-tuples
              rest-litvars
              x.rule
              ;; need to keep these canonical
              ;; so that we can find an existing
              ;; tuple if it exists
              (set::insert x.matching-lit x.existing-lits)
              new-existing-vars
              new-substs
              ccat)))
    (mv nil ccat)))




(defun gbc-process-new-lit-tuples (lit tuples ccat state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((when (atom tuples)) (mv nil ccat))
       ((mv substs1 ccat)
        (gbc-process-new-lit-tuple lit (car tuples) ccat state))
       ((mv substs-rest ccat)
        (gbc-process-new-lit-tuples lit (cdr tuples) ccat state)))
    (mv (append substs1 substs-rest) ccat)))


(defund gbc-process-new-lit (lit ccat state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((unless (and (consp lit)
                     (eq (tag lit) :g-apply)))
        (mv nil ccat))
       (tuples (cdr (hons-get (g-apply->fn lit) ccat))))
    (gbc-process-new-lit-tuples lit tuples ccat state)))


(defun gbc-tuples-make-fast (x)
  (if (atom x)
      nil
    (cons (change-constraint-tuple (car x)
                                   :sig-table
                                   (make-fast-alist
                                    (constraint-tuple->sig-table (car x))))
          (gbc-tuples-make-fast (cdr x)))))

(defun gbc-tuples-free (x)
  (if (atom x)
      nil
    (prog2$ (fast-alist-free (constraint-tuple->sig-table (car x)))
            (gbc-tuples-free (cdr x)))))

(defun gbc-db-make-fast-rec (x acc)
  (b* (((when (atom x)) acc)
       (acc (if (and (consp (car x))
                     (not (hons-get (caar x) acc)))
                (hons-acons (caar x)
                            (gbc-tuples-make-fast (cdar x))
                            acc)
              acc)))
    (gbc-db-make-fast-rec (cdr x) acc)))

(defund gbc-db-make-fast (x)
  (gbc-db-make-fast-rec x nil))

(defun gbc-db-free-rec (x)
  (if (atom x)
      nil
    (prog2$ (and (consp (car x))
                 (gbc-tuples-free (cdar x)))
            (gbc-db-free-rec (cdr x)))))

(defund gbc-db-free (x)
  (gbc-db-free-rec (fast-alist-free x)))




#||

(gl::def-gl-boolean-constraint logbitp-n-m
       :bindings ((x (logbitp n a))
                  (y (logbitp m a)))
       :syntaxp (and (acl2::<< n m)
                     (not (and (atom n) (atom m))))
       :body (implies (equal n m)
                      (equal x y)))

(time$ (b* ((ccat (table-alist 'gl-bool-constraints (w state)))
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
