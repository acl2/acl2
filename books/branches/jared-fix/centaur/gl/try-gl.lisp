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

(in-package "GL")

;; This is a wrapper for GL-HINT that is intended to be applied automatically
;; to certain subgoals.  There are many possible degrees of automation for this
;; sort of thing, but here we're looking at a use case where you could probably
;; take a failing subgoal and isolate it into a lemma, but would rather not do
;; the work; instead, perhaps you want to apply GL to several similar such
;; subgoals.

;; For example, suppose our proof fails on a subgoal:

;; (IMPLIES
;;  (AND
;;   (EQUAL (ST-GET :PC ST) 921)
;;   (NOT (LOGBITP 10 (U64-TR-GET 6 (ST-GET :C1REGS ST))))
;;   (CONSP (RET-STACK ST))
;;   (< 9
;;      (LOGHEAD 4 (U64-TR-GET 16 (ST-GET :GREGS ST))))
;;   (LOGBITP
;;    4
;;    (ACL2::RESET-ALL-RESERVED-BITS
;;         (RFLAGS-FROM-GFLAGS
;;              (LOGIOR (BOOL->BIT (LOGBITP 0 (NFIX (ST-GET :EFLAGS ST))))
;;                      (ASH (BOOL->BIT (LOGBITP 2 (NFIX (ST-GET :EFLAGS ST))))
;;                           1)
;;                      (ASH (BOOL->BIT (LOGBITP 4 (NFIX (ST-GET :EFLAGS ST))))
;;                           2)
;;                      (ASH (BOOL->BIT (LOGBITP 6 (NFIX (ST-GET :EFLAGS ST))))
;;                           3)
;;                      (ASH (BOOL->BIT (LOGBITP 7 (NFIX (ST-GET :EFLAGS ST))))
;;                           4)
;;                      (ASH (BOOL->BIT (LOGBITP 11 (NFIX (ST-GET :EFLAGS ST))))
;;                           5)))
;;         32)))
;;  (EQUAL
;;   (LOGAND 17
;;           (LOGIOR 17 (NFIX (ST-GET :EFLAGS ST))))
;;   (LOGAND
;;    17
;;    (LOGIOR
;;     17
;;     (ACL2::RESET-ALL-RESERVED-BITS
;;         (RFLAGS-FROM-GFLAGS
;;              (LOGIOR (BOOL->BIT (LOGBITP 0 (NFIX (ST-GET :EFLAGS ST))))
;;                      (ASH (BOOL->BIT (LOGBITP 2 (NFIX (ST-GET :EFLAGS ST))))
;;                           1)
;;                      (ASH (BOOL->BIT (LOGBITP 4 (NFIX (ST-GET :EFLAGS ST))))
;;                           2)
;;                      (ASH (BOOL->BIT (LOGBITP 6 (NFIX (ST-GET :EFLAGS ST))))
;;                           3)
;;                      (ASH (BOOL->BIT (LOGBITP 7 (NFIX (ST-GET :EFLAGS ST))))
;;                           4)
;;                      (ASH (BOOL->BIT (LOGBITP 11 (NFIX (ST-GET :EFLAGS ST))))
;;                           5)))
;;         32)))))

;; What a mess.  Still, looking at this goal we can see that we might have a
;; good chance of proving this goal just by bit-blasting it.  In particular,
;; notice that there are six bits of (NFIX (ST-GET :EFLAGS ST)) mentioned, and
;; if we abstracted these away into separate Boolean variables it seems likely
;; that we might be able to prove this.

;; So the hint allows you to do something like this:

;;  - Identify subterms that you want to abstract away into symbolic values,
;;  e.g., (logbitp k (nfix (st-get :eflags st))), and identify types for those
;;  subterms, e.g. (booleanp (logbitp k (nfix (st-get :eflags st))))
;;  - Add explicit type assumptions of those subterms.
;;  - Generalize away these subterms (and maybe others) into variables.
;;  - Drop some literals of the clause that don't seem to involve any
;;  bit-blastable objects.
;;  - Apply GL to the resulting clause.

;; So far we have no idea how to do this well in BDD mode, because we don't
;; know how to specify a variable ordering in a sane way.  So we recommend
;; using one of the AIG modes (e.g. satlink) for this strategy.

(include-book "clause-processors/find-matching" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/let-abstraction" :dir :system)
(include-book "def-gl-clause-proc")
(include-book "gl-generic-clause-proc")
(include-book "centaur/misc/numlist" :dir :system)
(include-book "shape-spec")

(defun uniquify-nat-list (x next-idx)
  (declare (xargs :guard (natp next-idx)))
  (mv (numlist next-idx 1 (len x))
      (+ (lnfix next-idx) (len x))))

(defthm natp-next-idx-of-uniquify-nat-list
  (natp (mv-nth 1 (uniquify-nat-list x next-idx))))

(defun uniquify-number-spec (x next-idx)
  (declare (xargs :guard (natp next-idx)))
  (if (atom x)
      (mv nil (lnfix next-idx))
    (b* (((mv field next-idx)
          (uniquify-nat-list (car x) next-idx))
         ((mv rest next-idx)
          (uniquify-number-spec (cdr X) next-idx)))
      (mv (cons field rest) next-idx))))

(defthm natp-next-idx-of-uniquify-number-spec
  (natp (mv-nth 1 (uniquify-number-spec x next-idx))))

;; Transforms a shape spec so that all bit indices and var names are unique;
;; they'll just be sequentially numbered.
(defun uniquify-shape-spec (x next-idx next-var)
  (declare (xargs :guard (and (shape-specp x)
                              (natp next-idx)
                              (natp next-var))
                  :verify-guards nil))
  (if (atom x)
      (mv x (lnfix next-idx) (lnfix next-var))
    (case (tag x)
      (:g-number (mv-let (numspec next-idx)
                   (uniquify-number-spec (g-number->num x) next-idx)
                   (mv (g-number numspec) next-idx (lnfix next-var))))
      (:g-integer (b* ((sign next-idx)
                       ((mv bits next-idx)
                        (uniquify-nat-list (g-integer->bits x)
                                           (+ 1 (lnfix next-idx))))
                       (var next-var))
                    (mv (g-integer sign bits var)
                        next-idx (+ 1 (lnfix next-var)))))
      (:g-integer? (b* ((intp next-idx)
                        (sign (+ 1 (lnfix next-idx)))
                        ((mv bits next-idx)
                         (uniquify-nat-list (g-integer?->bits x)
                                            (+ 2 (lnfix next-idx))))
                        (var next-var))
                     (mv (g-integer? sign bits var intp)
                         next-idx (+ 1 (lnfix next-var)))))
      (:g-boolean (mv (g-boolean next-idx) (+ 1 (lnfix next-idx)) (lnfix next-var)))
      (:g-concrete (mv x (lnfix next-idx) (lnfix next-var)))
      (:g-var (mv (g-var next-var) (lnfix next-idx) (1+ (lnfix next-var))))
      (:g-ite
       (b* (((mv test next-idx next-var)
             (uniquify-shape-spec (g-ite->test x) next-idx next-var))
            ((mv then next-idx next-var)
             (uniquify-shape-spec (g-ite->then x) next-idx next-var))
            ((mv else next-idx next-var)
             (uniquify-shape-spec (g-ite->else x) next-idx next-var)))
         (mv (g-ite test then else) next-idx next-var)))
      (:g-call
       (b* (((mv args next-idx next-var)
             (uniquify-shape-spec (g-call->args x) next-idx next-var)))
         (mv (g-call (g-call->fn x) args
                     (g-call->inverse x))
             next-idx next-var)))
      (otherwise
       (b* (((mv car next-idx next-var)
             (uniquify-shape-spec (car x) next-idx next-var))
            ((mv cdr next-idx next-var)
             (uniquify-shape-spec (cdr x) next-idx next-var)))
         (mv (cons car cdr) next-idx next-var))))))

(defthm natp-next-idx-of-uniquify-shape-spec
  (natp (mv-nth 1 (uniquify-shape-spec x next-idx next-var)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-next-var-of-uniquify-shape-spec
  (natp (mv-nth 2 (uniquify-shape-spec x next-idx next-var)))
  :rule-classes (:rewrite :type-prescription))

(verify-guards uniquify-shape-spec
  :hints(("Goal" :in-theory (enable shape-specp))))

(defun integer-with-nbitsp (n x)
  (declare (xargs :guard t)
           (ignore n))
  (integerp x))

(defun integer?-with-nbitsp (n x)
  (declare (xargs :guard t)
           (ignore n x))
  t)

(defconst *default-symobj-generators*
  '(((booleanp x) (g-boolean 0))
    ((unsigned-byte-p n x) (g-number (list (numlist 0 1 (+ 1 n)))))
    ((signed-byte-p n x) (g-number (list (numlist 0 1 n))))
    ((integer-with-nbitsp n x) (g-integer 0 (numlist 0 1 n) 0))
    ((integer?-with-nbitsp n x) (g-integer? 0 (numlist 0 1 n) 0 0))))

(defun translate-term-alist (gens wrld state-vars)
  (declare (xargs :mode :program))
  (b* (((when (atom gens)) (acl2::value-cmp nil))
       ((acl2::cmp key) (acl2::translate-cmp (caar gens) t t t 'try-gl-hint wrld state-vars))
       ((acl2::cmp val) (acl2::translate-cmp (cdar gens) t t t 'try-gl-hint wrld state-vars))
       ((acl2::cmp rest) (translate-term-alist (cdr gens) wrld state-vars)))
    (acl2::value-cmp (cons (cons key val) rest))))

(defun translate-term-list (x wrld state-vars)
  (declare (xargs :mode :program))
  (b* (((when (atom x)) (acl2::value-cmp nil))
       ((acl2::cmp x) (acl2::translate-cmp (car x) t t t 'try-gl-hint wrld state-vars))
       ((acl2::cmp rest) (translate-term-alist (cdr x) wrld state-vars)))
    (acl2::value-cmp (cons x rest))))

;; Subterms-types is a list with entries of the form
;; (term-pattern initial-alist predicate)
;; or (term-pattern predicate),
;; where predicate may either be a unary predicate symbol or a term containing
;; variables of term-pattern and also X, which stands for the term itself, and
;; initial-alist modifies how term-pattern may match.  For
;; example,
;;   (((logbitp n z)   ((z . (nfix y)))  booleanp)
;;    ((loghead m y)                     (unsigned-byte-p m x)))
(defun translate-subterms-types (alist wrld state-vars xsubst)
  (declare (xargs :mode :program))
  (b* (((when (atom alist)) (acl2::value-cmp nil))
       ((acl2::cmp subterm)
        (acl2::translate-cmp (caar alist) t t t 'try-gl-hint wrld state-vars))
       ((acl2::cmp initial-alist)
        (translate-term-alist (if (eql 3 (len (car alist)))
                                  (cadar alist)
                                nil)
                              wrld state-vars))
       ((acl2::cmp type-term)
        (acl2::translate-cmp (if (eql 3 (len (car alist)))
                                 (caddar alist)
                                (cadar alist))
                            t t t 'try-gl-hint wrld state-vars))
       (final-type (if xsubst
                       (if (symbolp type-term)
                           (list type-term subterm)
                         (let ((vars (acl2::term-vars type-term)))
                           (acl2::substitute-into-term
                            type-term (cons (cons 'x subterm)
                                            (pairlis$ vars vars)))))
                     type-term))
       ((acl2::cmp rest)
        (translate-subterms-types (cdr alist) wrld state-vars xsubst)))
    (acl2::value-cmp (cons (list subterm initial-alist final-type) rest))))


(defun collect-substitutions (terms pattern subst)
  (b* (((when (atom terms)) nil)
       ((mv ?ok alist) (acl2::simple-one-way-unify pattern (car terms) nil))
       (- (and (not ok) (er hard? 'collect-substitutions
                            "Unexpected: terms should all match pattern")))
       (subst-term (acl2::substitute-into-term subst alist)))
    (cons subst-term
          (collect-substitutions (cdr terms) pattern subst))))
    

;; Translate-subterms-types normalizes these to 3-tuples (adds the alist if it
;; doesn't exist).
(defun collect-subterm-types (clause subterms-types)
  ;; Collects (1) a list of subterms of the clause, and (2) a list of hyps to add
  ;; to the clause.
  (b* (((when (atom subterms-types)) (mv nil nil))
       ((list term-pattern initial-alist type-term) (car subterms-types))
       (subterms (acl2::find-matches-list term-pattern clause initial-alist))
       (types (collect-substitutions subterms term-pattern type-term))
       ((mv rest-terms rest-types)
        (collect-subterm-types clause (cdr subterms-types))))
    (mv (append subterms rest-terms)
        (append types rest-types))))


(defevaluator add-hyps-ev add-hyps-ev-lst 
  ((if a b c) (not a) (acl2::use-these-hints x) (equal x y)))

(acl2::def-join-thms add-hyps-ev)

(defun my-dumb-negate-lit-lst (x)
  (declare (xargs :guard (pseudo-term-listp x)))
  (if (atom x)
      nil
    (cons (acl2::dumb-negate-lit (car x))
          (my-dumb-negate-lit-lst (cdr X)))))

(defun try-gl-add-hyps-cp (clause hints)
  ;; hints are (hyps computed-hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (and (true-listp hints)
                     (pseudo-term-listp (car hints))))
        (list clause))
       (hyps (car hints))
       (new-clause1 (append (my-dumb-negate-lit-lst hyps) clause))
       (new-clause2 (cons (conjoin hyps) clause))
       (new-clause1 (if (consp (cdr hints))
                        (cons `(not (acl2::use-these-hints ',(cadr hints)))
                              new-clause1)
                      new-clause1)))
    (list new-clause1 new-clause2)))

(defthm ev-of-dumb-negate-lit
  (implies (pseudo-termp x)
           (iff (add-hyps-ev (acl2::dumb-negate-lit x) a)
                (not (add-hyps-ev x a))))
  :hints(("Goal" :in-theory (enable acl2::dumb-negate-lit))))

(defthm ev-disjoin-dumb-negate-lit-lst
  (implies (pseudo-term-listp lst)
           (iff (add-hyps-ev (disjoin (my-dumb-negate-lit-lst lst)) a)
                (not (add-hyps-ev (conjoin lst) a)))))

(defthm try-gl-add-hyps-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (add-hyps-ev (conjoin-clauses
                              (try-gl-add-hyps-cp clause hints))
                             a))
           (add-hyps-ev (disjoin clause) a))
  :rule-classes :clause-processor)

;; Looks for a pattern matching the (previously negated) literal in the
;; type-gens alist.  Returns the var and a term to create a g-bindings entry.
(defun type-gen-lit (x type-gens state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (atom type-gens)) nil)
       (pat (caar type-gens))
       (alist (cadar type-gens))
       ((mv ok subst) (acl2::simple-one-way-unify pat x alist))
       ((unless ok)
        (type-gen-lit x (cdr type-gens) state))
       (var (cdr (assoc 'x subst)))
       ((unless (symbolp var))
        (type-gen-lit x (cdr type-gens) state))
       (gen (caddar type-gens))
       ((mv err val)
        (acl2::magic-ev
         (acl2::substitute-into-term gen subst) nil state t t))
       ((when err)
        (cw "error: ~x0~%" err)
        (type-gen-lit x (cdr type-gens) state)))
    (list var val)))

(defun type-gen-collect-bindings (clause type-gens state)
  (declare (xargs :mode :program :stobjs state))
  ;; Returns (mv bindings hyp-lits non-hyp-lits)
  (b* (((when (atom clause)) (mv nil nil nil))
       (lit (car clause))
       (nlit (acl2::dumb-negate-lit lit))
       (binding (type-gen-lit nlit type-gens state))
       ((mv rest-bindings rest-hyps rest-non)
        (type-gen-collect-bindings (cdr clause) type-gens state))
       ((unless binding)
        (mv rest-bindings rest-hyps (cons lit rest-non))))
    (mv (cons binding rest-bindings)
        (cons lit rest-hyps)
        rest-non)))


(mutual-recursion
 (defun subtermp (a x)
   (declare (xargs :guard t))
   (cond ((atom x) (equal a x))
         ((quotep x) (equal a x))
         (t (or (equal a x)
                (subtermp-aux a (cdr x))))))
 (defun subtermp-aux (a x)
   (declare (xargs :guard t))
   (if (atom x)
       nil
       (or (subtermp a (car x))
           (subtermp-aux a (cdr x))))))

;; Removes literals that don't contain any occurrences of vars.
(defun filter-nonhyp-lits (lits vars)
  (if (atom lits)
      nil
    (if (intersectp-eq (acl2::term-vars (car lits)) vars)
        (cons (car lits)
              (filter-nonhyp-lits (cdr lits) vars))
      (filter-nonhyp-lits (cdr lits) vars))))

(defun any-subtermp (subterms term)
  (if (atom subterms)
      nil
    (or (subtermp (car subterms) term)
        (any-subtermp (cdr subterms) term))))

(defun filter-bad-subterms (clause forbidden-subterms)
  (if (atom clause)
      nil
    (if (any-subtermp forbidden-subterms (car clause))
        (filter-bad-subterms (cdr clause) forbidden-subterms)
      (cons (car clause)
            (filter-bad-subterms (cdr clause) forbidden-subterms)))))

(defun group-lits-cp-rec (clause groups)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (true-list-listp groups))))
  (if (atom groups)
      nil
    (cons (disjoin (intersection-equal (car groups) clause))
          (group-lits-cp-rec clause (cdr groups)))))

(defthm disjoin-of-intersection
  (implies (not (add-hyps-ev (disjoin clause) a))
           (not (add-hyps-ev (disjoin (intersection-equal x clause)) a)))
  :hints(("Goal" :in-theory (enable member-equal intersection-equal))))

(defthm group-list-cp-rec-correct
  (implies (not (add-hyps-ev (disjoin clause) a))
           (not (add-hyps-ev (disjoin (group-lits-cp-rec clause groups)) a))))


(defun group-lits-cp (clause groups)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (true-list-listp groups)
      (list (group-lits-cp-rec clause groups))
    (list clause)))

(defthm group-lits-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (add-hyps-ev (conjoin-clauses (group-lits-cp clause groups))
                             a))
           (add-hyps-ev (disjoin clause) a))
  :rule-classes :clause-processor)

(defun run-let-abstraction-cp (clause)
  `(:clause-processor (acl2::let-abstraction-cp
                       clause
                       ',(let ((subs (acl2::collect-multi-occ-subterms-list clause)))
                           (pairlis$ subs
                                     (make-n-vars (len subs) 'y 0
                                                  (acl2::term-vars-list clause)))))))


(defun maybe-print-clause-fn (print pr-name message clause state)
  (declare (xargs :mode :program :stobjs state))
  (and (or (eq print :all)
           (member :all print)
           (member pr-name print))
       (cw message (acl2::prettyify-clause clause t (w state)))))

(defmacro maybe-print-clause (pr-name message)
  `(maybe-print-clause-fn print ,pr-name ,message clause state))

(defun gl-auto-hint-step2 (clause g-bindings print state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((gl-clause-proc (latest-gl-clause-proc))
       (- (maybe-print-clause :final-clause "using GL on clause: ~x0~%"))
       (config (make-glcp-config))
       (cov-hints (glcp-coverage-hints nil nil nil nil))
       (hyp (car clause))
       (concl (cadr clause))
       (vars (strip-cars g-bindings))
       (all-vars (acl2::term-vars-list (list hyp concl)))
       (missing-vars (remove-duplicates-eq (set-difference-eq all-vars vars)))
       (g-bindings (add-var-bindings missing-vars g-bindings))
       (untr-concl (untranslate concl nil (w state)))
       (call `(,gl-clause-proc
               clause '(,g-bindings nil ,(dumb-negate-lit hyp) nil ,concl ,untr-concl ,config)
               state)))
    (glcp-combine-hints call cov-hints nil nil nil)))


(defun gl-auto-hint-fn (clause type-gens bad-subterms print state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((- (maybe-print-clause :before-filtering "before filtering: ~x0~%"))
       (clause (filter-bad-subterms clause bad-subterms))
       ((mv bindings hyp-lits nonhyp-lits)
        (type-gen-collect-bindings clause type-gens state))
       (bindings (fast-alist-free (hons-shrink-alist bindings nil)))
       ((mv g-bindings & &) (uniquify-shape-spec bindings 0 0))
       (vars (strip-cars g-bindings))
       (concl-lits (filter-nonhyp-lits nonhyp-lits vars)))
    `(:computed-hint-replacement
      ((run-let-abstraction-cp clause)
       (gl-auto-hint-step2 clause ',g-bindings ',print state))
      :clause-processor (group-lits-cp clause ',(list (append hyp-lits (butlast concl-lits 1))
                                                      (last concl-lits))))))





(defun get-fixup-alist (clause fixups)
  (declare (xargs :mode :program))
  (b* (((when (atom fixups)) nil)
       ((list term-pattern initial-alist res-term) (car fixups))
       (subterms (remove-duplicates-equal
                  (acl2::find-matches-list term-pattern clause initial-alist)))
       (results (collect-substitutions subterms term-pattern res-term)))
    (append (pairlis$ subterms results)
            (get-fixup-alist clause (cdr fixups)))))

;; hints is (new-clause new-hints implies-hints)
(defun clause-casesplit-cp (clause hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (and (true-listp hints)
                     (pseudo-term-listp (car hints))))
        (list clause))
       ((list new-clause new-hints implies-hints) hints))
    (list (cons `(not (acl2::use-these-hints ',new-hints)) new-clause)
          (list* `(not (acl2::use-these-hints ',implies-hints))
                 (acl2::dumb-negate-lit (disjoin new-clause))
                 clause))))

(defthm clause-casesplit-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (add-hyps-ev
                 (conjoin-clauses (clause-casesplit-cp clause hints))
                 a))
           (add-hyps-ev (disjoin clause) a))
  :rule-classes :clause-processor)


    
(defun try-gl-hint-fn (clause stablep fixups subterms-types type-gens
                              bad-subterms print state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((unless stablep) nil)
       (- (maybe-print-clause :original-clause "original clause: ~x0~%"))

       ;; translate all the terms in the various arguments
       (state-vars (acl2::default-state-vars t))
       ((mv err bad-subterms)
        (translate-term-list bad-subterms (w state) state-vars))
       ((when err) (cw "error in ~x0: ~@1~%" err bad-subterms))
       ((mv err subterms-types)
        (translate-subterms-types subterms-types (w state) state-vars t))
       ((when err) (cw "error in ~x0: ~@1~%" err subterms-types))
       (type-gens (append type-gens *default-symobj-generators*))
       ((mv err type-gens)
        (translate-subterms-types type-gens (w state) state-vars nil))
       ((when err) (cw "error in ~x0: ~@1~%" err type-gens))
       ((mv err fixups)
        (translate-subterms-types fixups (w state) state-vars t))
       ((when err) (cw "error in ~x0: ~@1~%" err fixups))


       ;; fix up the clause with the fixups
       (fixup-subst (get-fixup-alist clause fixups))
       (fixup-clause (if fixup-subst
                         (acl2::replace-subterms-list clause fixup-subst)
                       clause))

       (- (and fixup-subst
               (maybe-print-clause :fixed-up-clause "fixed-up clause: ~x0~%")))

       ;; collect the subterms that we'll generalize away and their type hyps
       ((mv subterms type-hyps)
        (collect-subterm-types fixup-clause subterms-types))
       (subterms (remove-duplicates-equal subterms))
       (type-hyps (remove-duplicates-equal type-hyps))
       (clause-vars (acl2::term-vars-list fixup-clause))
       (fresh-vars (make-n-vars (len subterms) 'x 0 clause-vars))
       (add-hyps-hint
        `(:computed-hint-replacement
          ((acl2::use-these-hints-hint clause))
          :clause-processor
          (try-gl-add-hyps-cp
           clause '(,type-hyps
                    ((progn$
                      (let ((print ',print))
                        (maybe-print-clause :before-generalization
                                            "before generalization: ~x0~%"))
                      (cw "Variable mapping: ~x0~%"
                          ',(pairlis$ fresh-vars (pairlis$ subterms nil)))
                      '(:computed-hint-replacement
                        ((gl-auto-hint-fn clause ',type-gens ',bad-subterms
                                          ',print state))
                        :clause-processor
                        (acl2::simple-generalize-cp
                         clause ',(pairlis$ subterms fresh-vars))))))))))
    (if fixup-subst
        `(:computed-hint-replacement
          ((acl2::use-these-hints-hint clause))
          :clause-processor
          (clause-casesplit-cp
           clause '(,fixup-clause
                    (',add-hyps-hint)
                    nil)))
      add-hyps-hint)))


(defmacro try-gl (&key fixes subterms-types type-gens bad-subterms
                       print)
  `(try-gl-hint-fn
    clause stable-under-simplificationp
    ',fixes ',subterms-types ',type-gens ',bad-subterms ',print state))


;; (include-book "gl")

;; (include-book "ihs/logops-definitions" :dir :system)


;; (local #!acl2 (in-theory (disable logbit loghead logxor b-xor unsigned-byte-p logior)))

;; (defthm test2
;;   #!ACL2
;;   (implies (and (unsigned-byte-p 10 a)
;;                 (integerp b))
;;            (equal (logior (logbit 3 (logxor a (loghead 8 b)))
;;                           (logbit 3 (logxor a (loghead 8 b))))
;;                   (b-xor (logbit 3 a)
;;                          (logbit 3 (loghead 8 b)))))
;;   :hints ((try-gl :subterms-types
;;                   #!acl2 (((loghead n b) (unsigned-byte-p n x))))))
      
       
       
       
           
