; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "rulep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Theories.
;;
;; A theory represents a collection of rules.  The rules are stored in a search
;; structure so that, given a term, we can quickly look up the rules which
;; might apply to the term.
;;
;; The "public" functions for interfacing with theories are the following:
;;
;;    rw.theoryp         : any --> bool
;;    rw.theory-atblp    : thy * atbl --> bool
;;    rw.theory-env-okp  : thy * thms --> bool
;;
;;    rw.theory-insert      : rule * thy --> thy
;;    rw.theory-delete      : rule * thy --> thy
;;    rw.theory-insert-list : rulelist * thy --> thy
;;    rw.theory-delete-list : rulelist * thy --> thy
;;    rw.theory-union       : thy * thy --> thy
;;    rw.theory-difference  : thy * thy --> thy
;;
;;    rw.theory-allrules : thy --> rulelist
;;    rw.theory-lookup   : term * thy --> map of symbols to rulelists
;;
;;
;; Theory construction is straightforward.  The empty theory is simply nil, and
;; subsequent theories are built using the insert function.  Note that insert
;; is smart enough not to add the same rule multiple times.  We also provide a
;; delete function since "disabling" rules is often useful, and wrappers for
;; inserting or deleting entire lists or theories of rules.
;;
;; The allrules function retrieves a list of all the rules in the theory.  This
;; is a slow operation (we have to cons together all the rules) and should not
;; normally be used by functions.  But it's useful when proving theorems about
;; the theory, since it lets you say things like, "suppose all of the rules in
;; the theory are theorems..."
;;
;; Finally, the most important operation is lookup, which takes a term we wish
;; to rewrite as its input, and quickly throws away a lot of rules that can't
;; possibly apply to this term.  The rules are returned in a map based upon
;; their type, e.g., the map will look like:
;;
;;   ((inside . [list of potentially applicable inside-out rules])
;;    (outside . [list of potentially applicable outside-in rules])
;;    (... maybe other kinds of rules, in the future ...)
;;    )
;;
;; It's my understanding that ACL2 uses a raw-lisp properly list lookup on the
;; leading function symbol to achieve a similar effect.  In both systems, the
;; rules returned by lookup don't necessarily match with the term you gave it,
;; but you know for sure that other rules don't apply.  So, it's just a very
;; cheap way to avoid trying to pattern-match your term against every single
;; rule in the theory.  It's also implemented efficiently; it returns a pointer
;; into the internals of the theory structure, so it doesn't have to do any
;; consing.
;;
;; Future work.
;;
;; Orderedp recognizers.  Theories are intended to be ordered search trees.
;; That is, the leading symbol for each node is intended to be greater than all
;; the nodes on its left, and less than all the nodes on its right.  We tried
;; to implement a fast orderedness check and prove it equivalent to a simpler
;; version, but the equivalence proof was difficult so we have skipped that for
;; now.
;;
;; Showing order-preservingness.  We have not shown that the insert and delete
;; functions are order preserving, although this is obviously our intent.  If
;; the tree is not ordered correctly, our lookup function may "miss" rules.  It
;; would be nice to show that lookup retrieves all the rules with a compatible
;; leading function symbol, but this is not crucial to using theories so we
;; have skipped it for now.
;;
;; Rebalancing.  We have not implemented a rebalancing function, and our insert
;; operation does nothing to maintain balance.  If the tree becoems severely
;; unbalanced, our lookup operation may suffer a performance penalty.  But
;; again this has not become a problem yet, so we have skipped it for now.
;;
;; Inspection.  It would be nice to have functions to inspect theories and
;; print out summaries of what the theory contains.

(defthmd alternate-trichotomy-of-symbol-<
  ;; BOZO consider moving this to arithmetic
  (implies (and (not (symbol-< a b))
                (not (equal a b))
                (force (symbolp a))
                (force (symbolp b)))
           (equal (symbol-< b a)
                  t)))

(defthmd all-equalp-removal
  ;; BOZO consider moving this to utilities.
  ;; This might break some things, but it might also be really good.
  (equal (all-equalp a x)
         (equal (list-fix x) (repeat a (len x))))
  :hints(("Goal" :induct (cdr-induction x))))

(local (in-theory (enable alternate-trichotomy-of-symbol-<
                          all-equalp-removal)))




(definlined rw.leading-symbol (x)
  ;; We are going to group rules by "which function they are about".  We say
  ;; the leading symbol for a function term is its outermost function symbol,
  ;; e.g., "f" in (f ... (g ...) ...).
  (declare (xargs :guard (logic.termp x)))
  (if (logic.functionp x)
      (logic.function-name x)
    nil))

(defprojection :list (rw.leading-symbol-list x)
               :element (rw.leading-symbol x)
               :guard (logic.term-listp x)
               :nil-preservingp t)

(defthm forcing-symbolp-of-rw.leading-symbol
  (implies (force (logic.termp x))
           (equal (symbolp (rw.leading-symbol x))
                  t))
  :hints(("Goal" :in-theory (e/d (rw.leading-symbol)
                                 (forcing-lookup-of-logic.function-name)))))

(defthm forcing-symbol-listp-of-rw.leading-symbol-list
  (implies (force (logic.term-listp x))
           (equal (symbol-listp (rw.leading-symbol-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defmap
  :map (rw.typed-rulemapp x)
  :key (symbolp x)
  :val (rw.rule-listp x)
  :key-list (symbol-listp x)
  :val-list (rw.rule-list-listp x)
  :val-of-nil t)





(defund rw.rule-list-consistent-leading-symbolsp (name rules)
  (declare (xargs :guard (rw.rule-listp rules)))
  (if (consp rules)
      (and (equal name (rw.leading-symbol (rw.rule->lhs (car rules))))
           (rw.rule-list-consistent-leading-symbolsp name (cdr rules)))
    t))

(defthm rw.rule-list-consistent-leading-symbolsp-removal
  (equal (rw.rule-list-consistent-leading-symbolsp name rules)
         (all-equalp name (rw.leading-symbol-list (rw.rule-list-lhses rules))))
  :hints(("Goal" :in-theory (enable rw.rule-list-consistent-leading-symbolsp))))

(defund rw.rulemap-consistent-leading-symbolsp (name rulemap)
  (declare (xargs :guard (rw.typed-rulemapp rulemap)))
  (if (consp rulemap)
      (and (rw.rule-list-consistent-leading-symbolsp name (cdr (car rulemap)))
           (rw.rulemap-consistent-leading-symbolsp name (cdr rulemap)))
    t))

(defthm rw.rulemap-consistent-leading-symbolsp-removal
  (equal (rw.rulemap-consistent-leading-symbolsp name rulemap)
         (all-equalp name
                     (rw.leading-symbol-list
                      (rw.rule-list-lhses
                       (simple-flatten
                        (range rulemap))))))
  :hints(("Goal" :in-theory (e/d (rw.rulemap-consistent-leading-symbolsp)
                                 (all-equalp-removal)))))


(defsection rw.theroyp

  (defund rw.theoryp (x)
    ;; A theory is a search tree for rules.  Each theory is either empty,
    ;; represented by nil, or is an aggregate of:
    ;;
    ;;  - Rules, a list of rules which agree on the leading symbol of their lhses,
    ;;  - Name, the "leading symbol" that these rules agree upon,
    ;;  - Left, recursively a rule finder for "smaller" rules, and
    ;;  - Right, recursively a rule finder for "larger" rules.
    ;;
    ;; All the rules whose leading symbol is "f" are thrown into the same bucket,
    ;; which then has to be linearly searched.
    (declare (xargs :guard t))
    (or (equal x nil)
        (and (tuplep 4 x)
             (let ((name     (first x))
                   (left     (second x))
                   (right    (third x))
                   (rulemap (fourth x)))
               (and (symbolp name)
                    (rw.theoryp left)
                    (rw.theoryp right)
                    (rw.typed-rulemapp rulemap)
                    (rw.rulemap-consistent-leading-symbolsp name rulemap))))))

  (definlined rw.theory->name (x)
    (declare (xargs :guard (rw.theoryp x)))
    (first x))

  (definlined rw.theory->left (x)
    (declare (xargs :guard (rw.theoryp x)))
    (second x))

  (definlined rw.theory->right (x)
    (declare (xargs :guard (rw.theoryp x)))
    (third x))

  (definlined rw.theory->rulemap (x)
    (declare (xargs :guard (rw.theoryp x)))
    (fourth x))

  (definlined rw.theory (name left right rulemap)
    (declare (xargs :guard (and (symbolp name)
                                (rw.theoryp left)
                                (rw.theoryp right)
                                (rw.typed-rulemapp rulemap)
                                (rw.rulemap-consistent-leading-symbolsp name rulemap))))
    (list name left right rulemap))

  (defthm booleanp-of-rw.theoryp
    (equal (booleanp (rw.theoryp x))
           t)
    :hints(("Goal" :in-theory (enable rw.theoryp))))

  (defthm consp-of-rw.theory
    (equal (consp (rw.theory name left right rulemap))
           t)
    :hints(("Goal" :in-theory (enable rw.theory))))

  (defthm rw.theory-under-iff
    (iff (rw.theory name left right rulemap)
         t)
    :hints(("Goal" :in-theory (enable rw.theory))))

  (defthm forcing-rw.theoryp-of-rw.theory
    (implies (force (and (symbolp name)
                         (rw.theoryp left)
                         (rw.theoryp right)
                         (rw.typed-rulemapp rulemap)
                         (rw.rulemap-consistent-leading-symbolsp name rulemap)))
             (equal (rw.theoryp (rw.theory name left right rulemap))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory rw.theoryp rw.theory->name))))

  (defthm rw.theory->name-of-rw.theory
    (equal (rw.theory->name (rw.theory name left right rulemap))
           name)
    :hints(("Goal" :in-theory (enable rw.theory rw.theory->name))))

  (defthm rw.theory->left-of-rw.theory
    (equal (rw.theory->left (rw.theory name left right rulemap))
           left)
    :hints(("Goal" :in-theory (enable rw.theory rw.theory->left))))

  (defthm rw.theory->right-of-rw.theory
    (equal (rw.theory->right (rw.theory name left right rulemap))
           right)
    :hints(("Goal" :in-theory (enable rw.theory rw.theory->right))))

  (defthm rw.theory->rulemap-of-rw.theory
    (equal (rw.theory->rulemap (rw.theory name left right rulemap))
           rulemap)
    :hints(("Goal" :in-theory (enable rw.theory rw.theory->rulemap))))

  (defthm forcing-symbolp-of-rw.theory->name
    (implies (force (rw.theoryp x))
             (equal (symbolp (rw.theory->name x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theoryp rw.theory->name))))

  (defthm forcing-theoryp-of-rw.theory->left
    (implies (force (rw.theoryp x))
             (equal (rw.theoryp (rw.theory->left x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theoryp rw.theory->left))))

  (defthm forcing-theoryp-of-rw.theory->right
    (implies (force (rw.theoryp x))
             (equal (rw.theoryp (rw.theory->right x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theoryp rw.theory->right))))

  (defthm forcing-rw.typed-rulemapp-of-rw.theory->rulemap
    (implies (force (rw.theoryp x))
             (equal (rw.typed-rulemapp (rw.theory->rulemap x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theoryp rw.theory->rulemap))))

  (defthm forcing-leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.theory->rulemap
    (implies (force (rw.theoryp x))
             (equal (rw.leading-symbol-list (rw.rule-list-lhses (simple-flatten (range (rw.theory->rulemap x)))))
                    (repeat (rw.theory->name x) (len (simple-flatten (range (rw.theory->rulemap x)))))))
    :hints(("Goal" :in-theory (enable rw.theoryp rw.theory->rulemap rw.theory->name))))

  (defthm rank-of-rw.theory->left
    (implies (consp x)
             (< (rank (rw.theory->left x))
                (rank x)))
    :hints(("Goal" :in-theory (enable rw.theory->left))))

  (defthm rank-of-rw.theory->right
    (implies (consp x)
             (< (rank (rw.theory->right x))
                (rank x)))
    :hints(("Goal" :in-theory (enable rw.theory->right))))

  (defthm rw.theory->left-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory->left x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.theory->left))))

  (defthm rw.theory->right-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory->right x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.theory->right)))))



(defsection rw.theory-atblp

  (defund rw.theory-atblp (x atbl)
    ;; Check that every rule throughout the finder is a rule-atblp.
    (declare (xargs :guard (and (rw.theoryp x)
                                (logic.arity-tablep atbl))))
    (if (consp x)
        (let ((left  (rw.theory->left x))
              (right (rw.theory->right x))
              (rulemap (rw.theory->rulemap x)))
          (and (rw.rule-list-list-atblp (range rulemap) atbl)
               (rw.theory-atblp left atbl)
               (rw.theory-atblp right atbl)))
      t))

  (defthm booleanp-of-rw.theory-atblp
    (equal (booleanp (rw.theory-atblp x atbl))
           t)
    :hints(("Goal" :in-theory (enable rw.theory-atblp))))

  (defthm rw.theory-atblp-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory-atblp x atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-atblp))))

  (defthm forcing-theory-atblp-of-rw.theory->left
    (implies (force (rw.theory-atblp x atbl))
             (equal (rw.theory-atblp (rw.theory->left x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-atblp rw.theory->left))))

  (defthm forcing-theory-atblp-of-rw.theory->right
    (implies (force (rw.theory-atblp x atbl))
             (equal (rw.theory-atblp (rw.theory->right x) atbl)
                    t))
    :hints(("Goal" :in-theory (e/d (rw.theory-atblp rw.theory->right)
                                   (forcing-theory-atblp-of-rw.theory->left)))))

  (defthm forcing-rw.rule-list-list-atblp-of-of-range-of-rw.theory->rulemap
    (implies (force (rw.theory-atblp x atbl))
             (equal (rw.rule-list-list-atblp (range (rw.theory->rulemap x)) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-atblp rw.theory->rulemap))))

  (defthm forcing-rw.theory-atblp-of-rw.theory
    (implies (force (and (rw.theory-atblp left atbl)
                         (rw.theory-atblp right atbl)
                         (rw.rule-list-list-atblp (range rules) atbl)))
             (equal (rw.theory-atblp (rw.theory name left right rules) atbl)
                    t))
    :hints(("Goal" :in-theory (e/d (rw.theory-atblp)
                                   ((:executable-counterpart acl2::force)))))))




(defsection rw.theory-env-okp

  (defund rw.theory-env-okp (x thms)
    ;; Check that every rule throughout the finder is a rule-atblp.
    (declare (xargs :guard (and (rw.theoryp x)
                                (logic.formula-listp thms))))
    (if (consp x)
        (let ((left    (rw.theory->left x))
              (right   (rw.theory->right x))
              (rulemap (rw.theory->rulemap x)))
          (and (rw.rule-list-list-env-okp (range rulemap) thms)
               (rw.theory-env-okp left thms)
               (rw.theory-env-okp right thms)))
      t))

  (defthm booleanp-of-rw.theory-env-okp
    (equal (booleanp (rw.theory-env-okp x thms))
           t)
    :hints(("Goal" :in-theory (enable rw.theory-env-okp))))

  (defthm rw.theory-env-okp-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory-env-okp x thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-env-okp))))

  (defthm forcing-theory-env-okp-of-rw.theory->left
    (implies (force (rw.theory-env-okp x thms))
             (equal (rw.theory-env-okp (rw.theory->left x) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-env-okp rw.theory->left))))

  (defthm forcing-theory-env-okp-of-rw.theory->right
    (implies (force (rw.theory-env-okp x thms))
             (equal (rw.theory-env-okp (rw.theory->right x) thms)
                    t))
    :hints(("Goal" :in-theory (e/d (rw.theory-env-okp rw.theory->right)
                                   (forcing-theory-env-okp-of-rw.theory->left)))))

  (defthm forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory->rulemap
    (implies (force (rw.theory-env-okp x thms))
             (equal (rw.rule-list-list-env-okp (range (rw.theory->rulemap x)) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-env-okp rw.theory->rulemap))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory
    (implies (force (and (rw.theory-env-okp left thms)
                         (rw.theory-env-okp right thms)
                         (rw.rule-list-list-env-okp (range rules) thms)))
             (equal (rw.theory-env-okp (rw.theory name left right rules) thms)
                    t))
    :hints(("Goal" :in-theory (e/d (rw.theory-env-okp)
                                   ((:executable-counterpart acl2::force)))))))





;; BOZO misplaced.
(defthm rw.rule-list-atblp-of-simple-flatten
  (equal (rw.rule-list-atblp (simple-flatten x) atbl)
         (rw.rule-list-list-atblp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.rule-list-env-okp-of-simple-flatten
  (equal (rw.rule-list-env-okp (simple-flatten x) thms)
         (rw.rule-list-list-env-okp x thms))
  :hints(("Goal" :induct (cdr-induction x))))


(defsection rw.theory-allrules

  (defund rw.fast-theory-all-rules (x acc)
    (declare (xargs :guard (and (rw.theoryp x)
                                (true-listp acc))
                    :verify-guards nil))
    (if (consp x)
        (let ((local-rules (fast-simple-flatten-of-range$ (rw.theory->rulemap x) nil)))
          (rw.fast-theory-all-rules (rw.theory->left x)
                                    (rw.fast-theory-all-rules (rw.theory->right x)
                                                              (revappend local-rules acc))))
      acc))

  (defun rw.slow-theory-all-rules (x)
    (declare (xargs :guard (rw.theoryp x)))
    (if (consp x)
        (app (rw.slow-theory-all-rules (rw.theory->left x))
             (app (rw.slow-theory-all-rules (rw.theory->right x))
                  (simple-flatten (range (rw.theory->rulemap x)))))
      nil))

  (definlined rw.theory-allrules (x)
    ;; Make a list of all the rules in the finder.
    (declare (xargs :guard (rw.theoryp x)
                    :verify-guards nil))
    (rw.fast-theory-all-rules x nil))

  (defthm true-listp-of-rw.fast-theory-all-rules
    (implies (force (true-listp acc))
             (equal (true-listp (rw.fast-theory-all-rules x acc))
                    t))
    :hints(("Goal" :in-theory (enable rw.fast-theory-all-rules))))

  (verify-guards rw.fast-theory-all-rules)
  (verify-guards rw.theory-allrules)

  (defthmd lemma-for-definition-of-rw.theory-allrules
    (implies (force (true-listp acc))
             (equal (rw.fast-theory-all-rules x acc)
                    (app (rw.slow-theory-all-rules x) acc)))
    :hints(("Goal"
            :in-theory (enable rw.fast-theory-all-rules
                               rw.slow-theory-all-rules)
            :induct (rw.fast-theory-all-rules x acc))))

  (defthmd definition-of-rw.theory-allrules
    (equal (rw.theory-allrules x)
           (if (consp x)
               (app (rw.theory-allrules (rw.theory->left x))
                    (app (rw.theory-allrules (rw.theory->right x))
                         (simple-flatten (range (rw.theory->rulemap x)))))
             nil))
    :rule-classes :definition
    :hints(("Goal" :in-theory (enable rw.theory-allrules
                                      rw.slow-theory-all-rules
                                      lemma-for-definition-of-rw.theory-allrules
                                      ))))

  (defthm induction-for-rw.theory-allrules
    t
    :rule-classes ((:induction :corollary t
                               :pattern (rw.theory-allrules x)
                               :scheme (rw.slow-theory-all-rules x))))

  (defthm rw.fast-theory-all-rules-elim
    (implies (force (true-listp acc))
             (equal (rw.fast-theory-all-rules x acc)
                    (app (rw.theory-allrules x) acc)))
    :hints(("Goal" :in-theory (enable rw.theory-allrules
                                      lemma-for-definition-of-rw.theory-allrules))))

  (ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.theory-allrules))))

  (defthm forcing-true-listp-of-rw.theory-allrules
    (implies (force (rw.theoryp x))
             (equal (true-listp (rw.theory-allrules x))
                    t))
    :hints(("Goal" :in-theory (enable definition-of-rw.theory-allrules))))

  (defthm forcing-rw.rule-listp-of-rw.theory-allrules
    (implies (force (rw.theoryp x))
             (equal (rw.rule-listp (rw.theory-allrules x))
                    t))
    :hints(("Goal" :in-theory (enable definition-of-rw.theory-allrules))))

  (defthm forcing-rw.rule-listp-atblp-of-rw.theory-allrules
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl)))
             (equal (rw.rule-list-atblp (rw.theory-allrules x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable definition-of-rw.theory-allrules))))

  (defthm forcing-rw.rule-listp-env-okp-of-rw.theory-allrules
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms)))
             (equal (rw.rule-list-env-okp (rw.theory-allrules x) thms)
                    t))
    :hints(("Goal" :in-theory (enable definition-of-rw.theory-allrules)))))




(defsection rw.theory-lookup

  (defund rw.theory-lookup-aux (goal x)
    (declare (xargs :guard (and (symbolp goal)
                                (rw.theoryp x))))
    (if (consp x)
        (let ((this (rw.theory->name x)))
          (cond ((symbol-< goal this)
                 (rw.theory-lookup-aux goal (rw.theory->left x)))
                ((symbol-< this goal)
                 (rw.theory-lookup-aux goal (rw.theory->right x)))
                (t
                 (rw.theory->rulemap x))))
      nil))

  (definlined rw.theory-lookup (term x)
    ;; List all the rules that might apply to term.
    ;;
    ;; This is the main operation of a rule finder.  We cache the term's leading
    ;; symbol, then perform a binary search and return the rules attached to this
    ;; node.  This should be quite fast, since the search is tail recursive and
    ;; we do not need to do any consing.
    (declare (xargs :guard (and (logic.termp term)
                                (rw.theoryp x))))
    (rw.theory-lookup-aux (rw.leading-symbol term) x))

  (defthm rw.theory-lookup-aux-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory-lookup-aux goal x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux))))

  (defthm forcing-rw.typed-rulemapp-of-rw.theory-lookup-aux
    (implies (force (rw.theoryp x))
             (equal (rw.typed-rulemapp (rw.theory-lookup-aux goal x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux))))

  (defthm forcing-rw.rule-list-list-atblp-of-range-of-rw.theory-lookup-aux
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl)))
             (equal (rw.rule-list-list-atblp (range (rw.theory-lookup-aux goal x)) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux))))

  (defthm forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory-lookup-aux
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms)))
             (equal (rw.rule-list-list-env-okp (range (rw.theory-lookup-aux goal x)) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux))))

  (defthm rw.theory-lookup-aux-of-rw.theory
    (equal (rw.theory-lookup-aux goal (rw.theory name left right rules))
           (cond ((symbol-< goal name)
                  (rw.theory-lookup-aux goal left))
                 ((symbol-< name goal)
                  (rw.theory-lookup-aux goal right))
                 (t
                  rules)))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux))))

  (defthm forcing-rw.typed-rulemapp-of-rw.theory-lookup
    (implies (force (rw.theoryp x))
             (equal (rw.typed-rulemapp (rw.theory-lookup term x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup))))

  (defthm forcing-rw.rule-list-listp-atblp-of-range-of-rw.theory-lookup
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl)))
             (equal (rw.rule-list-list-atblp (range (rw.theory-lookup term x)) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup))))

  (defthm forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory-lookup
    (implies (and (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms)))
             (equal (rw.rule-list-list-env-okp (range (rw.theory-lookup term x)) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup)))))



(defsection rw.extend-typed-rulemap

  (defund rw.extend-typed-rulemap (rule rulemap)
    (declare (xargs :guard (and (rw.rulep rule)
                                (rw.typed-rulemapp rulemap))))
    (if (consp rulemap)
        (let* ((entry (car rulemap))
               (entry-type (car entry))
               (entry-rules (cdr entry)))
          (if (equal (rw.rule->type rule) entry-type)
              ;; This is the proper row for this rule.  Add it only if it does
              ;; not already exist.
              (if (memberp rule entry-rules)
                  rulemap
                (cons (cons entry-type (cons rule entry-rules))
                      (cdr rulemap)))
            ;; Not the proper row yet.  Keep looking.
            (cons entry (rw.extend-typed-rulemap rule (cdr rulemap)))))
      ;; Out of rows.  Create a new row for this type.
      (list (cons (rw.rule->type rule)
                  (list rule)))))

  (defthm forcing-rw.typed-rulemapp-of-rw.extend-typed-rulemap
    (implies (force (and (rw.rulep rule)
                         (rw.typed-rulemapp rulemap)))
             (equal (rw.typed-rulemapp (rw.extend-typed-rulemap rule rulemap))
                    t))
    :hints(("Goal" :in-theory (enable rw.extend-typed-rulemap))))

  (defthm forcing-rw.rule-list-list-atblp-of-range-of-rw.extend-typed-rulemap
    (implies (force (and (rw.rulep rule)
                         (rw.typed-rulemapp rulemap)
                         (rw.rule-atblp rule atbl)
                         (rw.rule-list-list-atblp (range rulemap) atbl)))
             (equal (rw.rule-list-list-atblp (range (rw.extend-typed-rulemap rule rulemap)) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.extend-typed-rulemap))))

  (defthm forcing-rw.rule-list-list-env-okp-of-range-of-rw.extend-typed-rulemap
    (implies (force (and (rw.rulep rule)
                         (rw.typed-rulemapp rulemap)
                         (rw.rule-env-okp rule thms)
                         (rw.rule-list-list-env-okp (range rulemap) thms)))
             (equal (rw.rule-list-list-env-okp (range (rw.extend-typed-rulemap rule rulemap)) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.extend-typed-rulemap))))

  (defthm lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap
    (implies (all-equalp (rw.leading-symbol (rw.rule->lhs rule))
                         (rw.leading-symbol-list
                          (rw.rule-list-lhses
                           (simple-flatten
                            (range rulemap)))))
             (all-equalp (rw.leading-symbol (rw.rule->lhs rule))
                         (rw.leading-symbol-list
                          (rw.rule-list-lhses
                           (simple-flatten
                            (range (rw.extend-typed-rulemap rule rulemap)))))))
    :rule-classes nil
    :hints(("Goal" :in-theory (e/d (rw.extend-typed-rulemap)
                                   (all-equalp-removal)))))

  (defthm forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap
    (implies (force (all-equalp (rw.leading-symbol (rw.rule->lhs rule))
                                (rw.leading-symbol-list
                                 (rw.rule-list-lhses
                                  (simple-flatten
                                   (range rulemap))))))
             (equal (rw.leading-symbol-list
                     (rw.rule-list-lhses
                      (simple-flatten
                       (range (rw.extend-typed-rulemap rule rulemap)))))
                    (repeat (rw.leading-symbol (rw.rule->lhs rule))
                            (len (simple-flatten
                                  (range (rw.extend-typed-rulemap rule rulemap)))))))
    :hints(("Goal"
            :use ((:instance lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-rw.extend-typed-rulemap)))))

  (defthm rw.extend-typed-rulemap-of-nil
    (equal (rw.extend-typed-rulemap rule nil)
           (list (cons (rw.rule->type rule)
                       (list rule))))
    :hints(("Goal" :in-theory (enable rw.extend-typed-rulemap)))))



(defsection rw.theory-insert

  (defund rw.theory-insert-aux (goal rule x)
    (declare (xargs :guard (and (rw.rulep rule)
                                (equal goal (rw.leading-symbol (rw.rule->lhs rule)))
                                (rw.theoryp x))
                    :verify-guards nil))
    (if (consp x)
        (let ((name    (rw.theory->name x))
              (left    (rw.theory->left x))
              (right   (rw.theory->right x))
              (rulemap (rw.theory->rulemap x)))
          (cond ((symbol-< goal name)
                 (rw.theory name (rw.theory-insert-aux goal rule left) right rulemap))
                ((symbol-< name goal)
                 (rw.theory name left (rw.theory-insert-aux goal rule right) rulemap))
                (t
                 (rw.theory name left right (rw.extend-typed-rulemap rule rulemap)))))
      (rw.theory goal nil nil (rw.extend-typed-rulemap rule nil))))

  (definlined rw.theory-insert (rule x)
    ;; Add a rule to the finder.
    (declare (xargs :guard (and (rw.rulep rule)
                                (rw.theoryp x))
                    :verify-guards nil))
    (rw.theory-insert-aux (rw.leading-symbol (rw.rule->lhs rule)) rule x))

  (defthm rw.theory-insert-aux-under-iff
    (iff (rw.theory-insert-aux goal rule x)
         t)
    :hints(("Goal" :in-theory (enable rw.theory-insert-aux))))

  (defthm lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux
    (implies (and (rw.rulep rule)
                  (rw.theoryp x)
                  (equal goal (rw.leading-symbol (rw.rule->lhs rule))))
             (and (rw.theoryp (rw.theory-insert-aux goal rule x))
                  (equal (rw.theory->name (rw.theory-insert-aux goal rule x))
                         (if (consp x)
                             (rw.theory->name x)
                           goal))))
    :rule-classes nil
    :hints(("Goal"
            :in-theory (enable rw.theory-insert-aux)
            :induct (rw.theory-insert-aux goal rule x))))

  (defthm forcing-rw.theoryp-of-rw.theory-insert-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theoryp (rw.theory-insert-aux goal rule x))
                    t))
    :hints(("Goal" :use ((:instance lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux)))))

  (defthm forcing-rw.theory-name-of-rw.theory-insert-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory->name (rw.theory-insert-aux goal rule x))
                    (if (consp x)
                        (rw.theory->name x)
                      goal)))
    :hints(("Goal" :use ((:instance lemma-for-forcing-rw.theoryp-of-rw.theory-insert-aux)))))

  (verify-guards rw.theory-insert-aux)
  (verify-guards rw.theory-insert)

  (defthm forcing-rw.theory-atblp-of-rw.theory-insert-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-atblp rule atbl))
                  (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-atblp (rw.theory-insert-aux goal rule x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert-aux))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-insert-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-env-okp rule thms))
                  (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-env-okp (rw.theory-insert-aux goal rule x) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert-aux))))


  (defthmd lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
    (implies (and (symbolp get-goal)
                  (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal put-goal (rw.leading-symbol (rw.rule->lhs rule))))
                  (not (equal put-goal get-goal)))
             (equal (rw.theory-lookup-aux get-goal (rw.theory-insert-aux put-goal rule x))
                    (rw.theory-lookup-aux get-goal x)))
    :hints(("Goal"
            :in-theory (enable rw.theory-lookup-aux
                               rw.theory-insert-aux)
            :induct (rw.theory-insert-aux put-goal rule x))))

  (defthmd lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-lookup-aux goal (rw.theory-insert-aux goal rule x))
                    (rw.extend-typed-rulemap rule (rw.theory-lookup-aux goal x))))
    :hints(("Goal"
            :in-theory (enable rw.theory-lookup-aux
                               rw.theory-insert-aux)
            :induct (rw.theory-insert-aux goal rule x))))

  (defthm forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux
    (implies (and (force (symbolp get-goal))
                  (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal put-goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-lookup-aux get-goal (rw.theory-insert-aux put-goal rule x))
                    (if (equal put-goal get-goal)
                        (rw.extend-typed-rulemap rule (rw.theory-lookup-aux get-goal x))
                      (rw.theory-lookup-aux get-goal x))))
    :hints(("Goal"
            :use ((:instance lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux (goal get-goal))
                  (:instance lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-insert-aux)))))


  (defthm forcing-rw.theoryp-of-rw.theory-insert
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x)))
             (equal (rw.theoryp (rw.theory-insert rule x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert))))

  (defthm forcing-rw.theory-atblp-of-rw.theory-insert
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-atblp rule atbl))
                  (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl)))
             (equal (rw.theory-atblp (rw.theory-insert rule x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-insert
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-env-okp rule thms))
                  (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms)))
             (equal (rw.theory-env-okp (rw.theory-insert rule x) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert))))

  (defthm forcing-rw.theory-lookup-of-rw.theory-insert
    (implies (and (force (logic.termp term))
                  (force (rw.rulep rule))
                  (force (rw.theoryp x)))
             (equal (rw.theory-lookup term (rw.theory-insert rule x))
                    (if (equal (rw.leading-symbol term)
                               (rw.leading-symbol (rw.rule->lhs rule)))
                        (rw.extend-typed-rulemap rule (rw.theory-lookup term x))
                      (rw.theory-lookup term x))))
    :hints(("Goal" :in-theory (enable rw.theory-insert rw.theory-lookup))))

  (defthm forcing-subsetp-of-rw.theory-lookup-aux-and-rw.theory-allrules
    (implies (force (rw.theoryp x))
             (equal (subsetp (simple-flatten (range (rw.theory-lookup-aux goal x)))
                             (rw.theory-allrules x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup-aux
                                      definition-of-rw.theory-allrules))))

  (defthm forcing-subsetp-of-rw.theory-lookup-and-rw.theory-allrules
    (implies (force (rw.theoryp x))
             (equal (subsetp (simple-flatten (range (rw.theory-lookup goal x)))
                             (rw.theory-allrules x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-lookup)))))




(defthm forcing-rw.typed-rulemapp-of-remove-all-from-ranges
  (implies (force (rw.typed-rulemapp x))
           (equal (rw.typed-rulemapp (remove-all-from-ranges a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.rule-list-list-atblp-of-range-of-remove-all-from-ranges
  (implies (force (and (rw.rulep rule)
                       (rw.typed-rulemapp rulemap)
                       (rw.rule-list-list-atblp (range rulemap) atbl)))
           (equal (rw.rule-list-list-atblp (range (remove-all-from-ranges rule rulemap)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction rulemap))))

(defthm forcing-rw.rule-list-env-okp-of-range-of-remove-all-from-ranges
  (implies (force (and (rw.rulep rule)
                       (rw.typed-rulemapp rulemap)
                       (rw.rule-list-list-env-okp (range rulemap) thms)))
           (equal (rw.rule-list-list-env-okp (range (remove-all-from-ranges rule rulemap)) thms)
                  t))
  :hints(("Goal" :induct (cdr-induction rulemap))))



(defthm lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges
  (implies (all-equalp name (rw.leading-symbol-list
                             (rw.rule-list-lhses
                              (simple-flatten
                               (range rulemap)))))
           (all-equalp name (rw.leading-symbol-list
                             (rw.rule-list-lhses
                              (simple-flatten
                               (range
                                (remove-all-from-ranges rule rulemap)))))))
  :rule-classes nil
  :hints(("Goal"
          :induct (cdr-induction rulemap)
          :in-theory (disable all-equalp-removal))))

(defthm forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges
  (implies (all-equalp (rw.leading-symbol (rw.rule->lhs rule))
                       (rw.leading-symbol-list
                        (rw.rule-list-lhses
                         (simple-flatten
                          (range rulemap)))))
           (equal (rw.leading-symbol-list
                   (rw.rule-list-lhses
                    (simple-flatten
                     (range
                      (remove-all-from-ranges rule rulemap)))))
                  (repeat (rw.leading-symbol (rw.rule->lhs rule))
                          (len (simple-flatten
                                (range
                                 (remove-all-from-ranges rule rulemap)))))))
  :hints(("Goal"
          :use ((:instance lemma-for-forcing-rw.leading-symbol-list-of-rw.rule-list-lhses-of-simple-flatten-of-range-of-remove-all-from-ranges
                           (name (rw.leading-symbol (rw.rule->lhs rule))))))))



(defsection rw.theory-delete

  (defund rw.theory-delete-aux (goal rule x)
    (declare (xargs :guard (and (rw.rulep rule)
                                (equal goal (rw.leading-symbol (rw.rule->lhs rule)))
                                (rw.theoryp x))
                    :verify-guards nil))
    (if (consp x)
        (let ((name    (rw.theory->name x))
              (left    (rw.theory->left x))
              (right   (rw.theory->right x))
              (rulemap (rw.theory->rulemap x)))
          (cond ((symbol-< goal name)
                 (rw.theory name (rw.theory-delete-aux goal rule left) right rulemap))
                ((symbol-< name goal)
                 (rw.theory name left (rw.theory-delete-aux goal rule right) rulemap))
                (t
                 ;; We could remove the node entirely if we remove all its rules,
                 ;; but this seems easier.
                 (rw.theory name left right (remove-all-from-ranges rule rulemap)))))
      nil))

  (definlined rw.theory-delete (rule x)
    ;; Delete a rule from the finder.
    (declare (xargs :guard (and (rw.rulep rule)
                                (rw.theoryp x))
                    :verify-guards nil))
    (rw.theory-delete-aux (rw.leading-symbol (rw.rule->lhs rule)) rule x))

  (defthm rw.theory-delete-aux-when-not-consp
    (implies (not (consp x))
             (equal (rw.theory-delete-aux goal rule x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.theory-delete-aux))))

  (defthm lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux
    (implies (and (rw.rulep rule)
                  (rw.theoryp x)
                  (equal goal (rw.leading-symbol (rw.rule->lhs rule))))
             (and (rw.theoryp (rw.theory-delete-aux goal rule x))
                  (or (not (rw.theory-delete-aux goal rule x))
                      (equal (rw.theory->name (rw.theory-delete-aux goal rule x))
                             (rw.theory->name x)))))
    :rule-classes nil
    :hints(("Goal"
            :in-theory (enable rw.theory-delete-aux)
            :induct (rw.theory-delete-aux goal rule x))))

  (defthm forcing-rw.theoryp-of-rw.theory-delete-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theoryp (rw.theory-delete-aux goal rule x))
                    t))
    :hints(("Goal" :use ((:instance lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux)))))

  (defthm forcing-rw.theory-name-of-rw.theory-delete-aux
    (implies (and (rw.theory-delete-aux goal rule x)
                  (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory->name (rw.theory-delete-aux goal rule x))
                    (rw.theory->name x)))
    :hints(("Goal" :use ((:instance lemma-for-forcing-rw.theoryp-of-rw.theory-delete-aux)))))

  (verify-guards rw.theory-delete-aux)
  (verify-guards rw.theory-delete)

  (defthm forcing-rw.theory-atblp-of-rw.theory-delete-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-atblp rule atbl))
                  (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-atblp (rw.theory-delete-aux goal rule x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete-aux))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-delete-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-env-okp rule thms))
                  (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-env-okp (rw.theory-delete-aux goal rule x) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete-aux))))

  (defthmd lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
    (implies (and (symbolp get-goal)
                  (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal put-goal (rw.leading-symbol (rw.rule->lhs rule))))
                  (not (equal put-goal get-goal)))
             (equal (rw.theory-lookup-aux get-goal (rw.theory-delete-aux put-goal rule x))
                    (rw.theory-lookup-aux get-goal x)))
    :hints(("Goal"
            :in-theory (enable rw.theory-lookup-aux
                               rw.theory-delete-aux)
            :induct (rw.theory-delete-aux put-goal rule x)
            :do-not-induct t)))

  (defthmd lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-lookup-aux goal (rw.theory-delete-aux goal rule x))
                    (remove-all-from-ranges rule (rw.theory-lookup-aux goal x))))
    :hints(("Goal"
            :in-theory (enable rw.theory-lookup-aux
                               rw.theory-delete-aux)
            :induct (rw.theory-delete-aux goal rule x))))

  (defthm forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
    (implies (and (force (symbolp get-goal))
                  (force (rw.rulep rule))
                  (force (rw.theoryp x))
                  (force (equal put-goal (rw.leading-symbol (rw.rule->lhs rule)))))
             (equal (rw.theory-lookup-aux get-goal (rw.theory-delete-aux put-goal rule x))
                    (if (equal put-goal get-goal)
                        (remove-all-from-ranges rule (rw.theory-lookup-aux get-goal x))
                      (rw.theory-lookup-aux get-goal x))))
    :hints(("Goal" :in-theory (enable lemma-2-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux
                                      lemma-for-forcing-rw.theory-lookup-aux-of-rw.theory-delete-aux))))

  (defthm forcing-rw.theoryp-of-rw.theory-delete
    (implies (and (force (rw.rulep rule))
                  (force (rw.theoryp x)))
             (equal (rw.theoryp (rw.theory-delete rule x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete))))

  (defthm forcing-rw.theory-atblp-of-rw.theory-delete
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-atblp rule atbl))
                  (force (rw.theoryp x))
                  (force (rw.theory-atblp x atbl)))
             (equal (rw.theory-atblp (rw.theory-delete rule x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-delete
    (implies (and (force (rw.rulep rule))
                  (force (rw.rule-env-okp rule thms))
                  (force (rw.theoryp x))
                  (force (rw.theory-env-okp x thms)))
             (equal (rw.theory-env-okp (rw.theory-delete rule x) thms)
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete))))

  (defthm forcing-rw.theory-lookup-of-rw.theory-delete
    (implies (and (force (logic.termp term))
                  (force (rw.rulep rule))
                  (force (rw.theoryp x)))
             (equal (rw.theory-lookup term (rw.theory-delete rule x))
                    (if (equal (rw.leading-symbol term)
                               (rw.leading-symbol (rw.rule->lhs rule)))
                        (remove-all-from-ranges rule (rw.theory-lookup term x))
                      (rw.theory-lookup term x))))
    :hints(("Goal" :in-theory (enable rw.theory-delete rw.theory-lookup)))))




(defsection rw.theory-insert-list

  (defund rw.theory-insert-list (rules x)
    (declare (xargs :guard (and (rw.rule-listp rules)
                                (rw.theoryp x))))
    (if (consp rules)
        (rw.theory-insert-list (cdr rules)
                               (rw.theory-insert (car rules) x))
      x))

  (defthm rw.theory-insert-list-when-not-consp
    (implies (not (consp rules))
             (equal (rw.theory-insert-list rules theory)
                    theory))
    :hints(("Goal" :in-theory (enable rw.theory-insert-list))))

  (defthm rw.theory-insert-list-of-cons
    (equal (rw.theory-insert-list (cons rule rules) theory)
           (rw.theory-insert-list rules
                                  (rw.theory-insert rule theory)))
    :hints(("Goal" :in-theory (enable rw.theory-insert-list))))

  (defthm forcing-rw.theoryp-of-rw.theory-insert-list
    (implies (force (and (rw.rule-listp rules)
                         (rw.theoryp x)))
             (equal (rw.theoryp (rw.theory-insert-list rules x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-insert-list))))

  (defthm forcing-rw.theory-atblp-of-rw.theory-insert-list
    (implies (force (and (rw.theory-atblp theory atbl)
                         (rw.rule-list-atblp rules atbl)
                         (rw.theoryp theory)
                         (rw.rule-listp rules)))
             (equal (rw.theory-atblp (rw.theory-insert-list rules theory) atbl)
                    t))
    :hints(("Goal"
            :induct (rw.theory-insert-list rules theory)
            :in-theory (enable (:induction rw.theory-insert-list)))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-insert-list
    (implies (force (and (rw.theory-env-okp theory thms)
                         (rw.rule-list-env-okp rules thms)
                         (rw.theoryp theory)
                         (rw.rule-listp rules)))
             (equal (rw.theory-env-okp (rw.theory-insert-list rules theory) thms)
                    t))
    :hints(("Goal"
            :induct (rw.theory-insert-list rules theory)
            :in-theory (enable (:induction rw.theory-insert-list))))))




(defsection rw.theory-delete-list

  (defund rw.theory-delete-list (rules x)
    (declare (xargs :guard (and (rw.rule-listp rules)
                                (rw.theoryp x))))
    (if (consp rules)
        (rw.theory-delete-list (cdr rules)
                               (rw.theory-delete (car rules) x))
      x))

  (defthm rw.theory-delete-list-when-not-consp
    (implies (not (consp rules))
             (equal (rw.theory-delete-list rules theory)
                    theory))
    :hints(("Goal" :in-theory (enable rw.theory-delete-list))))

  (defthm rw.theory-delete-list-of-cons
    (equal (rw.theory-delete-list (cons rule rules) theory)
           (rw.theory-delete-list rules
                                  (rw.theory-delete rule theory)))
    :hints(("Goal" :in-theory (enable rw.theory-delete-list))))

  (defthm forcing-rw.theoryp-of-rw.theory-delete-list
    (implies (force (and (rw.rule-listp rules)
                         (rw.theoryp x)))
             (equal (rw.theoryp (rw.theory-delete-list rules x))
                    t))
    :hints(("Goal" :in-theory (enable rw.theory-delete-list))))

  (defthm forcing-rw.theory-atblp-of-rw.theory-delete-list
    (implies (force (and (rw.theory-atblp theory atbl)
                         (rw.rule-list-atblp rules atbl)
                         (rw.theoryp theory)
                         (rw.rule-listp rules)
                         ))
             (equal (rw.theory-atblp (rw.theory-delete-list rules theory) atbl)
                    t))
    :hints(("Goal"
            :induct (rw.theory-delete-list rules theory)
            :in-theory (enable (:induction rw.theory-delete-list)))))

  (defthm forcing-rw.theory-env-okp-of-rw.theory-delete-list
    (implies (force (and (rw.theory-env-okp theory thms)
                         (rw.rule-list-env-okp rules thms)
                         (rw.theoryp theory)
                         (rw.rule-listp rules)))
             (equal (rw.theory-env-okp (rw.theory-delete-list rules theory) thms)
                    t))
    :hints(("Goal"
            :induct (rw.theory-delete-list rules theory)
            :in-theory (enable (:induction rw.theory-delete-list))))))






;; Never used, I think

;; (definlined rw.theory-union (x y)
;;   (declare (xargs :guard (and (rw.theoryp x)
;;                               (rw.theoryp y))))
;;   (rw.theory-insert-list (rw.theory-allrules y) x))

;; (defthm forcing-rw.theoryp-of-rw.theory-union
;;   (implies (force (and (rw.theoryp x)
;;                        (rw.theoryp y)))
;;            (equal (rw.theoryp (rw.theory-union x y))
;;                   t))
;;   :hints(("Goal" :in-theory (enable rw.theory-union))))





;; (definlined rw.theory-difference (x y)
;;   (declare (xargs :guard (and (rw.theoryp x)
;;                               (rw.theoryp y))))
;;   (rw.theory-delete-list (rw.theory-allrules y) x))

;; (defthm forcing-rw.theoryp-of-rw.theory-difference
;;   (implies (force (and (rw.theoryp x)
;;                        (rw.theoryp y)))
;;            (equal (rw.theoryp (rw.theory-difference x y))
;;                   t))
;;   :hints(("Goal" :in-theory (enable rw.theory-difference))))




;; Hopefully not needed anymore.

;; (defthm rw.rule-list-atblp-of-lookup-when-rw.rule-list-atblp-of-simple-flatten-of-range
;;   (implies (rw.rule-list-atblp (simple-flatten (range rulemap)) atbl)
;;            (equal (rw.rule-list-atblp (cdr (lookup type rulemap)) atbl)
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction rulemap))))

;; (defthm rw.rule-list-env-okp-of-lookup-when-rw.rule-list-atblp-of-simple-flatten-of-range
;;   (implies (rw.rule-list-env-okp (simple-flatten (range rulemap)) thms)
;;            (equal (rw.rule-list-env-okp (cdr (lookup type rulemap)) thms)
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction rulemap))))






(deflist rw.theory-listp (x)
  (rw.theoryp x)
  :guard t
  :elementp-of-nil t)

(deflist rw.theory-list-atblp (x atbl)
  (rw.theory-atblp x atbl)
  :guard (and (rw.theory-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)

(deflist rw.theory-list-env-okp (x thms)
  (rw.theory-env-okp x thms)
  :guard (and (rw.theory-listp x)
              (logic.formula-listp thms))
  :elementp-of-nil t)

(defsection rw.theory-list-allrules

  (defund rw.fast-theory-list-all-rules (x acc)
    (declare (xargs :guard (and (rw.theory-listp x)
                                (true-listp acc))
                    :verify-guards nil))
    (if (consp x)
        (rw.fast-theory-all-rules (car x)
                                  (rw.fast-theory-list-all-rules (cdr x) acc))
      acc))

  (defund rw.slow-theory-list-all-rules (x)
    (declare (xargs :guard (rw.theory-listp x)))
    (if (consp x)
        (app (rw.theory-allrules (car x))
             (rw.slow-theory-list-all-rules (cdr x)))
      nil))

  (defund rw.theory-list-allrules (x)
    (declare (xargs :guard (rw.theory-listp x)
                    :verify-guards nil))
    (rw.fast-theory-list-all-rules x nil))

  (defthm true-listp-of-rw.fast-theory-list-all-rules
    (implies (force (true-listp acc))
             (equal (true-listp (rw.fast-theory-list-all-rules x acc))
                    t))
    :hints(("Goal" :in-theory (enable rw.fast-theory-list-all-rules))))

  (verify-guards rw.fast-theory-list-all-rules)
  (verify-guards rw.theory-list-allrules)

  (defthmd lemma-for-definition-of-rw.theory-list-allrules
    (implies (force (true-listp acc))
             (equal (rw.fast-theory-list-all-rules x acc)
                    (app (rw.slow-theory-list-all-rules x) acc)))
    :hints(("Goal"
            :in-theory (enable rw.fast-theory-list-all-rules
                               rw.slow-theory-list-all-rules)
            :induct (rw.fast-theory-list-all-rules x acc))))

  (defthmd definition-of-rw.theory-list-allrules
    (equal (rw.theory-list-allrules x)
           (if (consp x)
               (app (rw.theory-allrules (car x))
                    (rw.theory-list-allrules (cdr x)))
             nil))
    :rule-classes :definition
    :hints(("Goal" :in-theory (enable rw.theory-list-allrules
                                      rw.slow-theory-list-all-rules
                                      lemma-for-definition-of-rw.theory-list-allrules))))

  (defthm rw.fast-theory-list-all-rules-elim
    (implies (force (true-listp acc))
             (equal (rw.fast-theory-list-all-rules x acc)
                    (app (rw.theory-list-allrules x) acc)))
    :hints(("Goal" :in-theory (enable rw.theory-list-allrules
                                      lemma-for-definition-of-rw.theory-list-allrules))))

  (ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.theory-list-allrules))))

  (defthm forcing-true-listp-of-rw.theory-list-allrules
    (equal (true-listp (rw.theory-list-allrules x))
           t)
    :hints(("Goal"
            :in-theory (enable definition-of-rw.theory-list-allrules)
            :induct (cdr-induction x))))

  (defthm forcing-rw.rule-listp-of-rw.theory-list-allrules
    (implies (force (rw.theory-listp x))
             (equal (rw.rule-listp (rw.theory-list-allrules x))
                    t))
    :hints(("Goal"
            :in-theory (enable definition-of-rw.theory-list-allrules)
            :induct (cdr-induction x))))

  (defthm forcing-rw.rule-listp-atblp-of-rw.theory-list-allrules
    (implies (and (force (rw.theory-listp x))
                  (force (rw.theory-list-atblp x atbl)))
             (equal (rw.rule-list-atblp (rw.theory-list-allrules x) atbl)
                    t))
    :hints(("Goal"
            :in-theory (enable definition-of-rw.theory-list-allrules)
            :induct (cdr-induction x))))

  (defthm forcing-rw.rule-listp-env-okp-of-rw.theory-list-allrules
    (implies (and (force (rw.theory-listp x))
                  (force (rw.theory-list-env-okp x thms)))
             (equal (rw.rule-list-env-okp (rw.theory-list-allrules x) thms)
                    t))
    :hints(("Goal"
            :in-theory (enable definition-of-rw.theory-list-allrules)
            :induct (cdr-induction x)))))



(defmap :map (rw.theory-mapp x)
        :key (symbolp x)
        :val (rw.theoryp x)
        :key-list (symbol-listp x)
        :val-list (rw.theory-listp x))

(defthm rw.theory-mapp-of-clean-update
  (implies (force (and (rw.theory-mapp map)
                       (symbolp key)
                       (rw.theoryp val)))
           (equal (rw.theory-mapp (clean-update key val map))
                  t))
  :hints(("Goal"
          :induct (clean-update key val map)
          :in-theory (enable (:induction clean-update)))))



(defund rw.theory-list-atblp-of-range (x atbl)
  (declare (xargs :guard (and (rw.theory-mapp x)
                              (logic.arity-tablep atbl))))
  (if (consp x)
      (and (rw.theory-atblp (cdr (car x)) atbl)
           (rw.theory-list-atblp-of-range (cdr x) atbl))
    t))

(defthm rw.theory-list-atblp-of-range-removal
  (equal (rw.theory-list-atblp-of-range x atbl)
         (rw.theory-list-atblp (range x) atbl))
  :hints(("Goal" :in-theory (enable rw.theory-list-atblp-of-range))))


(defund rw.theory-list-env-okp-of-range (x thms)
  (declare (xargs :guard (and (rw.theory-mapp x)
                              (logic.formula-listp thms))))
  (if (consp x)
      (and (rw.theory-env-okp (cdr (car x)) thms)
           (rw.theory-list-env-okp-of-range (cdr x) thms))
    t))

(defthm rw.theory-list-env-okp-of-range-removal
  (equal (rw.theory-list-env-okp-of-range x thms)
         (rw.theory-list-env-okp (range x) thms))
  :hints(("Goal" :in-theory (enable rw.theory-list-env-okp-of-range))))








(defund rw.slow-rule-list-thms (x)
  (declare (xargs :guard (rw.rule-listp x)))
  (if (consp x)
      (app (rw.slow-rule-list-thms (cdr x))
           (list (clause.clause-formula (rw.rule-clause (car x)))))
    nil))

(defund rw.rule-list-thms (x acc)
  (declare (xargs :guard (and (rw.rule-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.rule-list-thms (cdr x)
                         (cons (clause.clause-formula (rw.rule-clause (car x)))
                               acc))
    acc))

(defthm true-listp-of-rw.rule-list-thms
  (implies (force (true-listp acc))
           (true-listp (rw.rule-list-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-thms))))

(defthm rw.rule-list-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.rule-list-thms x acc)
                  (app (rw.slow-rule-list-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-thms
                                    rw.slow-rule-list-thms))))

(defthm rw.slow-rule-list-thms-correct
  (equal (subsetp (rw.slow-rule-list-thms x) thms)
         (rw.rule-list-env-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-rule-list-thms
                           rw.rule-list-env-okp
                           rw.rule-env-okp)))))




(defund rw.slow-rule-list-list-thms (x)
  (declare (xargs :guard (rw.rule-list-listp x)))
  (if (consp x)
      (app (rw.slow-rule-list-list-thms (cdr x))
           (rw.slow-rule-list-thms (car x)))
    nil))

(defund rw.rule-list-list-thms (x acc)
  (declare (xargs :guard (and (rw.rule-list-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.rule-list-list-thms (cdr x)
                              (rw.rule-list-thms (car x) acc))
    acc))

(defthm true-listp-of-rw.rule-list-list-thms
  (implies (force (true-listp acc))
           (true-listp (rw.rule-list-list-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-list-thms))))

(defthm rw.rule-list-list-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.rule-list-list-thms x acc)
                  (app (rw.slow-rule-list-list-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-list-thms
                                    rw.slow-rule-list-list-thms))))

(defthm rw.slow-rule-list-list-thms-correct
  (equal (subsetp (rw.slow-rule-list-list-thms x) thms)
         (rw.rule-list-list-env-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-rule-list-list-thms
                           rw.rule-list-list-env-okp
                           rw.rule-list-env-okp)))))






(defund rw.slow-typed-rulemap-thms (x)
  (declare (xargs :guard (rw.typed-rulemapp x)))
  (if (consp x)
      (app (rw.slow-typed-rulemap-thms (cdr x))
           (rw.slow-rule-list-thms (cdr (car x))))
    nil))

(defund rw.typed-rulemap-thms (x acc)
  (declare (xargs :guard (and (rw.typed-rulemapp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.typed-rulemap-thms (cdr x)
                             (rw.rule-list-thms (cdr (car x)) acc))
    acc))

(defthm true-listp-of-rw.typed-rulemap-thms
  (implies (force (true-listp acc))
           (true-listp (rw.typed-rulemap-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.typed-rulemap-thms))))

(defthm rw.typed-rulemap-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.typed-rulemap-thms x acc)
                  (app (rw.slow-typed-rulemap-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.typed-rulemap-thms
                                    rw.slow-typed-rulemap-thms))))

(defthm rw.slow-typed-rulemap-thms-correct
  (equal (subsetp (rw.slow-typed-rulemap-thms x) thms)
         (rw.rule-list-list-env-okp (range x) thms))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-typed-rulemap-thms
                           rw.rule-list-list-env-okp)))))




(defund rw.slow-theory-thms (x)
  (declare (xargs :guard (rw.theoryp x)))
  (if (consp x)
      (let* ((res (rw.slow-typed-rulemap-thms (rw.theory->rulemap x)))
             (res (app (rw.slow-theory-thms (rw.theory->left x)) res))
             (res (app (rw.slow-theory-thms (rw.theory->right x)) res)))
        res)
    nil))

(defund rw.theory-thms (x acc)
  (declare (xargs :guard (and (rw.theoryp x)
                              (true-listp acc))
                  :verify-guards nil))
  (if (consp x)
      (let* ((acc (rw.typed-rulemap-thms (rw.theory->rulemap x) acc))
             (acc (rw.theory-thms (rw.theory->left x) acc)))
        (rw.theory-thms (rw.theory->right x) acc))
    acc))

(defthm true-listp-of-rw.theory-thms
  (implies (force (true-listp acc))
           (true-listp (rw.theory-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.theory-thms))))

(verify-guards rw.theory-thms)

(defthm rw.theory-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.theory-thms x acc)
                  (app (rw.slow-theory-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.theory-thms
                                    rw.slow-theory-thms))))

(defthm rw.slow-theory-thms-correct
  (equal (subsetp (rw.slow-theory-thms x) thms)
         (rw.theory-env-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-theory-thms
                           rw.theory-env-okp)
                          (forcing-theory-env-okp-of-rw.theory->left
                           forcing-theory-env-okp-of-rw.theory->right
                           forcing-rw.rule-list-list-env-okp-of-range-of-rw.theory->rulemap)))))




(defund rw.slow-theory-list-thms (x)
  (declare (xargs :guard (rw.theory-listp x)))
  (if (consp x)
      (app (rw.slow-theory-list-thms (cdr x))
           (rw.slow-theory-thms (car x)))
    nil))

(defund rw.theory-list-thms (x acc)
  (declare (xargs :guard (and (rw.theory-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.theory-list-thms (cdr x)
                           (rw.theory-thms (car x) acc))
    acc))

(defthm true-listp-of-rw.theory-list-thms
  (implies (force (true-listp acc))
           (true-listp (rw.theory-list-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.theory-list-thms))))

(defthm rw.theory-list-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.theory-list-thms x acc)
                  (app (rw.slow-theory-list-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.theory-list-thms
                                    rw.slow-theory-list-thms))))

(defthm rw.slow-theory-list-thms-correct
  (equal (subsetp (rw.slow-theory-list-thms x) thms)
         (rw.theory-list-env-okp x thms))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-theory-list-thms)))))




(defund rw.slow-theory-map-thms (x)
  (declare (xargs :guard (rw.theory-mapp x)))
  (if (consp x)
      (app (rw.slow-theory-map-thms (cdr x))
           (rw.slow-theory-thms (cdr (car x))))
    nil))

(defund rw.theory-map-thms (x acc)
  (declare (xargs :guard (and (rw.theory-mapp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.theory-map-thms (cdr x)
                          (rw.theory-thms (cdr (car x)) acc))
    acc))

(defthm true-listp-of-rw.theory-map-thms
  (implies (force (true-listp acc))
           (true-listp (rw.theory-map-thms x acc)))
  :hints(("Goal" :in-theory (enable rw.theory-map-thms))))

(defthm rw.theory-map-thms-removal
  (implies (force (true-listp acc))
           (equal (rw.theory-map-thms x acc)
                  (app (rw.slow-theory-map-thms x)
                       acc)))
  :hints(("Goal" :in-theory (enable rw.theory-map-thms
                                    rw.slow-theory-map-thms))))

(defthm rw.slow-theory-map-thms-correct
  (equal (subsetp (rw.slow-theory-map-thms x) thms)
         (rw.theory-list-env-okp (range x) thms))
  :hints(("Goal" :in-theory (e/d (rw.slow-theory-map-thms)))))
