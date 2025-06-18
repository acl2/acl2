; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/osets/computed-hints" :dir :system)

(include-book "in-defs")
(include-book "set-defs")
(include-book "subset-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "in"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pick-a-point
  :parents (set)
  :short "Pick-a-point automation for @(tsee subset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "We borrow the @(see set::std/osets) machinery for pick-a-point style
       proofs. See @(see set::pick-a-point-subset-strategy)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following is adapted from std/osets/membership.lisp.

(encapsulate ()
  (encapsulate
    (((set-predicate *) => *))
    (local (defun set-predicate (x) x)))

  (define all-predicate
    ((set setp))
    (or (emptyp set)
        (and (set-predicate (head set))
             (all-predicate (left set))
             (all-predicate (right set))))
    :hints (("Goal" :in-theory (enable o< o-finp))))

  (encapsulate
    (((all-hyps) => *)
     ((all-set) => *))

    (local (defun all-hyps () nil))
    (local (defun all-set () nil))

    (defruled membership-constraint
      (implies (all-hyps)
               (implies (in arbitrary-element (all-set))
                        (set-predicate arbitrary-element)))))

  (local
    (define find-not ((set setp))
      (cond ((emptyp set)
             nil)
            ((not (set-predicate (head set)))
             set)
            (t (or (find-not (left set))
                   (find-not (right set)))))
      :hints (("Goal" :in-theory (enable o< o-finp)))))

  (defrulel find-not-type-prescription
    (or (consp (find-not set))
        (equal (find-not set)
               nil))
    :rule-classes :type-prescription
    :induct t
    :enable find-not)

  (defrulel in-of-head-of-find-not-when-not-emptyp-of-find-not
    (implies (not (emptyp (find-not set)))
             (in (head (find-not set))
                 set))
    :induct t
    :enable find-not)

  (defruledl emptyp-of-find-not-when-find-not
    (implies (find-not set)
             (not (emptyp (find-not set))))
    :induct t
    :enable find-not)

  (defruledl emptyp-of-find-not-left-when-emptyp-of-find-not
    (implies (emptyp (find-not set))
             (emptyp (find-not (left set))))
    :induct t
    :enable find-not)

  (defruledl emptyp-of-find-not-right-when-emptyp-of-find-not
    (implies (emptyp (find-not set))
             (emptyp (find-not (right set))))
    :induct t
    :enable (find-not
             emptyp-of-find-not-when-find-not))

  (defruledl all-predicate-when-emptyp-of-find-not
    (implies (emptyp (find-not set))
             (all-predicate set))
    :induct t
    :enable (all-predicate
             find-not
             emptyp-of-find-not-left-when-emptyp-of-find-not
             emptyp-of-find-not-right-when-emptyp-of-find-not))

  (defruledl emptyp-of-find-not-when-set-predicate-of-head-of-find-not
    (implies (set-predicate (head (find-not set)))
             (emptyp (find-not set)))
    :induct t
    :enable find-not)

  (defruledl all-predicate-when-set-predicate-of-head-of-find-not
    (implies (set-predicate (head (find-not set)))
             (all-predicate set))
    :enable (emptyp-of-find-not-when-set-predicate-of-head-of-find-not
             all-predicate-when-emptyp-of-find-not))

  (defrulel lemma-find-not-is-a-witness
    (implies (not (all-predicate set))
             (and (in (head (find-not set)) set)
                  (not (set-predicate (head (find-not set))))))
    :use all-predicate-when-emptyp-of-find-not
    :enable emptyp-of-find-not-when-set-predicate-of-head-of-find-not)

  (defruled all-by-membership
    (implies (all-hyps)
             (all-predicate (all-set)))
    :use (:instance membership-constraint
                    (arbitrary-element (head (find-not (all-set)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset-trigger
  ((x setp)
   (y setp))
  (subset x y))

(defruled pick-a-point
  (implies (and (syntaxp (computed-hints::rewriting-goal-lit mfc state))
                (syntaxp (computed-hints::rewriting-conc-lit `(subset ,x ,y) mfc state)))
           (equal (subset x y)
                  (subset-trigger x y)))
  :enable subset-trigger)

(computed-hints::automate-instantiation
  :new-hint-name pick-a-point-subset-hint
  :generic-theorem all-by-membership
  :generic-predicate set-predicate
  :generic-hyps all-hyps
  :generic-collection all-set
  :generic-collection-predicate all-predicate
  :actual-collection-predicate subset
  :actual-trigger subset-trigger
  :predicate-rewrite (((set-predicate ?x ?y) (in ?x ?y)))
  :tagging-theorem pick-a-point)

(defrule pick-a-point-subset-constraint-helper
  (implies (syntaxp (equal set-for-all-reduction 'set-for-all-reduction))
           (equal (subset set-for-all-reduction rhs)
                  (cond ((emptyp set-for-all-reduction) t)
                        ((in (head set-for-all-reduction) rhs)
                         (and (subset (left set-for-all-reduction) rhs)
                              (subset (right set-for-all-reduction) rhs)))
                        (t nil))))
  :enable subset)
