; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/bst-defs")
(include-book "internal/heap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define setp (x)
  :returns (yes/no booleanp)
  :parents (treeset)
  :short "Recognizer for @(see treeset)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (and (treep x)
       (bstp x)
       (heapp x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t setp)))

(defrule setp-type-prescription
  (booleanp (setp x))
  :rule-classes ((:type-prescription :typed-term (setp x))))

(defruled setp-compound-recognizer
  (if (setp set)
      (or (consp set)
          (equal set nil))
    (not (equal set nil)))
  :rule-classes :compound-recognizer
  :enable setp)

(add-to-ruleset break-abstraction '(setp-compound-recognizer))

(defruled treep-when-setp-forward-chaining
  (implies (setp set)
           (treep set))
  :rule-classes :forward-chaining
  :enable setp)

(add-to-ruleset break-abstraction '(treep-when-setp-forward-chaining))

(defruled bstp-when-setp-forward-chaining
  (implies (setp set)
           (bstp set))
  :rule-classes :forward-chaining
  :enable setp)

(add-to-ruleset break-abstraction '(bstp-when-setp-forward-chaining))

(defruled heapp-when-setp-forward-chaining
  (implies (setp set)
           (heapp set))
  :rule-classes :forward-chaining
  :enable setp)

(add-to-ruleset break-abstraction '(heapp-when-setp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;

(defruled setp-of-tree->left
  (implies (setp tree)
           (setp (tree->left tree)))
  :enable setp)

(add-to-ruleset break-abstraction '(setp-of-tree->left))

(defruled setp-of-tree->right
  (implies (setp tree)
           (setp (tree->right tree)))
  :enable setp)

(add-to-ruleset break-abstraction '(setp-of-tree->right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (set setp)
  :parents (treeset)
  :short "The empty @(see treeset)."
  nil
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t empty) (:e empty)))

(add-to-ruleset break-abstraction '((:t empty)))

(defruled treep-of-empty
  (treep (empty))
  :enable ((:e empty)))

(add-to-ruleset break-abstraction '(treep-of-empty))

(defruled bstp-of-empty
  (bstp (empty))
  :enable ((:e empty)))

(add-to-ruleset break-abstraction '(bstp-of-empty))

(defruled heapp-of-empty
  (heapp (empty))
  :enable ((:e empty)))

(add-to-ruleset break-abstraction '(heapp-of-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fix ((set setp))
  :returns (set$ setp)
  :parents (treeset)
  :short "Fixer for @(see treeset)s."
  (mbe :logic (if (setp set)
                  set
                (empty))
       :exec (the list set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t fix)))

(defruled fix-type-prescription
  (or (consp (fix set))
      (equal (fix set) nil))
  :rule-classes :type-prescription
  :enable (fix
           setp
           empty))

(add-to-ruleset break-abstraction '(fix-type-prescription))

(defrule fix-when-setp
  (implies (setp set)
           (equal (fix set)
                  set))
  :enable fix)

(defruled fix-when-not-setp
  (implies (not (setp set))
           (equal (fix set)
                  (empty)))
  :enable fix)

(defrule fix-when-not-setp-cheap
  (implies (not (setp set))
           (equal (fix set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-setp)

(defruled treep-of-fix
  (treep (fix set))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(treep-of-fix))

(defruled bstp-of-fix
  (bstp (fix set))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(bstp-of-fix))

(defruled heapp-of-fix
  (heapp (fix set))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(heapp-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x setp)
   (y setp))
  :returns (yes/no booleanp)
  :parents (treeset)
  :short "Equivalence up to @(tsee fix)."
  (equal (fix x)
         (fix y))
  :inline t

  ///
  (defequiv equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t equiv)))

(defrule equiv-type-prescription
  (booleanp (equiv x y))
  :rule-classes ((:type-prescription :typed-term (equiv x y))))

(defruled equiv-when-tree-equiv-refinement
  (implies (tree-equiv tree0 tree1)
           (equiv tree0 tree1))
  :rule-classes :refinement
  :enable (equiv
           tree-equiv
           setp
           fix
           empty))

(add-to-ruleset break-abstraction '(equiv-when-tree-equiv-refinement))

(defrule fix-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (fix set0)
                  (fix set1)))
  :rule-classes :congruence
  :enable equiv)

(defrule fix-under-equiv
  (equiv (fix set)
         set)
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((set setp))
  :returns (yes/no booleanp)
  :parents (treeset)
  :short "Check if a @(see treeset) is empty."
  (tree-empty-p (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t emptyp)))

(defrule emptyp-type-prescription
  (booleanp (emptyp set))
  :rule-classes ((:type-prescription :typed-term (emptyp set))))

(defruled emptyp-compound-recognizer
  (implies (not (emptyp set))
           (not (equal set nil)))
  :rule-classes :compound-recognizer
  :enable emptyp)

(add-to-ruleset break-abstraction '(emptyp-compound-recognizer))

(defrule emptyp-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (emptyp set0)
                  (emptyp set1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable empty)

(defruled fix-when-emptyp
  (implies (emptyp set)
           (equal (fix set)
                  (empty)))
  :enable (emptyp
           fix
           tree-empty-p
           setp
           empty))

(defrule fix-when-emptyp-cheap
  (implies (emptyp set)
           (equal (fix set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fix-when-emptyp)

(defrule setp-when-not-emptyp-forward-chaining
  (implies (not (emptyp set))
           (setp set))
  :rule-classes :forward-chaining
  :enable (emptyp
           setp
           empty))

;; TODO: Should this also be a regular rewrite rule?
(defrule emptyp-when-not-setp-forward-chaining
  (implies (not (setp set))
           (emptyp set))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((set setp))
  :guard (not (emptyp set))
  :parents (treeset)
  :short "Get an element of the nonempty @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, the logical result is @('nil').")
   (xdoc::p
     "From a user perspective, this should be viewed as an arbitrary element of
      the set. For a description of which element this actually provides, see
      @(tsee tree->head)."))
  (tagged-element->elem (tree->head (fix set)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp
                                           emptyp))))

;;;;;;;;;;;;;;;;;;;;

(defrule head-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (head set0)
                  (head set1)))
  :rule-classes :congruence
  :enable head)

(defruled head-when-emptyp
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :enable (head
           emptyp
           irr-tagged-element))

(defrule head-when-emptyp-cheap
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable head-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variants matching the equality primitives

(define set-all-acl2-numberp ((set setp))
  :returns (yes/no booleanp)
  (tree-all-acl2-numberp (fix set))
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-acl2-numberp)))

(defrule set-all-acl2-numberp-type-prescription
  (booleanp (set-all-acl2-numberp set))
  :rule-classes ((:type-prescription :typed-term (set-all-acl2-numberp set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-all-symbolp ((set setp))
  :returns (yes/no booleanp)
  (tree-all-symbolp (fix set))
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-symbolp)))

(defrule set-all-symbolp-type-prescription
  (booleanp (set-all-symbolp set))
  :rule-classes ((:type-prescription :typed-term (set-all-symbolp set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-all-eqlablep ((set setp))
  :returns (yes/no booleanp)
  (tree-all-eqlablep (fix set))
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-eqlablep)))

(defrule set-all-eqlablep-type-prescription
  (booleanp (set-all-eqlablep set))
  :rule-classes ((:type-prescription :typed-term (set-all-eqlablep set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: more efficient implementations (check setp and contents
;; simultaneously).

(define acl2-number-setp (x)
  :parents (setp)
  :short "Refinement of @(tsee setp) to sets whose elements are recognized by
          @(tsee acl2-numberp)."
  (and (setp x)
       (set-all-acl2-numberp x))
  :enabled t)

(define symbol-setp (x)
  :parents (setp)
  :short "Refinement of @(tsee setp) to sets whose elements are recognized by
          @(tsee symbolp)."
  (and (setp x)
       (set-all-symbolp x))
  :enabled t)

(define eqlable-setp (x)
  :parents (setp)
  :short "Refinement of @(tsee setp) to sets whose elements are recognized by
          @(tsee eqlablep)."
  (and (setp x)
       (set-all-eqlablep x))
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy set-extra-rules
  '(fix-when-not-setp
    fix-when-emptyp
    head-when-emptyp
    ))
