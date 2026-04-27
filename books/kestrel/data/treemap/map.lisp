; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

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

(define mapp (x)
  :returns (yes/no booleanp)
  :parents (treemap)
  :short "Recognizer for @(see treemap)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (and (treep x)
       (bstp x)
       (heapp x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t mapp)))

(defrule mapp-type-prescription
  (booleanp (mapp x))
  :rule-classes ((:type-prescription :typed-term (mapp x))))

(defruled mapp-compound-recognizer
  (if (mapp map)
      (or (consp map)
          (equal map nil))
    (not (equal map nil)))
  :rule-classes :compound-recognizer
  :enable mapp)

(add-to-ruleset break-abstraction '(mapp-compound-recognizer))

(defruled treep-when-mapp-forward-chaining
  (implies (mapp map)
           (treep map))
  :rule-classes :forward-chaining
  :enable mapp)

(add-to-ruleset break-abstraction '(treep-when-mapp-forward-chaining))

(defruled bstp-when-mapp-forward-chaining
  (implies (mapp map)
           (bstp map))
  :rule-classes :forward-chaining
  :enable mapp)

(add-to-ruleset break-abstraction '(bstp-when-mapp-forward-chaining))

(defruled heapp-when-mapp-forward-chaining
  (implies (mapp map)
           (heapp map))
  :rule-classes :forward-chaining
  :enable mapp)

(add-to-ruleset break-abstraction '(heapp-when-mapp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;

(defruled mapp-of-tree->left
  (implies (mapp tree)
           (mapp (tree->left tree)))
  :enable mapp)

(add-to-ruleset break-abstraction '(mapp-of-tree->left))

(defruled mapp-of-tree->right
  (implies (mapp tree)
           (mapp (tree->right tree)))
  :enable mapp)

(add-to-ruleset break-abstraction '(mapp-of-tree->right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (map mapp)
  :parents (treemap)
  :short "The empty @(see treemap)."
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

(define fix ((map mapp))
  :returns (map$ mapp)
  :parents (treemap)
  :short "Fixer for @(see treemap)s."
  (mbe :logic (if (mapp map)
                  map
                (empty))
       :exec (the list map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable mapp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t fix)))

(defruled fix-type-prescription
  (or (consp (fix map))
      (equal (fix map) nil))
  :rule-classes :type-prescription
  :enable (fix
           mapp
           empty))

(add-to-ruleset break-abstraction '(fix-type-prescription))

(defrule fix-when-mapp
  (implies (mapp map)
           (equal (fix map)
                  map))
  :enable fix)

(defruled fix-when-not-mapp
  (implies (not (mapp map))
           (equal (fix map)
                  (empty)))
  :enable fix)

(defrule fix-when-not-mapp-cheap
  (implies (not (mapp map))
           (equal (fix map)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-mapp)

(defruled treep-of-fix
  (treep (fix map))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(treep-of-fix))

(defruled bstp-of-fix
  (bstp (fix map))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(bstp-of-fix))

(defruled heapp-of-fix
  (heapp (fix map))
  :enable (fix
           break-abstraction))

(add-to-ruleset break-abstraction '(heapp-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x mapp)
   (y mapp))
  :returns (yes/no booleanp)
  :parents (treemap)
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
           mapp
           fix
           empty))

(add-to-ruleset break-abstraction '(equiv-when-tree-equiv-refinement))

(defrule fix-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (fix map0)
                  (fix map1)))
  :rule-classes :congruence
  :enable equiv)

(defrule fix-under-equiv
  (equiv (fix map)
         map)
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((map mapp))
  :returns (yes/no booleanp)
  :parents (treemap)
  :short "Check if a @(see treemap) is empty."
  (tree-empty-p (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable mapp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t emptyp)))

(defrule emptyp-type-prescription
  (booleanp (emptyp map))
  :rule-classes ((:type-prescription :typed-term (emptyp map))))

(defruled emptyp-compound-recognizer
  (implies (not (emptyp map))
           (not (equal map nil)))
  :rule-classes :compound-recognizer
  :enable emptyp)

(add-to-ruleset break-abstraction '(emptyp-compound-recognizer))

(defrule emptyp-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (emptyp map0)
                  (emptyp map1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable empty)

(defruled fix-when-emptyp
  (implies (emptyp map)
           (equal (fix map)
                  (empty)))
  :enable (emptyp
           fix
           tree-empty-p
           mapp
           empty))

(defrule fix-when-emptyp-cheap
  (implies (emptyp map)
           (equal (fix map)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fix-when-emptyp)

(defrule mapp-when-not-emptyp-forward-chaining
  (implies (not (emptyp map))
           (mapp map))
  :rule-classes :forward-chaining
  :enable (emptyp
           mapp
           empty))

;; TODO: Should this also be a regular rewrite rule?
(defrule emptyp-when-not-mapp-forward-chaining
  (implies (not (mapp map))
           (emptyp map))
  :rule-classes :forward-chaining)

;; This definition is useful for proving emptiness by extensionality.
(defruled emptyp-alt-definition
  (equal (emptyp map)
         (equal (fix map) (empty)))
  :rule-classes :definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head-key ((map mapp))
  :guard (not (emptyp map))
  :parents (treemap)
  :short "Get a key from the nonempty @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, the logical result is @('nil').")
   (xdoc::p
     "From a user perspective, this should be viewed as an arbitrary key in the
      the map. For a description of which element this actually provides, see
      @(tsee tree->head)."))
  (tree-element->key (tree->head (fix map)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule head-key-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (head-key map0)
                  (head-key map1)))
  :rule-classes :congruence
  :enable head-key)

(defruled head-key-when-emptyp
  (implies (emptyp map)
           (equal (head-key map)
                  nil))
  :enable (head-key
           emptyp
           irr-tree-element))

(defrule head-key-when-emptyp-cheap
  (implies (emptyp map)
           (equal (head-key map)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable head-key-when-emptyp)

(defrule head-key-of-empty
  (implies (emptyp map)
           (equal (head-key (empty))
                  nil))
  :enable head-key-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy map-extra-rules
  '(fix-when-not-mapp
    fix-when-emptyp
    head-key-when-emptyp
    ))
