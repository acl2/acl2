; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "internal/keys-defs")
(include-book "internal/submap-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "lookup-defs")
(include-book "keys-defs")
(include-book "size-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "std/omaps/core" :dir :system))
(local (include-book "std/omaps/submap" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/submap"))
(local (include-book "internal/antisymmetry"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "size"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc submap
  :parents (treemap)
  :short "Check if one @(see treemap) is a submap of the other."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n))$) (Note: the current implementation is
       slightly inefficient. This should eventually be @($O(m\\log(n/m))$),
       where @($n < m$). This may be implemented similar to @(tsee diff).)")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(submap x y :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro submap (x y &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(submap$inline ,x ,y))
    (=     `(submap-=      ,x ,y))
    (eq    `(submap-eq     ,x ,y))
    (eql   `(submap-eql    ,x ,y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define submap$inline
  ((x mapp)
   (y mapp))
  :returns (yes/no booleanp)
  (tree-submap-p (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn submap submap$inline))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t submap)))

(defrule submap-type-prescription
  (booleanp (submap x y))
  :rule-classes ((:type-prescription :typed-term (submap x y))))

(defrule submap-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (submap x0 y)
                  (submap x1 y)))
  :rule-classes :congruence
  :enable submap)

(defrule submap-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (submap x y0)
                  (submap x y1)))
  :rule-classes :congruence
  :enable submap)

(defrule submap-when-emptyp-of-arg1
  (implies (emptyp x)
           (submap x y))
  :enable (submap
           emptyp
           empty))

(defrule submap-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (submap x y)
                  (emptyp x)))
  :enable (submap
           emptyp))

(defrule subset-of-keys
  (implies (submap x y)
           (treeset::subset (keys x) (keys y)))
  :enable (submap
           keys))

;; TODO: too aggressive?
(defrule subset-of-keys-forward-chaining
  (implies (submap x y)
           (treeset::subset (keys x) (keys y)))
  :rule-classes :forward-chaining)

;; Free from subset-of-keys-forward-chaining
;; (defrule in-of-keys-when-in-of-keys-and-submap
;;   (implies (and (treeset::in key (keys x))
;;                 (submap x y))
;;            (treeset::in key (keys y))))

(defruled lookup-when-in-of-keys-and-submap
  (implies (and (treeset::in key (keys x))
                (submap x y))
           (equal (lookup key y :default default)
                  (lookup key x :default default)))
  :enable (keys
           submap
           lookup))

;; TODO: disable by default?
(defrule lookup-when-in-of-keys-and-proper-submap
  (implies (and (treeset::in key (keys x))
                (submap x y)
                ;; This hypothesis is not necessary logically (see
                ;; lookup-when-in-of-keys-and-submap). It is used to establish
                ;; that (not (equiv x y)), and thus avoid rewriting loops.
                (not (submap y x)))
           (equal (lookup key y :default default)
                  (lookup key x :default default)))
  :by lookup-when-in-of-keys-and-submap)

;; Free from subset-of-keys-forward-chaining
;; (defrule in-of-keys-when-submap-and-in-of-keys
;;   (implies (and (submap x y)
;;                 (treeset::in key (keys x)))
;;            (treeset::in key (keys y))))

(defruled lookup-when-submap-and-in-of-keys
  (implies (and (submap x y)
                (treeset::in key (keys x)))
           (equal (lookup key y :default default)
                  (lookup key x :default default)))
  :by lookup-when-in-of-keys-and-submap)

;; TODO: disable by default?
(defrule lookup-when-proper-submap-and-in-of-keys
  (implies (and (submap x y)
                (treeset::in key (keys x))
                ;; This hypothesis is not necessary logically (see
                ;; lookup-when-submap-and-in-of-keys). It is used to establish
                ;; that (not (equiv x y)), and thus avoid rewriting loops.
                (not (submap y x)))
           (equal (lookup key y :default default)
                  (lookup key x :default default)))
  :by lookup-when-submap-and-in-of-keys)

(defrule lookup-when-in-of-keys-and-submap-forward-chaining
  (implies (and (treeset::in key (keys x))
                (submap x y))
           (equal (lookup key y)
                  (lookup key x)))
  :rule-classes ((:forward-chaining :trigger-terms ((treeset::in key (keys x))
                                                    (submap x y))))
  :by lookup-when-in-of-keys-and-submap)

;;;;;;;;;;;;;;;;;;;;

(defrule submap-reflexivity
  (submap x x)
  :enable (submap
           break-abstraction))

(defruled submap-antisymmetry
  (implies (and (submap x y)
                (submap y x))
           (equal (fix x) (fix y)))
  :use (:instance tree-submap-p-antisymmetry
                  (x (fix x))
                  (y (fix y)))
  :enable (submap
           fix
           mapp
           empty))

(defruled submap-antisymmetry-equiv
  (implies (and (submap x y)
                (submap y x))
           (equiv x y))
  :use submap-antisymmetry
  :enable equiv)

(defrule submap-antisymmetry-equiv-forward-chaining
  (implies (and (submap x y)
                (submap y x))
           (equiv x y))
  :rule-classes ((:forward-chaining :trigger-terms ((and (submap x y)
                                                         (submap y x)))))
  :by submap-antisymmetry-equiv)

(defrule submap-transitivity
  (implies (and (submap x y)
                (submap y z))
           (submap x z))
  :enable submap)

;;;;;;;;;;;;;;;;;;;;

;; (defruled submap-when-not-in-of-head
;;   (implies (and (not (emptyp x))
;;                 (not (in (head x) y)))
;;            (not (submap x y)))
;;   :enable (submap
;;            in
;;            head
;;            emptyp))
;;
;; (defrule submap-when-not-in-of-head-cheap
;;   (implies (and (not (in (head x) y))
;;                 (not (emptyp x)))
;;            (not (submap x y)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
;;   :by submap-when-not-in-of-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-containment
  :parents (treemap)
  :short "Prove map equalities via @(see submap) antisymmetry."
  :long
  (xdoc::topstring
    (xdoc::p
      "This mirrors the @(see set::std/osets) rule, @(see
       set::double-containment). Here, we disable it by default."))

  (defruled equal-becomes-submap-when-mapp
    (implies (and (mapp x)
                  (mapp y))
             (equal (equal x y)
                    (and (submap x y)
                         (submap y x))))
    :use submap-antisymmetry)

  (defruled double-containment
    (implies (and (mapp x)
                  (mapp y))
             (equal (equal x y)
                    (and (submap x y)
                         (submap y x))))
    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
    :by equal-becomes-submap-when-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk submap-sk (x y)
  :parents (submap)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (key default)
    (non-exec
      (implies (treeset::in key (keys x))
               ;; Note:: we don't need to assert (treeset::in key (keys y)).
               ;; This is implied by the quantification over default.
               ;; (If the key was not in y, we could construct a default value
               ;; which is not equal to the lookup of x. The equality would
               ;; then fail.)
               (equal (lookup key x :default default)
                      (lookup key y :default default))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t submap-sk)))

(defruled submap-sk-becomes-tree-submap-p-sk
  (equal (submap-sk x y)
         (tree-submap-p-sk (fix x) (fix y)))
  :use (submap-sk-becomes-tree-submap-p-sk-lemma0
        submap-sk-becomes-tree-submap-p-sk-lemma1)

  :prep-lemmas
  ((defruled submap-sk-becomes-tree-submap-p-sk-lemma0
     (implies (submap-sk x y)
              (tree-submap-p-sk (fix x) (fix y)))
     :use (:instance submap-sk-necc
                     (key (tree-submap-p-sk-witness (fix x) (fix y)))
                     ;; We construct an arbitrary value that does not conflict with the lookup.
                     (default (list (tree-lookup (tree-submap-p-sk-witness (fix x) (fix y)) (fix x)))))
     :enable (tree-submap-p-sk
              keys
              lookup))

   (defruled submap-sk-becomes-tree-submap-p-sk-lemma1
     (implies (tree-submap-p-sk (fix x) (fix y))
              (submap-sk x y))
     :use (:instance tree-submap-p-sk-necc
                     (x (fix x))
                     (y (fix y))
                     (key (mv-nth 0 (submap-sk-witness x y))))
     :enable (submap-sk
              keys
              lookup))))

(defruled submap-becomes-submap-sk
  (equal (submap x y)
         (submap-sk x y))
  :enable (submap
           submap-sk-becomes-tree-submap-p-sk
           tree-submap-p-sk-becomes-tree-submap-p
           break-abstraction))

(defruled submap-sk-becomes-submap
  (equal (submap-sk x y)
         (submap x y))
  :by submap-becomes-submap-sk)

(defrule submap-sk-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (submap-sk x0 y)
                  (submap-sk x1 y)))
  :rule-classes :congruence
  :enable submap-sk-becomes-submap)

(defrule submap-sk-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (submap-sk x y0)
                  (submap-sk x y1)))
  :rule-classes :congruence
  :enable submap-sk-becomes-submap)

(defthy pick-a-point
  '(submap-becomes-submap-sk
    submap-sk))

(defruled submap-becomes-submap-sk-polar
  (implies (syntaxp (acl2::want-to-weaken (submap x y)))
           (equal (submap x y)
                  (submap-sk x y)))
  :by submap-becomes-submap-sk)

(defthy pick-a-point-polar
  '(submap-becomes-submap-sk-polar
    submap-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-keys-when-proper-submap
  (implies (and (submap x y)
                (not (submap y x)))
           (not (treeset::subset (keys y) (keys x))))
  :use ((:instance lookup-when-in-of-keys-and-submap
                   (key (mv-nth 0 (submap-sk-witness y x)))
                   (default nil)))
  :enable pick-a-point-polar)

(defrule subset-of-keys-when-proper-submap-forward-chaining
  (implies (and (submap x y)
                (not (submap y x)))
           (not (treeset::subset (keys y) (keys x))))
  :rule-classes ((:forward-chaining :trigger-terms ((submap x y)
                                                    (submap y x))))
  :by subset-of-keys-when-proper-submap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-to-omap-to-omap
  (equal (omap::submap (to-omap x) (to-omap y))
         (submap x y))
  :use (lemma0 lemma1)

  :prep-lemmas
  ((defruled lemma0
     (implies (submap x y)
              (omap::submap (to-omap x) (to-omap y)))
     :enable omap::pick-a-point)

   (defruled lemma1
     (implies (omap::submap (to-omap x) (to-omap y))
              (submap x y))
     :enable (pick-a-point
              to-omap-theory
              omap::in-of-keys-to-assoc
              omap::assoc-when-submap-and-assoc)
     :disable from-omap-theory)))

(add-to-ruleset from-omap-theory '(submap-of-to-omap-to-omap))

(defruled submap-becomes-omap-submap
  (equal (submap x y)
         (omap::submap (to-omap x) (to-omap y))))

(add-to-ruleset to-omap-theory '(submap-becomes-omap-submap))

;;;;;;;;;;;;;;;;;;;;

;; Note: these two theorems have not been proven for omaps. They should be
;; proven at some point.

(defrule cardinality-when-submap-linear
  (implies (submap x y)
           (<= (treeset::cardinality (keys x))
               (treeset::cardinality (keys y))))
  :rule-classes :linear)

(defrule cardinality-when-proper-submap-linear
  (implies (and (submap x y)
                (not (submap y x)))
           (< (treeset::cardinality (keys x))
              (treeset::cardinality (keys y))))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define submap-=
  ((x acl2-number-mapp)
   (y acl2-number-mapp))
  (mbe :logic (submap x y)
       :exec (tree-submap-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-acl2-numberp
                                            submap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define submap-eq
  ((x symbol-mapp)
   (y symbol-mapp))
  (mbe :logic (submap x y)
       :exec (tree-submap-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-symbolp
                                            submap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define submap-eql
  ((x eqlable-mapp)
   (y eqlable-mapp))
  (mbe :logic (submap x y)
       :exec (tree-submap-p x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-eqlablep
                                            submap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthy submap-extra-rules
;;   '(;; submap-when-not-in-of-head
;;     ))
