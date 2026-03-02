; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
;
; Some rules in this book are "ported" from std/osets/top.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)

(include-book "internal/join-defs")
(include-book "internal/delete-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "submap-defs")
(include-book "update-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/omaps/core" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/join"))
(local (include-book "internal/delete"))
;; (local (include-book "internal/count"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
;; (local (include-book "cardinality"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "submap"))
(local (include-book "extensionality"))
(local (include-book "update"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc delete
  :parents (treeset)
  :short "Remove a value (or multiple values) from a @(see treemap)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$) (for a single delete).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(delete x-0 x-1 ... x-n set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-macro-loop
  (delete
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq delete
                         '(delete$inline delete-= delete-eq delete-eql)))
  (if (endp (rest (rest list)))
      (list delete
            (first list)
            (second list))
    (list delete
          (first list)
          (delete-macro-loop delete (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define delete-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'delete "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'delete "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (delete-macro-loop 'delete$inline rest))
                       (= (delete-macro-loop 'delete-= rest))
                       (eq (delete-macro-loop 'delete-eq rest))
                       (eql (delete-macro-loop 'delete-eql rest))
                       (otherwise
                        (er hard? 'delete
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (delete-macro-loop 'delete$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro delete (&rest forms)
  (declare (xargs :guard t))
  (delete-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete$inline
  (key
   (map mapp))
  :returns (map$ mapp
                 :hints (("Goal" :in-theory (enable mapp
                                                    fix
                                                    empty))))
  (tree-delete key (fix map))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn delete delete$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t delete)))

(defruled delete-type-prescription
  (or (consp (delete key map))
      (equal (delete key map) nil))
  :rule-classes :type-prescription
  :enable delete)

(add-to-ruleset break-abstraction '(delete-type-prescription))

(defrule delete-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (delete key map0)
                  (delete key map1)))
  :rule-classes :congruence
  :enable delete)

(defrule keys-of-delete
  (equal (keys (delete key map))
         (treeset::delete key (keys map)))
  :enable (delete
           keys
           mapp
           break-abstraction))

(defrule lookup-of-delete
  (equal (lookup x (delete y map) :default default)
         (if (equal x y)
             default
           (lookup x map :default default)))
  :enable (delete
           lookup
           keys
           mapp
           break-abstraction))

(defrule commutativity-of-delete
  (equal (delete y x map)
         (delete x y map))
  :enable extensionality)

(defrule delete-contraction
  (equal (delete x x set)
         (delete x set))
  :enable extensionality)

(defruled delete-when-not-in-of-keys
  (implies (not (treeset::in key (keys map)))
           (equal (delete key map)
                  (fix map)))
  :enable extensionality)

(defrule delete-when-not-in-of-keys-cheap
  (implies (not (treeset::in key (keys map)))
           (equal (delete key map)
                  (fix map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-when-not-in-of-keys)

(defrule equal-of-delete-and-arg2
  (equal (equal (delete key map) map)
         (and (mapp map)
              (not (treeset::in key (keys map))))))

;; TODO: add to expensive-rules
(defruled delete-of-update
  (equal (delete x (update y val map))
         (if (equal x y)
             (delete x map)
           (update y val (delete x map))))
  :enable extensionality)

(defrule delete-of-update-same
  (equal (delete key (update key val map))
         (delete key map))
  :enable delete-of-update)

(defruled delete-of-update-when-not-equal
  (implies (not (equal x y))
           (equal (delete x (update y val map))
                  (update y val (delete x map))))
  :by delete-of-update)

(defrule delete-of-update-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (delete x (update y val map))
                  (update y val (delete x map))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-of-update-when-not-equal)

(defrule update-of-delete-same
  (equal (update key val (delete key map))
         (update key val map))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-delete
  (submap (delete key map) map)
  :enable pick-a-point)

(defrule submap-of-arg1-and-delete
  (equal (submap map (delete key map))
         (not (treeset::in key (keys map))))
  :use ((:instance subset-of-keys
                   (x map)
                   (y (delete key map))))
  :disable (subset-of-keys
            subset-of-keys-forward-chaining))

(defrule monotonicity-of-delete
  (implies (submap map0 map1)
           (submap (delete key map0)
                   (delete key map1)))
  :use ((:instance lookup-when-in-of-keys-and-submap
                   (x map0)
                   (y map1)
                   (key (mv-nth 0 (submap-sk-witness (delete key map0)
                                                     (delete key map1))))
                   (default (mv-nth 1 (submap-sk-witness (delete key map0)
                                                         (delete key map1))))))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule to-omap-of-delete
  (equal (to-omap (delete key map))
         (omap::delete key (to-omap map)))
  :enable (to-omap
           delete
           mapp
           break-abstraction))

(add-to-ruleset to-omap-theory '(to-omap-of-delete))

(defrule from-omap-of-omap-delete
  (equal (from-omap (omap::delete key omap))
         (delete key (from-omap omap)))
  :enable extensionality)

(add-to-ruleset from-omap-theory '(from-omap-of-omap-delete))

(defruled delete-becomes-omap-delete
  (equal (delete key map)
         (from-omap (omap::delete key (to-omap map)))))

(add-to-ruleset to-omap-theory '(delete-becomes-omap-delete))

(defruled omap-delete-becomes-delete
  (equal (omap::delete key omap)
         (to-omap (delete key (from-omap omap)))))

(add-to-ruleset from-omap-theory '(omap-delete-becomes-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-=
  ((key acl2-numberp)
   (map acl2-number-mapp))
  (mbe :logic (delete key map)
       :exec (acl2-number-tree-delete key map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            map-keys-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eq
  ((key symbolp)
   (map symbol-mapp))
  (mbe :logic (delete key map)
       :exec (symbol-tree-delete key map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            map-keys-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eql
  ((key eqlablep)
   (map eqlable-mapp))
  (mbe :logic (delete key map)
       :exec (eqlable-tree-delete key map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            map-keys-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define tail
;;   ((map mapp))
;;   :parents (delete)
;;   :short "Remove the @(see head) from a nonempty @(see treemap)."
;;   :long
;;   (xdoc::topstring
;;    (xdoc::p
;;      "This is slightly faster than calling @(tsee delete) on the head.")
;;    (xdoc::p
;;      "Note: it is <emph>not</emph> recommended to iterate over a @(see treemap)
;;       using @(tsee tail) (unless you need to maintain a map of the remaining
;;       key-value pairs)."))
;;   :guard (not (emptyp map))
;;   (mbe :logic (delete (head map) map)
;;        :exec (tree-join (tree->left map)
;;                         (tree->right map)))
;;   :enabled t
;;   :inline t
;;   :guard-hints (("Goal" :in-theory (enable* break-abstraction
;;                                             delete
;;                                             head
;;                                             tree-delete
;;                                             tree-join-at))))
