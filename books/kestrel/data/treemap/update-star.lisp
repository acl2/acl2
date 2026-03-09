; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/min-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/max-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/update-star-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "min-max-defs")
(include-book "submap-defs")
(include-book "update-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/max" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/update-star"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "min-max"))
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "submap"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc update*
  :parents (treemap)
  :short "An @($n$)-ary left-biased union on @(see treemap)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$) (for binary update*, where
       @($m < n$)).")
    (xdoc::p
      "This union is left-biased. When a key is present in both the left and
       right maps, the value of the left map is used.")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(union map-0 map-1 ... map-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update*-macro-loop
  (update*
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq update*
                         '(update*$inline update*-= update*-eq update*-eql)))
  (if (endp (rest (rest list)))
      (list update*
            (first list)
            (second list))
    (list update*
          (first list)
          (update*-macro-loop update* (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define update*-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'update* "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'update* "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (update*-macro-loop 'update*$inline rest))
                       (=     (update*-macro-loop 'update*-=      rest))
                       (eq    (update*-macro-loop 'update*-eq     rest))
                       (eql   (update*-macro-loop 'update*-eql    rest))
                       (otherwise
                        (er hard? 'update*
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (update*-macro-loop 'update*$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro update* (&rest forms)
  (declare (xargs :guard t))
  (update*-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update*$inline
  ((x mapp)
   (y mapp))
  :returns (map mapp
                :hints (("Goal" :in-theory (enable mapp
                                                   fix
                                                   empty))))
  (tree-update* (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

(add-macro-fn update* update*$inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update*)))

(defruled update*-type-prescription
  (or (consp (update* x y))
      (equal (update* x y) nil))
  :rule-classes :type-prescription
  :enable update*)

(add-to-ruleset break-abstraction '(update*-type-prescription))

(defrule update*-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (update* x0 y)
                  (update* x1 y)))
  :rule-classes :congruence
  :enable update*)

(defrule update*-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (update* x y0)
                  (update* x y1)))
  :rule-classes :congruence
  :enable update*)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-update*
  (equal (emptyp (update* x y))
         (and (emptyp x)
              (emptyp y)))
  :enable (update*
           emptyp
           mapp
           break-abstraction))

(defrule keys-of-update*
  (equal (keys (update* x y))
         (treeset::union (keys x)
                         (keys y)))
  :enable (update*
           keys
           mapp
           break-abstraction))

(defrule lookup-of-update*
  (equal (lookup key (update* x y) :default default)
         (if (treeset::in key (keys x))
             (lookup key x :default default)
           (lookup key y :default default)))
  :enable (update*
           lookup
           keys
           mapp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-arg1-and-update*-of-arg1
  (submap x (update* x y))
  :enable (pick-a-point
           submap))

;; (defrule submap-of-arg1-and-update*-of-arg2-when-compatiblep
;;   (implies (compatiblep x y)
;;            (subset x (update* y x)))
;;   :enable (pick-a-point
;;            subset))

;; TODO
#|
(defrule monotonicity-of-update*
  (implies (and (submap x0 x1)
                (submap y0 y1))
           (submap (update* x0 y0)
                   (update* x1 y1)))
  :use ((:instance lookup-when-in-of-keys-and-submap
                   (x x0)
                   (y x1)
                   (key (mv-nth 0
                                (submap-sk-witness (update* x0 y0)
                                                   (update* x1 y1))))
                   (default (mv-nth 1
                                    (submap-sk-witness (update* x0 y0)
                                                       (update* x1 y1)))))
        (:instance lookup-when-in-of-keys-and-submap
                   (x y0)
                   (y y1)
                   (key (mv-nth 0
                                (submap-sk-witness (update* x0 y0)
                                                   (update* x1 y1))))
                   (default (mv-nth 1
                                    (submap-sk-witness (update* x0 y0)
                                                       (update* x1 y1)))))
        ;; (:instance lookup-when-in-of-keys-and-submap
        ;;            (x x0)
        ;;            (y x1)
        ;;            (key (mv-nth 0
        ;;                         (submap-sk-witness (update* x0 y0)
        ;;                                            (update* x1 y1))))
        ;;            (default nil))
        ;; (:instance lookup-when-in-of-keys-and-submap
        ;;            (x y0)
        ;;            (y y1)
        ;;            (key (mv-nth 0
        ;;                         (submap-sk-witness (update* x0 y0)
        ;;                                            (update* x1 y1))))
        ;;            (default nil))
        )
  :enable (pick-a-point-polar
           lookup-with-default-becomes-lookup-syntaxp))
|#

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-update*
  (equal (update* (update* x y) z)
         (update* x y z))
  :enable extensionality)

;; (defrule commutativity-of-update*-when-compatiblep
;;   (implies (compatiblep x y)
;;            (equal (update* y x)
;;                   (update* x y)))
;;   :enable extensionality)

;; (defrule commutativity-2-of-update*-when-compatiblep
;;   (implies (compatiblep x y)
;;            (equal (update* y x z)
;;                   (update* x y z)))
;;   :enable extensionality)

(defrule idempotence-of-update*
  (equal (update* x x)
         (fix x))
  :enable extensionality)

(defrule update*-when-submap-of-arg1-arg2
  (implies (submap x y)
           (equal (update* x y)
                  (fix y)))
  :enable extensionality)

(defrule update*-when-submap-of-arg2-arg1
  (implies (submap y x)
           (equal (update* x y)
                  (fix x)))
  :use ((:instance lookup-when-in-of-keys-and-submap
                   (x y)
                   (y x)
                   (key (mv-nth 0
                                (ext-equal-witness (update* x y)
                                                   (fix x))))
                   (default (mv-nth 1
                                    (ext-equal-witness (update* x y)
                                                       (fix x))))))
  :enable extensionality)

(defrule update*-contraction
  (equal (update* x x y)
         (update* x y))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled update*-when-emptyp-of-arg1
  (implies (emptyp x)
           (equal (update* x y)
                  (fix y))))

(defrule update*-when-emptyp-of-arg1-cheap
  (implies (emptyp x)
           (equal (update* x y)
                  (fix y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by update*-when-emptyp-of-arg1)

(defrule update*-of-empty
  (equal (update* (empty) y)
         (fix y))
  :enable update*-when-emptyp-of-arg1)

(defruled update*-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (update* x y)
                  (fix x))))

(defrule update*-when-emptyp-of-arg2-cheap
  (implies (emptyp y)
           (equal (update* x y)
                  (fix x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by update*-when-emptyp-of-arg2)

(defrule update*-of-arg1-and-empty
  (equal (update* x (empty))
         (fix x))
  :enable update*-when-emptyp-of-arg2)

(defrule update*-of-update
  (equal (update* (update key val x) y)
         (update key val (update* x y)))
  :enable extensionality)

;; TODO: expensive? Disable and introduce cheap rule?
(defrule update*-of-arg1-and-update
  (implies (not (treeset::in key (keys x)))
           (equal (update* x (update key val y))
                  (update key val (update* x y))))
  :enable extensionality)

(defruled update*-of-delete
  (equal (update* (delete key x) y)
         (if (treeset::in key (keys y))
             ;; It isn't clear that this is simpler than the LHS.
             ;; TODO: clarify normal forms we are striving for.
             (update key (lookup key y) (update* x y))
           (delete key (update* x y))))
  :enable extensionality)

;; TODO: expensive? Disable and introduce cheap rule?
(defrule update*-of-delete-when-not-in-of-keys
  (implies (not (treeset::in key (keys y)))
           (equal (update* (delete key x) y)
                  (delete key (update* x y))))
  :by update*-of-delete)

;; TODO: disable by default? Introduce conditional/cheap rules?
(defrule update*-of-arg1-and-delete
  (equal (update* x (delete key y))
         (if (treeset::in key (keys x))
             (update* x y)
           (delete key (update* x y))))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

#|
(defrule min-of-update*
  (equal (min (update* x y))
         (cond ((emptyp x) (min y))
               ((emptyp y) (min x))
               (t (min-<< (min x) (min y)))))
  ;; TODO: improve proof
  :use ((:instance <<-of-arg1-and-min-when-in
                   (x (not-<<-all-l-sk-witness (update* x y) (min x)))
                   (set x))
        (:instance <<-of-arg1-and-min-when-in
                   (x (not-<<-all-l-sk-witness (update* x y) (min x)))
                   (set y))
        (:instance <<-of-arg1-and-min-when-in
                   (x (not-<<-all-l-sk-witness (update* x y) (min y)))
                   (set x))
        (:instance <<-of-arg1-and-min-when-in
                   (x (not-<<-all-l-sk-witness (update* x y) (min y)))
                   (set y)))
  :enable (equal-of-min-becomes-sk
           not-<<-all-l-sk
           min-<<
           data::<<-rules)
  :disable <<-of-arg1-and-min-when-in)

(defrule max-of-update*
  (equal (max (update* x y))
         (cond ((emptyp x) (max y))
               ((emptyp y) (max x))
               (t (max-<< (max x) (max y)))))
  ;; TODO: improve proof
  :use ((:instance <<-of-max-when-in
                   (x (not-<<-all-r-sk-witness (max x) (update* x y)))
                   (set x))
        (:instance <<-of-max-when-in
                   (x (not-<<-all-r-sk-witness (max x) (update* x y)))
                   (set y))
        (:instance <<-of-max-when-in
                   (x (not-<<-all-r-sk-witness (max y) (update* x y)))
                   (set x))
        (:instance <<-of-max-when-in
                   (x (not-<<-all-r-sk-witness (max y) (update* x y)))
                   (set y)))
  :enable (equal-of-max-becomes-sk
           not-<<-all-r-sk
           max-<<
           data::<<-rules)
  :disable (<<-of-max-when-in
            <<-of-arg1-and-max-when-in))
|#

;;;;;;;;;;;;;;;;;;;;

(defrule to-omap-of-update*
  (equal (to-omap (update* x y))
         (omap::update* (to-omap x)
                        (to-omap y)))
  :enable (to-omap
           update*
           mapp
           break-abstraction))

(add-to-ruleset to-omap-theory '(to-omap-of-update*))

(defrule from-omap-of-update*
  (equal (from-omap (omap::update* x y))
         (update* (from-omap x)
                  (from-omap y)))
  :enable (extensionality
           omap::assoc-to-in-of-keys))

(add-to-ruleset from-omap-theory '(from-omap-of-update*))

(defruled update*-becomes-omap-update*
  (equal (update* x y)
         (from-omap (omap::update* (to-omap x)
                                   (to-omap y)))))

(add-to-ruleset to-omap-theory '(update*-becomes-omap-update*))

(defruled omap-update*-becomes-update*
  (equal (omap::update* x y)
         (to-omap (update* (from-omap x)
                           (from-omap y)))))

(add-to-ruleset from-omap-theory '(omap-update*-becomes-update*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update*-=
  ((x acl2-number-mapp)
   (y acl2-number-mapp))
  (mbe :logic (update* x y)
       :exec (acl2-number-tree-update* x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update*
                                            keys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update*-eq
  ((x symbol-mapp)
   (y symbol-mapp))
  (mbe :logic (update* x y)
       :exec (symbol-tree-update* x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update*
                                            keys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update*-eql
  ((x eqlable-mapp)
   (y eqlable-mapp))
  (mbe :logic (update* x y)
       :exec (eqlable-tree-update* x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update*
                                            keys))))
