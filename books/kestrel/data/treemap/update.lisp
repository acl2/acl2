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

(include-book "kestrel/data/treeset/hash-defs" :dir :system)
(include-book "kestrel/data/treeset/to-oset-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/update-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "size-defs")
(include-book "in-defs")
(include-book "lookup-defs")
(include-book "values-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "std/omaps/extensionality" :dir :system))

(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/alist" :dir :system))
(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/lists/reverse" :dir :system))

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))
(local (include-book "internal/keys"))
(local (include-book "internal/update"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "size"))
(local (include-book "in"))
(local (include-book "values"))
(local (include-book "lookup"))
(local (include-book "submap"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc update
  :parents (treemap)
  :short "Add a key-value pair (or multiples pairs) to a @(see treemap)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$) (for a single update).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(update key-0 val-0 key-1 val-1 ... key-n val-n map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-macro-loop
  (update
   (list true-listp))
  :guard (and (consp (cdr list))
              (member-eq update
                         '(update$inline update-= update-eq update-eql)))
  (cond ((endp (cddr list))
         (er hard? 'update "Missing value for key: ~x0." (first list)))
        ((endp (cdddr list))
         (cons update list))
        (t
         (list update
               (first list)
               (second list)
               (update-macro-loop update (cddr list)))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define update-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'update "Arguments are ill-formed: ~x0" list))
          ((not (consp rest))
           (er hard? 'update "Too few arguments: ~x0" list))
          ((not (consp (rest rest)))
           (list 'fix (first list)))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (update-macro-loop 'update$inline rest))
                       (=     (update-macro-loop 'update-=      rest))
                       (eq    (update-macro-loop 'update-eq     rest))
                       (eql   (update-macro-loop 'update-eql    rest))
                       (otherwise
                        (er hard? 'update
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (update-macro-loop 'update$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro update (&rest forms)
  (declare (xargs :guard t))
  (update-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update$inline
  (key
   val
   (map mapp))
  :returns (map$ mapp
                 :hints (("Goal" :in-theory (enable* break-abstraction
                                                     mapp))))
  (tree-update key (hash key) val (fix map))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn update update$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update)))

(defrule update-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (update key val map0)
                  (update key val map1)))
  :rule-classes :congruence
  :enable update)

(defrule emptyp-of-update
  (not (emptyp (update key val map)))
  :enable (emptyp
           update
           fix
           mapp))

(defruled update-type-prescription
  (consp (update key val map))
  :rule-classes :type-prescription
  :enable emptyp
  :disable emptyp-of-update
  :use emptyp-of-update)

(add-to-ruleset break-abstraction '(update-type-prescription))

(defrule keys-of-update
  (equal (keys (update key val map))
         (treeset::insert key (keys map)))
  :enable (keys
           update
           fix
           mapp
           empty))

(defrule lookup-of-update
  (equal (lookup x (update y val map) :default default)
         (if (equal x y)
             val
           (lookup x map :default default)))
  :enable (lookup
           update
           keys
           fix
           mapp
           empty))

;; TODO: disable and introduce cheap rules?
(defrule commutativity-of-update-when
  (implies (or (not (equal key0 key1))
               (equal val0 val1))
           (equal (update key1 val1 key0 val0 map)
                  (update key0 val0 key1 val1 map)))
  :enable extensionality)

(defruled update-redundant
  (implies (and (treeset::in key (keys map))
                (equal (lookup key map) val))
           (equal (update key val map)
                  (fix map)))
  :enable extensionality)

(defrule update-redundant-cheap
  (implies (and (equal (lookup key map) val)
                (treeset::in key (keys map)))
           (equal (update key val map)
                  (fix map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by update-redundant)

(defrule update-contraction
  (equal (update key val0 key val1 map)
         (update key val0 map))
  :enable extensionality)

(defrule equal-of-update
  (equal (equal (update key val map) map)
         (and (mapp map)
              (treeset::in key (keys map))
              (equal (lookup key map) val))))

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-update
  (implies (submap x y)
           (equal (submap (update key val x) y)
                  (and (treeset::in key (keys y))
                       (equal (lookup key y) val))))
  :prep-lemmas
  ((defrule lemma0
     (implies (and (submap x y)
                   (submap (update key val x) y))
              (and (treeset::in key (keys y))
                   (equal (lookup key y) val)))
     ;; TODO: can this proof be improved?
     :use ((:instance lookup-when-in-of-keys-and-submap
                      (x (update key val x))
                      (default nil))
           (:instance subset-of-keys
                      (x (update key val x))))
     :disable subset-of-keys)

   (defrule lemma1
     (implies (and (submap x y)
                   (treeset::in key (keys y))
                   (equal (lookup key y) val))
              (submap (update key val x) y))
     :enable pick-a-point-polar)))

(defrule submap-of-arg1-and-update
  (equal (submap map (update key val map))
         (or (not (treeset::in key (keys map)))
             (equal (lookup key map) val)))
  :use (:instance lookup-when-in-of-keys-and-submap
                  (x map)
                  (y (update key val map))
                  (default nil))
  :enable pick-a-point-polar
  :disable lookup-when-in-of-keys-and-submap)

(defrule monotonicity-of-update
  (implies (submap map0 map1)
           (submap (update key val map0)
                   (update key val map1)))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule to-omap-of-update
  (equal (to-omap (update key val map))
         (omap::update key val (to-omap map)))
  :enable (to-omap
           update
           mapp
           break-abstraction))

(add-to-ruleset to-omap-theory '(to-omap-of-update))

(defruled update-of-to-omap
  (equal (omap::update key val (to-omap map))
         (to-omap (update key val map))))

(add-to-ruleset from-omap-theory '(update-of-to-omap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton-with-hash
  (key
   (hash (unsigned-byte-p 32 hash))
   val)
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  (mbe :logic (update key val (empty))
       :exec (tree-singleton key hash val))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           update
                                           empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton (key val)
  (mbe :logic (update key val (empty))
       :exec (tree-singleton key (hash key) val))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable update
                                           empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-from-alist-rev
  ((alist alistp)
   (map mapp))
  :returns (map$ mapp)
  (if (endp alist)
      (fix map)
    (update-from-alist-rev (rest alist)
                           (update (car (first alist))
                                   (cdr (first alist))
                                   map))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update-from-alist-rev)))

(defruled update-from-alist-rev-type-prescription
  (or (consp (update-from-alist-rev alist map))
      (equal (update-from-alist-rev alist map) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (update-from-alist-rev
           break-abstraction))

(add-to-ruleset break-abstraction '(update-from-alist-rev-type-prescription))

(defruled update-from-alist-rev-when-consp-of-arg1-type-prescription
  (implies (consp alist)
           (consp (update-from-alist-rev alist map)))
  :rule-classes :type-prescription
  :induct t
  :enable (update-from-alist-rev
           break-abstraction))

(add-to-ruleset break-abstraction
  '(update-from-alist-rev-when-consp-of-arg1-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule update-from-alist-rev-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (update-from-alist-rev list map0)
                  (update-from-alist-rev list map1)))
  :rule-classes :congruence
  :induct t
  :enable update-from-alist-rev)

(defrule emptyp-of-update-from-alist-rev
  (equal (emptyp (update-from-alist-rev list map))
         (and (not (consp list))
              (emptyp map)))
  :induct t
  :enable update-from-alist-rev)

(defrule keys-of-update-from-alist-rev
  (equal (keys (update-from-alist-rev alist map))
         (treeset::insert-all (strip-cars alist) (keys map)))
  :induct t
  :enable (update-from-alist-rev
           treeset::insert-all
           strip-cars))

(defrule lookup-of-update-from-alist-rev
  (implies (alistp alist)
           (equal (lookup key (update-from-alist-rev alist map) :default default)
                  (if (assoc-equal key alist)
                      (cdr (assoc-equal key (reverse alist)))
                    (lookup key map :default default))))
  :induct t
  :enable update-from-alist-rev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-from-alist
  ((alist alistp)
   (map mapp))
  :returns (map$ mapp)
  :parents (update)
  :short "Add an alist of key-value pairs to a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the
      alist, and @($m$) is the size of the map."))
  (mbe :logic (if (endp alist)
                  (fix map)
                (update (car (first alist))
                        (cdr (first alist))
                        (update-from-alist (rest alist) map)))
       :exec (update-from-alist-rev (reverse (the list alist)) map))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update-from-alist)))

(defruled update-from-alist-type-prescription
  (or (consp (update-from-alist alist map))
      (equal (update-from-alist alist map) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (update-from-alist
           break-abstraction))

(add-to-ruleset break-abstraction '(update-from-alist-type-prescription))

(defruled update-from-alist-when-consp-of-arg1-type-prescription
  (implies (consp alist)
           (consp (update-from-alist alist map)))
  :rule-classes :type-prescription
  :induct t
  :enable (update-from-alist
           break-abstraction))

(add-to-ruleset break-abstraction
  '(update-from-alist-when-consp-of-arg1-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule update-from-alist-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (update-from-alist list map0)
                  (update-from-alist list map1)))
  :rule-classes :congruence
  :induct t
  :enable update-from-alist)

(defrule emptyp-of-update-from-alist
  (equal (emptyp (update-from-alist list map))
         (and (not (consp list))
              (emptyp map)))
  :induct t
  :enable update-from-alist)

(defrule keys-of-update-from-alist
  (equal (keys (update-from-alist alist map))
         (treeset::insert-all (strip-cars alist) (keys map)))
  :induct t
  :enable (update-from-alist
           treeset::insert-all
           strip-cars))

(defrule lookup-of-update-from-alist
  (implies (alistp alist)
           (equal (lookup key (update-from-alist alist map) :default default)
                  (if (assoc-equal key alist)
                      (cdr (assoc-equal key alist))
                    (lookup key map :default default))))
  :induct t
  :enable update-from-alist)

(defrule update-from-alist-rev-becomes-update-from-alist
  (implies (alistp alist)
           (equal (update-from-alist-rev alist map)
                  (update-from-alist (reverse alist) map)))
  :enable extensionality)

(verify-guards update-from-alist$inline
  :hints (("Goal" :in-theory (enable update-from-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-alist
  ((alist alistp))
  :parents (treemap)
  :short "Create a map from an alist of key-value pairs."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee update-from-alist).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  :returns (map$ mapp)
  (update-from-alist alist (empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-alist)))

(defruled from-alist-type-prescription
  (or (consp (from-alist alist))
      (equal (from-alist alist) nil))
  :rule-classes :type-prescription
  :enable (from-alist
           break-abstraction))

(add-to-ruleset break-abstraction '(from-alist-type-prescription))

(defruled consp-of-from-alist-when-consp-of-arg1-type-prescription
  (implies (consp alist)
           (consp (from-alist alist)))
  :rule-classes :type-prescription
  :enable (from-alist
           break-abstraction))

(add-to-ruleset break-abstraction
  '(consp-of-from-alist-when-consp-of-arg1-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-from-alist
  (equal (emptyp (from-alist alist))
         (not (consp alist)))
  :enable from-alist)

(defrule keys-of-from-alist
  (equal (keys (from-alist alist))
         (treeset::from-list (strip-cars alist)))
  :enable (from-alist
           treeset::from-list))

(defrule lookup-of-from-alist
  (implies (alistp alist)
           (equal (lookup key (from-alist alist) :default default)
                  (if (assoc-equal key alist)
                      (cdr (assoc-equal key alist))
                    default)))
  :enable from-alist)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-from-omap
  ((omap omap::mapp)
   (map mapp))
  :returns (map$ mapp)
  :parents (update)
  :short "Add an omap of key-value pairs to a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the
      alist, and @($m$) is the size of the map."))
  (if (omap::emptyp$inline omap)
      (fix map)
    (update-from-omap (omap::tail$inline omap)
                      (mv-let (key val)
                              (omap::head$inline omap)
                        (update key val map)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update-from-omap)))

(defruled update-from-omap-type-prescription
  (or (consp (update-from-omap omap map))
      (equal (update-from-omap omap map) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (update-from-omap
           break-abstraction))

(add-to-ruleset break-abstraction '(update-from-omap-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule update-from-omap-when-mequiv-congruence
  (implies (omap::mequiv omap0 omap1)
           (equal (update-from-omap omap0 map)
                  (update-from-omap omap1 map)))
  :rule-classes :congruence
  :induct t
  :enable update-from-omap
  :disable omap::mequiv)

(defrule update-from-omap-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (update-from-omap omap map0)
                  (update-from-omap omap map1)))
  :rule-classes :congruence
  :induct t
  :enable update-from-omap)

(defrule emptyp-of-update-from-omap
  (equal (emptyp (update-from-omap omap map))
         (and (omap::emptyp omap)
              (emptyp map)))
  :induct t
  :enable update-from-omap)

(defrule update-from-omap-of-mfix
  (equal (update-from-omap (omap::mfix omap) map)
         (update-from-omap omap map))
  :induct t
  :enable update-from-omap)

(defrule keys-of-update-from-omap
  (equal (keys (update-from-omap omap map))
         (treeset::union (treeset::from-oset (omap::keys omap))
                         (keys map)))
  :induct t
  :enable (update-from-omap
           omap::keys)
  ;; TODO: maybe this should be disabled in general
  :disable ((:e treeset::from-oset)))

(defrule assoc-of-update-from-omap
  (equal (lookup key (update-from-omap omap map) :default default)
         (if (omap::assoc key omap)
             (cdr (omap::assoc key omap))
           (lookup key map :default default)))
  :induct t
  :enable update-from-omap
  :prep-books ((include-book "std/omaps/assoc" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-omap
  ((omap omap::mapp))
  :parents (treemap)
  :short "Create a map from an omap."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee update-from-omap).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  :returns (map$ mapp)
  (update-from-omap omap (empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-omap)))

(defruled from-omap-type-prescription
  (or (consp (from-omap omap))
      (equal (from-omap omap) nil))
  :rule-classes :type-prescription
  :enable (from-omap
           break-abstraction))

(add-to-ruleset break-abstraction '(from-omap-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule from-omap-when-mequiv-congruence
  (implies (omap::mequiv omap0 omap1)
           (equal (from-omap omap0)
                  (from-omap omap1)))
  :rule-classes :congruence
  :enable from-omap
  :disable omap::mequiv)

(defrule emptyp-of-from-omap
  (equal (emptyp (from-omap omap))
         (omap::emptyp omap))
  :enable from-omap)

(add-to-ruleset to-omap-theory '(emptyp-of-from-omap))

(defruled omap-emptyp-becomes-emptyp
  (equal (omap::emptyp omap)
         (emptyp (from-omap omap))))

(add-to-ruleset from-omap-theory '(omap-emptyp-becomes-emptyp))

(defrule keys-of-from-omap
  (equal (keys (from-omap omap))
         (treeset::from-oset (omap::keys omap)))
  :enable from-omap)

(add-to-ruleset to-omap-theory '(keys-of-from-omap))

(defruled omap-keys-becomes-keys
  (equal (omap::keys omap)
         (treeset::to-oset (keys (from-omap omap)))))

(add-to-ruleset from-omap-theory '(omap-keys-becomes-keys))

(defrule lookup-of-from-omap
  (equal (lookup key (from-omap omap) :default default)
         (if (omap::assoc key omap)
             (cdr (omap::assoc key omap))
           default))
  :enable from-omap)

(add-to-ruleset to-omap-theory '(lookup-of-from-omap))

(defruled omap-assoc-becomes-lookup
  (equal (omap::assoc key omap)
         (if (treeset::in key (keys (from-omap omap)))
             (cons key (lookup key (from-omap omap)))
           nil))
  :enable omap::in-of-keys-to-assoc)

(add-to-ruleset from-omap-theory '(omap-assoc-becomes-lookup))

;; TODO
;; (defrule values-of-from-omap
;;   (equal (values (from-omap omap))
;;          (treeset::from-oset (omap::values omap)))
;;   :enable from-omap)
;;
;; (add-to-ruleset to-omap-theory '(values-of-from-omap))
;;
;; (defruled omap-values-becomes-values
;;   (equal (omap::values omap)
;;          (treeset::to-oset (values (from-omap omap)))))
;;
;; (add-to-ruleset from-omap-theory '(omap-values-becomes-values))

(defrule to-omap-of-from-omap
  (equal (to-omap (from-omap omap))
         (omap::mfix omap))
  :enable (omap::extensionality
           omap::assoc-to-in-of-keys))

(add-to-ruleset to-omap-theory '(to-omap-of-from-omap))

(defruled mfix-becomes-to-omap
  (equal (omap::mfix omap)
         (to-omap (from-omap omap))))

(add-to-ruleset from-omap-theory '(mfix-becomes-to-omap))

(defruled omap-size-becomes-cardinality-of-keys
  (equal (omap::size omap)
         (treeset::cardinality (keys (from-omap omap))))
  :use (:instance size-of-to-omap
                  (map (from-omap omap)))
  :disable size-of-to-omap)

(add-to-ruleset from-omap-theory '(omap-size-becomes-cardinality-of-keys))

(defrule from-omap-of-to-omap
  (equal (from-omap (to-omap map))
         (fix map))
  :enable extensionality)

(add-to-ruleset from-omap-theory '(from-omap-of-to-omap))

(defrule equal-of-from-omap-of-to-omap
  (equal (equal (from-omap (to-omap map)) map)
         (mapp map)))

(defruled fix-becomes-from-omap
  (equal (fix map)
         (from-omap (to-omap map))))

(add-to-ruleset to-omap-theory '(fix-becomes-from-omap))

(defrule submap-of-from-omap-from-omap
  (equal (submap (from-omap x) (from-omap y))
         (omap::submap x y))
  :enable to-omap-theory
  :disable from-omap-theory)

(add-to-ruleset to-omap-theory '(submap-of-from-omap-from-omap))

(defrule from-omap-of-omap-update
  (equal (from-omap (omap::update key val omap))
         (update key val (from-omap omap)))
  :enable extensionality)

(add-to-ruleset from-omap-theory '(from-omap-of-omap-update))

(defruled omap-update-becomes-update
  (equal (omap::update key val omap)
         (to-omap (update key val (from-omap omap))))
  :enable omap::extensionality)

(add-to-ruleset from-omap-theory '(from-omap-of-omap-update))

(defruled update-becomes-omap-update
  (equal (update key val map)
         (from-omap (omap::update key val (to-omap map)))))

(add-to-ruleset to-omap-theory '(update-becomes-omap-update))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc map
  :parents (treemap)
  :short "Build a @(see treemap)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the analogue of @(tsee list) to @(see acl2::lists). It is a
       macro which constructs a chain of @(tsee update)s.")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(map key-0 val-1 key-1 val-1 ... key-n val-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

(define map-macro-loop
  (test
   (list true-listp))
  :guard (consp list)
  (cond ((endp (cdr list))
         (er hard? 'map "Missing value for key: ~x0." (first list)))
        ((endp (cddr list))
         (cons 'singleton list))
        (t
         (list 'update
               (first list)
               (second list)
               (map-macro-loop test (cddr list))
               :test test)))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define map-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
            (er hard? 'update "Arguments are ill-formed: ~x0" list))
          ((not (consp rest))
           '(empty))
          (t (let* ((test? (assoc-eq :test alist))
                    (test (if test? (cdr test?) 'equal)))
               (map-macro-loop test rest)))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro map (&rest forms)
  (declare (xargs :guard t))
  (map-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-=
  ((key acl2-numberp)
   val
   (map acl2-number-mapp))
  (mbe :logic (update key val map)
       :exec (acl2-number-tree-update key
                                      (acl2-number-hash key)
                                      val
                                      map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update
                                            keys))))

(define update-eq
  ((key symbolp)
   val
   (map symbol-mapp))
  (mbe :logic (update key val map)
       :exec (symbol-tree-update key
                                 (symbol-hash key)
                                 val
                                 map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update
                                            keys))))
(define update-eql
  ((key eqlablep)
   val
   (map eqlable-mapp))
  (mbe :logic (update key val map)
       :exec (eqlable-tree-update key
                                 (eqlable-hash key)
                                 val
                                 map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            update
                                            keys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-with-hash
  (key
   (hash (unsigned-byte-p 32 hash))
   val
   (map mapp))
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  (mbe :logic (update key val map)
       :exec (tree-update key hash val (fix map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* data::u32-equal
                                            break-abstraction
                                            update))))
