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

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/keys-defs")
(include-book "internal/lookup-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc lookup
  :parents (treemap)
  :short "Lookup the value associated with a key under a @(see treemap)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(lookup key map :default default :test test)")
      (xdoc::desc
        "@(':default') &mdash; optional"
        (xdoc::p
          "The default value when the key is not @(see in) the @(see treemap).
           If no value is provided, the default is @('nil')."))
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro lookup (key map &key (default 'nil) (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(lookup$inline ,key ,map ,default))
    (=     `(lookup-=      ,key ,map ,default))
    (eq    `(lookup-eq     ,key ,map ,default))
    (eql   `(lookup-eql    ,key ,map ,default))))

;;;;;;;;;;;;;;;;;;;;

(defun untranslate-preproc-for-lookup (term wrld)
  (declare (xargs :mode :program))
  (declare (ignore wrld))
  (and (consp term)
       (eq (car term) 'lookup$inline)
       (if (equal (fourth term) ''nil)
           `(lookup ,(second term) ,(third term))
         `(lookup ,(second term) ,(third term) :default ,(fourth term)))))

(make-event
  (let* ((alist (table-alist 'acl2::user-defined-functions-table (w state)))
         (untranslate-preproc (cdr (assoc 'acl2::untranslate-preprocess alist))))
    `(defund lookup-extended-untranslate-preproc (term wrld)
       (declare (xargs :mode :program))
       (or (,untranslate-preproc term wrld)
           (untranslate-preproc-for-lookup term wrld)))))

(table acl2::user-defined-functions-table
       'acl2::untranslate-preprocess
       'lookup-extended-untranslate-preproc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup$inline
  (key
   (map mapp)
   default)
  (mbe :logic (if (treeset::in key (keys map))
                  (tree-lookup key (fix map))
                default)
       :exec (let ((assoc (tree-search-assoc key map)))
               (if (consp (the (or cons null) assoc))
                   (cdr assoc)
                 default)))
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction)))

  ///
  (add-macro-alias lookup lookup$inline))

;;;;;;;;;;;;;;;;;;;;

(defrule lookup-when-map-equiv-congruence
  (implies (equiv map0 map1)
           (equal (lookup key map0 :default default)
                  (lookup key map1 :default default)))
  :rule-classes :congruence
  :enable lookup)

(defruled lookup-with-default-becomes-lookup
  (equal (lookup key map :default default)
         (if (treeset::in key (keys map))
             (lookup key map)
           default))
  :enable (lookup
           keys))

;; TODO: do we want to enable this, and always rewrite to `:default nil`?
;;   This introduces a case split, and at the moment, I don't see an advantage.
(defruled lookup-with-default-becomes-lookup-syntaxp
  (implies (syntaxp (not (equal default ''nil)))
           (equal (lookup key map :default default)
                  (if (treeset::in key (keys map))
                      (lookup key map)
                    default)))
  :by lookup-with-default-becomes-lookup)

;; TODO: should this be a cheap rule?
(defrule lookup-with-default-becomes-lookup-when-in-of-keys-syntaxp
  (implies (and (syntaxp (not (equal default ''nil)))
                (treeset::in key (keys map)))
           (equal (lookup key map :default default)
                  (lookup key map)))
  :by lookup-with-default-becomes-lookup)

(defruled lookup-when-not-in-of-keys
  (implies (not (treeset::in key (keys map)))
           (equal (lookup key map :default default)
                  default))
  :by lookup-with-default-becomes-lookup)

(defrule lookup-when-not-in-of-keys-cheap
  (implies (not (treeset::in key (keys map)))
           (equal (lookup key map :default default)
                  default))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by lookup-when-not-in-of-keys)

(defruled lookup-when-emptyp
  (implies (emptyp map)
           (equal (lookup key map :default default)
                  default))
  :enable (lookup
           lookup-with-default-becomes-lookup-syntaxp))

(defrule lookup-when-emptyp-cheap
  (implies (emptyp map)
           (equal (lookup key map :default default)
                  default))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable lookup-when-emptyp)

(defrule lookup-of-arg1-and-empty
  (equal (lookup key (empty) :default default)
         default)
  :enable lookup-when-emptyp)

(defruled in-of-keys-when-lookup-not-default
  (implies (not (equal (lookup key map :default default) default))
           (treeset::in key (keys map)))
  :enable (lookup
           keys))

(defrule in-of-keys-when-lookup-not-default-forward-chaining
  (implies (not (equal (lookup key map :default default) default))
           (treeset::in key (keys map)))
  :by in-of-keys-when-lookup-not-default)

(defrule in-of-keys-when-lookup-forward-chaining
  (implies (lookup key map)
           (treeset::in key (keys map)))
  :use (:instance in-of-keys-when-lookup-not-default
                  (default nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO to-omap and from-omap theories

(defrule assoc-of-to-omap
  (equal (omap::assoc key (to-omap map))
         (if (treeset::in key (keys map))
             (cons key (lookup key map))
           nil))
  :enable (to-omap
           keys
           lookup
           break-abstraction))

(add-to-ruleset from-omap-theory '(assoc-of-to-omap))

;; TODO: assoc becomes lookup of from-omap

(defruled lookup-becomes-omap-assoc
  (equal (lookup key map :default default)
         (if (omap::assoc key (to-omap map))
             (cdr (omap::assoc key (to-omap map)))
           default)))

(add-to-ruleset to-omap-theory '(lookup-becomes-omap-assoc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head-val ((map mapp))
  :guard (not (emptyp map))
  :parents (treemap)
  :short "Get a value from the nonempty @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, the logical result is @('nil').")
   (xdoc::p
     "This is the value associated with the key returned by the @(tsee
      head-key)."))
  (mbe :logic (lookup (head-key map) map)
       :exec (tree-element->val (tree->head map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            head-key
                                            keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((map mapp))
  :guard (not (emptyp map))
  :returns (mv key value)
  :parents (treemap)
  :short "Get an element of the nonempty @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, the logical result is @('nil').")
   (xdoc::p
     "From a user perspective, this should be viewed as an arbitrary key-value
      pair from the map. For a description of which element this actually
      provides, see @(tsee tree->head)."))
  (mbe :logic (mv (head-key map)
                  (head-val map))
       :exec (let ((head (tree->head map)))
               (mv (tree-element->key head)
                   (tree-element->val head))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* head-key
                                            lookup
                                            keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc lookup?
  :parents (treemap)
  :short "Get the results of @(tsee in) and @(tsee lookup) simultaneously."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$). This is faster than calling the two
       functions independently.")
    (xdoc::p
      "Logically, a call of @('(lookup? key map)') rewrites to
       @('(mv (treeset::in key (keys map)) (lookup key map))').")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(lookup? key map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro lookup? (key map &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(lookup?$inline ,key ,map))
    (=     `(lookup?-=      ,key ,map))
    (eq    `(lookup?-eq     ,key ,map))
    (eql   `(lookup?-eql    ,key ,map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup?$inline
  (key
   (map mapp))
  (mbe :logic (mv (treeset::in key (keys map))
                  (lookup key map))
       :exec (let ((assoc (tree-search-assoc key map)))
               (mv (consp (the (or cons null) assoc))
                   (cdr (the (or cons null) assoc)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction)))

  ///
  (add-macro-fn lookup? lookup?$inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc lookup!
  :parents (treemap)
  :short "Variant of @(tsee lookup) with a stronger guard."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$). This function should be slightly faster
       than @(tsee lookup), but has a guard of @('(in key map)').")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(lookup! key map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro lookup! (key map &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(lookup!$inline ,key ,map))
    (=     `(lookup!-=      ,key ,map))
    (eq    `(lookup!-eq     ,key ,map))
    (eql   `(lookup!-eql    ,key ,map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup!$inline
  (key
   (map mapp))
  :guard (in key map)
  (mbe :logic (lookup key map)
       :exec (tree-search-lookup! key map))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            tree-search-lookup!
                                            break-abstraction)))

  ///
  (add-macro-fn lookup! lookup!$inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-=
  ((key acl2-numberp)
   (map acl2-number-mapp)
   default)
  (mbe :logic (lookup key map :default default)
       :exec (let ((assoc (acl2-number-tree-search-assoc key map)))
               (if (consp (the (or cons null) assoc))
                   (cdr assoc)
                 default)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-acl2-numberp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-eq
  ((key symbolp)
   (map symbol-mapp)
   default)
  (mbe :logic (lookup key map :default default)
       :exec (let ((assoc (symbol-tree-search-assoc key map)))
               (if (consp (the (or cons null) assoc))
                   (cdr assoc)
                 default)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-symbolp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-eql
  ((key eqlablep)
   (map eqlable-mapp)
   default)
  (mbe :logic (lookup key map :default default)
       :exec (let ((assoc (eqlable-tree-search-assoc key map)))
               (if (consp (the (or cons null) assoc))
                   (cdr assoc)
                 default)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-eqlablep
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup?-=
  ((key acl2-numberp)
   (map acl2-number-mapp))
  (mbe :logic (lookup? key map)
       :exec (let ((assoc (acl2-number-tree-search-assoc key map)))
               (mv (consp (the (or cons null) assoc))
                   (cdr (the (or cons null) assoc)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-acl2-numberp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup?-eq
  ((key symbolp)
   (map symbol-mapp))
  (mbe :logic (lookup? key map)
       :exec (let ((assoc (symbol-tree-search-assoc key map)))
               (mv (consp (the (or cons null) assoc))
                   (cdr (the (or cons null) assoc)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-symbolp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup?-eql
  ((key eqlablep)
   (map eqlable-mapp))
  (mbe :logic (lookup? key map)
       :exec (let ((assoc (eqlable-tree-search-assoc key map)))
               (mv (consp (the (or cons null) assoc))
                   (cdr (the (or cons null) assoc)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-eqlablep
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup!-=
  ((key acl2-numberp)
   (map acl2-number-mapp))
  :guard (in key map)
  (mbe :logic (lookup! key map)
       :exec (acl2-number-tree-search-lookup! key map))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-acl2-numberp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup!-eq
  ((key symbolp)
   (map symbol-mapp))
  :guard (in key map)
  (mbe :logic (lookup! key map)
       :exec (symbol-tree-search-lookup! key map))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-symbolp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup!-eql
  ((key eqlablep)
   (map eqlable-mapp))
  :guard (in key map)
  (mbe :logic (lookup! key map)
       :exec (eqlable-tree-search-lookup! key map))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* lookup
                                            keys
                                            map-keys-eqlablep
                                            break-abstraction))))
