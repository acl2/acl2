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

(include-book "internal/tree-defs")
(include-book "internal/keys-defs")
(include-book "internal/lookup-defs")
(include-book "map-defs")
(include-book "keys-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "map"))

;; We include keys non-locally since `in` simply rewrites to `keys`.
(include-book "keys")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc in
  :parents (treemap)
  :short "Determine if a key is bound under a @(see treemap)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$).")
    (xdoc::p
      "This is <i>not</i> the logical normal form used by this library.
       Instead, we rewrite @('(in key map)') to
       @('(treeset::in key (keys map))').")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(in x map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the map consists of keys
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro in (key map &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(in$inline ,key ,map))
    (=     `(in-=      ,key ,map))
    (eq    `(in-eq     ,key ,map))
    (eql   `(in-eql    ,key ,map))))

;;;;;;;;;;;;;;;;;;;;

(define in$inline
  (key
   (map mapp))
  (mbe :logic (treeset::in key (keys map))
       :exec (consp (the (or cons null) (tree-search-assoc key map))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction)))

  ///
  (add-macro-fn in in$inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-=
  ((key acl2-numberp)
   (map acl2-number-mapp))
  (mbe :logic (in key map)
       :exec (consp (the (or cons null) (acl2-number-tree-search-assoc key map))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-acl2-numberp
                                            keys))))

(define in-eq
  ((key symbolp)
   (map symbol-mapp))
  (mbe :logic (in key map)
       :exec (consp (the (or cons null) (symbol-tree-search-assoc key map))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-symbolp
                                            keys))))

(define in-eql
  ((key eqlablep)
   (map eqlable-mapp))
  (mbe :logic (in key map)
       :exec (consp (the (or cons null) (eqlable-tree-search-assoc key map))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-eqlablep
                                            keys))))
