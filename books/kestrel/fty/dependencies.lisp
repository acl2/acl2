; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "centaur/depgraph/toposort" :dir :system)

(include-book "database")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable tau-system)))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ dependencies
  :parents (fty-extensions)
  :short "Collect type dependencies."
  :long
  (xdoc::topstring
   (xdoc::p
     "The main functionality is provided by @(tsee depgraph),
      which builds a directed acyclic graph which can be used with the "
     (xdoc::seetopic "depgraph::depgraph" "depgraph")
     " package."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-of-flextypes-containing-recognizer ((recog symbolp)
                                                 (fty-table alistp))
  :returns (flextypes-name? symbolp)
  :short "Get the name of a flextypes object which contains a type
          corresponding to the recognizer."
  :long
  (xdoc::topstring
   (xdoc::p
     "If no such flextypes object exists, returns @('nil')."))
  (b* ((flextype (flextype-with-recognizer recog fty-table))
       ((unless flextype)
        nil)
       (name (flextype->name flextype))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0."
               name))
       (flextypes (flextypes-containing-flextype name fty-table))
       ((unless (flextypes-p flextypes))
        (raise "Internal error: no flextypes containing type ~x0." name))
       (name (flextypes->name flextypes))
       ((unless (symbolp name))
        (raise "Internal error: malformed flextypes name ~x0." name)))
    name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flexprod-fields-direct-dependencies
  ((flexprod-fields flexprod-field-listp)
   (fty-table alistp))
  :returns (dependencies symbol-listp)
  (if (consp flexprod-fields)
      (b* ((recog (flexprod-field->type (first flexprod-fields)))
           ((unless (symbolp recog))
            (raise "Internal error: malformed type recognizer ~x0."
                   recog))
           (name? (name-of-flextypes-containing-recognizer recog fty-table))
           (names
             (flexprod-fields-direct-dependencies (rest flexprod-fields)
                                                  fty-table)))
        (if (or (not name?)
                (member-eq name? names))
            names
          (cons name? names)))
    nil)
  ///
  (more-returns
   (dependencies true-listp :rule-classes :type-prescription)))

(define flexprods-direct-dependencies ((flexprods flexprod-listp)
                                       (fty-table alistp))
  :returns (dependencies symbol-listp)
  (if (consp flexprods)
      (b* ((fields (flexprod->fields (first flexprods)))
           ((unless (flexprod-field-listp fields))
            (raise "Internal error: malformed flexprod field list ~x0."
                   fields)))
        (union-eq (flexprod-fields-direct-dependencies fields fty-table)
                  (flexprods-direct-dependencies (rest flexprods) fty-table)))
    nil)
  :verify-guards nil ;; Verified below
  ///
  (more-returns
   (dependencies true-listp :rule-classes :type-prescription))
  (verify-guards flexprods-direct-dependencies))

(define flextype-direct-dependencies (flextype (fty-table alistp))
  :returns (dependencies symbol-listp)
  (cond ((flexsum-p flextype)
         (b* ((prods (flexsum->prods flextype))
              ((unless (flexprod-listp prods))
               (raise "Internal error: malformed flexprod list ~x0."
                      prods)))
           (flexprods-direct-dependencies prods fty-table)))
        ((flexlist-p flextype)
         (b* ((recog (flexlist->elt-type flextype))
              ((unless (symbolp recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      recog))
              (clique-name?
                (name-of-flextypes-containing-recognizer recog fty-table)))
           (if clique-name?
               (list clique-name?)
             nil)))
        ((flexset-p flextype)
         (b* ((recog (flexset->elt-type flextype))
              ((unless (symbolp recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      recog))
              (clique-name?
                (name-of-flextypes-containing-recognizer recog fty-table)))
           (if clique-name?
               (list clique-name?)
             nil)))
        ((flexalist-p flextype)
         (b* ((key-recog (flexalist->key-type flextype))
              ((unless (symbolp key-recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      key-recog))
              (key-clique-name?
                (name-of-flextypes-containing-recognizer key-recog fty-table))
              (val-recog (flexalist->val-type flextype))
              ((unless (symbolp val-recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      key-recog))
              (val-clique-name?
                (name-of-flextypes-containing-recognizer val-recog fty-table)))
           (if key-clique-name?
               (cons key-clique-name?
                     (if val-clique-name?
                         (list val-clique-name?)
                       nil))
             (if val-clique-name?
                 (list val-clique-name?)
               nil))))
        ((flexomap-p flextype)
         (b* ((key-recog (flexomap->key-type flextype))
              ((unless (symbolp key-recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      key-recog))
              (key-clique-name?
                (name-of-flextypes-containing-recognizer key-recog fty-table))
              (val-recog (flexomap->val-type flextype))
              ((unless (symbolp val-recog))
               (raise "Internal error: malformed type recognizer ~x0."
                      key-recog))
              (val-clique-name?
                (name-of-flextypes-containing-recognizer val-recog fty-table)))
           (if key-clique-name?
               (cons key-clique-name?
                     (if val-clique-name?
                         (list val-clique-name?)
                       nil))
             (if val-clique-name?
                 (list val-clique-name?)
               nil))))
        (t (raise "Internal error: unsupported type ~x0." flextype))))

(define flextype-list-direct-dependencies (flextype-list (fty-table alistp))
  :returns (dependencies symbol-listp)
  (if (consp flextype-list)
      (union-eq
        (flextype-direct-dependencies (first flextype-list) fty-table)
        (flextype-list-direct-dependencies (rest flextype-list) fty-table))
    nil))

(define flextypes-direct-dependencies ((flextypes flextypes-p)
                                       (fty-table alistp))
  :returns (dependencies symbol-listp)
  (b* ((flextype-list (flextypes->types flextypes))
       ((unless (true-listp flextype-list))
        (raise "Internal error: malformed flextype-list ~x0" flextype-list))
       (dependencies
         (flextype-list-direct-dependencies flextype-list fty-table)))
    (remove-eq (flextypes->name flextypes) dependencies)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define depgraph ((name symbolp) (fty-table alistp))
  :returns (depgraph alistp)
  :short "Build a directed acyclic graph of type (clique) dependencies."
  :long
  (xdoc::topstring
   (xdoc::p
     "The graph is represented as an "
     (xdoc::seetopic "alistp" "alist")
     " from symbols to lists of symbols. Each symbol is the name of a
      standalone type or of a type clique."))
  (depgraph-loop (list name) nil fty-table (1- (expt 2 acl2::*fixnat-bits*)))

  :prepwork
  (;; TODO: get rid of count argument
   (define depgraph-loop ((names symbol-listp)
                          (depgraph alistp)
                          (fty-table alistp)
                          (count (unsigned-byte-p acl2::*fixnat-bits* count)))
     (declare (xargs :split-types t)
              (type #.acl2::*fixnat-type* count))
     :parents nil
     :returns (new-depgraph alistp)
     (b* (((when (or (endp names)
                     (= (mbe :logic (nfix count)
                             :exec (the #.acl2::*fixnat-type* count))
                        0)))
           (mbe :logic (if (alistp depgraph) depgraph nil)
                :exec depgraph))
          (name (first names))
          ((when (assoc-eq name depgraph))
           (depgraph-loop (rest names) depgraph fty-table (1- count)))
          (flextypes (flextypes-with-name name fty-table))
          ((unless (flextypes-p flextypes))
           (raise "Internal error: type does not have a corresponding flextypes
                   entry ~x0."
                  name))
          (dependencies (flextypes-direct-dependencies flextypes fty-table))
          (depgraph (acons name dependencies depgraph)))
       (depgraph-loop (append dependencies (rest names))
                      depgraph
                      fty-table
                      (1- count)))
     :measure (nfix count)
     :guard-hints (("Goal" :in-theory (enable nfix)))
     :hints (("Goal" :in-theory (enable nfix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topo-dependencies ((name symbolp) (fty-table alistp))
  :returns (dependencies symbol-listp)
  :short "A topological ordering of type (clique) based on type dependencies."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the topological ordering of @(tsee depgraph), obtained via
      @(depgraph::toposort)."))
  (b* ((depgraph (depgraph name fty-table))
       ((mv successp result)
        (depgraph::toposort depgraph))
       ((unless successp)
        (raise "Internal error: assembled graph is not a DAG ~x0" depgraph))
       ((unless (symbol-listp result))
        (raise "Internal error: result is not a symbol-list ~x0" result)))
    result))
