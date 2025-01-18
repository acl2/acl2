; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/database" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ database
  :parents (fty-extensions)
  :short "Extensions for the FTY database."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('[books]/centaur/fty/database.lisp') defines aggregates
     that encode fixtype information in the fixtype table.
     Here we define some extensions of these aggregates,
     e.g. lists of some of those types,
     and we also define operations on those aggregates.")
   (xdoc::p
    "The FTY table is the table of all (fix)types
     (except some built-in ones, such as @('nat')),
     i.e. the table @('flextypes-table').
     The format is defined in @('[books]/centaur/fty/database.lisp').
     It has one entry for each mutually recursive clique of types,
     with singly recursive or non-recursive types
     being in singleton cliques."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist flexprod-field-listp (x)
  :short "Recognize lists of @('flexprod-field-p') values."
  (flexprod-field-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist flexprod-listp (x)
  :short "Recognize lists of @('flexprod') values."
  (flexprod-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;

(define flexprod-list->kind-list ((prods flexprod-listp))
  :returns (kinds true-listp)
  :short "Lift @('flexprod->kind') to lists."
  (cond ((endp prods) nil)
        (t (cons (flexprod->kind (car prods))
                 (flexprod-list->kind-list (cdr prods))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextype->name (flextype)
  :returns (name symbolp)
  :short "Name of a sum, list, alist, transparent sum, set, or omap type,
          given the information associated to the type."
  (b* ((name (cond ((flexsum-p flextype) (flexsum->name flextype))
                   ((flexlist-p flextype) (flexlist->name flextype))
                   ((flexalist-p flextype) (flexalist->name flextype))
                   ((flextranssum-p flextype) (flextranssum->name flextype))
                   ((flexset-p flextype) (flexset->name flextype))
                   ((flexomap-p flextype) (flexomap->name flextype))
                   (t (raise "Internal error: malformed type ~x0." flextype))))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0." name)))
    name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextype-list->name-list ((flextype-list true-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee flextype->name) to lists."
  (cond ((endp flextype-list) nil)
        (t (cons (flextype->name (car flextype-list))
                 (flextype-list->name-list (cdr flextype-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextype-with-name ((name symbolp) (fty-table alistp))
  :returns flextype?
  :short "Find, in the FTY table,
          the information for a type with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type has a unique name, so we stop as soon as we find a match.
     We return @('nil') if there is no match.")
   (xdoc::p
    "Based on the format as described in @(see database),
     we do an outer loop on the entries of the table,
     and for each element an inner loop on
     the elements of the mutually recursive clique
     (which may be a singleton)."))
  (b* (((when (endp fty-table)) nil)
       ((cons & flextypes) (car fty-table))
       ((unless (flextypes-p flextypes))
        (raise "Internal error: malformed type clique ~x0." flextypes))
       (flextype-list (flextypes->types flextypes))
       (flextype? (flextype-with-name-loop name flextype-list)))
    (or flextype?
        (flextype-with-name name (cdr fty-table))))
  :prepwork
  ((define flextype-with-name-loop ((name symbolp) flextype-list)
     :returns flextype?
     :parents nil
     (b* (((when (atom flextype-list)) nil)
          (flextype (car flextype-list))
          (foundp (cond ((flexsum-p flextype)
                         (eq name (flexsum->name flextype)))
                        ((flexlist-p flextype)
                         (eq name (flexlist->name flextype)))
                        ((flexalist-p flextype)
                         (eq name (flexalist->name flextype)))
                        ((flextranssum-p flextype)
                         (eq name (flextranssum->name flextype)))
                        ((flexset-p flextype)
                         (eq name (flexset->name flextype)))
                        ((flexomap-p flextype)
                         (eq name (flexomap->name flextype)))
                        (t nil)))
          ((when foundp) flextype))
       (flextype-with-name-loop name (cdr flextype-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-with-recognizer ((recog symbolp) (fty-table alistp))
  :returns info?
  :short "Look up, in the FTY table,
          the information for a type with a given recognizer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type should have a unique recognizer,
     so we stop as soon as we find a match.
     We return @('nil') if there is no match.")
   (xdoc::p
    "This is similar to @(tsee flextype-with-name),
     but we check the recognizer instead of the name."))
  (b* (((when (endp fty-table)) nil)
       ((cons & clique-info) (car fty-table))
       ((unless (flextypes-p clique-info))
        (raise "Internal error: malformed type clique ~x0." clique-info))
       (type-infos (flextypes->types clique-info))
       (type-info? (type-with-recognizer-loop recog type-infos)))
    (or type-info?
        (type-with-recognizer recog (cdr fty-table))))
  :prepwork
  ((define type-with-recognizer-loop ((recog symbolp) type-infos)
     :returns type-info?
     :parents nil
     (b* (((when (atom type-infos)) nil)
          (type-info (car type-infos))
          (foundp (cond ((flexsum-p type-info)
                         (eq recog (flexsum->pred type-info)))
                        ((flexlist-p type-info)
                         (eq recog (flexlist->pred type-info)))
                        ((flexalist-p type-info)
                         (eq recog (flexalist->pred type-info)))
                        ((flextranssum-p type-info)
                         (eq recog (flextranssum->pred type-info)))
                        ((flexset-p type-info)
                         (eq recog (flexset->pred type-info)))
                        ((flexomap-p type-info)
                         (eq recog (flexomap->pred type-info)))
                        (t nil)))
          ((when foundp) type-info))
       (type-with-recognizer-loop recog (cdr type-infos))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-clique-with-name ((clique-name symbolp) (fty-table alistp))
  :returns (clique-info? (implies clique-info? (flextypes-p clique-info?)))
  :short "Find, in the FTY table,
          the information for a type clique with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type clique has a unique name,
     we we stop as soon as we find a match.
     We return @('nil') if there is no match."))
  (b* ((clique-info? (cdr (assoc-eq clique-name fty-table)))
       ((unless (or (flextypes-p clique-info?)
                    (eq clique-info? nil)))
        (raise "Internal error: malformed type clique ~x0." clique-info?)))
    clique-info?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-names-in-cliques-with-names ((clique-names symbol-listp)
                                          (fty-table alistp))
  :returns (type-names symbol-listp)
  :short "Collect, from the FTY table,
          all the type names from the named cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "If any named clique is not found in the table, it is skipped."))
  (b* (((when (endp clique-names)) nil)
       (clique-name (car clique-names))
       (clique-info (type-clique-with-name clique-name fty-table))
       ((unless clique-info)
        (type-names-in-cliques-with-names (cdr clique-names) fty-table))
       (type-infos (flextypes->types clique-info))
       ((unless (true-listp type-infos))
        (raise "Internal error: malformed clique members ~x0." type-infos))
       (type-names (flextype-list->name-list type-infos))
       (more-type-names (type-names-in-cliques-with-names (cdr clique-names)
                                                          fty-table)))
    (append type-names more-type-names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define option-type->components ((option-type-name symbolp)
                                 (fty-table alistp))
  :returns (mv (base-type-name symbolp)
               (some-accessor symbolp))
  :short "Components of an option type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the name of the base type,
     and the name of the accessor for the @(':some') case.
     These are both @('nil') if
     the given option type name does not resolve to an actual option type.")
   (xdoc::p
    "We look up the information for the option type.
     We find the product for the @(':some') summand.
     We obtain the field recognizer and accessor.
     We use the recognizer to look up the base type."))
  (b* ((type-info (flextype-with-name option-type-name fty-table))
       ((unless type-info) (mv nil nil))
       ((unless (flexsum-p type-info)) (mv nil nil))
       ((unless (eq (flexsum->typemacro type-info) 'defoption))
        (mv nil nil))
       (prod-infos (flexsum->prods type-info))
       ((unless (and (flexprod-listp prod-infos)
                     (consp prod-infos)
                     (consp (cdr prod-infos))
                     (endp (cddr prod-infos))))
        (raise "Internal error: malformed option products ~x0." prod-infos)
        (mv nil nil))
       (prod-info1 (first prod-infos))
       (prod-info2 (second prod-infos))
       (prod-info (cond ((eq (flexprod->kind prod-info1) :some) prod-info1)
                        ((eq (flexprod->kind prod-info2) :some) prod-info2)
                        (t (prog2$
                            (raise "Internal error: no :SOME product in ~x0."
                                   prod-infos)
                            prod-info1))))
       (field-infos (flexprod->fields prod-info))
       ((unless (and (flexprod-field-listp field-infos)
                     (= (len field-infos) 1)))
        (raise "Internal error: malformed option :SOME fields ~x0." field-infos)
        (mv nil nil))
       (field-info (car field-infos))
       (base-recog (flexprod-field->type field-info))
       ((unless (symbolp base-recog))
        (raise "Internal error: malformed :SOME field recognizer ~x0."
               base-recog)
        (mv nil nil))
       (base-info (type-with-recognizer base-recog fty-table))
       (base-type-name (flextype->name base-info))
       ((unless (symbolp base-type-name))
        (raise "Internal error: malformed type name ~x0." base-type-name)
        (mv nil nil))
       (some-accessor (flexprod-field->acc-name field-info))
       ((unless (symbolp some-accessor))
        (raise "Internal error: malformed accessor name ~x0." some-accessor)
        (mv nil nil)))
    (mv base-type-name some-accessor)))
