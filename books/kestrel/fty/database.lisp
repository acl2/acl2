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
     and operations on those aggregates.")
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

(define flex->name (info)
  :returns (name symbolp)
  :short "Name of a sum, list, alist, transparent sum, set, or omap type,
          given the information associated to the type."
  (b* ((name (cond ((flexsum-p info) (flexsum->name info))
                   ((flexlist-p info) (flexlist->name info))
                   ((flexalist-p info) (flexalist->name info))
                   ((flextranssum-p info) (flextranssum->name info))
                   ((flexset-p info) (flexset->name info))
                   ((flexomap-p info) (flexomap->name info))
                   (t (raise "Internal error: malformed type ~x0." info))))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0." name)))
    name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flex-list->name-list ((infos true-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee flex->name) to lists."
  (cond ((endp infos) nil)
        (t (cons (flex->name (car infos))
                 (flex-list->name-list (cdr infos))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-with-name ((type symbolp) (fty-table alistp))
  :returns info?
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
       ((cons & info) (car fty-table))
       ((unless (flextypes-p info))
        (raise "Internal error: malformed type clique ~x0." info))
       (type-entries (flextypes->types info))
       (info? (type-with-name-loop type type-entries)))
    (or info?
        (type-with-name type (cdr fty-table))))
  :prepwork
  ((define type-with-name-loop ((type symbolp) type-entries)
     :returns info?
     :parents nil
     (b* (((when (atom type-entries)) nil)
          (type-entry (car type-entries))
          (foundp (cond ((flexsum-p type-entry)
                         (eq type (flexsum->name type-entry)))
                        ((flexlist-p type-entry)
                         (eq type (flexlist->name type-entry)))
                        ((flexalist-p type-entry)
                         (eq type (flexalist->name type-entry)))
                        ((flextranssum-p type-entry)
                         (eq type (flextranssum->name type-entry)))
                        ((flexset-p type-entry)
                         (eq type (flexset->name type-entry)))
                        ((flexomap-p type-entry)
                         (eq type (flexomap->name type-entry)))
                        (t nil)))
          ((when foundp) type-entry))
       (type-with-name-loop type (cdr type-entries))))))

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
    "This is similar to @(tsee type-with-name),
     but we check the recognizer instead of the name."))
  (b* (((when (endp fty-table)) nil)
       ((cons & info) (car fty-table))
       ((unless (flextypes-p info))
        (raise "Internal error: malformed type clique ~x0." info))
       (type-entries (flextypes->types info))
       (info? (type-with-recognizer-loop recog type-entries)))
    (or info?
        (type-with-recognizer recog (cdr fty-table))))
  :prepwork
  ((define type-with-recognizer-loop ((recog symbolp) type-entries)
     :returns info?
     :parents nil
     (b* (((when (atom type-entries)) nil)
          (type-entry (car type-entries))
          (foundp (cond ((flexsum-p type-entry)
                         (eq recog (flexsum->pred type-entry)))
                        ((flexlist-p type-entry)
                         (eq recog (flexlist->pred type-entry)))
                        ((flexalist-p type-entry)
                         (eq recog (flexalist->pred type-entry)))
                        ((flextranssum-p type-entry)
                         (eq recog (flextranssum->pred type-entry)))
                        ((flexset-p type-entry)
                         (eq recog (flexset->pred type-entry)))
                        ((flexomap-p type-entry)
                         (eq recog (flexomap->pred type-entry)))
                        (t nil)))
          ((when foundp) type-entry))
       (type-with-recognizer-loop recog (cdr type-entries))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-clique-with-name ((clique symbolp) (fty-table alistp))
  :returns (info? (implies info? (flextypes-p info?)))
  :short "Find, in the FTY table,
          the information for a type clique with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type clique has a unique name,
     we we stop as soon as we find a match.
     We return @('nil') if there is no match."))
  (b* ((info? (cdr (assoc-eq clique fty-table)))
       ((unless (or (flextypes-p info?)
                    (eq info? nil)))
        (raise "Internal error: malformed type clique ~x0." info?)))
    info?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-names-in-cliques-with-names ((cliques symbol-listp)
                                          (fty-table alistp))
  :returns (types symbol-listp)
  :short "Collect, from the FTY table,
          all the type names from the named cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "If any named clique is not found in the table, it is skipped."))
  (b* (((when (endp cliques)) nil)
       (clique (car cliques))
       (info (type-clique-with-name clique fty-table))
       ((unless info)
        (type-names-in-cliques-with-names (cdr cliques) fty-table))
       (infos (flextypes->types info))
       ((unless (true-listp infos))
        (raise "Internal error: malformed clique members ~x0." infos))
       (types (flex-list->name-list infos))
       (more-types (type-names-in-cliques-with-names (cdr cliques) fty-table)))
    (append types more-types)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define option-type->components ((option-type symbolp)
                                 (fty-table alistp))
  :returns (mv (base-type symbolp)
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
  (b* ((info (type-with-name option-type fty-table))
       ((unless info) (mv nil nil))
       ((unless (flexsum-p info)) (mv nil nil))
       ((unless (eq (flexsum->typemacro info) 'defoption))
        (mv nil nil))
       (prods (flexsum->prods info))
       ((unless (and (flexprod-listp prods)
                     (consp prods)
                     (consp (cdr prods))
                     (endp (cddr prods))))
        (raise "Internal error: malformed option products ~x0." prods)
        (mv nil nil))
       (prod1 (first prods))
       (prod2 (second prods))
       (prod (cond ((eq (flexprod->kind prod1) :some) prod1)
                   ((eq (flexprod->kind prod2) :some) prod2)
                   (t (prog2$
                       (raise "Internal error: no :SOME product in ~x0."
                              prods)
                       prod1))))
       (fields (flexprod->fields prod))
       ((unless (and (flexprod-field-listp fields)
                     (= (len fields) 1)))
        (raise "Internal error: malformed option :SOME fields ~x0." fields)
        (mv nil nil))
       (field (car fields))
       (base-recog (flexprod-field->type field))
       ((unless (symbolp base-recog))
        (raise "Internal error: malformed :SOME field recognizer ~x0."
               base-recog)
        (mv nil nil))
       (base-info (type-with-recognizer base-recog fty-table))
       (base-type (flex->name base-info))
       ((unless (symbolp base-type))
        (raise "Internal error: malformed type name ~x0." base-type)
        (mv nil nil))
       (some-accessor (flexprod-field->acc-name field))
       ((unless (symbolp some-accessor))
        (raise "Internal error: malformed accessor name ~x0." some-accessor)
        (mv nil nil)))
    (mv base-type some-accessor)))
