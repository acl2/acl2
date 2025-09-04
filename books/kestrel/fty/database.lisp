; FTY Library
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

;;;;;;;;;;;;;;;;;;;;

(define flexprod-field-list->name-list ((fields flexprod-field-listp))
  :returns (names symbol-listp)
  :short "Lift @('flexprod-field->name') to lists."
  (b* (((when (endp fields)) nil)
       (name (flexprod-field->name (car fields)))
       ((unless (symbolp name))
        (raise "Internal error: malformed field name ~x0." name))
       (names (flexprod-field-list->name-list (cdr fields))))
    (cons name names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist flexprod-listp (x)
  :short "Recognize lists of @('flexprod-p') values."
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

(define flextype->fix (flextype)
  :returns (name symbolp)
  :short "Name of the fix function for a sum, list, alist, transparent sum,
          set, or omap type, given the information associated to the type."
  (b* ((name (cond ((flexsum-p flextype) (flexsum->fix flextype))
                   ((flexlist-p flextype) (flexlist->fix flextype))
                   ((flexalist-p flextype) (flexalist->fix flextype))
                   ((flextranssum-p flextype) (flextranssum->fix flextype))
                   ((flexset-p flextype) (flexset->fix flextype))
                   ((flexomap-p flextype) (flexomap->fix flextype))
                   (t (raise "Internal error: malformed type ~x0." flextype))))
       ((unless (symbolp name))
        (raise "Internal error: malformed fix function name ~x0." name)))
    name))

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

(define flextype-with-recognizer ((recog symbolp) (fty-table alistp))
  :returns flextype?
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
       ((cons & flextypes) (car fty-table))
       ((unless (flextypes-p flextypes))
        (raise "Internal error: malformed type clique ~x0." flextypes))
       (flextype-list (flextypes->types flextypes))
       (flextype? (flextype-with-recognizer-loop recog flextype-list)))
    (or flextype?
        (flextype-with-recognizer recog (cdr fty-table))))
  :prepwork
  ((define flextype-with-recognizer-loop ((recog symbolp) flextype-list)
     :returns flextype?
     :parents nil
     (b* (((when (atom flextype-list)) nil)
          (flextype (car flextype-list))
          (foundp (cond ((flexsum-p flextype)
                         (eq recog (flexsum->pred flextype)))
                        ((flexlist-p flextype)
                         (eq recog (flexlist->pred flextype)))
                        ((flexalist-p flextype)
                         (eq recog (flexalist->pred flextype)))
                        ((flextranssum-p flextype)
                         (eq recog (flextranssum->pred flextype)))
                        ((flexset-p flextype)
                         (eq recog (flexset->pred flextype)))
                        ((flexomap-p flextype)
                         (eq recog (flexomap->pred flextype)))
                        (t nil)))
          ((when foundp) flextype))
       (flextype-with-recognizer-loop recog (cdr flextype-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextypes-with-name ((name symbolp) (fty-table alistp))
  :returns (flextypes? (implies flextypes? (flextypes-p flextypes?)))
  :short "Find, in the FTY table,
          the information for a type clique with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type clique has a unique name,
     we we stop as soon as we find a match.
     We return @('nil') if there is no match."))
  (b* ((flextypes? (cdr (assoc-eq name fty-table)))
       ((unless (or (flextypes-p flextypes?)
                    (eq flextypes? nil)))
        (raise "Internal error: malformed type clique ~x0." flextypes?)))
    flextypes?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextype-names-in-flextypes-with-names ((flextypes-names symbol-listp)
                                                (fty-table alistp))
  :returns (flextype-names symbol-listp)
  :short "Collect, from the FTY table,
          all the type names from the named cliques."
  :long
  (xdoc::topstring
   (xdoc::p
    "If any named clique is not found in the table, it is skipped."))
  (b* (((when (endp flextypes-names)) nil)
       (flextypes-name (car flextypes-names))
       (flextypes (flextypes-with-name flextypes-name fty-table))
       ((unless flextypes)
        (flextype-names-in-flextypes-with-names (cdr flextypes-names)
                                                fty-table))
       (flextype-list (flextypes->types flextypes))
       ((unless (true-listp flextype-list))
        (raise "Internal error: malformed clique members ~x0." flextype-list))
       (flextype-names (flextype-list->name-list flextype-list))
       (more-flextype-names
        (flextype-names-in-flextypes-with-names (cdr flextypes-names)
                                                fty-table)))
    (append flextype-names more-flextype-names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flextypes-containing-flextype ((name symbolp) (fty-table alistp))
  :returns flextype?
  :short "Find, in the FTY table,
          the information for a type clique
          containing a type of the given name."
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
       (foundp (flextypes-containing-flextype-loop name flextype-list)))
    (if foundp
        flextypes
      (flextypes-containing-flextype name (cdr fty-table))))
  :prepwork
  ((define flextypes-containing-flextype-loop ((name symbolp) flextype-list)
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
                        (t nil))))
       (or foundp
           (flextypes-containing-flextype-loop name (cdr flextype-list)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define components-of-flexoption-with-name ((name symbolp) (fty-table alistp))
  :returns (mv (base-name symbolp)
               (some-accessor symbolp))
  :short "Components of a named option type."
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
  (b* ((flextype (flextype-with-name name fty-table))
       ((unless flextype) (mv nil nil))
       ((unless (flexsum-p flextype)) (mv nil nil))
       ((unless (eq (flexsum->typemacro flextype) 'defoption))
        (mv nil nil))
       (flexprod-list (flexsum->prods flextype))
       ((unless (and (flexprod-listp flexprod-list)
                     (consp flexprod-list)
                     (consp (cdr flexprod-list))
                     (endp (cddr flexprod-list))))
        (raise "Internal error: malformed option products ~x0." flexprod-list)
        (mv nil nil))
       (flexprod1 (first flexprod-list))
       (flexprod2 (second flexprod-list))
       (flexprod (cond ((eq (flexprod->kind flexprod1) :some) flexprod1)
                       ((eq (flexprod->kind flexprod2) :some) flexprod2)
                       (t (prog2$
                           (raise "Internal error: no :SOME product in ~x0."
                                  flexprod-list)
                           flexprod1))))
       (flexfield-list (flexprod->fields flexprod))
       ((unless (and (flexprod-field-listp flexfield-list)
                     (= (len flexfield-list) 1)))
        (raise "Internal error: malformed option :SOME fields ~x0."
               flexfield-list)
        (mv nil nil))
       (flexfield (car flexfield-list))
       (base-recog (flexprod-field->type flexfield))
       ((unless (symbolp base-recog))
        (raise "Internal error: malformed :SOME field recognizer ~x0."
               base-recog)
        (mv nil nil))
       (base-flextype (flextype-with-recognizer base-recog fty-table))
       (base-name (flextype->name base-flextype))
       ((unless (symbolp base-name))
        (raise "Internal error: malformed type name ~x0." base-name)
        (mv nil nil))
       (some-accessor (flexprod-field->acc-name flexfield))
       ((unless (symbolp some-accessor))
        (raise "Internal error: malformed accessor name ~x0." some-accessor)
        (mv nil nil)))
    (mv base-name some-accessor)))
