; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(progn
  (verify-termination fty::flexprod-field-p)
  (verify-termination fty::flexprod-field->acc-name$inline)
  (verify-termination fty::flexprod-field->type$inline))

(progn
  (verify-termination fty::flexprod-p)
  (verify-termination fty::flexprod->kind$inline)
  (verify-termination fty::flexprod->fields$inline)
  (verify-termination fty::flexprod->type-name$inline))

(progn
  (verify-termination fty::flexsum-p)
  (verify-termination fty::flexsum->name$inline)
  (verify-termination fty::flexsum->pred$inline)
  (verify-termination fty::flexsum->count$inline)
  (verify-termination fty::flexsum->case$inline)
  (verify-termination fty::flexsum->prods$inline)
  (verify-termination fty::flexsum->recp$inline)
  (verify-termination fty::flexsum->typemacro$inline))

(progn
  (verify-termination fty::flexlist-p)
  (verify-termination fty::flexlist->name$inline)
  (verify-termination fty::flexlist->pred$inline)
  (verify-termination fty::flexlist->count$inline)
  (verify-termination fty::flexlist->elt-type$inline)
  (verify-termination fty::flexlist->recp$inline))

(progn
  (verify-termination fty::flexalist-p)
  (verify-termination fty::flexalist->name$inline)
  (verify-termination fty::flexalist->pred$inline))

(progn
  (verify-termination fty::flextranssum-p)
  (verify-termination fty::flextranssum->name$inline)
  (verify-termination fty::flextranssum->pred$inline))

(progn
  (verify-termination fty::flexset-p)
  (verify-termination fty::flexset->name$inline)
  (verify-termination fty::flexset->pred$inline))

(progn
  (verify-termination fty::flexomap-p)
  (verify-termination fty::flexomap->name$inline)
  (verify-termination fty::flexomap->pred$inline)
  (verify-termination fty::flexomap->count$inline)
  (verify-termination fty::flexomap->val-type$inline)
  (verify-termination fty::flexomap->recp$inline))

(progn
  (verify-termination fty::flextypes-p)
  (verify-termination fty::flextypes->name$inline)
  (verify-termination fty::flextypes->types$inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist fty::flexprod-field-listp (acl2::x)
  (fty::flexprod-field-p acl2::x)
  :true-listp t
  :elementp-of-nil nil)

(std::deflist fty::flexprod-listp (acl2::x)
  (fty::flexprod-p acl2::x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;

(define fty::flexprod-list->kind-list ((prods fty::flexprod-listp))
  :returns (kinds true-listp)
  (cond ((endp prods) nil)
        (t (cons (fty::flexprod->kind (car prods))
                 (fty::flexprod-list->kind-list (cdr prods))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defpred

 :items

 ((xdoc::evmac-topic-implementation-item-input "suffix")

  (xdoc::evmac-topic-implementation-item-input "default")

  (xdoc::evmac-topic-implementation-item-input "override")

  "@('overrides') is an alist representation of the @(':override') input.
   With reference to the documentation page of @(tsee defpred):
   for each element @('<type> <term>') in @(':override'),
   this alist has an element @('(cons <type> <term>)');
   for each element @('<type> <kind> <term>') in @(':override'),
   this alist has an element @('(cons (cons <type> <kind>) <term>)')."

  "@('fty-table') is the alist of the table of all (fix)types
   (except some built-in ones, such as @('nat')),
   i.e. the table @('fty::flextypes-table').
   The format is defined in @('[books]/centaur/fty/database.lisp').
   It has one entry for each mutually recursive clique of types,
   with singly recursive or non-recursive types
   being in singleton cliques."

  "@('types') is a list (in no particular order)
   of all the type names for which predicates are generated."

  "@('type') is an element of @('types') explained above."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defpred-library-extensions
  :short "Some FTY library extensions for @(tsee defpred)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These should be moved to the FTY library eventually.
     Perhaps there is already something like that there,
     but it may be in program mode."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-type-with-name ((type symbolp) (fty-table alistp))
  :returns info?
  :short "Find, in the FTY table,
          the information for a type with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type has a unique name, so we stop as soon as we find a match.
     We return @('nil') if there is no match.")
   (xdoc::p
    "Based on the format as described in @(see defpred-implementation),
     we do an outer loop on the entries of the table,
     and for each element an inner loop on
     the elements of the mutually recursive clique
     (which may be a singleton)."))
  (b* (((when (endp fty-table)) nil)
       ((cons & info) (car fty-table))
       ((unless (fty::flextypes-p info))
        (raise "Internal error: malformed type clique ~x0." info))
       (type-entries (fty::flextypes->types info))
       (info? (defpred-type-with-name-loop type type-entries)))
    (or info?
        (defpred-type-with-name type (cdr fty-table))))
  :prepwork
  ((define defpred-type-with-name-loop ((type symbolp) type-entries)
     :returns info?
     :parents nil
     (b* (((when (atom type-entries)) nil)
          (type-entry (car type-entries))
          (foundp (cond ((fty::flexsum-p type-entry)
                         (eq type (fty::flexsum->name type-entry)))
                        ((fty::flexlist-p type-entry)
                         (eq type (fty::flexlist->name type-entry)))
                        ((fty::flexalist-p type-entry)
                         (eq type (fty::flexalist->name type-entry)))
                        ((fty::flextranssum-p type-entry)
                         (eq type (fty::flextranssum->name type-entry)))
                        ((fty::flexset-p type-entry)
                         (eq type (fty::flexset->name type-entry)))
                        ((fty::flexomap-p type-entry)
                         (eq type (fty::flexomap->name type-entry)))
                        (t nil)))
          ((when foundp) type-entry))
       (defpred-type-with-name-loop type (cdr type-entries))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-type-with-recognizer ((recog symbolp) (fty-table alistp))
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
    "This is similar to @(tsee defpred-type-with-name),
     but we check the recognizer instead of the name."))
  (b* (((when (endp fty-table)) nil)
       ((cons & info) (car fty-table))
       ((unless (fty::flextypes-p info))
        (raise "Internal error: malformed type clique ~x0." info))
       (type-entries (fty::flextypes->types info))
       (info? (defpred-type-with-recognizer-loop recog type-entries)))
    (or info?
        (defpred-type-with-recognizer recog (cdr fty-table))))
  :prepwork
  ((define defpred-type-with-recognizer-loop ((recog symbolp) type-entries)
     :returns info?
     :parents nil
     (b* (((when (atom type-entries)) nil)
          (type-entry (car type-entries))
          (foundp (cond ((fty::flexsum-p type-entry)
                         (eq recog (fty::flexsum->pred type-entry)))
                        ((fty::flexlist-p type-entry)
                         (eq recog (fty::flexlist->pred type-entry)))
                        ((fty::flexalist-p type-entry)
                         (eq recog (fty::flexalist->pred type-entry)))
                        ((fty::flextranssum-p type-entry)
                         (eq recog (fty::flextranssum->pred type-entry)))
                        ((fty::flexset-p type-entry)
                         (eq recog (fty::flexset->pred type-entry)))
                        ((fty::flexomap-p type-entry)
                         (eq recog (fty::flexomap->pred type-entry)))
                        (t nil)))
          ((when foundp) type-entry))
       (defpred-type-with-recognizer-loop recog (cdr type-entries))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-flex->name (info)
  :returns (name symbolp)
  :short "Name of a sum, list, alist, transparent sum, set, or omap type,
          given the information associated to the type."
  (b* ((name (cond ((fty::flexsum-p info) (fty::flexsum->name info))
                   ((fty::flexlist-p info) (fty::flexlist->name info))
                   ((fty::flexalist-p info) (fty::flexalist->name info))
                   ((fty::flextranssum-p info) (fty::flextranssum->name info))
                   ((fty::flexset-p info) (fty::flexset->name info))
                   ((fty::flexomap-p info) (fty::flexomap->name info))
                   (t (raise "Internal error: malformed type ~x0." info))))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0." name)))
    name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-flex-list->name-list ((infos true-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee defpred-flex->name) to lists."
  (cond ((endp infos) nil)
        (t (cons (defpred-flex->name (car infos))
                 (defpred-flex-list->name-list (cdr infos))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-option-type->components ((option-type symbolp)
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
  (b* ((info (defpred-type-with-name option-type fty-table))
       ((unless info) (mv nil nil))
       ((unless (fty::flexsum-p info)) (mv nil nil))
       ((unless (eq (fty::flexsum->typemacro info) 'fty::defoption))
        (mv nil nil))
       (prods (fty::flexsum->prods info))
       ((unless (and (fty::flexprod-listp prods)
                     (consp prods)
                     (consp (cdr prods))
                     (endp (cddr prods))))
        (raise "Internal error: malformed option products ~x0." prods)
        (mv nil nil))
       (prod1 (first prods))
       (prod2 (second prods))
       (prod (cond ((eq (fty::flexprod->kind prod1) :some) prod1)
                   ((eq (fty::flexprod->kind prod2) :some) prod2)
                   (t (prog2$
                       (raise "Internal error: no :SOME product in ~x0."
                              prods)
                       prod1))))
       (fields (fty::flexprod->fields prod))
       ((unless (and (fty::flexprod-field-listp fields)
                     (= (len fields) 1)))
        (raise "Internal error: malformed option :SOME fields ~x0." fields)
        (mv nil nil))
       (field (car fields))
       (base-recog (fty::flexprod-field->type field))
       ((unless (symbolp base-recog))
        (raise "Internal error: malformed :SOME field recognizer ~x0."
               base-recog)
        (mv nil nil))
       (base-info (defpred-type-with-recognizer base-recog fty-table))
       (base-type (defpred-flex->name base-info))
       ((unless (symbolp base-type))
        (raise "Internal error: malformed type name ~x0." base-type)
        (mv nil nil))
       (some-accessor (fty::flexprod-field->acc-name field))
       ((unless (symbolp some-accessor))
        (raise "Internal error: malformed accessor name ~x0." some-accessor)
        (mv nil nil)))
    (mv base-type some-accessor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-type-clique-with-name ((clique symbolp) (fty-table alistp))
  :returns (info? (implies info? (fty::flextypes-p info?)))
  :short "Find, in the FTY table,
          the information for a type clique with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each type clique has a unique name,
     we we stop as soon as we find a match.
     We return @('nil') if there is no match."))
  (b* ((info? (cdr (assoc-eq clique fty-table)))
       ((unless (or (fty::flextypes-p info?)
                    (eq info? nil)))
        (raise "Internal error: malformed type clique ~x0." info?)))
    info?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-type-names-in-cliques-with-names ((cliques symbol-listp)
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
       (info (defpred-type-clique-with-name clique fty-table))
       ((unless info)
        (defpred-type-names-in-cliques-with-names (cdr cliques) fty-table))
       (infos (fty::flextypes->types info))
       ((unless (true-listp infos))
        (raise "Internal error: malformed clique members ~x0." infos))
       (types (defpred-flex-list->name-list infos))
       (more-types (defpred-type-names-in-cliques-with-names
                     (cdr cliques) fty-table)))
    (append types more-types)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing defpred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-process-override (override (fty-table alistp))
  :returns (mv erp (overrides alistp))
  :short "Process the @(':override') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(':override') input must be a list.
     We go through each eleemnt,
     which must be a 2-tuple or a 3-tuple.
     In that tuple, the first element must be always a type name,
     which we must find in the FTY table.
     Both sum and product types are stored in the table as sum types,
     but the data structure indicates the type macro,
     i.e. whether it is a @(tsee fty::defprod) or @(tsee fty::deftagsum);
     we use that to distinguish them."))
  (b* (((reterr) nil)
       ((unless (true-listp override))
        (reterr (msg "The :OVERRIDE input must be a list, ~
                      but it is ~x0 instead."
                     override))))
    (defpred-process-override-loop override fty-table))
  :prepwork
  ((define defpred-process-override-loop ((override true-listp)
                                          (fty-table alistp))
     :returns (mv erp (overrides alistp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp override)) (retok nil))
          (ovrd (car override))
          ((unless (or (std::tuplep 2 ovrd)
                       (std::tuplep 3 ovrd)))
           (reterr (msg "Every element of the :OVERRIDE list ~
                         must be a list of 2 or 3 elements, ~
                         but the element ~x0 is not."
                        ovrd)))
          (type (car ovrd))
          (term (car (last ovrd)))
          ((unless (symbolp type))
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be a symbol, ~
                         but ~x0 is not."
                        type)))
          (info (defpred-type-with-name type fty-table))
          ((unless info)
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be the name of a type, ~
                         but ~x0 is not."
                        type)))
          ((unless (fty::flexsum-p info))
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be the name of a product or sum type, ~
                         but ~x0 is not."
                        type)))
          (typemacro (fty::flexsum->typemacro info))
          ((unless (member-eq typemacro (list 'fty::defprod 'fty::deftagsum)))
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be the name of a product or sum type, ~
                         but ~x0 is not."
                        type)))
          ((erp key val)
           (if (= (len ovrd) 2)
               (mv nil type term)
             (b* (((reterr) nil nil)
                  (kind (cadr ovrd))
                  ((unless (keywordp kind))
                   (reterr (msg "The second element of ~
                                 every element of the :OVERRIDE list ~
                                 that is a 3-tuple ~
                                 must be a keyword, ~
                                 but ~x0 is not."
                                kind)))
                  (prods (fty::flexsum->prods info))
                  ((unless (fty::flexprod-listp prods))
                   (raise "Internal error: malformed summands ~x0." prods)
                   (reterr t))
                  ((unless (member-eq kind
                                      (fty::flexprod-list->kind-list prods)))
                   (reterr (msg "The kind ~x0 that accompanies ~
                                 the type ~x1 in the :OVERRIDE list ~
                                 is not one of the kinds of that sum type."
                                kind type))))
               (retok (cons type kind) term))))
          ((erp alist)
           (defpred-process-override-loop (cdr override) fty-table)))
       (retok (acons key val alist)))
     :prepwork ((local (in-theory (enable acons))))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defpred-allowed-options*
  :short "Keyword options accepted by @(tsee defpred)."
  '(:default
    :override))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-process-inputs ((args true-listp) (fty-table alistp))
  :returns (mv erp
               (suffix symbolp)
               (default booleanp)
               (overrides alistp))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil)
       ((mv erp suffix options)
        (partition-rest-and-keyword-args args *defpred-allowed-options*))
       ((when (or erp
                  (not (consp suffix))
                  (not (endp (cdr suffix)))))
        (reterr (msg "The inputs must be the suffix name ~
                      followed by the options ~&0."
                     *defpred-allowed-options*)))
       (suffix (car suffix))
       ((unless (symbolp suffix))
        (reterr (msg "The SUFFIX input must be a symbol, ~
                      but it is ~x0 instead."
                     suffix)))
       (default-option (assoc-eq :default options))
       ((unless (consp default-option))
        (reterr (msg "The :DEFAULT input must be supllied.")))
       (default (cdr default-option))
       ((unless (booleanp default))
        (reterr (msg "The :DEFAULT input must be a boolean, ~
                      but it is ~x0 instead."
                     default)))
       (override-option (assoc-eq :override options))
       (override (if override-option
                     (cdr override-option)
                   nil))
       ((erp overrides) (defpred-process-override override fty-table)))
    (retok suffix default overrides))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defpred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-name ((type symbolp) (suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of a predicate."
  (packn-pos (list type '- suffix) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod-conjuncts ((type symbolp)
                                    (fields fty::flexprod-field-listp)
                                    (types symbol-listp)
                                    (suffix symbolp)
                                    (fty-table alistp))
  :returns (terms true-listp)
  :short "Generate the conjuncts for the fields of a product type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conjunction of this conjuncts is used as
     the body of the predicate generated for the product type,
     unless there is an overriding term.")
   (xdoc::p
    "We go through the fields, and we return the list of conjuncts.
     For each field, we obtain the recognizer name,
     and from that we obtain the type information.
     If there is no type information,
     which means that the field has a built-in type (e.g. @('nat')),
     then we generate no conjunct,
     because we do not generate a predicate for a built-in type.
     If there is type information,
     we generate a conjunct only if the type is in @('types')
     (the list of types for which we generate predicates).
     The conjunct consists of the predicate generated for that type,
     applied to the accessor of the field
     applied to a variable with the same name as
     the product (not field) type;
     this relies on the fact that the predicates we generate
     use the type names as their formal."))
  (b* (((when (endp fields)) nil)
       (field (car fields))
       (recog (fty::flexprod-field->type field))
       ((unless (symbolp recog))
        (raise "Internal error: malformed field recognizer ~x0." recog))
       (info (defpred-type-with-recognizer recog fty-table))
       (field-type (and info
                        (defpred-flex->name info)))
       ((unless (and field-type
                     (member-eq field-type types)))
        (defpred-gen-prod-conjuncts type (cdr fields) types suffix fty-table))
       (accessor (fty::flexprod-field->acc-name field))
       (field-type-suffix (defpred-gen-name field-type suffix))
       (term `(,field-type-suffix (,accessor ,type)))
       (terms
        (defpred-gen-prod-conjuncts type (cdr fields) types suffix fty-table)))
    (cons term terms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-sum-cases ((type symbolp)
                               (prods fty::flexprod-listp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (default booleanp)
                               (overrides alistp)
                               (fty-table alistp))
  :returns (keyword+term-list true-listp)
  :short "Generate the code for the cases of a sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a list @('(<kind1> <term1> <kind2> <term2> ...)'),
     where @('<kind1>'), @('<kind2>'), etc.
     are the kind keywords of the sum type,
     and @('<term1>'), @('<term2>'), etc. are the corresponding terms.
     This list forms the bulk of the body of
     the generated predicate for a sum type.")
   (xdoc::p
    "For each case, first we check whether there is an overriding term,
     in which case we use that as the term for the case.
     Otherwise, we obtain the conjuncts for the fields.
     If there are no conjuncts, we use the @(':default') input as the term.
     If there are conjuncts, we use their conjunction as the term."))
  (b* (((when (endp prods)) nil)
       (prod (car prods))
       (kind (fty::flexprod->kind prod))
       ((unless (keywordp kind))
        (raise "Internal error: kind ~x0 is not a keyword." kind))
       (term
        (b* ((term-assoc (assoc-equal (cons type kind) overrides))
             ((when term-assoc) (cdr term-assoc))
             (fields (fty::flexprod->fields prod))
             ((unless (fty::flexprod-field-listp fields))
              (raise "Internal error: malformed fields ~x0." fields))
             (conjuncts
              (defpred-gen-prod-conjuncts
                type fields types suffix fty-table))
             ((when (endp conjuncts)) default))
          `(and ,@conjuncts))))
    (list* kind
           term
           (defpred-gen-sum-cases
             type (cdr prods) types suffix default overrides fty-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod-pred ((sum fty::flexsum-p)
                               (mutrecp booleanp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (overrides alistp)
                               (fty-table alistp))
  :guard (eq (fty::flexsum->typemacro sum) 'fty::defprod)
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a product type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, product types are stored as a sum types,
     but with an indication of @(tsee fty::defprod) as the type macro.
     This sum type must have a single product entry.")
   (xdoc::p
    "If the override alist includes an entry for this product type,
     we use that as the body of the predicate.
     In this case, we also generate an `ignorable' declaration,
     in case the overriding term does not mention the formal.")
   (xdoc::p
    "If there is no overriding term,
     the body is the conjunction
     whose conjuncts are returned by @(tsee defpred-gen-prod-conjuncts),
     which is never expected to be empty.")
   (xdoc::p
    "The @('mutrec') flag says whether
     this product type is part of a mutually recursive clique."))
  (b* ((type (fty::flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-name type suffix))
       (type-count (fty::flexsum->count sum))
       (recog (fty::flexsum->pred sum))
       (recp (fty::flexsum->recp sum))
       ((mv body ignorable)
        (b* ((term-assoc (assoc-equal type overrides))
             ((when term-assoc) (mv (cdr term-assoc) t))
             (prods (fty::flexsum->prods sum))
             ((unless (fty::flexprod-listp prods))
              (raise "Internal error: malformed products ~x0." prods)
              (mv nil nil))
             ((unless (and (consp prods)
                           (endp (cdr prods))))
              (raise "Internal error: non-singleton product ~x0." prods)
              (mv nil nil))
             (prod (car prods))
             (fields (fty::flexprod->fields prod))
             ((unless (fty::flexprod-field-listp fields))
              (raise "Internal error: malformed fields ~x0." fields)
              (mv nil nil)))
          (mv `(and ,@(defpred-gen-prod-conjuncts
                        type fields types suffix fty-table))
              t))))
    `(define ,type-suffix ((,type ,recog))
       ,@(and ignorable `((declare (ignorable ,type))))
       :returns (yes/no booleanp)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-sum-pred ((sum fty::flexsum-p)
                              (mutrecp booleanp)
                              (types symbol-listp)
                              (suffix symbolp)
                              (default booleanp)
                              (overrides alistp)
                              (fty-table alistp))
  :guard (eq (fty::flexsum->typemacro sum) 'fty::deftagsum)
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, sum types are distinguished
     from other types that are also stored as sum types
     by an indication of the type macro @(tsee fty::deftagsum).")
   (xdoc::p
    "If the override alist includes an entry for this (whole) sum type,
     we use that as the body of the predicate.
     In this case, we also generate an `ignorable' declaration,
     in case the overriding term does not mention the formal.")
   (xdoc::p
    "Otherwise, the predicate is defined by cases,
     which are generated by @(tsee defpred-gen-sum-cases).")
   (xdoc::p
    "The @('mutrec') flag says whether
     this product type is part of a mutually recursive clique."))
  (b* ((type (fty::flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-name type suffix))
       (type-count (fty::flexsum->count sum))
       (recog (fty::flexsum->pred sum))
       (recp (fty::flexsum->recp sum))
       ((mv body ignorable)
        (b* ((term-assoc (assoc-equal type overrides))
             ((when term-assoc) (mv (cdr term-assoc) t))
             (type-case (fty::flexsum->case sum))
             (prods (fty::flexsum->prods sum))
             ((unless (fty::flexprod-listp prods))
              (raise "Internal error: products ~x0 have the wrong type." prods)
              (mv nil nil))
             (cases (defpred-gen-sum-cases
                      type prods types suffix default overrides fty-table))
             (body `(,type-case ,type ,@cases)))
          (mv body nil))))
    `(define ,type-suffix ((,type ,recog))
       ,@(and ignorable `((declare (ignorable ,type))))
       :returns (yes/no booleanp)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-option-pred ((sum fty::flexsum-p)
                                 (mutrecp booleanp)
                                 (suffix symbolp)
                                 (fty-table alistp))
  :guard (eq (fty::flexsum->typemacro sum) 'fty::defoption)
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for an option type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, option types are stored as sum types,
     but with an indication of @(tsee fty::defoption) as the type macro.")
   (xdoc::p
    "This predicate is as described in @(tsee defpred).")
   (xdoc::p
    "The @('mutrec') flag says whether
     this product type is part of a mutually recursive clique."))
  (b* ((type (fty::flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-name type suffix))
       (type-count (fty::flexsum->count sum))
       (recog (fty::flexsum->pred sum))
       (recp (fty::flexsum->recp sum))
       (type-case (fty::flexsum->case sum))
       ((mv base-type accessor)
        (defpred-option-type->components type fty-table))
       (base-type-suffix (defpred-gen-name base-type suffix))
       (body `(,type-case ,type
                          :some (,base-type-suffix (,accessor ,type))
                          :none t)))
    `(define ,type-suffix ((,type ,recog))
       :returns (yes/no booleanp)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod/sum/option-pred ((sum fty::flexsum-p)
                                          (mutrecp booleanp)
                                          (types symbol-listp)
                                          (suffix symbolp)
                                          (default booleanp)
                                          (overrides alistp)
                                          (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a product, sum, or option type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, these are all stored as sum types,
     but with a discriminator as the type macro."))
  (b* ((typemacro (fty::flexsum->typemacro sum)))
    (cond
     ((eq typemacro 'fty::defprod)
      (defpred-gen-prod-pred sum mutrecp types suffix overrides fty-table))
     ((eq typemacro 'fty::deftagsum)
      (defpred-gen-sum-pred sum mutrecp types suffix default overrides fty-table))
     ((eq typemacro 'fty::defoption)
      (defpred-gen-option-pred sum mutrecp suffix fty-table))
     (t (prog2$
         (raise "Internal error: unsupported sum type ~x0." sum)
         '(_))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-list-pred ((list fty::flexlist-p)
                               (mutrecp booleanp)
                               (suffix symbolp)
                               (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a list type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(tsee defpred).")
   (xdoc::p
    "The @('mutrec') flag says whether
     this product type is part of a mutually recursive clique."))
  (b* ((type (fty::flexlist->name list))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-name type suffix))
       (type-count (fty::flexlist->count list))
       (recog (fty::flexlist->pred list))
       (elt-recog (fty::flexlist->elt-type list))
       ((unless (symbolp elt-recog))
        (raise "Internal error: malformed recognizer ~x0." elt-recog)
        '(_))
       (elt-info (defpred-type-with-recognizer elt-recog fty-table))
       (elt-type (defpred-flex->name elt-info))
       (recp (fty::flexlist->recp list))
       ((unless (symbolp elt-type))
        (raise "Internal error: malformed type name ~x0." elt-type)
        '(_))
       (elt-type-suffix (defpred-gen-name elt-type suffix))
       (body `(or (endp ,type)
                  (and (,elt-type-suffix (car ,type))
                       (,type-suffix (cdr ,type))))))
    `(define ,type-suffix ((,type ,recog))
       :returns (yes/no booleanp)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-omap-pred ((omap fty::flexomap-p)
                               (mutrecp booleanp)
                               (suffix symbolp)
                               (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for an omap type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(tsee defpred).")
   (xdoc::p
    "The @('recur') input has the same purpose and use
     as in @(tsee defpred-gen-prod-pred): see that function's documentation."))
  (b* ((type (fty::flexomap->name omap))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-name type suffix))
       (type-count (fty::flexomap->count omap))
       (recog (fty::flexomap->pred omap))
       (recp (fty::flexomap->recp omap))
       (val-recog (fty::flexomap->val-type omap))
       ((unless (symbolp val-recog))
        (raise "Internal error: malformed recognizer ~x0." val-recog)
        '(_))
       (val-info (defpred-type-with-recognizer val-recog fty-table))
       (val-type (defpred-flex->name val-info))
       (val-type-suffix (defpred-gen-name val-type suffix))
       (body `(or (not (mbt (,recog ,type)))
                  (omap::emptyp ,type)
                  (and (,val-type-suffix (omap::head-val ,type))
                       (,type-suffix (omap::tail ,type))))))
    `(define ,type-suffix ((,type ,recog))
       :returns (yes/no booleanp)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-type-pred (flex
                               (mutrecp booleanp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (default booleanp)
                               (overrides alistp)
                               (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a type."
  (cond ((fty::flexsum-p flex)
         (defpred-gen-prod/sum/option-pred
           flex mutrecp types suffix default overrides fty-table))
        ((fty::flexlist-p flex)
         (defpred-gen-list-pred flex mutrecp suffix fty-table))
        ((fty::flexomap-p flex)
         (defpred-gen-omap-pred flex mutrecp suffix fty-table))
        (t (prog2$ (raise "Internal error: unsupported type ~x0." flex) '(_)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-types-preds ((flexs true-listp)
                                 (mutrecp booleanp)
                                 (types symbol-listp)
                                 (suffix symbolp)
                                 (default booleanp)
                                 (overrides alistp)
                                 (fty-table alistp))
  :returns (events pseudo-event-form-listp)
  :short "Generate a list of predicates for a list of types."
  (cond ((endp flexs) nil)
        (t (cons
            (defpred-gen-type-pred
              (car flexs) mutrecp types suffix default overrides fty-table)
            (defpred-gen-types-preds
              (cdr flexs) mutrecp types suffix default overrides fty-table)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-clique-pred/preds ((clique fty::flextypes-p)
                                       (types symbol-listp)
                                       (suffix symbolp)
                                       (default booleanp)
                                       (overrides alistp)
                                       (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate, or a clique of mutually recursive predicates,
          for a clique of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the clique is empty, it is an internal error.
     If the clique is a singleton, we generate a single predicate,
     which may be recursive or not,
     based on the flag we read from the information about the type.
     If the clique consists of two or more types,
     we generate a clique of mutually recursive predicates,
     with a @(tsee fty::deffixequiv-mutual) at the end;
     the name of the clique of predicates is derived from
     the name of the clique of types.")
   (xdoc::p
    "We also generate a @(':flag-local nil') to export
     the flag macro @('defthm-<name>-flag'),
     where @('<name>') is the name of the @(tsee defines) clique.
     This facilitates proving theorems by induction on the predicates."))
  (b* ((members (fty::flextypes->types clique))
       ((unless (true-listp members))
        (raise "Internal error: malformed members of type clique ~x0." clique)
        '(_))
       ((when (endp members))
        (raise "Internal error: empty type clique ~x0." clique)
        '(_))
       ((when (endp (cdr members)))
        (defpred-gen-type-pred
          (car members) nil types suffix default overrides fty-table))
       (clique-name (fty::flextypes->name clique))
       ((unless (symbolp clique-name))
        (raise "Internal error: malformed clique name ~x0." clique-name)
        '(_))
       (clique-name-suffix (defpred-gen-name clique-name suffix))
       (events (defpred-gen-types-preds
                 members t types suffix default overrides fty-table)))
    `(defines ,clique-name-suffix
       ,@events
       :hints (("Goal" :in-theory (enable o< o-finp)))
       :flag-local nil
       ///
       (fty::deffixequiv-mutual ,clique-name-suffix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-cliques-preds ((clique-names symbol-listp)
                                   (types symbol-listp)
                                   (suffix symbolp)
                                   (default booleanp)
                                   (overrides alistp)
                                   (fty-table alistp))
  :returns (events pseudo-event-form-listp)
  :short "Generate a list of predicates, or predicate cliques,
          for a list of type cliques with given names."
  (b* (((when (endp clique-names)) nil)
       (clique-name (car clique-names))
       (clique (defpred-type-clique-with-name clique-name fty-table))
       ((unless clique)
        (raise "Internal error: no type clique with name ~x0." clique-name))
       ((unless (fty::flextypes-p clique))
        (raise "Internal error: malformed type clique ~x0." clique))
       (event (defpred-gen-clique-pred/preds
                clique types suffix default overrides fty-table))
       (events (defpred-gen-cliques-preds
                 (cdr clique-names) types suffix default overrides fty-table)))
    (cons event events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defpred-cliques*
  :short "Names of the type cliques to generate predicates for."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as stated in @(tsee defpred)."))
  '(exprs/decls/stmts
    type-spec-list
    expr/tyname
    declor/absdeclor
    decl/stmt
    fundef
    fundef-option
    extdecl
    extdecl-list
    transunit
    filepath-transunit-map
    transunit-ensemble))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-everything ((suffix symbolp)
                                (default booleanp)
                                (overrides alistp)
                                (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We obtain all the names of the types to generate predicates for,
     and then we call the code to generate the predicates,
     which we put into one event."))
  (b* ((types
        (defpred-type-names-in-cliques-with-names *defpred-cliques* fty-table))
       (events (defpred-gen-cliques-preds
                 *defpred-cliques* types suffix default overrides fty-table)))
    `(progn
       (set-bogus-mutual-recursion-ok t)
       ,@events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-process-inputs-and-gen-everything ((args true-listp)
                                                   (wrld plist-worldp))
  :returns (mv erp (event pseudo-event-formp))
  :parents (defpred-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       (fty-table (table-alist+ 'fty::flextypes-table wrld))
       ((erp suffix default overrides)
        (defpred-process-inputs args fty-table)))
    (retok (defpred-gen-everything suffix default overrides fty-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (defpred-implementation)
  :short "Event expansion of @(tsee defpred)."
  (b* (((mv erp event)
        (defpred-process-inputs-and-gen-everything args (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defpred-macro-definition
  :parents (defpred-implementation)
  :short "Definition of @(tsee defpred)."
  (defmacro defpred (&rest args)
    `(make-event (defpred-fn ',args 'defpred state))))
