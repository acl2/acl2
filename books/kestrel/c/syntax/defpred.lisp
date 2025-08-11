; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/database" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/true-listp" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/pseudo-event-form-listp" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
          (info (fty::flextype-with-name type fty-table))
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
  '(:extra-args
    :default
    :override
    :parents
    :short
    :long))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-process-inputs ((args true-listp) (fty-table alistp))
  :returns (mv erp
               (suffix symbolp)
               (extra-args true-listp)
               (default booleanp)
               (overrides alistp)
               (parents-presentp booleanp)
               parents
               (short-presentp booleanp)
               short
               (long-presentp booleanp)
               long)
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil nil nil)
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
       (extra-args-option (assoc-eq :extra-args options))
       (extra-args (if extra-args-option
                       (cdr extra-args-option)
                     nil))
       ((unless (true-listp extra-args))
        (reterr (msg "The :EXTRA-ARGS input must be a list, ~
                      but it is ~x0 instead."
                     extra-args)))
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
       ((erp overrides) (defpred-process-override override fty-table))
       (parents-option (assoc-eq :parents options))
       (parents-presentp (consp parents-option))
       (parents (cdr parents-option))
       (short-option (assoc-eq :short options))
       (short-presentp (consp short-option))
       (short (cdr short-option))
       (long-option (assoc-eq :long options))
       (long-presentp (consp long-option))
       (long (cdr long-option)))
    (retok suffix
           extra-args
           default
           overrides
           parents-presentp
           parents
           short-presentp
           short
           long-presentp
           long))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defpred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-topic-name ((suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of the XDOC topic."
  (packn-pos (list 'abstract-syntax- suffix) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-pred-name ((type symbolp) (suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of a predicate for a type."
  (packn-pos (list type '- suffix) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-ruleset-name ((suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of the ruleset."
  (packn-pos (list 'abstract-syntax- suffix '-rules) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-extra-args-to-names ((extra-args true-listp))
  :returns (names true-listp)
  :short "Map the @(':extra-args') input to
          a list of the names of the arguments."
  (b* (((when (endp extra-args)) nil)
       (extra-arg (car extra-args))
       (name (if (atom extra-arg) extra-arg (car extra-arg)))
       (names (defpred-extra-args-to-names (cdr extra-args))))
    (cons name names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod-conjuncts ((type symbolp)
                                    (fields fty::flexprod-field-listp)
                                    (types symbol-listp)
                                    (suffix symbolp)
                                    (extra-args true-listp)
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
       (info (fty::flextype-with-recognizer recog fty-table))
       (field-type (and info
                        (fty::flextype->name info)))
       ((unless (and field-type
                     (member-eq field-type types)))
        (defpred-gen-prod-conjuncts
          type (cdr fields) types suffix extra-args fty-table))
       (accessor (fty::flexprod-field->acc-name field))
       (field-type-suffix (defpred-gen-pred-name field-type suffix))
       (extra-args-names (defpred-extra-args-to-names extra-args))
       (term `(,field-type-suffix (,accessor ,type) ,@extra-args-names))
       (terms (defpred-gen-prod-conjuncts
                type (cdr fields) types suffix extra-args fty-table)))
    (cons term terms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-sum-cases ((type symbolp)
                               (prods fty::flexprod-listp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (extra-args true-listp)
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
                type fields types suffix extra-args fty-table))
             ((when (endp conjuncts)) default))
          `(and ,@conjuncts))))
    (list* kind
           term
           (defpred-gen-sum-cases
             type (cdr prods) types
             suffix extra-args default overrides fty-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod-pred ((sum fty::flexsum-p)
                               (mutrecp booleanp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (extra-args true-listp)
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
       (type-suffix (defpred-gen-pred-name type suffix))
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
                        type fields types suffix extra-args fty-table))
              t))))
    `(define ,type-suffix ((,type ,recog) ,@extra-args)
       ,@(and ignorable `((declare (ignorable ,type))))
       :returns (yes/no booleanp)
       :parents (,(defpred-gen-topic-name suffix))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-sum-pred ((sum fty::flexsum-p)
                              (mutrecp booleanp)
                              (types symbol-listp)
                              (suffix symbolp)
                              (extra-args true-listp)
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
       (type-suffix (defpred-gen-pred-name type suffix))
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
                      type prods types
                      suffix extra-args default overrides fty-table))
             (body `(,type-case ,type ,@cases)))
          (mv body nil))))
    `(define ,type-suffix ((,type ,recog) ,@extra-args)
       ,@(and ignorable `((declare (ignorable ,type))))
       :returns (yes/no booleanp)
       :parents (,(defpred-gen-topic-name suffix))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-option-pred ((sum fty::flexsum-p)
                                 (mutrecp booleanp)
                                 (suffix symbolp)
                                 (extra-args true-listp)
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
       (type-suffix (defpred-gen-pred-name type suffix))
       (type-count (fty::flexsum->count sum))
       (recog (fty::flexsum->pred sum))
       (recp (fty::flexsum->recp sum))
       (type-case (fty::flexsum->case sum))
       ((mv base-type accessor)
        (fty::components-of-flexoption-with-name type fty-table))
       (base-type-suffix (defpred-gen-pred-name base-type suffix))
       (extra-args-names (defpred-extra-args-to-names extra-args))
       (body `(,type-case ,type
                          :some (,base-type-suffix (,accessor ,type)
                                                   ,@extra-args-names)
                          :none t)))
    `(define ,type-suffix ((,type ,recog) ,@extra-args)
       :returns (yes/no booleanp)
       :parents (,(defpred-gen-topic-name suffix))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-prod/sum/option-pred ((sum fty::flexsum-p)
                                          (mutrecp booleanp)
                                          (types symbol-listp)
                                          (suffix symbolp)
                                          (extra-args true-listp)
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
      (defpred-gen-prod-pred
        sum mutrecp types suffix extra-args overrides fty-table))
     ((eq typemacro 'fty::deftagsum)
      (defpred-gen-sum-pred
        sum mutrecp types suffix extra-args default overrides fty-table))
     ((eq typemacro 'fty::defoption)
      (defpred-gen-option-pred
        sum mutrecp suffix extra-args fty-table))
     (t (prog2$
         (raise "Internal error: unsupported sum type ~x0." sum)
         '(_))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-list-pred ((list fty::flexlist-p)
                               (mutrecp booleanp)
                               (suffix symbolp)
                               (extra-args true-listp)
                               (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a list type, with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(tsee defpred).")
   (xdoc::p
    "The @('mutrec') flag says whether
     this product type is part of a mutually recursive clique.")
   (xdoc::p
    "The accompanying theorems are generated as a @(tsee std::deflist) event,
     which generates the actual theorems.
     For now we only generate theorems if there are no @(':extra-args');
     we need to do a little work to generate the appropriate @(':guard')."))
  (b* ((type (fty::flexlist->name list))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-suffix (defpred-gen-pred-name type suffix))
       (type-count (fty::flexlist->count list))
       (recog (fty::flexlist->pred list))
       (elt-recog (fty::flexlist->elt-type list))
       ((unless (symbolp elt-recog))
        (raise "Internal error: malformed recognizer ~x0." elt-recog)
        '(_))
       (elt-info (fty::flextype-with-recognizer elt-recog fty-table))
       (elt-type (fty::flextype->name elt-info))
       (recp (fty::flexlist->recp list))
       ((unless (symbolp elt-type))
        (raise "Internal error: malformed type name ~x0." elt-type)
        '(_))
       (elt-type-suffix (defpred-gen-pred-name elt-type suffix))
       (extra-args-names (defpred-extra-args-to-names extra-args))
       (body `(or (endp ,type)
                  (and (,elt-type-suffix (car ,type) ,@extra-args-names)
                       (,type-suffix (cdr ,type) ,@extra-args-names))))
       (deflist-event
         (if extra-args
             '(progn) ; no-op event -- temporary limitation
           `(std::deflist ,type-suffix (x)
              :guard (,recog x)
              (,elt-type-suffix x)
              :true-listp nil
              :parents nil)))
       (thm-events (list deflist-event))
       (event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           :returns (yes/no booleanp)
           :parents (,(defpred-gen-topic-name suffix))
           ,body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:hooks (:fix)))
           ///
           ,@thm-events)))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-omap-pred ((omap fty::flexomap-p)
                               (mutrecp booleanp)
                               (suffix symbolp)
                               (extra-args true-listp)
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
       (type-suffix (defpred-gen-pred-name type suffix))
       (type-count (fty::flexomap->count omap))
       (recog (fty::flexomap->pred omap))
       (recp (fty::flexomap->recp omap))
       (key-recog (fty::flexomap->key-type omap))
       ((unless (symbolp key-recog))
        (raise "Internal error: malformed recognizer ~x0." key-recog)
        '(_))
       (key-info (fty::flextype-with-recognizer key-recog fty-table))
       (key-type (fty::flextype->name key-info))
       (val-recog (fty::flexomap->val-type omap))
       ((unless (symbolp val-recog))
        (raise "Internal error: malformed recognizer ~x0." val-recog)
        '(_))
       (val-info (fty::flextype-with-recognizer val-recog fty-table))
       (val-type (fty::flextype->name val-info))
       (val-type-suffix (defpred-gen-pred-name val-type suffix))
       (extra-args-names (defpred-extra-args-to-names extra-args))
       (body `(or (not (mbt (,recog ,type)))
                  (omap::emptyp ,type)
                  (and (,val-type-suffix (omap::head-val ,type)
                                         ,@extra-args-names)
                       (,type-suffix (omap::tail ,type)
                                     ,@extra-args-names))))
       (type-suffix-when-emptyp
        (packn-pos (list type-suffix '-when-emptyp) suffix))
       (type-suffix-of-update
        (packn-pos (list type-suffix '-of-update) suffix))
       (val-type-suffix-of-head-when-type-suffix
        (packn-pos (list val-type '-of-head-when- type-suffix) suffix))
       (type-suffix-of-tail
        (packn-pos (list type-suffix '-of-tail) suffix))
       (thm-events
        `((defruled ,type-suffix-when-emptyp
            (implies (omap::emptyp ,type)
                     (,type-suffix ,type ,@extra-args-names))
            :enable ,type-suffix)
          (defruled ,type-suffix-of-update
            (implies (and (,recog ,type)
                          (,val-type-suffix ,val-type ,@extra-args-names)
                          (,type-suffix ,type ,@extra-args-names))
                     (,type-suffix (omap::update ,key-type ,val-type ,type)
                                   ,@extra-args-names))
            :induct t
            :enable (,recog
                     omap::update
                     omap::emptyp
                     omap::mfix
                     omap::mapp
                     omap::head
                     omap::tail))
          (defruled ,val-type-suffix-of-head-when-type-suffix
            (implies (and (,recog ,type)
                          (,type-suffix ,type ,@extra-args-names)
                          (not (omap::emptyp ,type)))
                     (,val-type-suffix (mv-nth 1 (omap::head ,type))
                                       ,@extra-args-names)))
          (defruled ,type-suffix-of-tail
            (implies (and (,recog ,type)
                          (,type-suffix ,type ,@extra-args-names))
                     (,type-suffix (omap::tail ,type) ,@extra-args-names)))))
       (ruleset-event
        `(add-to-ruleset ,(defpred-gen-ruleset-name suffix)
                         '(,type-suffix-when-emptyp
                           ,type-suffix-of-update
                           ,val-type-suffix-of-head-when-type-suffix
                           ,type-suffix-of-tail))))
    `(define ,type-suffix ((,type ,recog) ,@extra-args)
       :returns (yes/no booleanp)
       :parents (,(defpred-gen-topic-name suffix))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix)))
       ///
       ,@thm-events
       ,ruleset-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-type-pred (flex
                               (mutrecp booleanp)
                               (types symbol-listp)
                               (suffix symbolp)
                               (extra-args true-listp)
                               (default booleanp)
                               (overrides alistp)
                               (fty-table alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a predicate for a type, with accompanying theorems."
  (cond ((fty::flexsum-p flex)
         (defpred-gen-prod/sum/option-pred
           flex mutrecp types suffix extra-args default overrides fty-table))
        ((fty::flexlist-p flex)
         (defpred-gen-list-pred flex mutrecp suffix extra-args fty-table))
        ((fty::flexomap-p flex)
         (defpred-gen-omap-pred flex mutrecp suffix extra-args fty-table))
        (t (prog2$ (raise "Internal error: unsupported type ~x0." flex)
                   '(_)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-types-preds ((flexs true-listp)
                                 (mutrecp booleanp)
                                 (types symbol-listp)
                                 (suffix symbolp)
                                 (extra-args true-listp)
                                 (default booleanp)
                                 (overrides alistp)
                                 (fty-table alistp))
  :returns (events pseudo-event-form-listp)
  :short "Generate a list of predicates for a list of types,
          with accompanying theorems."
  (b* (((when (endp flexs)) nil)
       (event
        (defpred-gen-type-pred
          (car flexs) mutrecp types
          suffix extra-args default overrides fty-table))
       (more-events
        (defpred-gen-types-preds
          (cdr flexs) mutrecp types
          suffix extra-args default overrides fty-table)))
    (cons event more-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-clique-pred/preds ((clique fty::flextypes-p)
                                       (types symbol-listp)
                                       (suffix symbolp)
                                       (extra-args true-listp)
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
     with a @(tsee fty::deffixequiv-mutual) after the @('///'),
     and with the deferred events after that;
     the name of the clique of predicates is derived from
     the name of the clique of types.")
   (xdoc::p
    "We also generate a @(':flag-local nil') to export
     the flag macro @('defthm-<name>-flag'),
     where @('<name>') is the name of the @(tsee defines) clique.
     This facilitates proving theorems by induction on the predicates.")
   (xdoc::p
    "We also generate a form to allow bogus mutual recursion,
     since we have no control on how the user overrides the boilerplate.
     Note that this form is automatically local to the @(tsee defines)."))
  (b* ((members (fty::flextypes->types clique))
       ((unless (true-listp members))
        (raise "Internal error: malformed members of type clique ~x0." clique)
        '(_))
       ((when (endp members))
        (raise "Internal error: empty type clique ~x0." clique)
        '(_))
       ((when (endp (cdr members)))
        (defpred-gen-type-pred
          (car members) nil types
          suffix extra-args default overrides fty-table))
       (clique-name (fty::flextypes->name clique))
       ((unless (symbolp clique-name))
        (raise "Internal error: malformed clique name ~x0." clique-name)
        '(_))
       (clique-name-suffix (defpred-gen-pred-name clique-name suffix))
       (events
        (defpred-gen-types-preds
          members t types suffix extra-args default overrides fty-table)))
    `(defines ,clique-name-suffix
       :parents (,(defpred-gen-topic-name suffix))
       ,@events
       :hints (("Goal" :in-theory (enable o< o-finp)))
       :flag-local nil
       :prepwork ((set-bogus-mutual-recursion-ok t))
       ///
       (fty::deffixequiv-mutual ,clique-name-suffix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-gen-cliques-preds ((clique-names symbol-listp)
                                   (types symbol-listp)
                                   (suffix symbolp)
                                   (extra-args true-listp)
                                   (default booleanp)
                                   (overrides alistp)
                                   (fty-table alistp))
  :returns (events pseudo-event-form-listp)
  :short "Generate a list of predicates, or predicate cliques,
          for a list of type cliques with given names."
  (b* (((when (endp clique-names)) nil)
       (clique-name (car clique-names))
       (clique (fty::flextypes-with-name clique-name fty-table))
       ((unless clique)
        (raise "Internal error: no type clique with name ~x0." clique-name))
       ((unless (fty::flextypes-p clique))
        (raise "Internal error: malformed type clique ~x0." clique))
       (event (defpred-gen-clique-pred/preds
                clique types
                suffix extra-args default overrides fty-table))
       (events (defpred-gen-cliques-preds
                 (cdr clique-names) types
                 suffix extra-args default overrides fty-table)))
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
                                (extra-args true-listp)
                                (default booleanp)
                                (overrides alistp)
                                (parents-presentp booleanp)
                                parents
                                (short-presentp booleanp)
                                short
                                (long-presentp booleanp)
                                long
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
        (fty::flextype-names-in-flextypes-with-names *defpred-cliques*
                                                     fty-table))
       (pred-events
        (defpred-gen-cliques-preds
          *defpred-cliques* types
          suffix extra-args default overrides fty-table))
       (xdoc-name (defpred-gen-topic-name suffix))
       (xdoc-event
        `(defxdoc+ ,xdoc-name
           ,@(and parents-presentp `(:parents ,parents))
           ,@(and short-presentp `(:short ,short))
           ,@(and long-presentp `(:long ,long))
           :order-subtopics t))
       (ruleset-event
        `(def-ruleset! ,(defpred-gen-ruleset-name suffix) nil)))
    `(encapsulate
       ()
       ,xdoc-event
       ,ruleset-event
       ,@pred-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defpred-process-inputs-and-gen-everything ((args true-listp)
                                                   (wrld plist-worldp))
  :returns (mv erp (event pseudo-event-formp))
  :parents (defpred-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       (fty-table (table-alist+ 'fty::flextypes-table wrld))
       ((erp suffix
             extra-args
             default
             overrides
             parents-presentp
             parents
             short-presentp
             short
             long-presentp
             long)
        (defpred-process-inputs args fty-table)))
    (retok (defpred-gen-everything
             suffix
             extra-args
             default
             overrides
             parents-presentp
             parents
             short-presentp
             short
             long-presentp
             long
             fty-table))))

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
