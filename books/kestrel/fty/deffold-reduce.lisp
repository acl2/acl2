; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/screen-printing" :dir :system)
(include-book "kestrel/fty/database" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/true-listp" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/pseudo-event-formp" :dir :system))
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

(defmacro patbind-reterr (&rest args) `(acl2::patbind-reterr ,@args))

(defmacro patbind-erp (&rest args) `(acl2::patbind-erp ,@args))

(defmacro reterr (&rest args) `(acl2::reterr ,@args))

(defmacro retok (&rest args) `(acl2::retok ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 deffold-reduce

 :items

 ((xdoc::evmac-topic-implementation-item-input "suffix")

  (xdoc::evmac-topic-implementation-item-input "types")

  (xdoc::evmac-topic-implementation-item-input "extra-args")

  (xdoc::evmac-topic-implementation-item-input "result")

  (xdoc::evmac-topic-implementation-item-input "default")

  (xdoc::evmac-topic-implementation-item-input "combine")

  (xdoc::evmac-topic-implementation-item-input "override")

  (xdoc::evmac-topic-implementation-item-input "parents")

  (xdoc::evmac-topic-implementation-item-input "short")

  (xdoc::evmac-topic-implementation-item-input "long")

  "@('overrides') is an alist representation of the @(':override') input.
   With reference to the documentation page of @(tsee deffold-reduce):
   for each element @('<type> <term>') in @(':override'),
   this alist has an element @('(cons <type> <term>)');
   for each element @('<type> <kind> <term>') in @(':override'),
   this alist has an element @('(cons (cons <type> <kind>) <term>)')."

  "@('fty-table') is the alist of the table of all (fix)types
   (except some built-in ones, such as @('nat')),
   i.e. the table @('flextypes-table').
   The format is defined in @('[books]/centaur/fty/database.lisp').
   It has one entry for each mutually recursive clique of types,
   with singly recursive or non-recursive types
   being in singleton cliques."

  "@('targets') is a list (in no particular order)
   of all the type names for which fold functions are generated."

  "@('target') is an element of @('targets') explained above."

  "Although in some cases the accompanying theorems could be generated
   as part of the @(tsee define) or @(tsee defines) after the @('///'),
   we have found cases in which the fixing theorems are needed
   to prove some of the accompanying theorems.
   If a generated function is not mutually recursive
   we could use an explicit @(tsee deffixequiv) instead of @(':hooks (:fix)');
   but for a mutually recursive function we need to generate the theorem
   after all the functions in the clique and the @(tsee deffixequiv-mutual).
   Some of the functions that implement @(tsee deffold-reduce) return
   separate events for functions and theorems."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing deffold-reduce)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-process-types (types (fty-table alistp))
  :returns (mv erp
               (types symbol-listp)
               (targets symbol-listp))
  :short "Process the @(':types') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If processing is successful,
     we return the list of all the fixtype names (symbols)
     for which fold functions must be generated.")
   (xdoc::p
    "We just check that this input is a list of symbols;
     we do not yet check that each symbol identifies a fixtype clique
     (note that FTY stores non-recursive and single recursive fixtypes
     into singleton cliques, so checking clique names is appropriate),
     or that the names are given in bottom-up order.")
   (xdoc::p
    "Note that @(tsee flextype-names-in-flextypes-with-names)
     just ignores symbols that do not name any clique."))
  (b* (((reterr) nil nil)
       ((unless (symbol-listp types))
        (reterr (msg "The :TYPES input must be a alist of symbols, ~
                            but it is ~x0 instead."
                     types))))
    (retok types
           (flextype-names-in-flextypes-with-names types fty-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-process-override (override (fty-table alistp))
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
     i.e. whether it is a @(tsee defprod) or @(tsee deftagsum);
     we use that to distinguish them."))
  (b* (((reterr) nil)
       ((unless (true-listp override))
        (reterr (msg "The :OVERRIDE input must be a list, ~
                      but it is ~x0 instead."
                     override))))
    (deffoldred-process-override-loop override fty-table))
  :prepwork
  ((define deffoldred-process-override-loop ((override true-listp)
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
          (info (flextype-with-name type fty-table))
          ((unless info)
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be the name of a type, ~
                         but ~x0 is not."
                        type)))
          ((unless (flexsum-p info))
           (reterr (msg "The first element of ~
                         every element of the :OVERRIDE list ~
                         must be the name of a product or sum type, ~
                         but ~x0 is not."
                        type)))
          (typemacro (flexsum->typemacro info))
          ((unless (member-eq typemacro (list 'defprod 'deftagsum)))
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
                  (prods (flexsum->prods info))
                  ((unless (flexprod-listp prods))
                   (raise "Internal error: malformed summands ~x0." prods)
                   (reterr t))
                  ((unless (member-eq kind
                                      (flexprod-list->kind-list prods)))
                   (reterr (msg "The kind ~x0 that accompanies ~
                                 the type ~x1 in the :OVERRIDE list ~
                                 is not one of the kinds of that sum type."
                                kind type))))
               (retok (cons type kind) term))))
          ((erp alist)
           (deffoldred-process-override-loop (cdr override) fty-table)))
       (retok (acons key val alist)))
     :prepwork ((local (in-theory (enable acons))))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *deffoldred-allowed-options*
  :short "Keyword options accepted by @(tsee deffold-reduce)."
  '(:types
    :extra-args
    :result
    :default
    :combine
    :override
    :parents
    :short
    :long
    :print))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-process-inputs ((args true-listp) (fty-table alistp))
  :returns (mv erp
               (suffix symbolp)
               (types symbol-listp)
               (targets symbol-listp)
               (extra-args true-listp)
               (result symbolp)
               (default t)
               (combine symbolp)
               (overrides alistp)
               (parents-presentp booleanp)
               parents
               (short-presentp booleanp)
               short
               (long-presentp booleanp)
               long
               (print acl2::evmac-input-print-p))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil)
       ((mv erp suffix options)
        (partition-rest-and-keyword-args args *deffoldred-allowed-options*))
       ((when (or erp
                  (not (consp suffix))
                  (not (endp (cdr suffix)))))
        (reterr (msg "The inputs must be the suffix name ~
                      followed by the options ~&0."
                     *deffoldred-allowed-options*)))
       (suffix (car suffix))
       ((unless (symbolp suffix))
        (reterr (msg "The SUFFIX input must be a symbol, ~
                      but it is ~x0 instead."
                     suffix)))
       (types-option (assoc-eq :types options))
       ((unless types-option)
        (reterr (msg "The :TYPES input must be supplied.")))
       (types (cdr types-option))
       ((erp types targets) (deffoldred-process-types types fty-table))
       (extra-args-option (assoc-eq :extra-args options))
       (extra-args (if extra-args-option
                       (cdr extra-args-option)
                     nil))
       ((unless (true-listp extra-args))
        (reterr (msg "The :EXTRA-ARGS input must be a list, ~
                      but it is ~x0 instead."
                     extra-args)))
       (result-option (assoc-eq :result options))
       ((unless result-option)
        (reterr (msg "The :RESULT input must be supplied.")))
       (result (cdr result-option))
       ((unless (symbolp result))
        (reterr (msg "The :RESULT input must be a symbol, ~
                      but it is ~x0 instead."
                     result)))
       (default-option (assoc-eq :default options))
       ((unless default-option)
        (reterr (msg "The :DEFAULT input must be supplied.")))
       (default (cdr default-option))
       (combine-option (assoc-eq :combine options))
       ((unless combine-option)
        (reterr (msg "The :COMBINE input must be supplied.")))
       (combine (cdr combine-option))
       ((unless (symbolp combine))
        (reterr (msg "The :COMBINE input must be a symbol, ~
                      but it is ~x0 instead."
                     combine)))
       (override-option (assoc-eq :override options))
       (override (if override-option
                     (cdr override-option)
                   nil))
       ((erp overrides) (deffoldred-process-override override fty-table))
       (parents-option (assoc-eq :parents options))
       (parents-presentp (consp parents-option))
       (parents (cdr parents-option))
       (short-option (assoc-eq :short options))
       (short-presentp (consp short-option))
       (short (cdr short-option))
       (long-option (assoc-eq :long options))
       (long-presentp (consp long-option))
       (long (cdr long-option))
       (print-option (assoc-eq :print options))
       ((unless (or (atom print-option)
                    (acl2::evmac-input-print-p (cdr print-option))))
        (reterr (msg "The :PRINT input must be one of: nil, :error, :result, ~
                      :info, or :all, but it is ~x0 instead."
                     print-option)))
       (print (if (consp print-option)
                  (cdr print-option)
                :result)))
    (retok suffix
           types
           targets
           extra-args
           result
           default
           combine
           overrides
           parents-presentp
           parents
           short-presentp
           short
           long-presentp
           long
           print))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation deffold-reduce)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-topic-name ((suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of the XDOC topic."
  (acl2::packn-pos (list 'abstract-syntax- suffix) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-fold-name ((type symbolp) (suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of the fold function for a type."
  (acl2::packn-pos (list type '- suffix) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-ruleset-name ((suffix symbolp))
  :returns (name symbolp)
  :short "Generate the name of the ruleset."
  (acl2::packn-pos (list 'abstract-syntax- suffix '-rules) suffix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-extra-args-to-names ((extra-args true-listp))
  :returns (names true-listp)
  :short "Map the @(':extra-args') input to
          a list of the names of the arguments."
  (b* (((when (endp extra-args)) nil)
       (extra-arg (car extra-args))
       (name (if (atom extra-arg) extra-arg (car extra-arg)))
       (names (deffoldred-extra-args-to-names (cdr extra-args))))
    (cons name names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-prod-combination ((type symbolp)
                                         (fields flexprod-field-listp)
                                         (suffix symbolp)
                                         (targets symbol-listp)
                                         (extra-args true-listp)
                                         (default t)
                                         (combine symbolp)
                                         (fty-table alistp))
  :returns (mv fn-term
               thm-term
               (field-names symbol-listp))
  :short "Generate the combination for the fields of
          a product type or a case of a sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('type') input is the name of the product or sum type.
     The @('fields') input consists of the fields of
     the product type or the case of the sum type
     (the latter is represented as a product type in the FTY table).")
   (xdoc::p
    "We generate two combination terms:
     one for the fold function, and one for an associated theorem.
     We also return the list of names of the fields, in order.")
   (xdoc::p
    "The @('fn-term') is the term returned, in the absence of overriding,
     by the fold function of a @(tsee defprod),
     or by a case of the fold function of a @(tsee deftagsum).
     See @(tsee deffold-reduce).")
   (xdoc::p
    "The @('thm-term') is the term used, in the absence of overriding,
     as the right side of the theorem @('<type>-<suffix>-of-<type>')
     described in the user documentation of @(tsee deffold-reduce).")
   (xdoc::p
    "We go through the fields,
     and we return a right-associated nest of the @(':combine') operator
     of the result of the fold functions applied to
     the fields for which fold functions are generated,
     starting with the @(':default') term,
     but in case of a single @('(combine X default)'), we just return @('X').
     For each field, we obtain the recognizer name,
     and from that we obtain the type information.
     If there is no type information,
     which means that the field has a built-in type (e.g. @('nat')),
     then we skip the field.
     If there is type information,
     we skip the field unless its type is in @('targets').
     If a field is not skipped:")
   (xdoc::ul
    (xdoc::li
     "For @('fn-term'),
      we apply the fold function for the field's type to
      the accessor of the field
      applied to a variable with the same name as
      the product (not field) type.
      This relies on the fact that the functions we generate
      use the type names as their formals.")
    (xdoc::li
     "For @('thm-term'),
      we apply the fold function for the field's type to
      a variable with the same name as the field.
      This relies on the fact that the left side of the theorem
      includes a call of the product type constructor
      applied to arguments with the same names as the the fields.")))
  (b* (((when (endp fields)) (mv default default nil))
       (field (car fields))
       (name (flexprod-field->name field))
       ((unless (symbolp name))
        (raise "Internal error: malformed field name ~x0." name)
        (mv nil nil nil))
       (recog (flexprod-field->type field))
       ((unless (symbolp recog))
        (raise "Internal error: malformed field recognizer ~x0." recog)
        (mv nil nil nil))
       (info (flextype-with-recognizer recog fty-table))
       (field-type (and info
                        (flextype->name info)))
       ((unless (and field-type
                     (member-eq field-type targets)))
        (b* (((mv fn-term thm-term rest-names)
              (deffoldred-gen-prod-combination
                type (cdr fields) suffix
                targets extra-args default combine fty-table)))
          (mv fn-term thm-term (cons name rest-names))))
       (accessor (flexprod-field->acc-name field))
       (field-type-suffix (deffoldred-gen-fold-name field-type suffix))
       (extra-args-names (deffoldred-extra-args-to-names extra-args))
       (fn-term `(,field-type-suffix (,accessor ,type) ,@extra-args-names))
       (thm-term `(,field-type-suffix ,name ,@extra-args-names))
       ((mv rest-fn-term rest-thm-term rest-names)
        (deffoldred-gen-prod-combination
          type (cdr fields) suffix
          targets extra-args default combine fty-table))
       (names (cons name rest-names))
       ((when (equal rest-fn-term default)) (mv fn-term thm-term names)))
    (mv `(,combine ,fn-term ,rest-fn-term)
        `(,combine ,thm-term ,rest-thm-term)
        names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-prod-combination+theorem ((type symbolp)
                                                 (constr symbolp)
                                                 (prod flexprod-p)
                                                 (kind-fn symbolp)
                                                 (suffix symbolp)
                                                 (targets symbol-listp)
                                                 (extra-args true-listp)
                                                 (default t)
                                                 (combine symbolp)
                                                 (fty-table alistp))
  :returns (mv fn-term
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the combination for the fields of
          a product type or a case of a sum type,
          as well as a theorem about
          the predicate for the product or sum type
          applied to the constructor of
          the product type or the case of the sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('type') input is the name of the product type or sum type.
     The @('constr') input is the name of the constructor of
     the product type or the case of the sum type;
     it is the same as @('type') in the case of a product type,
     but in the case of a sum type it consists of @('type')
     followed by the kind of the case of the sum.")
   (xdoc::p
    "The @('fn-term') result is from @(tsee deffoldred-gen-prod-combination):
     see that function for details.
     The theorem's formula involves
     the @('thm-term') and @('field-names') results of that function:
     this is the theorem @('<type>-<suffix>-of-<type>')
     described in @(tsee deffold-reduce).")
   (xdoc::p
    "If we are dealing with the summand of a sum type
     (which we can tell from whether
     the kind function @('kind-fn') passed as input is not @('nil')),
     and if that summand has no fields,
     then we generate a theorem of a different form,
     which is more amenable to rewriting in proofs."))
  (b* ((fields (flexprod->fields prod))
       ((unless (flexprod-field-listp fields))
        (raise "Internal error: malformed fields ~x0." fields)
        (mv nil nil))
       ((mv fn-term thm-rhs field-names)
        (deffoldred-gen-prod-combination
          type fields suffix targets extra-args default combine fty-table))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (extra-args-names (deffoldred-extra-args-to-names extra-args))
       ((mv thm-name thm-event)
        (if (and kind-fn
                 (not fields))
            (b* ((kind (flexprod->kind prod))
                 ((unless (or (not kind) (keywordp kind)))
                  (raise "Internal error: malformed kind ~x0." kind)
                  (mv nil '(_)))
                 (type-suffix-when-kind
                  (acl2::packn-pos (list type-suffix '-when- kind) suffix)))
              (mv type-suffix-when-kind
                  `(defruled ,type-suffix-when-kind
                     (implies (equal (,kind-fn ,type) ,kind)
                              (equal (,type-suffix ,type ,@extra-args-names)
                                     ,default))
                     :enable ,type-suffix)))
          (b* ((type-suffix-of-constr
                (acl2::packn-pos (list type-suffix '-of- constr) suffix))
               (thm-lhs `(,type-suffix (,constr ,@field-names)
                                       ,@extra-args-names)))
            (mv type-suffix-of-constr
                `(defruled ,type-suffix-of-constr
                   (equal ,thm-lhs ,thm-rhs)
                   ,@(if fields
                         `(:expand ,thm-lhs)
                       `(:enable ,type-suffix)))))))
       (thm-events
        `(,thm-event
          (add-to-ruleset ,(deffoldred-gen-ruleset-name suffix)
                          '(,thm-name)))))
    (mv fn-term thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-sum-cases ((type symbolp)
                                  (prods flexprod-listp)
                                  (kind-fn symbolp)
                                  (suffix symbolp)
                                  (targets symbol-listp)
                                  (extra-args true-listp)
                                  (default t)
                                  (combine symbolp)
                                  (overrides alistp)
                                  (fty-table alistp))
  :returns (mv (keyword+term-list true-listp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the code for the cases of a sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a list @('(<kind1> <term1> <kind2> <term2> ...)'),
     where @('<kind1>'), @('<kind2>'), etc.
     are the kind keywords of the sum type,
     and @('<term1>'), @('<term2>'), etc. are the corresponding terms.
     This list forms the bulk of the body of
     the generated function for a sum type.")
   (xdoc::p
    "For each case, first we check whether there is an overriding term,
     in which case we use that as the term for the case.
     Otherwise, we obtain the combination for the fields.")
   (xdoc::p
    "For now, we do not generate theorems via
     @(tsee deffoldred-gen-prod-combination+theorem),
     but we plan to do that soon."))
  (b* (((when (endp prods)) (mv nil nil))
       (prod (car prods))
       (kind (flexprod->kind prod))
       ((unless (keywordp kind))
        (raise "Internal error: kind ~x0 is not a keyword." kind)
        (mv nil nil))
       ((mv term thm-events)
        (b* ((term-assoc (assoc-equal (cons type kind) overrides))
             ((when term-assoc) (mv (cdr term-assoc) nil))
             (constr (flexprod->ctor-name prod))
             ((unless (symbolp constr))
              (raise "Internal error: malformed constructor ~x0." constr)
              (mv nil nil)))
          (deffoldred-gen-prod-combination+theorem
            type constr prod kind-fn
            suffix targets extra-args default combine fty-table)))
       ((mv more-keywords+terms more-thm-events)
        (deffoldred-gen-sum-cases
          type (cdr prods) kind-fn
          suffix targets extra-args default combine overrides fty-table)))
    (mv (list* kind term more-keywords+terms)
        (append thm-events more-thm-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-prod-fold ((sum flexsum-p)
                                  (mutrecp booleanp)
                                  (suffix symbolp)
                                  (targets symbol-listp)
                                  (extra-args true-listp)
                                  (result symbolp)
                                  (default t)
                                  (combine symbolp)
                                  (overrides alistp)
                                  (fty-table alistp))
  :guard (eq (flexsum->typemacro sum) 'defprod)
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the fold function for a product type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, product types are stored as a sum types,
     but with an indication of @(tsee defprod) as the type macro.
     This sum type must have a single product entry.")
   (xdoc::p
    "If the override alist includes an entry for this product type,
     we use that as the body of the function.")
   (xdoc::p
    "If there is no overriding term,
     the body is the combination
     returned by @(tsee deffoldred-gen-prod-combination),
     which is never expected to be empty.")
   (xdoc::p
    "We also generate an `ignorable' declaration for the main formal,
     in case the overriding term does not mention the formal,
     or in case the combination is just the default.")
   (xdoc::p
    "The @('mutrecp') flag says whether
     this product type is part of a mutually recursive clique."))
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (mv '(_) nil))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       ((mv fn-body thm-events)
        (b* ((term-assoc (assoc-equal type overrides))
             ((when term-assoc) (mv (cdr term-assoc) nil))
             (prods (flexsum->prods sum))
             ((unless (flexprod-listp prods))
              (raise "Internal error: malformed products ~x0." prods)
              (mv nil nil))
             ((unless (and (consp prods)
                           (endp (cdr prods))))
              (raise "Internal error: non-singleton product ~x0." prods)
              (mv nil nil))
             (prod (car prods)))
          (deffoldred-gen-prod-combination+theorem
            type type prod nil
            suffix targets extra-args default combine fty-table)))
       (fn-event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           (declare (ignorable ,type))
           :returns (result ,result)
           :parents (,(deffoldred-gen-topic-name suffix))
           ,fn-body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:verify-guards :after-returns))
           ,@(and (not mutrecp) '(:hooks (:fix))))))
    (mv fn-event thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-sum-fold ((sum flexsum-p)
                                 (mutrecp booleanp)
                                 (suffix symbolp)
                                 (targets symbol-listp)
                                 (extra-args true-listp)
                                 (result symbolp)
                                 (default t)
                                 (combine symbolp)
                                 (overrides alistp)
                                 (fty-table alistp))
  :guard (eq (flexsum->typemacro sum) 'deftagsum)
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the fold function for a sum type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, sum types are distinguished
     from other types that are also stored as sum types
     by an indication of the type macro @(tsee deftagsum).")
   (xdoc::p
    "If the override alist includes an entry for this (whole) sum type,
     we use that as the body of the function.")
   (xdoc::p
    "Otherwise, the function is defined by cases,
     which are generated by @(tsee deffoldred-gen-sum-cases).")
   (xdoc::p
    "We also generate an `ignorable' declaration,
     in case the overriding term does not mention the formal,
     or in case all the cases are just the default.")
   (xdoc::p
    "The @('mutrecp') flag says whether
     this sum type is part of a mutually recursive clique."))
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (mv '(_) nil))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       ((mv body thm-events)
        (b* ((term-assoc (assoc-equal type overrides))
             ((when term-assoc) (mv (cdr term-assoc) nil))
             (type-case (flexsum->case sum))
             (prods (flexsum->prods sum))
             ((unless (flexprod-listp prods))
              (raise "Internal error: products ~x0 have the wrong type." prods)
              (mv nil nil))
             (kind-fn (flexsum->kind sum))
             ((unless (symbolp kind-fn))
              (raise "Internal error: malformed kind function ~x0." kind-fn)
              (mv nil nil))
             ((mv cases thm-events)
              (deffoldred-gen-sum-cases
                type prods kind-fn suffix
                targets extra-args default combine overrides fty-table)))
          (mv `(,type-case ,type ,@cases)
              thm-events)))
       (fn-event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           (declare (ignorable ,type))
           :returns (result ,result)
           :parents (,(deffoldred-gen-topic-name suffix))
           ,body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:verify-guards :after-returns))
           ,@(and (not mutrecp) '(:hooks (:fix))))))
    (mv fn-event thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-option-fold ((sum flexsum-p)
                                    (mutrecp booleanp)
                                    (suffix symbolp)
                                    (extra-args true-listp)
                                    (result symbolp)
                                    (default t)
                                    (combine symbolp)
                                    (fty-table alistp))
  :guard (eq (flexsum->typemacro sum) 'defoption)
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the fold function for an option type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, option types are stored as sum types,
     but with an indication of @(tsee defoption) as the type macro.")
   (xdoc::p
    "This function is as described in @(tsee deffold-reduce).")
   (xdoc::p
    "The @('mutrecp') flag says whether
     this option type is part of a mutually recursive clique."))
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (mv '(_) nil))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       (type-case (flexsum->case sum))
       ((mv base-type accessor)
        (components-of-flexoption-with-name type fty-table))
       (base-type-suffix (deffoldred-gen-fold-name base-type suffix))
       (extra-args-names (deffoldred-extra-args-to-names extra-args))
       (body `(,type-case ,type
                          :some (,base-type-suffix (,accessor ,type)
                                                   ,@extra-args-names)
                          :none ,default))
       (fn-event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           :returns (result ,result)
           :parents (,(deffoldred-gen-topic-name suffix))
           ,body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:verify-guards :after-returns))
           ,@(and (not mutrecp) '(:hooks (:fix)))))
       (type-suffix-when-base-type-suffix
        (acl2::packn-pos (list type-suffix '-when- base-type-suffix) suffix))
       (base-suffix-when-type-suffix-and-not-nil
        (acl2::packn-pos
         (list base-type-suffix '-when- type-suffix '-and-not-nil) suffix))
       (base-suffix-of-type-some->val
        (acl2::packn-pos (list base-type-suffix '-of- type '-some->val) suffix))
       (thm-events
        (and (eq combine 'and)
             (eq default t)
             `((defruled ,type-suffix-when-base-type-suffix
                 (implies (,base-type-suffix ,type ,@extra-args-names)
                          (,type-suffix ,type ,@extra-args-names))
                 :expand (,type-suffix ,type ,@extra-args-names)
                 :enable ,accessor)
               (defruled ,base-suffix-when-type-suffix-and-not-nil
                 (implies (and (,type-suffix ,type ,@extra-args-names)
                               ,type)
                          (,base-type-suffix ,type ,@extra-args-names))
                 :expand (,type-suffix ,type ,@extra-args-names)
                 :enable ,accessor)
               (defruled ,base-suffix-of-type-some->val
                 (implies (and (,type-suffix ,type ,@extra-args-names)
                               (,type-case ,type :some))
                          (,base-type-suffix (,accessor ,type)
                                             ,@extra-args-names))
                 :expand (,type-suffix ,type ,@extra-args-names))
               (add-to-ruleset ,(deffoldred-gen-ruleset-name suffix)
                               '(,type-suffix-when-base-type-suffix
                                 ,base-suffix-when-type-suffix-and-not-nil
                                 ,base-suffix-of-type-some->val))))))
    (mv fn-event thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-prod/sum/option-fold ((sum flexsum-p)
                                             (mutrecp booleanp)
                                             (suffix symbolp)
                                             (targets symbol-listp)
                                             (extra-args true-listp)
                                             (result symbolp)
                                             (default t)
                                             (combine symbolp)
                                             (overrides alistp)
                                             (fty-table alistp))
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the fold function for a product, sum, or option type."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the FTY table, these are all stored as sum types,
     but with a discriminator as the type macro."))
  (b* ((typemacro (flexsum->typemacro sum)))
    (cond
     ((eq typemacro 'defprod)
      (deffoldred-gen-prod-fold
        sum mutrecp suffix
        targets extra-args result default combine overrides fty-table))
     ((eq typemacro 'deftagsum)
      (deffoldred-gen-sum-fold
        sum mutrecp suffix
        targets extra-args result default combine overrides fty-table))
     ((eq typemacro 'defoption)
      (deffoldred-gen-option-fold
        sum mutrecp suffix extra-args result default combine fty-table))
     (t (prog2$
         (raise "Internal error: unsupported sum type ~x0." sum)
         (mv '(_) nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-list-fold ((list flexlist-p)
                                  (mutrecp booleanp)
                                  (suffix symbolp)
                                  (extra-args true-listp)
                                  (result symbolp)
                                  (default t)
                                  (combine symbolp)
                                  (fty-table alistp))
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate the fold function for a list type,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(tsee deffold-reduce).")
   (xdoc::p
    "The @('mutrecp') flag says whether
     this list type is part of a mutually recursive clique."))
  (b* ((type (flexlist->name list))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (mv '(_) nil))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (type-count (flexlist->count list))
       (recog (flexlist->pred list))
       (elt-recog (flexlist->elt-type list))
       ((unless (symbolp elt-recog))
        (raise "Internal error: malformed recognizer ~x0." elt-recog)
        (mv '(_) nil))
       (elt-info (flextype-with-recognizer elt-recog fty-table))
       (elt-type (flextype->name elt-info))
       (recp (flexlist->recp list))
       ((unless (symbolp elt-type))
        (raise "Internal error: malformed type name ~x0." elt-type)
        (mv '(_) nil))
       (elt-type-suffix (deffoldred-gen-fold-name elt-type suffix))
       (extra-args-names (deffoldred-extra-args-to-names extra-args))
       (body
        `(cond ((,(if (flexlist->true-listp list) 'endp 'atom) ,type)
                ,default)
               (t (,combine (,elt-type-suffix (car ,type) ,@extra-args-names)
                            (,type-suffix (cdr ,type) ,@extra-args-names)))))
       (fn-event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           :returns (result ,result)
           :parents (,(deffoldred-gen-topic-name suffix))
           ,body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:verify-guards :after-returns))
           ,@(and (not mutrecp) '(:hooks (:fix)))))
       (elt-type-suffix (deffoldred-gen-fold-name elt-type suffix))
       (type-suffix-when-atom
        (acl2::packn-pos (list type-suffix '-when-atom) suffix))
       (type-suffix-of-cons
        (acl2::packn-pos (list type-suffix '-of-cons) suffix))
       (type-suffix-of-append
        (acl2::packn-pos (list type-suffix '-of-append) suffix))
       (type-suffix-of-rcons
        (acl2::packn-pos (list type-suffix '-of-rcons) suffix))
       (elt-type-suffix-of-car-when-type-suffix
        (acl2::packn-pos (list elt-type-suffix '-of-car-when- type-suffix)
                         suffix))
       (type-suffix-of-cdr-when-type-suffix
        (acl2::packn-pos (list type-suffix '-of-cdr-when- type-suffix) suffix))
       (type1 (add-suffix-to-fn type "1"))
       (type-elem (add-suffix-to-fn type "-ELEM"))
       (thm-events
        (append
         `((defruled ,type-suffix-when-atom
             (implies (atom ,type)
                      (equal (,type-suffix ,type ,@extra-args-names)
                             ,default))
             :enable ,type-suffix)
           (defruled ,type-suffix-of-cons
             (equal (,type-suffix (cons ,elt-type ,type) ,@extra-args-names)
                    (,combine (,elt-type-suffix ,elt-type ,@extra-args-names)
                              (,type-suffix ,type ,@extra-args-names)))
             :expand (,type-suffix (cons ,elt-type ,type) ,@extra-args-names))
           (add-to-ruleset ,(deffoldred-gen-ruleset-name suffix)
                           '(,type-suffix-when-atom
                             ,type-suffix-of-cons)))
         (and (eq combine 'and)
              (eq default t)
              `((defruled ,type-suffix-of-append
                  (equal (,type-suffix (append ,type ,type1) ,@extra-args-names)
                         (and (,type-suffix ,type ,@extra-args-names)
                              (,type-suffix ,type1 ,@extra-args-names)))
                  :induct t
                  :enable (append
                           ,type-suffix
                           ,type-suffix-of-cons))
                (defruled ,type-suffix-of-rcons
                  (equal (,type-suffix (rcons ,type-elem ,type)
                                       ,@extra-args-names)
                         (and (,type-suffix ,type ,@extra-args-names)
                              (,elt-type-suffix ,type-elem ,@extra-args-names)))
                  :enable (rcons
                           ,type-suffix-of-append
                           ,type-suffix-of-cons))
                (defruled ,elt-type-suffix-of-car-when-type-suffix
                  (implies (and (,type-suffix ,type ,@extra-args-names)
                                (consp ,type))
                           (,elt-type-suffix (car ,type) ,@extra-args-names))
                  :enable ,type-suffix)
                (defruled ,type-suffix-of-cdr-when-type-suffix
                  (implies (,type-suffix ,type ,@extra-args-names)
                           (,type-suffix (cdr ,type) ,@extra-args-names))
                  :enable ,type-suffix)
                (add-to-ruleset
                 ,(deffoldred-gen-ruleset-name suffix)
                 '(,type-suffix-of-append
                   ,type-suffix-of-rcons
                   ,elt-type-suffix-of-car-when-type-suffix
                   ,type-suffix-of-cdr-when-type-suffix)))))))
    (mv fn-event thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-omap-fold ((omap flexomap-p)
                                  (mutrecp booleanp)
                                  (suffix symbolp)
                                  (extra-args true-listp)
                                  (result symbolp)
                                  (default t)
                                  (combine symbolp)
                                  (fty-table alistp))
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate a fold function for an omap type,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(tsee deffold-reduce).")
   (xdoc::p
    "The @('mutrecp') flag says whether
     this omap type is part of a mutually recursive clique."))
  (b* ((type (flexomap->name omap))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (mv '(_) nil))
       (type-suffix (deffoldred-gen-fold-name type suffix))
       (type-count (flexomap->count omap))
       (recog (flexomap->pred omap))
       (recp (flexomap->recp omap))
       (key-recog (fty::flexomap->key-type omap))
       ((unless (symbolp key-recog))
        (raise "Internal error: malformed recognizer ~x0." key-recog)
        (mv '(_) nil))
       (key-info (fty::flextype-with-recognizer key-recog fty-table))
       (key-type (or (and key-info
                          (fty::flextype->name key-info))
                     (case key-recog
                       (integerp 'acl2::int)
                       (t (raise "Not supported yet: key-recog.")))))
       (val-recog (flexomap->val-type omap))
       ((unless (symbolp val-recog))
        (raise "Internal error: malformed recognizer ~x0." val-recog)
        (mv '(_) nil))
       (val-info (flextype-with-recognizer val-recog fty-table))
       (val-type (flextype->name val-info))
       (val-type-suffix (deffoldred-gen-fold-name val-type suffix))
       (extra-args-names (deffoldred-extra-args-to-names extra-args))
       (body
        `(cond ((not (mbt (,recog ,type))) ,default)
               ((omap::emptyp ,type) ,default)
               (t (,combine (,val-type-suffix (omap::head-val ,type)
                                              ,@extra-args-names)
                            (,type-suffix (omap::tail ,type)
                                          ,@extra-args-names)))))
       (fn-event
        `(define ,type-suffix ((,type ,recog) ,@extra-args)
           :returns (result ,result)
           :parents (,(deffoldred-gen-topic-name suffix))
           ,body
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:verify-guards :after-returns))
           ,@(and (not mutrecp) '(:hooks (:fix)))))
       (type-suffix-when-emptyp
        (acl2::packn-pos (list type-suffix '-when-emptyp) suffix))
       (type-suffix-of-tail
        (acl2::packn-pos (list type-suffix '-of-tail) suffix))
       (type-suffix-of-update
        (acl2::packn-pos (list type-suffix '-of-update) suffix))
       (val-type-suffix-of-head-when-type-suffix
        (acl2::packn-pos (list val-type-suffix '-of-head-when- type-suffix)
                         suffix))
       (thm-events
        (append
         `((defruled ,type-suffix-when-emptyp
             (implies (omap::emptyp ,type)
                      (equal (,type-suffix ,type ,@extra-args-names)
                             ,default))
             :enable ,type-suffix)
           (add-to-ruleset ,(deffoldred-gen-ruleset-name suffix)
                           '(,type-suffix-when-emptyp)))
         (and (eq combine 'and)
              (eq default t)
              `((defruled ,type-suffix-of-tail
                  (implies (and (,recog ,type)
                                (,type-suffix ,type
                                              ,@extra-args-names))
                           (,type-suffix (omap::tail ,type)
                                         ,@extra-args-names))
                  :enable ,type-suffix)
                (defruled ,type-suffix-of-update
                  (implies (and (,recog ,type)
                                (,val-type-suffix ,val-type ,@extra-args-names)
                                (,type-suffix ,type ,@extra-args-names))
                           (,type-suffix (omap::update ,key-type
                                                       ,val-type
                                                       ,type)
                                         ,@extra-args-names))
                  :induct t
                  :enable (,type-suffix
                           ,recog
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
                                             ,@extra-args-names))
                  :enable ,type-suffix)
                (add-to-ruleset
                 ,(deffoldred-gen-ruleset-name suffix)
                 '(,type-suffix-of-tail
                   ,type-suffix-of-update
                   ,val-type-suffix-of-head-when-type-suffix)))))))
    (mv fn-event thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-type-fold (flex
                                  (mutrecp booleanp)
                                  (suffix symbolp)
                                  (targets symbol-listp)
                                  (extra-args true-listp)
                                  (result symbolp)
                                  (default t)
                                  (combine symbolp)
                                  (overrides alistp)
                                  (fty-table alistp))
  :returns (mv (fn-event acl2::pseudo-event-formp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate a fold function for a type, with accompanying theorems."
  (cond ((flexsum-p flex)
         (deffoldred-gen-prod/sum/option-fold
           flex mutrecp suffix
           targets extra-args result default combine overrides fty-table))
        ((flexlist-p flex)
         (deffoldred-gen-list-fold flex mutrecp suffix
           extra-args result default combine fty-table))
        ((flexomap-p flex)
         (deffoldred-gen-omap-fold flex mutrecp suffix
           extra-args result default combine fty-table))
        (t (prog2$ (raise "Internal error: unsupported type ~x0." flex)
                   (mv '(_) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-types-folds ((flexs true-listp)
                                    (mutrecp booleanp)
                                    (suffix symbolp)
                                    (targets symbol-listp)
                                    (extra-args true-listp)
                                    (result symbolp)
                                    (default t)
                                    (combine symbolp)
                                    (overrides alistp)
                                    (fty-table alistp))
  :returns (mv (fn-events acl2::pseudo-event-form-listp)
               (thm-events acl2::pseudo-event-form-listp))
  :short "Generate fold functions for a list of types,
          with accompanying theorems."
  (b* (((when (endp flexs)) (mv nil nil))
       ((mv fn-event thm-events)
        (deffoldred-gen-type-fold
          (car flexs) mutrecp suffix
          targets extra-args result default combine overrides fty-table))
       ((mv more-fn-events more-thm-events)
        (deffoldred-gen-types-folds
          (cdr flexs) mutrecp suffix
          targets extra-args result default combine overrides fty-table)))
    (mv (cons fn-event more-fn-events)
        (append thm-events more-thm-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-clique-fold/folds ((clique flextypes-p)
                                          (suffix symbolp)
                                          (targets symbol-listp)
                                          (extra-args true-listp)
                                          (result symbolp)
                                          (default t)
                                          (combine symbolp)
                                          (overrides alistp)
                                          (fty-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate a fold function,
          or a clique of mutually recursive fold functions,
          for a clique of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function or clique of functions may be followed by theorems.
     This is why this function returns a list of events.")
   (xdoc::p
    "If the clique is empty, it is an internal error.
     If the clique is a singleton, we generate a single function,
     which may be recursive or not,
     based on the flag we read from the information about the type.
     If the clique consists of two or more types,
     we generate a clique of mutually recursive functions,
     with a @(tsee deffixequiv-mutual) after the @('///'),
     and with the deferred events after that;
     the name of the clique of functions is derived from
     the name of the clique of types.")
   (xdoc::p
    "We also generate a @(':flag-local nil') to export
     the flag macro @('defthm-<name>-flag'),
     where @('<name>') is the name of the @(tsee defines) clique.
     This facilitates proving theorems by induction on the functions.")
   (xdoc::p
    "We also generate a form to allow bogus mutual recursion,
     since we have no control on how the user overrides the boilerplate.
     Note that this form is automatically local to the @(tsee defines)."))
  (b* ((members (flextypes->types clique))
       ((unless (true-listp members))
        (raise "Internal error: malformed members of type clique ~x0." clique))
       ((when (endp members))
        (raise "Internal error: empty type clique ~x0." clique))
       ((when (endp (cdr members)))
        (b* (((mv fn-event thm-events)
              (deffoldred-gen-type-fold
                (car members) nil suffix
                targets extra-args result default combine overrides fty-table)))
          (cons fn-event thm-events)))
       (clique-name (flextypes->name clique))
       ((unless (symbolp clique-name))
        (raise "Internal error: malformed clique name ~x0." clique-name))
       (clique-name-suffix (deffoldred-gen-fold-name clique-name suffix))
       ((mv fn-events thm-events)
        (deffoldred-gen-types-folds
          members t suffix
          targets extra-args result default combine overrides fty-table)))
    `((defines ,clique-name-suffix
        :parents (,(deffoldred-gen-topic-name suffix))
        ,@fn-events
        :hints (("Goal" :in-theory (enable o< o-finp)))
        :verify-guards :after-returns
        :flag-local nil
        :prepwork ((set-bogus-mutual-recursion-ok t))
        ///
        (deffixequiv-mutual ,clique-name-suffix
          :hints (("Goal" :in-theory (disable (tau-system))))))
      ,@thm-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-cliques-folds ((clique-names symbol-listp)
                                      (suffix symbolp)
                                      (targets symbol-listp)
                                      (extra-args true-listp)
                                      (result symbolp)
                                      (default t)
                                      (combine symbolp)
                                      (overrides alistp)
                                      (fty-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate fold functions, or fold function cliques,
          for a list of type cliques with given names."
  (b* (((when (endp clique-names)) nil)
       (clique-name (car clique-names))
       (clique (flextypes-with-name clique-name fty-table))
       ((unless clique)
        (raise "Internal error: no type clique with name ~x0." clique-name))
       ((unless (flextypes-p clique))
        (raise "Internal error: malformed type clique ~x0." clique))
       (events (deffoldred-gen-clique-fold/folds
                 clique suffix
                 targets extra-args result default combine
                 overrides fty-table))
       (more-events (deffoldred-gen-cliques-folds
                      (cdr clique-names) suffix
                      targets extra-args result default combine
                      overrides fty-table)))
    (append events more-events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-gen-everything ((suffix symbolp)
                                   (types symbol-listp)
                                   (targets symbol-listp)
                                   (extra-args true-listp)
                                   (result symbolp)
                                   (default t)
                                   (combine symbolp)
                                   (overrides alistp)
                                   (parents-presentp booleanp)
                                   parents
                                   (short-presentp booleanp)
                                   short
                                   (long-presentp booleanp)
                                   long
                                   (fty-table alistp)
                                   (print acl2::evmac-input-print-p))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate all the events."
  (b* ((fold-events
        (deffoldred-gen-cliques-folds
          types suffix targets extra-args result default combine
          overrides fty-table))
       (xdoc-name (deffoldred-gen-topic-name suffix))
       (xdoc-event
        `(acl2::defxdoc+ ,xdoc-name
           ,@(and parents-presentp `(:parents ,parents))
           ,@(and short-presentp `(:short ,short))
           ,@(and long-presentp `(:long ,long))
           :order-subtopics t))
       (ruleset-event
         `(def-ruleset! ,(deffoldred-gen-ruleset-name suffix) nil))
       (encapsulate
         `(encapsulate
            ()
            ,xdoc-event
            ,ruleset-event
            ,@fold-events))
       (encapsulate (acl2::restore-output? (eq print :all) encapsulate))
       (print-result (if (member-eq print '(:result :info))
                         `((acl2::cw-event "~x0~|" ',encapsulate))
                       nil)))
    `(progn
       ,@print-result
       ,encapsulate
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-process-inputs-and-gen-everything ((args true-listp)
                                                      (wrld plist-worldp))
  :returns (mv erp (event acl2::pseudo-event-formp))
  :parents (deffold-reduce-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       (fty-table (acl2::table-alist+ 'flextypes-table wrld))
       ((erp suffix
             types
             targets
             extra-args
             result
             default
             combine
             overrides
             parents-presentp
             parents
             short-presentp
             short
             long-presentp
             long
             print)
        (deffoldred-process-inputs args fty-table)))
    (retok (deffoldred-gen-everything
             suffix
             types
             targets
             extra-args
             result
             default
             combine
             overrides
             parents-presentp
             parents
             short-presentp
             short
             long-presentp
             long
             fty-table
             print))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffoldred-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event acl2::pseudo-event-formp) state)
  :parents (deffold-reduce-implementation)
  :short "Event expansion of @(tsee deffold-reduce)."
  (b* (((mv erp event)
        (deffoldred-process-inputs-and-gen-everything args (w state)))
       ((when erp) (acl2::er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deffoldred-macro-definition
  :parents (deffold-reduce-implementation)
  :short "Definition of @(tsee deffold-reduce)."
  (defmacro deffold-reduce (&rest args)
    `(acl2::make-event-terse (deffoldred-fn ',args 'deffold-reduce state))))
