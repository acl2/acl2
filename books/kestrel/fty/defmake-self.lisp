; FTY Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
; Contributions by: Eric McCarthy (bendyarm at GitHub)

; Based on deffold-reduce.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/screen-printing" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(include-book "database")
(include-book "dependencies")
(include-book "defresult")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable tau-system)))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "std/lists/true-listp" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/pseudo-event-form-listp" :dir :system))
(local (include-book "std/system/pseudo-event-formp" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Aliases in the FTY package

(defmacro patbind-reterr (&rest args) `(acl2::patbind-reterr ,@args))

(defmacro patbind-erp (&rest args) `(acl2::patbind-erp ,@args))

(defmacro patbind-macro (&rest args) `(acl2::patbind-macro ,@args))

(defmacro retmsg$ (&rest args) `(acl2::retmsg$ ,@args))

(defmacro retok (&rest args) `(acl2::retok ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defmake-self

 :items

 ((xdoc::evmac-topic-implementation-item-input "type")

  ;; TODO: I think print is missing from the deffolds
  (xdoc::evmac-topic-implementation-item-input "print")

  (xdoc::evmac-topic-implementation-item-input "parents")

  (xdoc::evmac-topic-implementation-item-input "short")

  (xdoc::evmac-topic-implementation-item-input "long")

  "@('type') is either the name of an FTY type, or the name of a type clique."

  "@('fty-table') is the alist of the table of all (fix)types
   (except some built-in ones, such as @('nat')),
   i.e. the table @('flextypes-table').
   The format is defined in @('[books]/centaur/fty/database.lisp').
   It has one entry for each mutually recursive clique of types,
   with singly recursive or non-recursive types
   being in singleton cliques."

  "@('make-self-table') is the alist of the table of registered ``make-self''
   functions. A type name maps to the corresponding ``make-self'' function.
   A non-singleton type clique name maps to @('nil') to indicate that
   ``make-self'' functions have been generated and registered for all functions
   in the clique."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The table of registered "make-self" functions. A type name maps to the
;; corresponding "make-self" function. A non-singleton type clique name maps to
;; nil to indicate that "make-self" functions have been generated and
;; registered for all functions in the clique.
(table make-self)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Provenance for :universal dispatchers: a dispatcher name maps to the root
;; clique it was generated for.  This distinguishes a redundant re-submission
;; (same name, same root) from a conflicting one (same name, different root).
(table make-self-universal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing defmake-self)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defmake-self-allowed-options*
  :short "Keyword options accepted by @(tsee defmake-self)."
  '(:ctor-style
    :universal
    :parents
    :short
    :long
    :print))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-process-inputs
  ((args true-listp))
  :returns (mv (er? acl2::maybe-msgp)
               (type symbolp)
               (ctor-style symbolp)
               (universal symbolp)
               (parents-presentp booleanp)
               parents
               (short-presentp booleanp)
               short
               (long-presentp booleanp)
               long
               (print acl2::evmac-input-print-p))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil nil nil)
       ((mv erp type options)
        (partition-rest-and-keyword-args args *defmake-self-allowed-options*))
       ((when (or erp
                  (not (consp type))
                  (not (endp (cdr type)))))
        (retmsg$ "The inputs must be the type (clique) name ~
                  followed by the options ~&0."
                 *defmake-self-allowed-options*))
       (type (car type))
       ((unless (and (symbolp type) type))
        (retmsg$ "The TYPE input must be a symbol other than NIL,
                  but it is ~x0 instead."
                 type))
       (ctor-style-option (assoc-eq :ctor-style options))
       (ctor-style (if (consp ctor-style-option)
                       (cdr ctor-style-option)
                     :positional))
       ((unless (member-eq ctor-style '(:positional :maker)))
        (retmsg$ "The :CTOR-STYLE input, if specified, must be ~
                  :POSITIONAL (the default) or :MAKER, ~
                  but it is ~x0 instead."
                 ctor-style))
       (universal-option (assoc-eq :universal options))
       (universal (cdr universal-option))
       ((when (and (consp universal-option)
                   (not (and (symbolp universal) universal))))
        (retmsg$ "The :UNIVERSAL input, if specified, must be a symbol other ~
                  than NIL naming the dispatcher function to generate, ~
                  but it is ~x0 instead."
                 universal))
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
        (retmsg$ "The :PRINT input must be one of: nil, :error, :result, ~
                  :info, or :all, but it is ~x0 instead."
                 print-option))
       (print (if (consp print-option)
                  (cdr print-option)
                :result)))
    (retok type
           ctor-style
           universal
           parents-presentp
           parents
           short-presentp
           short
           long-presentp
           long
           print))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defmake-self)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-topic-name ((type symbolp))
  :returns (name symbolp)
  :short "Generate the name of the XDOC topic."
  (acl2::packn-pos (list 'make-self- type) type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-name
  ((type symbolp))
  :returns (name symbolp)
  :short "Generate the name of the ``make-self'' function for a type."
  (acl2::packn-pos (list type '-make-self) type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-get-make-self-fn
  ((type symbolp)
   (make-self-table alistp))
  :returns (mv (er? acl2::maybe-msgp)
               (fn symbolp))
  :short "Get the name of the ``make-self'' function for a type."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the type has an entry in the @('make-self') table, use that.
      Otherwise, generate the name."))
  (b* (((reterr) nil)
       (lookup (assoc-eq type make-self-table))
       ((unless lookup)
        (retok (defmake-self-gen-name type)))
       (fn (cdr lookup)))
    (if (symbolp fn)
        (retok fn)
      (retmsg$ "Internal error: malformed value ~x0 for type ~x1
                in the make-self table."
               fn type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-sum-case
  ((type symbolp)
   (prod flexprod-p)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns term
  :short "Generate the ``make-self'' calls for the fields of a product type."
  :long
  (xdoc::topstring
   (xdoc::p
     "When @('ctor-style') is @(':maker'), the generated form uses the keyword
      constructor macro (e.g. @('make-foo')) with @(':field') keywords;
      otherwise it uses the by-position constructor function (e.g. @('foo'))."))
  (b* ((fields (flexprod->fields prod))
       ((unless (flexprod-field-listp fields))
        (raise "Internal error: malformed fields ~x0." fields))
       (ctor (if (eq ctor-style :maker)
                 (flexprod->ctor-macro prod)
               (flexprod->ctor-name prod)))
       (make-selfs
         (defmake-self-gen-sum-case-loop
           type fields member-names ctor-style fty-table make-self-table)))
    (list* 'list (list 'quote ctor) make-selfs))

  :prepwork
  ((define defmake-self-gen-sum-case-loop
     ((type symbolp)
      (fields flexprod-field-listp)
      (member-names symbol-listp)
      (ctor-style symbolp)
      (fty-table alistp)
      (make-self-table alistp))
     :returns (make-selfs true-listp)
     :parents nil
     (b* (((when (endp fields)) nil)
          (field (car fields))
          (recog (flexprod-field->type field))
          ((unless (symbolp recog))
           (raise "Internal error: malformed field recognizer ~x0." recog))
          (field-name (flexprod-field->name field))
          ((unless (symbolp field-name))
           (raise "Internal error: malformed field name ~x0." field-name))
          (kwd (intern-in-package-of-symbol (symbol-name field-name) :keyword))
          (info (flextype-with-recognizer recog fty-table))
          (field-type (and info
                           (flextype->name info)))
          (accessor (flexprod-field->acc-name field))
          ((mv erp field-type-make-self)
           (if field-type
               (defmake-self-get-make-self-fn field-type make-self-table)
             (mv nil nil)))
          ((when erp)
           (raise "~@0~%" erp))
          (make-self (if field-type
                         `(,field-type-make-self (,accessor ,type))
                       `(,accessor ,type)))
          (make-selfs
           (defmake-self-gen-sum-case-loop
             type (cdr fields) member-names ctor-style fty-table make-self-table)))
       (if (eq ctor-style :maker)
           (list* kwd make-self make-selfs)
         (cons make-self make-selfs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-sum-cases
  ((type symbolp)
   (prods flexprod-listp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (keyword+term-list true-listp)
  :short "Generate the code for the cases of a sum type."
  (b* (((when (endp prods)) nil)
       (prod (car prods))
       (kind (flexprod->kind prod))
       ((unless (keywordp kind))
        (raise "Internal error: kind ~x0 is not a keyword." kind)))
    (list* kind
           (defmake-self-gen-sum-case
             type prod member-names ctor-style fty-table make-self-table)
           (defmake-self-gen-sum-cases
             type (cdr prods) member-names ctor-style fty-table make-self-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-prod
  ((sum flexsum-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :guard (eq (flexsum->typemacro sum) 'defprod)
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a product type."
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-make-self (defmake-self-gen-name type))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       (body
        (b* ((prods (flexsum->prods sum))
             ((unless (flexprod-listp prods))
              (raise "Internal error: malformed products ~x0." prods))
             ((unless (and (consp prods)
                           (endp (cdr prods))))
              (raise "Internal error: non-singleton product ~x0." prods))
             (prod (car prods)))
          (defmake-self-gen-sum-case
            type prod member-names ctor-style fty-table make-self-table))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,topic-name)
       ,body
       ,@(cond (mutrecp
                 `(:measure (acl2::nat-list-measure
                              (list (,type-count ,type) 1))))
               (recp
                 `(:measure (,type-count ,type)))
               (t nil))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-sum
  ((sum flexsum-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :guard (eq (flexsum->typemacro sum) 'deftagsum)
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a sum type."
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-make-self (defmake-self-gen-name type))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       (body
        (b* ((type-case (flexsum->case sum))
             (prods (flexsum->prods sum))
             ((unless (flexprod-listp prods))
              (raise "Internal error: products ~x0 have the wrong type."
                     prods))
             (cases
               (defmake-self-gen-sum-cases
                 type prods member-names ctor-style fty-table make-self-table)))
          `(,type-case ,type ,@cases))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,topic-name)
       ,body
       ,@(cond (mutrecp
                 `(:measure (acl2::nat-list-measure
                              (list (,type-count ,type) 1))))
               (recp
                 `(:measure (,type-count ,type)))
               (t nil))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-option
  ((sum flexsum-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (fty-table alistp))
  :guard (eq (flexsum->typemacro sum) 'defoption)
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for an option type."
  (b* ((type (flexsum->name sum))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-make-self (defmake-self-gen-name type))
       (type-count (flexsum->count sum))
       (recog (flexsum->pred sum))
       (recp (flexsum->recp sum))
       (type-case (flexsum->case sum))
       ((mv base-type accessor)
        (components-of-flexoption-with-name type fty-table))
       (base-flextype (flextype-with-name base-type fty-table))
       ((unless base-flextype)
        (raise "Internal error: malformed type ~x0." base-type)
        '(_))
       (base-type-make-self (defmake-self-gen-name base-type))
       (body `(,type-case ,type
                          :some (,base-type-make-self (,accessor ,type))
                          :none nil)))
    `(define ,type-make-self ((,type ,recog))
       :parents (,topic-name)
       ,body
       ,@(cond (mutrecp
                 `(:measure (acl2::nat-list-measure
                              (list (,type-count ,type) 1))))
               (recp
                 `(:measure (,type-count ,type)))
               (t nil))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-prod/sum/option
  ((sum flexsum-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a product, sum, or option
          type."
  (b* ((typemacro (flexsum->typemacro sum)))
    (cond
     ((eq typemacro 'defprod)
      (defmake-self-gen-prod
        sum mutrecp topic-name member-names ctor-style fty-table make-self-table))
     ((eq typemacro 'deftagsum)
      (defmake-self-gen-sum
        sum mutrecp topic-name member-names ctor-style fty-table make-self-table))
     ((eq typemacro 'defoption)
      (defmake-self-gen-option
        sum mutrecp topic-name fty-table))
     (t (prog2$
         (raise "Internal error: unsupported sum type ~x0." sum)
         '(_))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-list
  ((list flexlist-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate the ``make-self'' function for a list type."
  (b* ((type (flexlist->name list))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        (list '(_)))
       (type-make-self (defmake-self-gen-name type))
       (type-make-self-loop
         (acl2::packn-pos (list type-make-self '-loop) type-make-self))
       (type-count (flexlist->count list))
       (type-fix (flextype->fix list))
       (recog (flexlist->pred list))
       (elt-recog (flexlist->elt-type list))
       ((unless (symbolp elt-recog))
        (raise "Internal error: malformed recognizer ~x0." elt-recog)
        (list '(_)))
       (elt-info (flextype-with-recognizer elt-recog fty-table))
       (elt-type? (if elt-info
                      (flextype->name elt-info)
                    nil))
       (elt-type-make-self?
         (b* (((unless elt-type?)
               nil)
              ((mv erp elt-type-make-self)
               (defmake-self-get-make-self-fn elt-type? make-self-table)))
           (if erp
               (raise "~@0~%" erp)
             elt-type-make-self)))
       (loop-body
        `(if (,(if (flexlist->true-listp list) 'endp 'atom) ,type)
             nil
           (cons ,(if elt-type?
                      `(,elt-type-make-self? (car ,type))
                    `(car (,type-fix ,type)))
                 (,type-make-self-loop (cdr ,type)))))
       (body
         `(let ((list (,type-make-self-loop ,type)))
            (if list
                (cons 'list (,type-make-self-loop ,type))
              'nil))))
    `((define ,type-make-self-loop ((,type ,recog))
        :parents (,topic-name)
        ,loop-body
        ,@(if mutrecp
              `(:measure (acl2::nat-list-measure
                           (list (,type-count ,type) 0)))
            `(:measure (,(or type-count 'acl2-count) ,type))))
      (define ,type-make-self ((,type ,recog))
        :parents (,topic-name)
        ,body
        ,@(and mutrecp
               `(:measure (acl2::nat-list-measure
                            (list (,type-count ,type) 1))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-omap
  ((omap flexomap-p)
   (mutrecp booleanp)
   (topic-name symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self function for an omap type."
  (b* ((type (flexomap->name omap))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (type-make-self (defmake-self-gen-name type))
       (type-count (flexomap->count omap))
       (recog (flexomap->pred omap))
       (recp (flexomap->recp omap))
       (key-recog (flexomap->key-type omap))
       ((unless (symbolp key-recog))
        (raise "Internal error: malformed recognizer ~x0." key-recog)
        '(_))
       (key-info (flextype-with-recognizer key-recog fty-table))
       (key-type? (if key-info
                      (flextype->name key-info)
                    nil))
       (key-type-make-self?
         (b* (((unless key-type?)
               nil)
              ((mv erp key-type-make-self)
               (defmake-self-get-make-self-fn key-type? make-self-table)))
           (if erp
               (raise "~@0~%" erp)
             key-type-make-self)))
       (val-recog (flexomap->val-type omap))
       ((unless (symbolp val-recog))
        (raise "Internal error: malformed recognizer ~x0." val-recog)
        '(_))
       (val-info (flextype-with-recognizer val-recog fty-table))
       (val-type? (if val-info
                      (flextype->name val-info)
                    nil))
       (val-type-make-self?
         (b* (((unless val-type?)
               nil)
              ((mv erp val-type-make-self)
               (defmake-self-get-make-self-fn val-type? make-self-table)))
           (if erp
               (raise "~@0~%" erp)
             val-type-make-self)))
       (body
        `(if (or (not (mbt (,recog ,type)))
                 (omap::emptyp ,type))
             nil
           (list 'omap::update
                 ,(if key-type?
                      `(,key-type-make-self? (omap::head-key ,type))
                    `(omap::head-key ,type))
                 ,(if val-type?
                      `(,val-type-make-self? (omap::head-val ,type))
                    `(omap::head-val ,type))
                 (,type-make-self (omap::tail ,type))))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,topic-name)
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-type
  (flex
   (mutrecp booleanp)
   (topic-name symbolp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate the ``make-self'' function for a type."
  (cond ((flexsum-p flex)
         (list
           (defmake-self-gen-prod/sum/option
             flex mutrecp topic-name member-names ctor-style fty-table make-self-table)))
        ((flexlist-p flex)
         (defmake-self-gen-list
           flex mutrecp topic-name fty-table make-self-table))
        ((flexomap-p flex)
         (list (defmake-self-gen-omap
                 flex mutrecp topic-name fty-table make-self-table)))
        (t (prog2$ (raise "Internal error: unsupported type ~x0." flex)
                   (list '(_))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-types
  ((flexs true-listp)
   (mutrecp booleanp)
   (topic-name symbolp)
   (member-names symbol-listp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate the ``make-self'' functions for a list of types."
  (b* (((when (endp flexs)) nil)
       (events1
        (defmake-self-gen-type
          (car flexs) mutrecp topic-name member-names ctor-style fty-table make-self-table))
       (events2
        (defmake-self-gen-types
          (cdr flexs) mutrecp topic-name member-names ctor-style fty-table make-self-table)))
    (append events1 events2)))

(defrulel defmake-self-gen-types-under-iff
  (iff (defmake-self-gen-types
         flexs mutrecp topic-name member-names ctor-style fty-table make-self-table)
       (consp flexs))
  :induct t
  :enable defmake-self-gen-types)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-table-events
  ((clique-name symbolp)
   (member-names symbol-listp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate the table-events for a type clique with the given members."
  (b* ((member-table-events (defmake-self-gen-table-events-loop member-names)))
    (if (member-eq clique-name member-names)
        member-table-events
      (cons `(table make-self ',clique-name 'nil)
            member-table-events)))

  :prepwork
  ((define defmake-self-gen-table-events-loop
     ((member-names symbol-listp))
     :returns (events acl2::pseudo-event-form-listp)
     (b* (((when (endp member-names))
           nil)
          (type (first member-names))
          (make-self-name (defmake-self-gen-name (first member-names))))
       (cons `(table make-self ',type ',make-self-name)
             (defmake-self-gen-table-events-loop (rest member-names))))
     ///
     (more-returns
      (events true-listp :rule-classes :type-prescription))))

  ///
  (more-returns
   (events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-clique
  ((clique-name symbolp)
   (topic-name symbolp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (mv (er? acl2::maybe-msgp)
               (events acl2::pseudo-event-form-listp))
  :short "Generate the events for a type clique."
  (b* (((reterr) nil)
       ((when (assoc-eq clique-name make-self-table))
        (retok nil))
       (clique (flextypes-with-name clique-name fty-table))
       ((unless clique)
        (retmsg$ "Internal error: No type (clique) with name ~x0."
                 clique-name))
       ((unless (flextypes-p clique))
        (retmsg$ "Internal error: malformed type clique ~x0." clique))
       (members (flextypes->types clique))
       ((unless (and (consp members)
                     (true-listp (cdr members))))
        (retmsg$ "Internal error: malformed members of type clique ~x0."
                 clique))
       ((when (endp members))
        (retmsg$ "Internal error: empty type clique ~x0." clique))
       (member-names (flextype-list->name-list members))
       (clique-name-make-self (defmake-self-gen-name clique-name))
       ;; TODO: do the deffolds properly handle non-deftypes?
       (mutrecp (< 1 (len members)))
       (definition-events
         (defmake-self-gen-types
           members mutrecp topic-name member-names ctor-style fty-table make-self-table))
       (table-events
         (defmake-self-gen-table-events clique-name member-names))
       ((unless mutrecp)
        (retok (append definition-events table-events)))
       (defines-event
         `(defines ,clique-name-make-self
            :parents (,topic-name)
            ,@definition-events
            :hints (("Goal" :in-theory (enable o< o-finp)))
            :flag-local nil
            :prepwork ((set-bogus-mutual-recursion-ok t))
            ///
            (deffixequiv-mutual ,clique-name-make-self
              :hints (("Goal" :in-theory (disable (tau-system))))))))
    (retok (cons defines-event table-events)))
  ///
  (more-returns
   (events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-cliques
  ((clique-names symbol-listp)
   (topic-name symbolp)
   (ctor-style symbolp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (mv (er? acl2::maybe-msgp)
               (events acl2::pseudo-event-form-listp))
  :short "Generate the events for a list of type cliques."
  (b* (((reterr) nil)
       ((when (endp clique-names))
        (retok nil))
       ((erp events1)
        (defmake-self-gen-clique
          (first clique-names) topic-name ctor-style fty-table make-self-table))
       ((erp events2)
        (defmake-self-gen-cliques
          (rest clique-names) topic-name ctor-style fty-table make-self-table)))
    (retok (append events1 events2)))
  ///
  (more-returns
   (events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-universal-node-p (flex)
  :returns (yes booleanp)
  :short "Recognize an AST ``node'' type that the @(':universal') dispatcher
          can serialize directly."
  (and (flexsum-p flex)
       (let ((typemacro (flexsum->typemacro flex)))
         (if (or (eq typemacro 'defprod)
                 (eq typemacro 'deftagsum))
             t
           nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-collect-clique-nodes ((members true-listp))
  :returns (nodes true-listp)
  :short "Collect the node types among the members of a clique."
  (cond ((endp members) nil)
        ((defmake-self-universal-node-p (car members))
         (cons (car members)
               (defmake-self-collect-clique-nodes (cdr members))))
        (t (defmake-self-collect-clique-nodes (cdr members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-collect-nodes
  ((clique-names symbol-listp)
   (fty-table alistp))
  :returns (mv (er? acl2::maybe-msgp)
               (nodes true-listp))
  :short "Collect all the node types in the given closure of cliques."
  (b* (((reterr) nil)
       ((when (endp clique-names))
        (retok nil))
       (clique (flextypes-with-name (car clique-names) fty-table))
       ((unless (flextypes-p clique))
        (retmsg$ "Internal error: no type clique with name ~x0."
                 (car clique-names)))
       (members (flextypes->types clique))
       ((unless (true-listp members))
        (retmsg$ "Internal error: malformed members ~x0 of clique ~x1."
                 members (car clique-names)))
       (nodes1 (defmake-self-collect-clique-nodes members))
       ((erp nodes2)
        (defmake-self-collect-nodes (cdr clique-names) fty-table)))
    (retok (append nodes1 nodes2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-universal-cand-bindings ((nodes true-listp))
  :returns (bindings true-listp)
  :short "Accumulate candidate binding forms, one per node type."
  (b* (((when (endp nodes)) nil)
       (flex (car nodes))
       ((unless (flexsum-p flex))
        (raise "Internal error: malformed node ~x0." flex))
       (name (flexsum->name flex))
       (pred (flexsum->pred flex)))
    ;; We cons here rather than appending, to avoid case-split blow-up
    ;; in guard proof.
    (cons `(cands (if (,pred x) (cons ',name cands) cands))
          (defmake-self-gen-universal-cand-bindings (cdr nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-universal-case-clauses
  ((nodes true-listp)
   (make-self-table alistp))
  :returns (mv (er? acl2::maybe-msgp)
               (clauses true-listp))
  :short "Generate the @('node-make-self') case clauses, one per node type."
  (b* (((reterr) nil)
       ((when (endp nodes)) (retok nil))
       (flex (car nodes))
       ((unless (flexsum-p flex))
        (retmsg$ "Internal error: malformed node ~x0." flex))
       (name (flexsum->name flex))
       ((unless (symbolp name))
        (retmsg$ "Internal error: malformed type name ~x0." name))
       (pred (flexsum->pred flex))
       ((erp fn) (defmake-self-get-make-self-fn name make-self-table))
       (clause `(,name (and (,pred x) (,fn x))))
       ((erp rest)
        (defmake-self-gen-universal-case-clauses (cdr nodes) make-self-table)))
    (retok (cons clause rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-universal-doc-items ((nodes true-listp))
  :returns (items true-listp)
  :short "Generate XDOC list items linking the node types the dispatcher
          covers, one per node type."
  (b* (((when (endp nodes)) nil)
       (flex (car nodes))
       ((unless (flexsum-p flex))
        (raise "Internal error: malformed node ~x0." flex))
       (name (flexsum->name flex))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0." name)))
    ;; Qualify with the package so the @(tsee ...) link resolves regardless of
    ;; the dispatcher topic's base package (the concatenate runs when xdoc
    ;; evaluates the :long, keeping this generator free of string-guard proofs).
    (cons `(xdoc::li (xdoc::@tsee (concatenate 'string
                                              ,(symbol-package-name name)
                                              "::"
                                              ,(symbol-name name))))
          (defmake-self-gen-universal-doc-items (cdr nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-universal-first-taken-name
  ((names symbol-listp)
   (wrld plist-worldp))
  :returns taken
  :short "The first dispatcher name already in use, or @('nil') if all are
          available."
  ;; This is only consulted on a fresh generation; a redundant re-submission is
  ;; detected earlier (the dispatcher is already in the make-self table), so
  ;; this check never breaks re-submission of an identical call.
  (cond ((endp names) nil)
        ((not (acl2::new-namep (car names) wrld)) (car names))
        (t (defmake-self-universal-first-taken-name (cdr names) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-universal
  ((name symbolp)
   (topic-name symbolp)
   (clique-name symbolp)
   (clique-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp)
   (wrld plist-worldp))
  :returns (mv (er? acl2::maybe-msgp)
               (events acl2::pseudo-event-form-listp))
  :short "Generate the events for the @(':universal') dispatcher and its
          helpers."
  (b* (((reterr) nil)
       (prev (assoc-eq name (acl2::table-alist+ 'make-self-universal wrld)))
       ;; Redundant re-submission: same name and root clique; do nothing.
       ((when (and (consp prev) (eq (cdr prev) clique-name)))
        (retok nil))
       ;; Same name, different root: would conflict.
       ((when (consp prev))
        (retmsg$ "The :UNIVERSAL name ~x0 was already used to generate a ~
                  dispatcher for the type (clique) ~x1, but this call is for ~
                  ~x2.  Use a different :UNIVERSAL name."
                 name (cdr prev) clique-name))
       ((erp nodes) (defmake-self-collect-nodes clique-names fty-table))
       ((unless (consp nodes))
        (retmsg$ "Cannot generate the :UNIVERSAL dispatcher ~x0 because there ~
                  are no product or tagged-sum types in the closure of ~x1."
                 name clique-name))
       (node-cands (acl2::packn-pos (list name '-node-cands) name))
       (node-make-self (acl2::packn-pos (list name '-node-make-self) name))
       (elts-common (acl2::packn-pos (list name '-elts-common) name))
       (list-elts (acl2::packn-pos (list name '-list-elts-make-self) name))
       ;; Check that the dispatcher name and all the helper names it derives are
       ;; available, so a conflict is reported early and names the offender.
       (taken-name
        (defmake-self-universal-first-taken-name
          (list name node-cands node-make-self elts-common list-elts)
          wrld))
       ((when taken-name)
        (retmsg$ "The :UNIVERSAL dispatcher ~x0 would introduce the function ~
                  ~x1, which is already in use.  (Helper names are derived from ~
                  the :UNIVERSAL name; choose a different name.)"
                 name taken-name))
       (cand-bindings (defmake-self-gen-universal-cand-bindings nodes))
       ((erp case-clauses)
        (defmake-self-gen-universal-case-clauses nodes make-self-table))
       (doc-items (defmake-self-gen-universal-doc-items nodes))
       (events
        (list
         `(define ,node-cands (x)
            :parents (,name)
            :returns (cands true-listp)
            (b* ((cands nil)
                 ,@cand-bindings)
              cands))
         `(define ,node-make-self (ty x)
            :parents (,name)
            (case ty ,@case-clauses (otherwise nil)))
         `(define ,elts-common ((elts true-listp) (acc true-listp) firstp)
            :parents (,name)
            :returns (common true-listp :hyp (true-listp acc))
            :measure (acl2-count elts)
            (if (endp elts)
                acc
              (let ((c (,node-cands (car elts))))
                (and c (,elts-common (cdr elts)
                                     (if firstp
                                         c
                                       (acl2::intersection-equal acc c))
                                     nil)))))
         `(define ,list-elts (ty (elts true-listp))
            :parents (,name)
            :measure (acl2-count elts)
            (if (endp elts)
                nil
              (cons (,node-make-self ty (car elts))
                    (,list-elts ty (cdr elts)))))
         `(define ,name (x)
            :parents (,topic-name)
            :short (xdoc::topstring
                    "Universal ``make-self'' dispatcher for the "
                    (xdoc::@tsee (concatenate 'string
                                              ,(symbol-package-name clique-name)
                                              "::"
                                              ,(symbol-name clique-name)))
                    " type clique.")
            :long (xdoc::topstring
                   (xdoc::p
                    "Serializes any value of the AST node types in the "
                    (xdoc::@tsee (concatenate 'string
                                              ,(symbol-package-name clique-name)
                                              "::"
                                              ,(symbol-name clique-name)))
                    " clique to a constructor form: for a single node, the form
                     produced by that type's @('<type>-make-self'); for a "
                    (xdoc::@tsee "true-listp")
                    " of nodes all of one type, the corresponding @('(list
                     ...)') form (@('nil') for the empty list).  Returns a "
                    (xdoc::@tsee "fty::reserrp")
                    " when the value is ambiguous (recognized by more than one
                     node type), heterogeneous (a list with no single common
                     element type), or not a recognized node or node list.")
                   (xdoc::p
                    "It covers the following node types:")
                   (xdoc::ul ,@doc-items))
            (b* ((c (,node-cands x)))
              (cond ((and (consp c) (not (consp (cdr c))))
                     (,node-make-self (car c) x))
                    ((consp c)
                     (reserrf (list "value matches more than one AST node type"
                                    :value x :candidates c)))
                    ((null x) nil)
                    ((true-listp x)
                     (b* ((common (,elts-common x nil t)))
                       (cond ((null common)
                              (reserrf (list "not a homogeneous list of AST nodes"
                                             :value x)))
                             ((not (consp (cdr common)))
                              (cons 'list (,list-elts (car common) x)))
                             (t
                              (reserrf (list "list element type is ambiguous"
                                             :value x :candidates common))))))
                    (t
                     (reserrf (list "not a recognized AST node or node list"
                                    :value x))))))
         `(table make-self-universal ',name ',clique-name))))
    (retok events))
  ///
  (more-returns
   (events true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-prods-first-no-ctor-macro ((prods true-listp))
  :returns macro
  :short "The constructor macro for the first product type with
          @(':no-ctor-macros')."
  ;; Such a product has no keyword constructor macro, so :ctor-style :maker
  ;; cannot serialize it.
  (b* (((when (endp prods)) nil)
       (prod (car prods))
       ((unless (flexprod-p prod))
        (defmake-self-prods-first-no-ctor-macro (cdr prods)))
       ((when (flexprod->no-ctor-macros prod))
        (flexprod->ctor-macro prod)))
    (defmake-self-prods-first-no-ctor-macro (cdr prods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-members-first-no-ctor-macro ((members true-listp))
  :returns macro
  :short "The constructor macro for the first member type
          declared with @(':no-ctor-macros')."
  (b* (((when (endp members)) nil)
       (flex (car members))
       ;; Only products and tagged sums have constructor macros (the same
       ;; types for which :maker emits them).
       ((unless (defmake-self-universal-node-p flex))
        (defmake-self-members-first-no-ctor-macro (cdr members)))
       ((unless (flexsum-p flex))
        (defmake-self-members-first-no-ctor-macro (cdr members)))
       (prods (flexsum->prods flex))
       ((unless (true-listp prods))
        (defmake-self-members-first-no-ctor-macro (cdr members)))
       (macro (defmake-self-prods-first-no-ctor-macro prods))
       ((when macro) macro))
    (defmake-self-members-first-no-ctor-macro (cdr members))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-cliques-first-no-ctor-macro
  ((clique-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns macro
  :short "The constructor macro for the first clique type
          declared with @(':no-ctor-macros')."
  :long
  (xdoc::topstring
   (xdoc::p
     "Cliques already in the @('make-self') table are skipped: their
      ``make-self'' functions are not regenerated, so this call would not emit
      a maker for them."))
  (b* (((when (endp clique-names)) nil)
       (clique-name (car clique-names))
       ((when (assoc-eq clique-name make-self-table))
        (defmake-self-cliques-first-no-ctor-macro
          (cdr clique-names) fty-table make-self-table))
       (clique (flextypes-with-name clique-name fty-table))
       ((unless (flextypes-p clique))
        (defmake-self-cliques-first-no-ctor-macro
          (cdr clique-names) fty-table make-self-table))
       (members (flextypes->types clique))
       ((unless (true-listp members))
        (defmake-self-cliques-first-no-ctor-macro
          (cdr clique-names) fty-table make-self-table))
       (macro (defmake-self-members-first-no-ctor-macro members))
       ((when macro) macro))
    (defmake-self-cliques-first-no-ctor-macro
      (cdr clique-names) fty-table make-self-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-everything
  ((type/clique-name symbolp)
   (parents-presentp booleanp)
   parents
   (short-presentp booleanp)
   short
   (long-presentp booleanp)
   long
   (print acl2::evmac-input-print-p)
   (ctor-style symbolp)
   (universal symbolp)
   (fty-table alistp)
   (make-self-table alistp)
   (wrld plist-worldp))
  :returns (mv (er? acl2::maybe-msgp)
               (event acl2::pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       (main-clique
         (or (flextypes-with-name type/clique-name fty-table)
             (flextypes-containing-flextype type/clique-name fty-table)))
       ((unless main-clique)
        (retmsg$ "No type (clique) with name ~x0." type/clique-name))
       ((unless (flextypes-p main-clique))
        (retmsg$ "Internal error: malformed type clique ~x0." main-clique))
       (clique-name (flextypes->name main-clique))
       ((unless (symbolp clique-name))
        (retmsg$ "Internal error: malformed clique name ~x0." clique-name))
       (clique-names (topo-dependencies clique-name fty-table))
       ;; :maker needs the keyword constructor macros, which are absent for
       ;; types defined with :no-ctor-macros; reject such a request clearly.
       (missing-maker
        (and (eq ctor-style :maker)
             (defmake-self-cliques-first-no-ctor-macro
               clique-names fty-table make-self-table)))
       ((when missing-maker)
        (retmsg$ "Cannot use :CTOR-STYLE :MAKER because the keyword ~
                  constructor macro ~x0 is not generated: its type was defined ~
                  with :NO-CTOR-MACROS, so only the by-position constructor ~
                  exists.  Use :CTOR-STYLE :POSITIONAL, or define the type ~
                  without :NO-CTOR-MACROS."
                 missing-maker))
       (xdoc-name (defmake-self-gen-topic-name clique-name))
       ((erp make-self-events)
        (defmake-self-gen-cliques
          clique-names xdoc-name ctor-style fty-table make-self-table))
       ((erp universal-events)
        (if universal
            (defmake-self-gen-universal
              universal xdoc-name clique-name clique-names
              fty-table make-self-table wrld)
          (retok nil)))
       (xdoc-event
        `(acl2::defxdoc+ ,xdoc-name
           ,@(and parents-presentp `(:parents ,parents))
           ,@(and short-presentp `(:short ,short))
           ,@(and long-presentp `(:long ,long))
           :order-subtopics t))
       (encapsulate
        `(encapsulate
           ()
           ,xdoc-event
           ,@make-self-events
           ,@universal-events))
       (encapsulate (acl2::restore-output? (eq print :all) encapsulate))
       (print-result (if (member-eq print '(:result :info))
                         `((acl2::cw-event "~x0~|" ',encapsulate))
                       nil)))
    (retok `(progn
              ,@print-result
              ,encapsulate
              (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-process-inputs-and-gen-everything
  ((args true-listp)
   (wrld plist-worldp))
  :returns (mv (er? acl2::maybe-msgp)
               (event acl2::pseudo-event-formp))
  :parents (defmake-self-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       (fty-table (acl2::table-alist+ 'flextypes-table wrld))
       (make-self-table (acl2::table-alist+ 'make-self wrld))
       ((erp type
             ctor-style
             universal
             parents-presentp
             parents
             short-presentp
             short
             long-presentp
             long
             print)
        (defmake-self-process-inputs args)))
    (defmake-self-gen-everything
      type
      parents-presentp
      parents
      short-presentp
      short
      long-presentp
      long
      print
      ctor-style
      universal
      fty-table
      make-self-table
      wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-fn
  ((args true-listp)
   (ctx ctxp)
   state)
  :returns (mv erp
               (event acl2::pseudo-event-formp)
               state)
  :parents (defmake-self-implementation)
  :short "Event expansion of @(tsee defmake-self)."
  (b* (((mv erp event)
        (defmake-self-process-inputs-and-gen-everything args (w state)))
       ((when erp)
        (acl2::er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmake-self-macro-definition
  :parents (defmake-self-implementation)
  :short "Definition of @(tsee defmake-self)."
  (defmacro defmake-self (&rest args)
    `(acl2::make-event-terse (defmake-self-fn ',args 'defmake-self state))))
