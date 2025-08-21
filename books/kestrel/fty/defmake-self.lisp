; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

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
(include-book "std/omaps/portcullis" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(include-book "database")
(include-book "dependencies")

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

(xdoc::evmac-topic-input-processing defmake-self)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defmake-self-allowed-options*
  :short "Keyword options accepted by @(tsee defmake-self)."
  '(:parents
    :short
    :long
    :print))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-process-inputs
  ((args true-listp))
  :returns (mv (er? acl2::maybe-msgp)
               (type symbolp)
               (parents-presentp booleanp)
               parents
               (short-presentp booleanp)
               short
               (long-presentp booleanp)
               long
               (print acl2::evmac-input-print-p))
  :short "Process all the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil)
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
        (retmsg$ "The TYPE input must be a non-nil symbol,
                  but it is ~x0 instead."
                 type))
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
   (member-names symbol-listp)
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
       ((when (member-eq type member-names))
        (retok (defmake-self-gen-name type)))
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
   (fty-table alistp)
   (make-self-table alistp))
  :returns term
  :short "Generate the ``make-self'' calls for the fields of a product type."
  (b* ((fields (flexprod->fields prod))
       ((unless (flexprod-field-listp fields))
        (raise "Internal error: malformed fields ~x0." fields))
       (make-selfs
         (defmake-self-gen-sum-case-loop
           type fields member-names fty-table make-self-table)))
    (list* 'list (list 'quote (flexprod->ctor-name prod)) make-selfs))

  :prepwork
  ((define defmake-self-gen-sum-case-loop
     ((type symbolp)
      (fields flexprod-field-listp)
      (member-names symbol-listp)
      (fty-table alistp)
      (make-self-table alistp))
     :returns (make-selfs true-listp)
     :parents nil
     (b* (((when (endp fields)) nil)
          (field (car fields))
          (recog (flexprod-field->type field))
          ((unless (symbolp recog))
           (raise "Internal error: malformed field recognizer ~x0." recog))
          (info (flextype-with-recognizer recog fty-table))
          (field-type (and info
                           (flextype->name info)))
          (accessor (flexprod-field->acc-name field))
          ((unless field-type)
           (b* ((make-selfs
                 (defmake-self-gen-sum-case-loop
                   type (cdr fields) member-names fty-table make-self-table)))
             (cons `(,accessor ,type) make-selfs)))
          ((mv erp field-type-make-self)
           (defmake-self-get-make-self-fn
             field-type member-names make-self-table))
          ((when erp)
           (raise "~@0~%" erp))
          (make-self `(,field-type-make-self (,accessor ,type)))
          (make-selfs
           (defmake-self-gen-sum-case-loop
             type (cdr fields) member-names fty-table make-self-table)))
       (cons make-self make-selfs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-sum-cases
  ((type symbolp)
   (prods flexprod-listp)
   (member-names symbol-listp)
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
             type prod member-names fty-table make-self-table)
           (defmake-self-gen-sum-cases
             type (cdr prods) member-names fty-table make-self-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-prod
  ((sum flexsum-p)
   (mutrecp booleanp)
   (member-names symbol-listp)
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
            type prod member-names fty-table make-self-table))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,(defmake-self-gen-topic-name type))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-sum
  ((sum flexsum-p)
   (mutrecp booleanp)
   (member-names symbol-listp)
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
                 type prods member-names fty-table make-self-table)))
          `(,type-case ,type ,@cases))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,(defmake-self-gen-topic-name type))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-option
  ((sum flexsum-p)
   (mutrecp booleanp)
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
       :parents (,(defmake-self-gen-topic-name type))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-prod/sum/option
  ((sum flexsum-p)
   (mutrecp booleanp)
   (member-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a product, sum, or option
          type."
  (b* ((typemacro (flexsum->typemacro sum)))
    (cond
     ((eq typemacro 'defprod)
      (defmake-self-gen-prod
        sum mutrecp member-names fty-table make-self-table))
     ((eq typemacro 'deftagsum)
      (defmake-self-gen-sum
        sum mutrecp member-names fty-table make-self-table))
     ((eq typemacro 'defoption)
      (defmake-self-gen-option
        sum mutrecp fty-table))
     (t (prog2$
         (raise "Internal error: unsupported sum type ~x0." sum)
         '(_))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-list
  ((list flexlist-p)
   (mutrecp booleanp)
   (member-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a list type."
  (b* ((type (flexlist->name list))
       ((unless (symbolp type))
        (raise "Internal error: malformed type name ~x0." type)
        '(_))
       (recp (flexlist->recp list))
       (type-make-self (defmake-self-gen-name type))
       (type-count (flexlist->count list))
       (type-fix (flextype->fix list))
       (recog (flexlist->pred list))
       (elt-recog (flexlist->elt-type list))
       ((unless (symbolp elt-recog))
        (raise "Internal error: malformed recognizer ~x0." elt-recog)
        '(_))
       (elt-info (flextype-with-recognizer elt-recog fty-table))
       ((unless elt-info)
        `(define ,type-make-self ((,type ,recog))
           :parents (,(defmake-self-gen-topic-name type))
           (if (,(if (flexlist->true-listp list) 'endp 'atom) ,type)
               nil
             (list 'cons
                   (car (,type-fix ,type))
                   (,type-make-self (cdr ,type))))
           ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
           ,@(and (not mutrecp) '(:hooks (:fix)))))
       (elt-type (flextype->name elt-info))
       ((unless (symbolp elt-type))
        (raise "Internal error: malformed type name ~x0." elt-type)
        '(_))
       ((mv erp elt-type-make-self)
        (defmake-self-get-make-self-fn
          elt-type member-names make-self-table))
       ((when erp)
        (raise "~@0~%" erp)
        '(_))
       (body
        `(if (,(if (flexlist->true-listp list) 'endp 'atom) ,type)
             nil
           (list 'cons
                 (,elt-type-make-self (car ,type))
                 (,type-make-self (cdr ,type))))))
    `(define ,type-make-self ((,type ,recog))
       :parents (,(defmake-self-gen-topic-name type))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-omap
  ((omap flexomap-p)
   (mutrecp booleanp)
   (fty-table alistp))
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
       (key-type-make-self? (if key-type?
                                (defmake-self-gen-name key-type?)
                              nil))
       (val-recog (flexomap->val-type omap))
       ((unless (symbolp val-recog))
        (raise "Internal error: malformed recognizer ~x0." val-recog)
        '(_))
       (val-info (flextype-with-recognizer val-recog fty-table))
       (val-type? (if val-info
                      (flextype->name val-info)
                    nil))
       (val-type-make-self? (if val-type?
                               (defmake-self-gen-name val-type?)
                             nil))
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
       :parents (,(defmake-self-gen-topic-name type))
       ,body
       ,@(and (or mutrecp recp) `(:measure (,type-count ,type)))
       ,@(and (not mutrecp) '(:hooks (:fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-type
  (flex
   (mutrecp booleanp)
   (member-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the ``make-self'' function for a type."
  (cond ((flexsum-p flex)
         (defmake-self-gen-prod/sum/option
           flex mutrecp member-names fty-table make-self-table))
        ((flexlist-p flex)
         (defmake-self-gen-list
           flex mutrecp member-names fty-table make-self-table))
        ((flexomap-p flex)
         (defmake-self-gen-omap flex mutrecp fty-table))
        (t (prog2$ (raise "Internal error: unsupported type ~x0." flex)
                   '(_)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmake-self-gen-types
  ((flexs true-listp)
   (mutrecp booleanp)
   (member-names symbol-listp)
   (fty-table alistp)
   (make-self-table alistp))
  :returns (events acl2::pseudo-event-form-listp)
  :short "Generate the ``make-self'' functions for a list of types."
  (b* (((when (endp flexs)) nil)
       (event
        (defmake-self-gen-type
          (car flexs) mutrecp member-names fty-table make-self-table))
       (more-events
        (defmake-self-gen-types
          (cdr flexs) mutrecp member-names fty-table make-self-table)))
    (cons event more-events)))

(defrulel defmake-self-gen-types-under-iff
  (iff (defmake-self-gen-types
         flexs mutrecp member-names fty-table make-self-table)
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
           members mutrecp member-names fty-table make-self-table))
       (table-events
         (defmake-self-gen-table-events clique-name member-names))
       ((unless mutrecp)
        (retok
          (cons (mbe :logic
                     (if (acl2::pseudo-event-formp (car definition-events))
                         (car definition-events)
                       '(_))
                     :exec (car definition-events))
                table-events)))
       (defines-event
         `(defines ,clique-name-make-self
            :parents (,(defmake-self-gen-topic-name clique-name))
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
          (first clique-names) fty-table make-self-table))
       ((erp events2)
        (defmake-self-gen-cliques
          (rest clique-names) fty-table make-self-table)))
    (retok (append events1 events2)))
  ///
  (more-returns
   (events true-listp :rule-classes :type-prescription)))

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
   (fty-table alistp)
   (make-self-table alistp))
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
       ((erp make-self-events)
         (defmake-self-gen-cliques clique-names fty-table make-self-table))
       (xdoc-name (defmake-self-gen-topic-name clique-name))
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
           ,@make-self-events))
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
      fty-table
      make-self-table)))

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
