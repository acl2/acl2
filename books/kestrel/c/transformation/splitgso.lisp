; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/unambiguity")
(include-book "../syntax/validation-information")
(include-book "deftrans")
(include-book "utilities/free-vars")

(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "std/system/w" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ splitgso
  :parents (transformation-tools)
  :short "A transformation to split a global struct object."
  :long
  (xdoc::topstring
   (xdoc::p
    "This transformation targets a global struct object,
     i.e. a file-scope (i.e. top-level) object (i.e. a global variable),
     that has a struct type.
     The transformation splits it into two objects, of two new struct types,
     each with a subset of the original struct members,
     which are divided between the two new struct types (and objects).
     Member access expressions are replaced with new access expressions with
     the original object replaced with one of the new objects.
     The transformation will fail if the original object appears in any other
     sorts of expressions.")
   (xdoc::p
    "This transformation expects translation unit ensembles to be annotated
     with validation information.
     See the @(see c$::validator).")
   (xdoc::section
    "Current Limitations"
    (xdoc::ul
     (xdoc::li "Fields in a struct type declaration must not share a type
                specification (e.g., @('int x, y;') is currently unsupported,
                where @('int x; int y;') <i>is</i> supported)")
     (xdoc::li "Similarly, struct object declarations must not share a type
                specification (e.g. @('struct myStruct foo, bar;') is currently
                unsupported, while @('struct myStruct foo; struct myStuct
                bar;') is allowed.)")
     (xdoc::li "The names of the new struct objects and their types are not yet
                checked for uniqueness/shadowing."))))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Find the object and its type

(define initdeclor-list-get-idents
  ((initdeclors initdeclor-listp))
  :returns (idents ident-listp)
  (b* (((when (endp initdeclors))
        nil)
       (ident? (c$::initdeclor->ident (first initdeclors))))
    (if ident?
        (cons ident?
              (initdeclor-list-get-idents (rest initdeclors)))
      (initdeclor-list-get-idents (rest initdeclors)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-gso-decl-specs-extdecl
  ((ident identp)
   (extdecl extdeclp))
  :returns (mv found
               (type decl-spec-listp))
  (extdecl-case
   extdecl
   :fundef (mv nil nil)
   :decl (decl-case
           extdecl.unwrap
           :decl
           (if (member-equal ident
                             (initdeclor-list-get-idents extdecl.unwrap.init))
               ;; TODO: does this necessarily contain a type? Perhaps check,
               ;;   and keep looking if incomplete type.
               (mv t extdecl.unwrap.specs)
             (mv nil nil))
           :statassert (mv nil nil))
   :empty (mv nil nil)
   :asm (mv nil nil)))

(define get-gso-decl-specs-extdecl-list
  ((ident identp)
   (extdecls extdecl-listp))
  :returns (mv erp
               (type decl-spec-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (reterr (msg "No object found")))
       ((mv found type)
        (get-gso-decl-specs-extdecl ident (first extdecls))))
    (if found
        (retok type)
      (get-gso-decl-specs-extdecl-list ident (rest extdecls)))))

(define get-gso-decl-specs-transunit
  ((ident identp)
   (tunit transunitp))
  :returns (mv erp
               (type decl-spec-listp))
  (b* (((transunit tunit) tunit))
    (get-gso-decl-specs-extdecl-list ident tunit.decls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-from-dec-spec
  ((decl-spec decl-specp))
  :returns (type-spec? type-spec-optionp)
  (decl-spec-case
   decl-spec
   :stoclass nil
   :typespec decl-spec.spec
   :typequal nil
   :function nil
   :align nil
   :attrib nil
   :stdcall nil
   :declspec nil))

(define type-spec-from-dec-specs
  ((decl-specs decl-spec-listp))
  :returns (type-spec? type-spec-optionp)
  (b* (((when (endp decl-specs))
        nil)
       (type-spec? (type-spec-from-dec-spec (first decl-specs))))
    (or type-spec?
        (type-spec-from-dec-specs (rest decl-specs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-gso-type-spec
  ((ident identp)
   (tunit transunitp))
  :returns (mv erp
               (type type-specp))
  (b* (((reterr) (irr-type-spec))
       ((erp decl-specs)
        (get-gso-decl-specs-transunit ident tunit))
       (type?
         (type-spec-from-dec-specs decl-specs)))
    (if type?
        (retok type?)
      (reterr (msg "Could not convert declaration specifiers to type")))))

(define get-gso-type-name
  ((ident identp)
   (tunit transunitp))
  :returns (mv erp
               (name identp))
  (b* (((reterr) (c$::irr-ident))
       ((erp type-spec)
        (get-gso-type-spec ident tunit)))
    (type-spec-case
      type-spec
      :struct (b* (((strunispec strunispec) type-spec.spec)
                   (ident? strunispec.name))
                (if ident?
                    (retok ident?)
                  (reterr (msg "Struct type is anonymous"))))
      :otherwise (reterr (msg "Type is not a struct")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-gso-linkage-from-valid-table
  ((ident identp)
   (table c$::valid-tablep))
  :returns (mv erp
               (linkage c$::linkagep))
  (b* (((reterr) (c$::irr-linkage))
       (scopes (c$::valid-table->scopes table))
       ((when (endp scopes))
        (reterr (msg "Ill-formed validation table, no scope found")))
       ((unless (endp (rest scopes)))
        (reterr (msg "Ill-formed validation table, more than one scope found:
                      ~x0"
                     scopes)))
       (scope (first scopes))
       (ord (c$::valid-scope->ord scope))
       (lookup (assoc-equal ident ord))
       ((unless lookup)
        (reterr (msg "Global struct object ~x0 not in the validation table."
                     ident)))
       (ord-info (cdr lookup)))
    (c$::valid-ord-info-case
      ord-info
      :objfun (if (equal ord-info.type (c$::type-struct))
                  ;; TODO also check defstatus isn't undefined?
                  (retok ord-info.linkage)
                (reterr (msg "~x0 has type ~x1, not a struct type"
                             ident
                             ord-info.type)))
      :otherwise (reterr (msg "~x0 is not an object." ident)))))

(define get-gso-filepath-linkage-search
  ((ident identp)
   (tunits filepath-transunit-mapp))
  :guard (c$::filepath-transunit-map-annop tunits)
  :returns (mv erp
               (filepath filepathp)
               (linkage c$::linkagep))
  (b* (((reterr) (filepath "") (c$::irr-linkage))
       ((when (omap::emptyp tunits))
        (reterr (msg "Global struct object ~x0 does not exist." ident)))
       (filepath (c$::filepath-fix (omap::head-key tunits)))
       (tunit (omap::head-val tunits))
       ((mv erp linkage)
        (get-gso-linkage-from-valid-table
          ident
          (c$::transunit-info->table (c$::transunit->info tunit))))
       ((unless erp)
        (retok filepath linkage)))
    (get-gso-filepath-linkage-search ident (omap::tail tunits)))
  :guard-hints (("Goal" :in-theory (enable c$::filepath-transunit-map-annop
                                           c$::transunit-annop))))

(defrulel assoc-of-get-gso-filepath-linkage-search.filepath
  (implies
    (and (filepath-transunit-mapp tunits)
         (not (mv-nth 0 (get-gso-filepath-linkage-search ident tunits))))
    (omap::assoc (mv-nth 1 (get-gso-filepath-linkage-search ident tunits))
                 tunits))
  :induct t
  :enable get-gso-filepath-linkage-search)

(define get-gso-filepath-linkage
  ((filepath? c$::filepath-optionp)
   (ident identp)
   (tunits transunit-ensemblep))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv erp
               (filepath filepathp)
               (linkage c$::linkagep))
  (b* (((reterr) (filepath "") (c$::irr-linkage) )
       (unwrapped-tunits (transunit-ensemble->unwrap tunits))
       ((unless filepath?)
        (get-gso-filepath-linkage-search ident unwrapped-tunits))
       (lookup
         (omap::assoc filepath? unwrapped-tunits))
       ((unless lookup)
        (reterr (msg "Provided filepath ~x0 does not exist in the translation
                      unit ensemble."
                     filepath?)))
       (tunit (cdr lookup))
       ((erp linkage)
        (get-gso-linkage-from-valid-table
          ident
          (c$::transunit-info->table (c$::transunit->info tunit)))))
    (retok filepath? linkage))
  :guard-hints (("Goal" :in-theory (enable c$::transunit-ensemble-annop)))
  :prepwork
  ((defrulel transunit-infop-of-assoc-tunits
     (implies (and (filepath-transunit-mapp tunits)
                   (c$::filepath-transunit-map-annop tunits)
                   (omap::assoc filepath tunits))
              (c$::transunit-infop
                (c$::transunit->info
                  (cdr (omap::assoc filepath tunits)))))
     :induct t
     :enable (omap::assoc
              c$::filepath-transunit-map-annop
              c$::transunit-annop))))

(defrulel assoc-of-get-gso-filepath-linkage.filepath
  (implies
    (and (transunit-ensemblep tunits)
         (not (mv-nth 0 (get-gso-filepath-linkage filepath? ident tunits))))
    (omap::assoc (mv-nth 1 (get-gso-filepath-linkage filepath? ident tunits))
                 (transunit-ensemble->unwrap tunits)))
  :enable get-gso-filepath-linkage)

(define get-gso-info
  ((filepath? c$::filepath-optionp)
   (ident identp)
   (tunits transunit-ensemblep))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv erp
               (struct-type identp)
               (filepath filepathp)
               (linkage c$::linkagep))
  (b* (((reterr) (c$::irr-ident) (filepath "") (c$::irr-linkage))
       ((erp filepath linkage)
        (get-gso-filepath-linkage filepath? ident tunits))
       (tunit
         (omap::lookup filepath (transunit-ensemble->unwrap tunits)))
       ((erp struct-type)
        (get-gso-type-name ident tunit)))
    (retok struct-type filepath linkage)))

(defruled assoc-of-get-gso-info.filepath?
  (implies
    (and (transunit-ensemblep tunits)
         (not (mv-nth 0 (get-gso-info filepath? ident tunits))))
    (omap::assoc (mv-nth 2 (get-gso-info filepath? ident tunits))
                 (transunit-ensemble->unwrap tunits)))
  :enable get-gso-info)

(local (in-theory (enable assoc-of-get-gso-info.filepath?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct type

(define structdeclor-list-get-ident
  ((structdeclors structdeclor-listp))
  :returns (mv erp
               (ident identp))
  (b* (((reterr) (c$::irr-ident))
       ((when (endp structdeclors))
        (reterr (msg "Syntax error: there should be at least one struct
                      declarator in the struct declaration.")))
       ((unless (endp (rest structdeclors)))
        (reterr (msg "Multiple struct declarators in a single struct
                      declaration are unsupported: ~x0"
                     structdeclors)))
       ((structdeclor structdeclor) (first structdeclors))
       ((when structdeclor.expr?)
        (reterr (msg "Bit-field struct declarator is unsupported: ~x0"
                     structdeclor.expr?)))
       ((unless structdeclor.declor?)
        (reterr (msg "Syntax error: a non-bit-field struct declarator must have
                      a declarator: ~x0"
                     structdeclor))))
    (retok (declor->ident structdeclor.declor?))))

(define structdecl-member-in-listp
  ((names ident-listp)
   (structdecl structdeclp))
  :returns (mv erp
               (yes/no booleanp
                       :rule-classes :type-prescription))
  (b* (((reterr) nil))
    (structdecl-case
      structdecl
      ;; TODO: properly handle struct declarations with multiple declarators
      ;;   instead of returning error.
      :member (b* (((erp ident)
                    (structdeclor-list-get-ident structdecl.declor)))
                (retok (and (member-equal ident names) t)))
      :statassert (reterr (msg "Static assertion structure declaration
                                unsupported: ~x0"
                               structdecl.unwrap))
      :empty (retok nil))))

(define split-structdecl-list
  ((split-members ident-listp)
   (structdecls structdecl-listp))
  :returns (mv erp
               (structdecls1 structdecl-listp)
               (structdecls2 structdecl-listp))
  (b* (((reterr) nil nil)
       ((when (endp structdecls))
        (retok nil nil))
       (structdecl (structdecl-fix (first structdecls)))
       ((erp split)
        (structdecl-member-in-listp split-members structdecl))
       ((erp structdecls1 structdecls2)
        (split-structdecl-list split-members (rest structdecls))))
    (if split
        (retok structdecls1 (cons structdecl structdecls2))
      (retok (cons structdecl structdecls1) structdecls2))))

(define dup-split-struct-type-decl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (decl declp))
  :returns (mv erp
               (found booleanp
                      :rule-classes :type-prescription)
               (decls decl-listp))
  (b* (((reterr) nil nil))
    (decl-case
      decl
      :decl
      (b* ((type-spec? (type-spec-from-dec-specs decl.specs))
           ((erp type-match remanining-struct-decls split-struct-decls)
            (b* (((reterr) nil nil nil)
                 ((unless (and type-spec?
                               (endp decl.init)))
                  (retok nil nil nil)))
              (type-spec-case
                type-spec?
                :struct (b* (((strunispec strunispec) type-spec?.spec)
                             (match (equal strunispec.name original))
                             ((unless match)
                              (retok nil nil nil))
                             ((erp remanining-struct-decls split-struct-decls)
                              ;; TODO: also check that split-members are
                              ;;   all in the struct.
                              (split-structdecl-list split-members strunispec.members)))
                          (retok t remanining-struct-decls split-struct-decls))
                :otherwise (retok nil nil nil))))
           ((unless type-match)
            (retok nil (list (decl-fix decl)))))
        (retok t
               (list (decl-fix decl)
                     (c$::make-decl-decl
                       :specs (list (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-strunispec
                                          :name new1
                                          :members remanining-struct-decls)))))
                     (c$::make-decl-decl
                       :specs (list (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-strunispec
                                          :name new2
                                          :members split-struct-decls))))))))
      :statassert (retok nil (list (decl-fix decl))))))

(define decl-list-to-extdecl-list
  ((decls decl-listp))
  :returns (extdecls extdecl-listp)
  (if (endp decls)
      nil
    (cons (c$::extdecl-decl (first decls))
          (decl-list-to-extdecl-list (rest decls)))))

(define dup-split-struct-type-extdecl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (extdecl extdeclp))
  :returns (mv erp
               (found booleanp
                      :rule-classes :type-prescription)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil))
    (extdecl-case
      extdecl
      :fundef (retok nil (list (extdecl-fix extdecl)))
      :decl (b* (((erp found decls)
                  (dup-split-struct-type-decl
                    original
                    new1
                    new2
                    split-members
                    extdecl.unwrap)))
              (retok found
                     (decl-list-to-extdecl-list decls)))
      :empty (retok nil (list (extdecl-fix extdecl)))
      :asm (retok nil (list (extdecl-fix extdecl))))))

(define dup-split-struct-type-extdecl-list
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv erp
               (extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((erp found new-extdecls1)
        (dup-split-struct-type-extdecl
          original
          new1
          new2
          split-members
          (first extdecls)))
       ((when found)
        (retok (append new-extdecls1
                       (extdecl-list-fix (rest extdecls)))))
       ((erp new-extdecls2)
        (dup-split-struct-type-extdecl-list
          original
          new1
          new2
          split-members
          (rest extdecls))))
    (retok (append new-extdecls1 new-extdecls2))))

(define dup-split-struct-type-transunit
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv erp
               (new-tunit transunitp))
  (b* (((reterr) (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp extdecls)
        (dup-split-struct-type-extdecl-list
          original
          new1
          new2
          split-members
          tunit.decls)))
    (retok (make-transunit :decls extdecls :info tunit.info))))

(define dup-split-struct-type-filepath-transunit-map
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (map filepath-transunit-mapp))
  :returns (mv erp
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil)
       ((when (omap::emptyp map))
        (retok nil))
       ((erp tunit)
        (dup-split-struct-type-transunit
          original
          new1
          new2
          split-members
          (omap::head-val map)))
       ((erp map$)
        (dup-split-struct-type-filepath-transunit-map
          original
          new1
          new2
          split-members
          (omap::tail map))))
    (retok (omap::update (c$::filepath-fix (omap::head-key map))
                         tunit
                         map$)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct object

(define match-designors
  ((split-members ident-listp)
   (designors designor-listp))
  :returns (mv erp
               (match booleanp
                      :rule-classes :type-prescription))
  (b* (((reterr) nil)
       ((when (endp designors))
        (reterr
          (msg "Initializer elements without designations are unsupported.")))
       ((unless (endp (rest designors)))
        (reterr
          (msg "Initializer element with mutiple designations is unuspported:
                ~x0"
               designors)))
       (designor (first designors)))
    (designor-case
      designor
      ;; :sub case should be ill-typed, since this function should only be
      ;; called on objects with struct types (not array types).
      :sub (reterr (msg "Array index initializer element is unsupported: ~x0"
                        designor))
      :dot (retok (and (member-equal designor.name split-members) t)))))

(define split-desiniter-list
  ((split-members ident-listp)
   (desiniters desiniter-listp))
  :returns (mv erp
               (desiniter-list1 desiniter-listp)
               (desiniter-list2 desiniter-listp))
  (b* (((reterr) nil nil)
       ((when (endp desiniters))
        (retok nil nil))
       ((erp desiniters1 desiniters2)
        (split-desiniter-list split-members (rest desiniters)))
       ((desiniter desiniter) (desiniter-fix (first desiniters)))
       ((erp match)
        (match-designors split-members desiniter.designors)))
    (if match
        (retok desiniters1 (cons desiniter desiniters2))
      (retok (cons desiniter desiniters1) desiniters2))))

(defrulel split-desiniter-list.desiniter-list1-type-prescription
  (true-listp (mv-nth 1 (split-desiniter-list split-members desiniters)))
  :rule-classes :type-prescription)

(defrulel split-desiniter-list.desiniter-list2-type-prescription
  (true-listp (mv-nth 2 (split-desiniter-list split-members desiniters)))
  :rule-classes :type-prescription)

(define split-struct-initer
  ((split-members ident-listp)
   (initer initerp))
  :returns (mv erp
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((reterr) nil nil))
    (initer-case
      initer
      :single (reterr
                (msg "Assignment expression initializers are unsupported: ~x0"
                     initer.expr))
      :list (b* (((erp elems1 elems2)
                  (split-desiniter-list split-members initer.elems))
                 (elems1 (desiniter-list-fix elems1))
                 (elems2 (desiniter-list-fix elems2)))
              (retok (if (endp elems1)
                         nil
                       (c$::make-initer-list
                         :elems elems1
                         :final-comma initer.final-comma))
                     (if (endp elems2)
                         nil
                       (c$::make-initer-list
                         :elems elems2
                         :final-comma initer.final-comma)))))))

(defines match-simple-declor-ident
  :parents (splitgso-implementation)
  :short "Matches against a simple declarator."
  :long
  (xdoc::topstring
   (xdoc::p
     "A simple declarator is an identifier, potentially in nested
      parentheses. It does not have any pointer qualifiers."))

  (define match-simple-declor-ident
    ((declor declorp)
     (ident identp))
    (declare (xargs
               :type-prescription (booleanp (match-simple-declor-ident declor ident))))
    (and (endp (c$::declor->pointers declor))
         (match-simple-dirdeclor-ident (declor->direct declor) ident))
    :measure (declor-count declor))

  (define match-simple-dirdeclor-ident
    ((dirdeclor dirdeclorp)
     (ident identp))
    (declare
     (xargs
       :type-prescription (booleanp
                            (match-simple-dirdeclor-ident dirdeclor ident))))
    (dirdeclor-case
     dirdeclor
     :ident (equal dirdeclor.unwrap ident)
     :paren (match-simple-declor-ident dirdeclor.unwrap ident)
     :array nil
     :array-static1 nil
     :array-static2 nil
     :array-star nil
     :function-params nil
     :function-names nil)
    :measure (dirdeclor-count dirdeclor))

  :hints (("Goal" :in-theory (enable o< o-finp))))

(define split-struct-initdeclor
  ((target identp)
   (split-members ident-listp)
   (initdeclor initdeclorp))
  :returns (mv erp
               ;; TODO: is the generated type-prescription reasonable?
               (match booleanp
                      :rule-classes :type-prescription)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((reterr) nil nil nil)
       ((initdeclor initdeclor) initdeclor)
       ((unless (match-simple-declor-ident initdeclor.declor target))
        (retok nil nil nil))
       ((unless initdeclor.init?)
        (retok t nil nil))
       ((erp initer-option1 initer-option2)
        (split-struct-initer split-members initdeclor.init?)))
    (retok t initer-option1 initer-option2)))

(define split-struct-initdeclors
  ((target identp)
   (split-members ident-listp)
   (initdeclors initdeclor-listp))
  :returns (mv erp
               (match booleanp
                      :rule-classes :type-prescription)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  ;; Only accepts singletons for now
  ;; TODO: broaden this
  (b* (((reterr) nil nil nil)
       ((when (endp initdeclors))
        (retok nil nil nil))
       ((unless (endp (rest initdeclors)))
        (reterr
          (msg "Multiple initializer declarators are not supported: ~x0"
               initdeclors))))
    (split-struct-initdeclor target
                             split-members
                             (first initdeclors))))

(define split-gso-decl
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (decl declp))
  :returns (mv erp
               (found booleanp
                      :rule-classes :type-prescription)
               (decls decl-listp))
  (b* (((reterr) nil nil))
    (decl-case
      decl
      :decl
      (b* ((type-spec? (type-spec-from-dec-specs decl.specs))
           ((unless type-spec?)
            (retok nil (list (decl-fix decl))))
           ;; TODO: check that the object is indeed file-scope, as assumed
           ((erp match initer-option1 initer-option2)
            (type-spec-case
              type-spec?
              :struct (split-struct-initdeclors original split-members decl.init)
              :otherwise (mv nil nil nil nil)))
           ((unless match)
            (retok nil (list (decl-fix decl))))
           (decl-new1-type
             (c$::decl-spec-typespec
               (c$::type-spec-struct
                 (c$::make-strunispec
                   :name new1-type))))
           (decl-new2-type
             (c$::decl-spec-typespec
               (c$::type-spec-struct
                 (c$::make-strunispec
                   :name new2-type)))))
        (retok
          t
          (list (c$::make-decl-decl
                  :specs (c$::linkage-case
                           linkage
                           :internal (list (c$::decl-spec-stoclass
                                             (c$::stor-spec-static))
                                           decl-new1-type)
                           :otherwise (list decl-new1-type))
                  :init (list (c$::make-initdeclor
                                :declor (c$::make-declor
                                          :direct (c$::dirdeclor-ident new1))
                                :init? initer-option1)))
                (c$::make-decl-decl
                  :specs (c$::linkage-case
                           linkage
                           :internal (list (c$::decl-spec-stoclass
                                             (c$::stor-spec-static))
                                           decl-new2-type)
                           :otherwise (list decl-new2-type))
                  :init (list (c$::make-initdeclor
                                :declor (c$::make-declor
                                          :direct (c$::dirdeclor-ident new2))
                                :init? initer-option2))))))
      :statassert (retok nil (list (decl-fix decl))))))

(define split-gso-extdecl
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecl extdeclp))
  :returns (mv erp
               (found booleanp
                      :rule-classes :type-prescription)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil))
    (extdecl-case
      extdecl
      :fundef (retok nil (list (extdecl-fix extdecl)))
      :decl (b* (((erp found decls)
                  (split-gso-decl
                    original
                    linkage
                    new1
                    new2
                    new1-type
                    new2-type
                    split-members
                    extdecl.unwrap)))
              (retok found
                     (decl-list-to-extdecl-list decls)))
      :empty (retok nil (list (extdecl-fix extdecl)))
      :asm (retok nil (list (extdecl-fix extdecl))))))

(define split-gso-extdecl-list
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv erp
               (extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((erp found new-extdecls1)
        (split-gso-extdecl
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (first extdecls)))
       ((when found)
        (retok (append new-extdecls1
                       (extdecl-list-fix (rest extdecls)))))
       ((erp new-extdecls2)
        (split-gso-extdecl-list
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (rest extdecls))))
    (retok (append new-extdecls1 new-extdecls2))))

(define split-gso-transunit
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv erp
               (new-tunit transunitp))
  (b* (((reterr) (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp extdecls)
        (split-gso-extdecl-list
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          tunit.decls)))
    (retok (make-transunit :decls extdecls :info tunit.info))))

(define split-gso-filepath-transunit-map
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (map filepath-transunit-mapp))
  :returns (mv erp
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil)
       ((when (omap::emptyp map))
        (retok nil))
       ((erp tunit)
        (split-gso-transunit
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (omap::head-val map)))
       ((erp map$)
        (split-gso-filepath-transunit-map
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (omap::tail map))))
    (retok (omap::update (c$::filepath-fix (omap::head-key map))
                         tunit
                         map$)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; replace all instances of `s.field` with `s1.field` or `s2.field`.

(encapsulate ()
  (local (xdoc::set-default-parents splitgso-implementation))

  ;; TODO: check if replacement struct objects have been shadowed
  (deftrans replace-field-access
    :parents (splitgso-implementation)
    :extra-args
    ((original identp)
     (linkage c$::linkagep)
     (new1 identp)
     (new2 identp)
     (split-members ident-listp))
    :expr
    (lambda (expr original linkage new1 new2 split-members)
      (expr-case
        expr
        :ident (b* (((unless (equal expr.ident original))
                     (expr-fix expr))
                    (ident-linkage
                      (c$::var-info->linkage
                        (c$::coerce-var-info expr.info)))
                    (- (and (equal linkage ident-linkage)
                            (raise "Global struct object ~x0 occurs in illegal
                                    expression."
                                   original))))
                 (expr-fix expr))
        :const (expr-fix expr)
        :string (expr-fix expr)
        :paren (expr-paren (replace-field-access-expr
                             expr.inner
                             original
                             linkage
                             new1
                             new2
                             split-members))
        :gensel (make-expr-gensel
                  :control (replace-field-access-expr
                             expr.control
                             original
                             linkage
                             new1
                             new2
                             split-members)
                  :assocs (replace-field-access-genassoc-list
                            expr.assocs
                            original
                            linkage
                            new1
                            new2
                            split-members))
        :arrsub (make-expr-arrsub
                  :arg1 (replace-field-access-expr
                          expr.arg1
                          original
                          linkage
                          new1
                          new2
                          split-members)
                  :arg2 (replace-field-access-expr
                          expr.arg2
                          original
                          linkage
                          new1
                          new2
                          split-members))
        :funcall (make-expr-funcall
                   :fun (replace-field-access-expr
                          expr.fun
                          original
                          linkage
                          new1
                          new2
                          split-members)
                   :args (replace-field-access-expr-list
                           expr.args
                           original
                           linkage
                           new1
                           new2
                           split-members))
        ;; TODO: handle when arg is a paren (and perhaps generic selection?)
        :member (b* ((match
                       (expr-case
                         expr.arg
                         :ident (b* (((unless (equal expr.arg.ident original))
                                      nil)
                                     (ident-linkage
                                       (c$::var-info->linkage
                                         (c$::coerce-var-info expr.arg.info))))
                                  (equal linkage ident-linkage))
                         :otherwise nil))
                     ((unless match)
                      (make-expr-member
                        :arg (replace-field-access-expr
                               expr.arg
                               original
                               linkage
                               new1
                               new2
                               split-members)
                        :name expr.name)))
                  (make-expr-member
                    :arg (c$::make-expr-ident
                           :ident (if (member-equal expr.name split-members)
                                      new2
                                    new1))
                    :name expr.name))
        :memberp (make-expr-memberp
                   :arg (replace-field-access-expr
                          expr.arg
                          original
                          linkage
                          new1
                          new2
                          split-members)
                   :name expr.name)
        :complit (make-expr-complit
                   :type (replace-field-access-tyname
                           expr.type
                           original
                           linkage
                           new1
                           new2
                           split-members)
                   :elems (replace-field-access-desiniter-list
                            expr.elems
                            original
                            linkage
                            new1
                            new2
                            split-members)
                   :final-comma expr.final-comma)
        :unary (make-expr-unary
                 :op expr.op
                 :arg (replace-field-access-expr
                        expr.arg
                        original
                        linkage
                        new1
                        new2
                        split-members))
        :sizeof (expr-sizeof (replace-field-access-tyname
                               expr.type
                               original
                               linkage
                               new1
                               new2
                               split-members))
        :sizeof-ambig (prog2$
                        (raise "Misusage error: ~x0." (expr-fix expr))
                        (expr-fix expr))
        :alignof (make-expr-alignof :type (replace-field-access-tyname
                                            expr.type
                                            original
                                            linkage
                                            new1
                                            new2
                                            split-members)
                                    :uscores expr.uscores)
        :cast (make-expr-cast
                :type (replace-field-access-tyname
                        expr.type
                        original
                        linkage
                        new1
                        new2
                        split-members)
                :arg (replace-field-access-expr
                       expr.arg
                       original
                       linkage
                       new1
                       new2
                       split-members))
        :binary (make-expr-binary
                  :op expr.op
                  :arg1 (replace-field-access-expr
                          expr.arg1
                          original
                          linkage
                          new1
                          new2
                          split-members)
                  :arg2 (replace-field-access-expr
                          expr.arg2
                          original
                          linkage
                          new1
                          new2
                          split-members))
        :cond (make-expr-cond
                :test (replace-field-access-expr
                        expr.test
                        original
                        linkage
                        new1
                        new2
                        split-members)
                :then (replace-field-access-expr-option
                        expr.then
                        original
                        linkage
                        new1
                        new2
                        split-members)
                :else (replace-field-access-expr
                        expr.else
                        original
                        linkage
                        new1
                        new2
                        split-members))
        :comma (make-expr-comma
                 :first (replace-field-access-expr
                          expr.first
                          original
                          linkage
                          new1
                          new2
                          split-members)
                 :next (replace-field-access-expr
                         expr.next
                         original
                         linkage
                         new1
                         new2
                         split-members))
        :cast/call-ambig (prog2$
                           (raise "Misusage error: ~x0." (expr-fix expr))
                           (expr-fix expr))
        :cast/mul-ambig (prog2$
                          (raise "Misusage error: ~x0." (expr-fix expr))
                          (expr-fix expr))
        :cast/add-ambig (prog2$
                          (raise "Misusage error: ~x0." (expr-fix expr))
                          (expr-fix expr))
        :cast/sub-ambig (prog2$
                          (raise "Misusage error: ~x0." (expr-fix expr))
                          (expr-fix expr))
        :cast/and-ambig (prog2$
                          (raise "Misusage error: ~x0." (expr-fix expr))
                          (expr-fix expr))
        :stmt (expr-stmt (replace-field-access-block-item-list
                           expr.items
                           original
                           linkage
                           new1
                           new2
                           split-members))
        :tycompat (make-expr-tycompat
                    :type1 (replace-field-access-tyname
                             expr.type1
                             original
                             linkage
                             new1
                             new2
                             split-members)
                    :type2 (replace-field-access-tyname
                             expr.type2
                             original
                             linkage
                             new1
                             new2
                             split-members))
        :offsetof (make-expr-offsetof
                    :type (replace-field-access-tyname
                            expr.type
                            original
                            linkage
                            new1
                            new2
                            split-members)
                    :member (replace-field-access-member-designor
                              expr.member
                              original
                              linkage
                              new1
                              new2
                              split-members))
        :va-arg (make-expr-va-arg
                  :list (replace-field-access-expr
                          expr.list
                          original
                          linkage
                          new1
                          new2
                          split-members)
                  :type (replace-field-access-tyname
                          expr.type
                          original
                          linkage
                          new1
                          new2
                          split-members))
        :extension (expr-extension (replace-field-access-expr
                                     expr.expr
                                     original
                                     linkage
                                     new1
                                     new2
                                     split-members))))))

(define replace-field-access-map
  ((map filepath-transunit-mapp)
   (original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp))
  :returns (map$ filepath-transunit-mapp)
  (if (omap::emptyp map)
      nil
    (omap::update
      (c$::filepath-fix (omap::head-key map))
      (replace-field-access-transunit
        (omap::head-val map)
        original
        linkage
        new1
        new2
        split-members)
      (replace-field-access-map
        (omap::tail map)
        original
        linkage
        new1
        new2
        split-members)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-rename-filepaths
  ((map filepath-transunit-mapp))
  :returns (map$ filepath-transunit-mapp)
  (b* (((when (omap::emptyp map)) nil)
       ((mv path tunit) (omap::head map))
       (path$ (deftrans-filepath path "SPLITGSO")))
    (omap::update path$
                  (c$::transunit-fix tunit)
                  (splitgso-rename-filepaths (omap::tail map))))
  :verify-guards :after-returns)

(define splitgso-filepath-transunit-map
  ((struct-type identp)
   (filepath filepathp)
   (linkage c$::linkagep)
   (orig-struct identp)
   (new-struct1 identp)
   (new-struct2 identp)
   (new-struct-type1 identp)
   (new-struct-type2 identp)
   (split-members ident-listp)
   (map filepath-transunit-mapp))
  :guard (omap::assoc filepath map)
  :returns (mv erp
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil)
       (map (c$::filepath-transunit-map-fix map))
       ((when (equal linkage (c$::linkage-none)))
        (reterr (msg "Invalid struct object linkage: ~x0" linkage)))
       ((when (equal linkage (c$::linkage-external)))
        (b* (((erp map)
              (dup-split-struct-type-filepath-transunit-map
                struct-type
                new-struct-type1
                new-struct-type2
                split-members
                map))
             ((erp map)
              (split-gso-filepath-transunit-map
                orig-struct
                linkage
                new-struct1
                new-struct2
                new-struct-type1
                new-struct-type2
                split-members
                map))
             (map
               (replace-field-access-map
                 map
                 orig-struct
                 linkage
                 new-struct1
                 new-struct2
                 split-members)))
          (retok map)))
       (tunit (omap::lookup filepath map))
       ((erp tunit)
        (dup-split-struct-type-transunit
          struct-type
          new-struct-type1
          new-struct-type2
          split-members
          tunit))
       ((erp tunit)
        (split-gso-transunit
          orig-struct
          linkage
          new-struct1
          new-struct2
          new-struct-type1
          new-struct-type2
          split-members
          tunit))
       (tunit
         (replace-field-access-transunit
           tunit
           orig-struct
           linkage
           new-struct1
           new-struct2
           split-members)))
    (retok (omap::update (c$::filepath-fix filepath)
                         tunit
                         map))))

(define splitgso-transunit-ensemble
  ((filepath? c$::filepath-optionp)
   (orig-struct identp)
   (new-struct1 identp)
   (new-struct2 identp)
   (new-struct-type1 identp)
   (new-struct-type2 identp)
   (split-members ident-listp)
   (tunits transunit-ensemblep))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv erp
               (tunits$ transunit-ensemblep))
  (b* (((reterr) (c$::transunit-ensemble-fix tunits))
       ((erp struct-type filepath linkage)
        (get-gso-info filepath? orig-struct tunits))
       (map (transunit-ensemble->unwrap tunits))
       ((erp map)
        (splitgso-filepath-transunit-map
          struct-type
          filepath
          linkage
          orig-struct
          new-struct1
          new-struct2
          new-struct-type1
          new-struct-type2
          split-members
          map)))
    (retok
      (transunit-ensemble (splitgso-rename-filepaths map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that const-new is a symbol usable as a new named constant.
; (At least check that it is a symbol at all.)
; Return it unchanged, but with type symbolp for further use
; (or use suitable theorems).

(define ident-map
  ((strings string-listp))
  :returns (idents ident-listp)
  (if (endp strings)
      nil
    (cons (ident (first strings))
          (ident-map (rest strings))))
  :guard-hints (("Goal" :in-theory (enable string-listp))))

(defrulel transunit-ensemble-annop-of-irr-transunit-ensemble
  (c$::transunit-ensemble-annop (c$::irr-transunit-ensemble))
  :enable ((:e c$::transunit-ensemble-annop)
           (:e c$::irr-transunit-ensemble)))

(define splitgso-process-inputs (const-old
                                 const-new
                                 object-name
                                 object-filepath
                                 new-object1
                                 new-object2
                                 new-type1
                                 new-type2
                                 split-members
                                 (wrld plist-worldp))
  :returns (mv erp
               (tunits (and (transunit-ensemblep tunits)
                            (c$::transunit-ensemble-annop tunits)))
               (object-ident identp)
               (filepath? c$::filepath-optionp)
               (new-object1 identp)
               (new-object2 identp)
               (new-type1 identp)
               (new-type2 identp)
               (split-members ident-listp)
               (const-new$ symbolp))
  :short "Process the inputs."
  (b* (((reterr)
        (c$::irr-transunit-ensemble)
        (c$::irr-ident)
        nil
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        nil
        nil)
       ((unless (symbolp const-old))
        (reterr (msg "~x0 must be a symbol" const-old)))
       (tunits (acl2::constant-value const-old wrld))
       ((unless (transunit-ensemblep tunits))
        (reterr (msg "~x0 must be a translation unit ensemble." const-old)))
       ((unless (c$::transunit-ensemble-annop tunits))
        (reterr (msg "~x0 must be an annotated with validation information." const-old)))
       ((unless (or (not object-filepath)
                    (stringp object-filepath)))
        (reterr (msg "~x0 must be nil or a string" object-filepath)))
       (object-filepath
         (and object-filepath
              (filepath object-filepath)))
       ((unless (stringp object-name))
        (reterr (msg "~x0 must be a string" object-name)))
       (object-ident (c$::ident object-name))
       ((unless (stringp new-object1))
        (reterr (msg "~x0 must be a string" new-object1)))
       (new-object1 (c$::ident new-object1))
       ((unless (stringp new-object2))
        (reterr (msg "~x0 must be a string" new-object2)))
       (new-object2 (c$::ident new-object2))
       ((unless (stringp new-type1))
        (reterr (msg "~x0 must be a string" new-type1)))
       (new-type1 (c$::ident new-type1))
       ((unless (stringp new-type2))
        (reterr (msg "~x0 must be a string" new-type2)))
       (new-type2 (c$::ident new-type2))
       ((unless (string-listp split-members))
        (reterr (msg "~x0 must be a string" split-members)))
       (split-members (ident-map split-members))
       ((unless (symbolp const-new))
        (reterr (msg "~x0 must be a symbol" const-new))))
    (retok tunits
           object-ident
           object-filepath
           new-object1
           new-object2
           new-type1
           new-type2
           split-members
           const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-gen-everything
  ((tunits transunit-ensemblep)
   (object-ident identp)
   (filepath? c$::filepath-optionp)
   (new-object1 identp)
   (new-object2 identp)
   (new-type1 identp)
   (new-type2 identp)
   (split-members ident-listp)
   (const-new symbolp))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv erp (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp tunit)
        (splitgso-transunit-ensemble
          filepath?
          object-ident
          new-object1
          new-object2
          new-type1
          new-type2
          split-members
          tunits))
       (defconst-event
         `(defconst ,const-new
            ',tunit)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-process-inputs-and-gen-everything
  (const-old
   const-new
   object-name
   object-filepath
   new-object1
   new-object2
   new-type1
   new-type2
   split-members
   (wrld plist-worldp))
  :returns (mv erp (event pseudo-event-formp))
  :parents (splitgso-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp tunits
             object-ident
             filepath?
             new-object1
             new-object2
             new-type1
             new-type2
             split-members
             const-new)
        (splitgso-process-inputs const-old
                                 const-new
                                 object-name
                                 object-filepath
                                 new-object1
                                 new-object2
                                 new-type1
                                 new-type2
                                 split-members
                                 wrld))
       ((erp event)
        (splitgso-gen-everything tunits
                                 object-ident
                                 filepath?
                                 new-object1
                                 new-object2
                                 new-type1
                                 new-type2
                                 split-members
                                 const-new)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-fn (const-old
                     const-new
                     object-name
                     object-filepath
                     new-object1
                     new-object2
                     new-type1
                     new-type2
                     split-members
                     (ctx ctxp)
                     state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (splitgso-implementation)
  :short "Event expansion of @(tsee splitgso)."
  (b* (((mv erp event)
        (splitgso-process-inputs-and-gen-everything const-old
                                                    const-new
                                                    object-name
                                                    object-filepath
                                                    new-object1
                                                    new-object2
                                                    new-type1
                                                    new-type2
                                                    split-members
                                                    (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection splitgso-macro-definition
  :parents (splitgso-implementation)
  :short "Definition of @(tsee splitgso)."
  (defmacro splitgso
    (const-old
     const-new
     &key
     object-name
     object-filepath
     new-object1
     new-object2
     new-type1
     new-type2
     split-members)
    `(make-event (splitgso-fn ',const-old
                              ',const-new
                              ',object-name
                              ',object-filepath
                              ',new-object1
                              ',new-object2
                              ',new-type1
                              ',new-type2
                              ',split-members
                              'splitgso
                              state))))
