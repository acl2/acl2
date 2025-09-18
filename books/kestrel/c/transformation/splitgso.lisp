; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "kestrel/fty/deffold-map" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/unambiguity")
(include-book "../syntax/validation-information")
(include-book "../syntax/code-ensembles")
(include-book "utilities/collect-idents")
(include-book "utilities/fresh-ident")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Find the object and its type

(define type-spec-from-decl-spec
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

(define type-spec-from-decl-specs
  ((decl-specs decl-spec-listp))
  :returns (type-spec? type-spec-optionp)
  (b* (((when (endp decl-specs))
        nil)
       (type-spec? (type-spec-from-decl-spec (first decl-specs))))
    (or type-spec?
        (type-spec-from-decl-specs (rest decl-specs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-gso-linkage-from-valid-table
  ((ident identp)
   (table c$::valid-tablep))
  :returns (mv (er? maybe-msgp)
               (linkage c$::linkagep)
               (tag? ident-optionp))
  (b* (((reterr) (c$::irr-linkage) nil)
       (scopes (c$::valid-table->scopes table))
       ((when (endp scopes))
        (retmsg$ "Ill-formed validation table, no scope found"))
       ((unless (endp (rest scopes)))
        (retmsg$ "Ill-formed validation table, more than one scope found: ~x0"
                 scopes))
       (scope (first scopes))
       (ord (c$::valid-scope->ord scope))
       (lookup (assoc-equal ident ord))
       ((unless lookup)
        (retmsg$ "Global struct object ~x0 not in the validation table."
                 ident))
       (ord-info (cdr lookup)))
    (c$::valid-ord-info-case
      ord-info
      ;; TODO: also return struct tag?
      :objfun (c$::type-case
                ord-info.type
                :struct ;; TODO also check defstatus isn't undefined?
                        (retok ord-info.linkage ord-info.type.tag?)
                :otherwise (retmsg$ "~x0 has type ~x1, not a struct type"
                                    ident
                                    ord-info.type))
      :otherwise (retmsg$ "~x0 is not an object." ident))))

(define get-gso-filepath-linkage-search
  ((ident identp)
   (tunits filepath-transunit-mapp))
  :guard (c$::filepath-transunit-map-annop tunits)
  :returns (mv (er? maybe-msgp)
               (filepath filepathp)
               (linkage c$::linkagep)
               (tag? ident-optionp))
  (b* (((reterr) (filepath "") (c$::irr-linkage) nil)
       ((when (omap::emptyp tunits))
        (retmsg$ "Global struct object ~x0 does not exist." ident))
       (filepath (c$::filepath-fix (omap::head-key tunits)))
       (tunit (omap::head-val tunits))
       ((mv erp linkage tag?)
        (get-gso-linkage-from-valid-table
          ident
          (c$::transunit-info->table-end (c$::transunit->info tunit))))
       ((unless erp)
        (retok filepath linkage tag?)))
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
  :returns (mv (er? maybe-msgp)
               (filepath filepathp)
               (linkage c$::linkagep)
               (tag? ident-optionp))
  (b* (((reterr) (filepath "") (c$::irr-linkage) nil)
       (unwrapped-tunits (transunit-ensemble->unwrap tunits))
       ((unless filepath?)
        (get-gso-filepath-linkage-search ident unwrapped-tunits))
       (lookup
         (omap::assoc filepath? unwrapped-tunits))
       ((unless lookup)
        (retmsg$ "Provided filepath ~x0 does not exist in the translation unit
                  ensemble."
                 filepath?))
       (tunit (cdr lookup))
       ((erp linkage tag?)
        (get-gso-linkage-from-valid-table
          ident
          (c$::transunit-info->table-end (c$::transunit->info tunit)))))
    (retok filepath? linkage tag?))
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
  :returns (mv (er? maybe-msgp)
               (struct-tag identp)
               (filepath filepathp)
               (linkage c$::linkagep))
  (b* (((reterr) (c$::irr-ident) (filepath "") (c$::irr-linkage))
       ((erp filepath linkage tag?)
        (get-gso-filepath-linkage filepath? ident tunits))
       ((unless tag?)
        (retmsg$ "Tagless struct type is not supported.")))
    (retok tag? filepath linkage)))

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

(define struct-declor-list-get-ident
  ((structdeclors struct-declor-listp))
  :returns (mv (er? maybe-msgp)
               (ident identp))
  (b* (((reterr) (c$::irr-ident))
       ((when (endp structdeclors))
        (retmsg$ "Syntax error: there should be at least one struct declarator
                  in the struct declaration."))
       ((unless (endp (rest structdeclors)))
        (retmsg$ "Multiple struct declarators in a single struct declaration
                  are unsupported: ~x0"
                 structdeclors))
       ((struct-declor structdeclor) (first structdeclors))
       ((when structdeclor.expr?)
        (retmsg$ "Bit-field struct declarator is unsupported: ~x0"
                 structdeclor.expr?))
       ((unless structdeclor.declor?)
        (retmsg$ "Syntax error: a non-bit-field struct declarator must have
                  a declarator: ~x0"
                 structdeclor)))
    (retok (declor->ident structdeclor.declor?))))

(define structdecl-member-in-listp
  ((names ident-listp)
   (structdecl structdeclp))
  :returns (mv (er? maybe-msgp)
               (yes/no booleanp
                       :rule-classes :type-prescription))
  (b* (((reterr) nil))
    (structdecl-case
      structdecl
      ;; TODO: properly handle struct declarations with multiple declarators
      ;;   instead of returning error.
      :member (b* (((erp ident)
                    (struct-declor-list-get-ident structdecl.declor)))
                (retok (and (member-equal ident names) t)))
      :statassert (retmsg$ "Static assertion structure declaration unsupported:
                            ~x0"
                           structdecl.unwrap)
      :empty (retok nil))))

(define split-structdecl-list
  ((split-members ident-listp)
   (structdecls structdecl-listp))
  :returns (mv (er? maybe-msgp)
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

(define all-no-init
  ((initdeclors initdeclor-listp))
  (declare (xargs :type-prescription (booleanp (all-no-init initdeclors))))
  (or (endp initdeclors)
      (and (null (c$::initdeclor->init? (first initdeclors)))
           (all-no-init (rest initdeclors)))))

(define dup-split-struct-type-decl
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (decl declp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (decls decl-listp))
  (b* (((reterr) nil nil nil))
    (decl-case
      decl
      :decl
      (b* ((type-spec? (type-spec-from-decl-specs decl.specs))
           ((erp type-match new1 new2 remanining-struct-decls split-struct-decls)
            (b* (((reterr) nil nil nil nil nil)
                 ((unless (and type-spec?
                               (all-no-init decl.init)))
                  (retok nil nil nil nil nil)))
              (type-spec-case
                type-spec?
                :struct (b* (((struni-spec struni-spec) type-spec?.spec)
                             (match (equal struni-spec.name? original))
                             ((unless match)
                              (retok nil nil nil nil nil))
                             ((erp remanining-struct-decls split-struct-decls)
                              ;; TODO: also check that split-members are
                              ;;   all in the struct.
                              (split-structdecl-list split-members
                                                     struni-spec.members))
                             (new1 (or new1 struni-spec.name? (ident "new_struct")))
                             (new2 (or new2 struni-spec.name? (ident "new_struct")))
                             ((list new1 new2)
                              (fresh-idents (list new1 new2) blacklist)))
                          (retok t new1 new2 remanining-struct-decls split-struct-decls))
                :otherwise (retok nil nil nil nil nil))))
           ((unless type-match)
            (retok nil nil (list (decl-fix decl)))))
        ;; TODO: get struct-type
        (retok new1
               new2
               (list (decl-fix decl)
                     (c$::make-decl-decl
                       :specs (list (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-struni-spec
                                          :name? new1
                                          :members remanining-struct-decls)))))
                     (c$::make-decl-decl
                       :specs (list (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-struni-spec
                                          :name? new2
                                          :members split-struct-decls))))))))
      :statassert (retok nil nil (list (decl-fix decl)))))
  ///

  (defret identp-of-dup-split-struct-type-decl.new2$
    (equal (identp new2$)
           (identp new1$))))

(define decl-list-to-extdecl-list
  ((decls decl-listp))
  :returns (extdecls extdecl-listp)
  (if (endp decls)
      nil
    (cons (c$::extdecl-decl (first decls))
          (decl-list-to-extdecl-list (rest decls)))))

(define dup-split-struct-type-extdecl
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (extdecl extdeclp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil nil))
    (extdecl-case
      extdecl
      :fundef (retok nil nil (list (extdecl-fix extdecl)))
      :decl (b* (((erp new1 new2 decls)
                  (dup-split-struct-type-decl
                    original
                    new1
                    new2
                    blacklist
                    split-members
                    extdecl.unwrap)))
              (retok new1
                     new2
                     (decl-list-to-extdecl-list decls)))
      :empty (retok nil nil (list (extdecl-fix extdecl)))
      :asm (retok nil nil (list (extdecl-fix extdecl)))))
  ///

  (defret identp-of-dup-split-struct-type-extdecl.new2$
    (equal (identp new2$)
           (identp new1$)))

  (defret dup-split-struct-type-extdecl.extdecls-type-prescription
    (true-listp extdecls)
    :rule-classes :type-prescription))

(define dup-split-struct-type-extdecl-list
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (extdecls$ extdecl-listp))
  (b* (((reterr) nil nil nil)
       ((when (endp extdecls))
        (retok nil nil nil))
       ((erp new1$ new2$ new-extdecls1)
        (dup-split-struct-type-extdecl
          original
          new1
          new2
          blacklist
          split-members
          (first extdecls)))
       ((when new1$)
        (retok new1$
               new2$
               (append new-extdecls1
                       (extdecl-list-fix (rest extdecls)))))
       ((erp new1 new2 new-extdecls2)
        (dup-split-struct-type-extdecl-list
          original
          new1
          new2
          blacklist
          split-members
          (rest extdecls))))
    (retok new1 new2 (append new-extdecls1 new-extdecls2)))

  :measure (acl2-count extdecls)
  ///

  (defret identp-of-dup-split-struct-type-extdecl-list.new2$
    (equal (identp new2$)
           (identp new1$))
    :hints (("Goal" :induct t))))

(define dup-split-struct-type-transunit
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (tunit$ transunitp))
  (b* (((reterr) nil nil (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp new1 new2 extdecls)
        (dup-split-struct-type-extdecl-list
          original
          new1
          new2
          blacklist
          split-members
          tunit.decls)))
    (retok new1
           new2
           (make-transunit :decls extdecls :info tunit.info)))
    ///

    (defret identp-of-dup-split-struct-type-transunit.new2$
      (equal (identp new2$)
             (identp new1$))))

(define dup-split-struct-type-filepath-transunit-map
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (map filepath-transunit-mapp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil nil nil)
       ((when (omap::emptyp map))
        (retok nil nil nil))
       ((erp new1$ new2$ tunit)
        (dup-split-struct-type-transunit
          original
          new1
          new2
          blacklist
          split-members
          (omap::head-val map)))
       ((erp new1 new2 map$)
        (dup-split-struct-type-filepath-transunit-map
          original
          new1
          new2
          blacklist
          split-members
          (omap::tail map)))
       (new1 (or new1 new1$))
       (new2 (or new2 new2$)))
    (retok new1
           new2
           (omap::update (c$::filepath-fix (omap::head-key map))
                         tunit
                         map$)))

  :measure (acl2-count map)
  :verify-guards :after-returns
  ///

  (defret identp-of-dup-split-struct-type-filepath-transunit-map.new2$
    (equal (identp new2$)
           (identp new1$))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct object

(define match-designors
  ((split-members ident-listp)
   (designors designor-listp))
  :returns (mv (er? maybe-msgp)
               (match booleanp
                      :rule-classes :type-prescription))
  (b* (((reterr) nil)
       ((when (endp designors))
        (retmsg$ "Initializer elements without designations are unsupported."))
       ((unless (endp (rest designors)))
        (retmsg$ "Initializer element with mutiple designations is unsupported:
                  ~x0"
                 designors))
       (designor (first designors)))
    (designor-case
      designor
      ;; :sub case should be ill-typed, since this function should only be
      ;; called on objects with struct types (not array types).
      :sub (retmsg$ "Array index initializer element is unsupported: ~x0"
                    designor)
      :dot (retok (and (member-equal designor.name split-members) t)))))

(define split-desiniter-list
  ((split-members ident-listp)
   (desiniters desiniter-listp))
  :returns (mv (er? maybe-msgp)
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
      (retok (cons desiniter desiniters1) desiniters2)))
  ///

  (more-returns
   (desiniter-list1 true-listp :rule-classes :type-prescription)
   (desiniter-list2 true-listp :rule-classes :type-prescription)))

(define split-struct-initer
  ((split-members ident-listp)
   (initer initerp))
  :returns (mv (er? maybe-msgp)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((reterr) nil nil))
    (initer-case
      initer
      :single (retmsg$ "Assignment expression initializers are unsupported:
                        ~x0"
                       initer.expr)
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
     :ident (equal dirdeclor.ident ident)
     :paren (match-simple-declor-ident dirdeclor.inner ident)
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
  :returns (mv (er? maybe-msgp)
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
  :returns (mv (er? maybe-msgp)
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
        (retmsg$ "Multiple initializer declarators are not supported: ~x0"
                 initdeclors)))
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
  :returns (mv (er? maybe-msgp)
               (found booleanp
                      :rule-classes :type-prescription)
               (decls decl-listp))
  (b* (((reterr) nil nil))
    (decl-case
      decl
      :decl
      (b* ((type-spec? (type-spec-from-decl-specs decl.specs))
           ((unless type-spec?)
            (retok nil (list (decl-fix decl))))
           ;; TODO: check that the object is indeed file-scope, as assumed
           ((erp match initer-option1 initer-option2)
            (type-spec-case
              type-spec?
              :struct (split-struct-initdeclors original split-members decl.init)
              :typedef (split-struct-initdeclors original split-members decl.init)
              :otherwise (mv nil nil nil nil)))
           ((unless match)
            (retok nil (list (decl-fix decl))))
           (decl-new1-type
             (c$::decl-spec-typespec
               (c$::type-spec-struct
                 (c$::make-struni-spec
                   :name? new1-type))))
           (decl-new2-type
             (c$::decl-spec-typespec
               (c$::type-spec-struct
                 (c$::make-struni-spec
                   :name? new2-type)))))
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
  :returns (mv (er? maybe-msgp)
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
      :asm (retok nil (list (extdecl-fix extdecl)))))
  ///

  (more-returns
   (extdecls true-listp :rule-classes :type-prescription)))

(define split-gso-extdecl-list
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv (er? maybe-msgp)
               (extdecls$ extdecl-listp))
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
  :returns (mv (er? maybe-msgp)
               (tunit$ transunitp))
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
  :returns (mv (er? maybe-msgp)
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

;; Replace all instances of `s.field` with `s1.field` or `s2.field`.

;; Note: we do not handle expressions such as `(s).field`. Instead, such
;;   expressions are currently considered illegal. In the future, we should try
;;   to extract/resolve the left expression of the member access and handle it
;;   appropriately.
(encapsulate ()
  ;; TODO: something in deffold-map seems dependent on tau
  (local (in-theory (enable (tau-system))))

  (fty::deffold-map replace-field-access
    :types #!c$(exprs/decls/stmts
                fundef
                extdecl
                extdecl-list
                transunit
                filepath-transunit-map)
    :extra-args
    ((original identp)
     (linkage c$::linkagep)
     (new1 identp)
     (new2 identp)
     (split-members ident-listp))
    :parents (splitgso-implementation)
    :override
    ((c$::expr
       :ident
       (b* ((original (ident-fix original))
            (linkage (c$::linkage-fix linkage))
            ((unless (equal expr.ident original))
             (expr-fix c$::expr))
            (ident-linkage
              (c$::var-info->linkage
                (c$::coerce-var-info expr.info)))
            (- (and (equal linkage ident-linkage)
                    (raise "Global struct object ~x0 occurs in illegal
                            expression."
                           original))))
         (expr-fix c$::expr)))
     (c$::expr
       :member
       (b* ((original (ident-fix original))
            (linkage (c$::linkage-fix linkage))
            (split-members (c$::ident-list-fix split-members))
            (match
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
               :arg (expr-replace-field-access
                      expr.arg original linkage new1 new2 split-members)
               :name expr.name)))
         (make-expr-member
           :arg (c$::make-expr-ident
                  :ident (if (member-equal expr.name split-members)
                             new2
                           new1)
                  :info nil)
           :name expr.name)))
     (c$::expr
       ;; TODO: factor out member expr matching
       :unary
       (if (and (or (equal expr.op (c$::unop-address))
                    (equal expr.op (c$::unop-sizeof)))
                (expr-case
                  expr.arg
                  :member (expr-case
                            expr.arg
                            :ident (b* ((original (ident-fix original))
                                        (linkage (c$::linkage-fix linkage))
                                        ((unless (equal expr.arg.ident original))
                                         nil)
                                        (ident-linkage
                                          (c$::var-info->linkage
                                            (c$::coerce-var-info expr.arg.info))))
                                     (equal linkage ident-linkage))
                            :otherwise nil)
                  :otherwise nil))
           (raise "Global struct object ~x0 occurs in illegal expression."
                  original)
         (make-expr-unary
           :op expr.op
           :arg (expr-replace-field-access
                  expr.arg original linkage new1 new2 split-members)
           :info nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-rename-filepaths
  ((map filepath-transunit-mapp))
  :returns (map$ filepath-transunit-mapp)
  (b* (((when (omap::emptyp map)) nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (c$::filepath-fix path)
                  (c$::transunit-fix tunit)
                  (splitgso-rename-filepaths (omap::tail map))))
  :verify-guards :after-returns)

;; TODO: add `:fragment` argument indicate the map does not represent a
;;   complete program. In such cases, fail if the gso is external.
(define splitgso-filepath-transunit-map
  ((struct-tag identp)
   (filepath filepathp)
   (linkage c$::linkagep)
   (orig-struct identp)
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (map filepath-transunit-mapp))
  :guard (omap::assoc filepath map)
  :returns (mv (er? maybe-msgp)
               (map$ filepath-transunit-mapp))
  (b* (((reterr) nil)
       (map (c$::filepath-transunit-map-fix map))
       ((when (equal linkage (c$::linkage-none)))
        (retmsg$ "Invalid struct object linkage: ~x0" linkage))
       (ident-blacklist (filepath-transunit-map-collect-idents map))
       (new-struct1 (or new-struct1 orig-struct))
       (new-struct2 (or new-struct2 orig-struct))
       ((when (equal linkage (c$::linkage-external)))
        (b* (((erp new-struct-tag1 new-struct-tag2 map)
              (dup-split-struct-type-filepath-transunit-map
                struct-tag
                new-struct-tag1
                new-struct-tag2
                ident-blacklist
                split-members
                map))
             ((when (or (not new-struct-tag1)
                        (not new-struct-tag2)))
              ;; Shouldn't happen; the AST is validated and the object is in
              ;; the validation table.
              (retmsg$ "Could not find struct type."))
             (ident-blacklist
               (insert new-struct-tag1 (insert new-struct-tag2 ident-blacklist)))
             ((list new-struct1 new-struct2)
              (fresh-idents (list new-struct1
                                  new-struct2)
                            ident-blacklist))
             ((erp map)
              (split-gso-filepath-transunit-map
                orig-struct
                linkage
                new-struct1
                new-struct2
                new-struct-tag1
                new-struct-tag2
                split-members
                map))
             (map
               (filepath-transunit-map-replace-field-access
                 map
                 orig-struct
                 linkage
                 new-struct1
                 new-struct2
                 split-members)))
          (retok map)))
       (tunit (omap::lookup filepath map))
       ((erp new-struct-tag1 new-struct-tag2 tunit)
        (dup-split-struct-type-transunit
          struct-tag
          new-struct-tag1
          new-struct-tag2
          ident-blacklist
          split-members
          tunit))
       ((when (or (not new-struct-tag1)
                  (not new-struct-tag2)))
        ;; Shouldn't happen; the AST is validated and the object is in
        ;; the validation table.
        (retmsg$ "Could not find struct type."))
       (ident-blacklist
         (insert new-struct-tag1 (insert new-struct-tag2 ident-blacklist)))
       ((list new-struct1 new-struct2)
        (fresh-idents (list new-struct1
                            new-struct2)
                      ident-blacklist))
       ((erp tunit)
        (split-gso-transunit
          orig-struct
          linkage
          new-struct1
          new-struct2
          new-struct-tag1
          new-struct-tag2
          split-members
          tunit))
       (tunit
         (transunit-replace-field-access
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
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (tunits transunit-ensemblep))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (tunits$ transunit-ensemblep))
  (b* (((reterr) (c$::transunit-ensemble-fix tunits))
       ((erp struct-tag filepath linkage)
        (get-gso-info filepath? orig-struct tunits))
       (map (transunit-ensemble->unwrap tunits))
       ((erp map)
        (splitgso-filepath-transunit-map
          struct-tag
          filepath
          linkage
          orig-struct
          new-struct1
          new-struct2
          new-struct-tag1
          new-struct-tag2
          split-members
          map)))
    (retok
      (transunit-ensemble (splitgso-rename-filepaths map)))))

(define splitgso-code-ensemble
  ((filepath? c$::filepath-optionp)
   (orig-struct identp)
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (code code-ensemblep))
  :guard (c$::transunit-ensemble-annop (code-ensemble->transunits code))
  :returns (mv (er? maybe-msgp)
               (code$ code-ensemblep))
  (b* (((reterr) (irr-code-ensemble))
       ((code-ensemble code) code)
       ((erp tunits) (splitgso-transunit-ensemble filepath?
                                                  orig-struct
                                                  new-struct1
                                                  new-struct2
                                                  new-struct-tag1
                                                  new-struct-tag2
                                                  split-members
                                                  code.transunits)))
    (retok (change-code-ensemble code :transunits tunits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-map
  ((strings string-listp))
  :returns (idents ident-listp)
  (if (endp strings)
      nil
    (cons (ident (first strings))
          (ident-map (rest strings))))
  :guard-hints (("Goal" :in-theory (enable string-listp))))

(defrulel transunit-ensemble-annop-of-irr-code-ensemble
  (c$::transunit-ensemble-annop
   (code-ensemble->transunits (c$::irr-code-ensemble)))
  :enable ((:e c$::transunit-ensemble-annop)
           (:e c$::irr-code-ensemble)))

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
  :returns (mv (er? maybe-msgp)
               (code (and (code-ensemblep code)
                          (c$::transunit-ensemble-annop
                           (code-ensemble->transunits code))))
               (object-ident identp)
               (filepath? c$::filepath-optionp)
               (new-object1 ident-optionp)
               (new-object2 ident-optionp)
               (new-type1 ident-optionp)
               (new-type2 ident-optionp)
               (split-members ident-listp)
               (const-new$ symbolp))
  :short "Process the inputs."
  (b* (((reterr)
        (c$::irr-code-ensemble)
        (c$::irr-ident)
        nil
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        nil
        nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol" const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       (tunits (code-ensemble->transunits code))
       ((unless (c$::transunit-ensemble-annop tunits))
        (retmsg$ "~x0 must be an annotated with validation information."
                 const-old))
       ((unless (or (not object-filepath)
                    (stringp object-filepath)))
        (retmsg$ "~x0 must be nil or a string" object-filepath))
       (object-filepath
         (and object-filepath
              (filepath object-filepath)))
       ((unless (stringp object-name))
        (retmsg$ "~x0 must be a string" object-name))
       (object-ident (c$::ident object-name))
       ((unless (or (stringp new-object1)
                    (not new-object1)))
        (retmsg$ "~x0 must be a string or @('nil')" new-object1))
       (new-object1 (and new-object1 (c$::ident new-object1)))
       ((unless (or (stringp new-object2)
                    (not new-object2)))
        (retmsg$ "~x0 must be a string or @('nil')" new-object2))
       (new-object2 (and new-object2 (c$::ident new-object2)))
       ((unless (or (stringp new-type1)
                    (not new-type1)))
        (retmsg$ "~x0 must be a string or @('nil')" new-type1))
       (new-type1 (and new-type1 (c$::ident new-type1)))
       ((unless (or (stringp new-type2)
                    (not new-type2)))
        (retmsg$ "~x0 must be a string or @('nil')" new-type2))
       (new-type2 (and new-type2 (c$::ident new-type2)))
       ((unless (string-listp split-members))
        (retmsg$ "~x0 must be a string list" split-members))
       (split-members (ident-map split-members))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol" const-new)))
    (retok code
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
  ((code code-ensemblep)
   (object-ident identp)
   (filepath? c$::filepath-optionp)
   (new-object1 ident-optionp)
   (new-object2 ident-optionp)
   (new-type1 ident-optionp)
   (new-type2 ident-optionp)
   (split-members ident-listp)
   (const-new symbolp))
  :guard (c$::transunit-ensemble-annop (code-ensemble->transunits code))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp code)
        (splitgso-code-ensemble
          filepath?
          object-ident
          new-object1
          new-object2
          new-type1
          new-type2
          split-members
          code))
       (defconst-event
         `(defconst ,const-new
            ',code)))
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
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :parents (splitgso-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code
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
        (splitgso-gen-everything code
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
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
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
