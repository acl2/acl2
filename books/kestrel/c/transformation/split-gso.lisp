; C Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "../syntax/validation-annotations")
(include-book "../syntax/code-ensembles")
(include-book "utilities/collect-idents")
(include-book "utilities/fresh-ident")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation split-gso)

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
                        (retok ord-info.linkage
                               (c$::type-struct->tag? ord-info.type))
                :otherwise (retmsg$ "~x0 has type ~x1, not a struct type"
                                    ident
                                    ord-info.type))
      :otherwise (retmsg$ "~x0 is not an object." ident))))

(define get-gso-filepath-linkage-search
  ((ident identp)
   (tunits filepath-trans-unit-mapp))
  :guard (c$::filepath-trans-unit-map-annop tunits)
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
          (c$::trans-unit-info->table-end (c$::trans-unit->info tunit))))
       ((unless erp)
        (retok filepath linkage tag?)))
    (get-gso-filepath-linkage-search ident (omap::tail tunits)))
  :guard-hints (("Goal" :in-theory (enable c$::filepath-trans-unit-map-annop
                                           c$::trans-unit-annop))))

(defrulel assoc-of-get-gso-filepath-linkage-search.filepath
  (implies
    (and (filepath-trans-unit-mapp tunits)
         (not (mv-nth 0 (get-gso-filepath-linkage-search ident tunits))))
    (omap::assoc (mv-nth 1 (get-gso-filepath-linkage-search ident tunits))
                 tunits))
  :induct t
  :enable get-gso-filepath-linkage-search)

(define get-gso-filepath-linkage
  ((filepath? c$::filepath-optionp)
   (ident identp)
   (tunits trans-ensemblep))
  :guard (c$::trans-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (filepath filepathp)
               (linkage c$::linkagep)
               (tag? ident-optionp))
  (b* (((reterr) (filepath "") (c$::irr-linkage) nil)
       (unwrapped-tunits (trans-ensemble->units tunits))
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
          (c$::trans-unit-info->table-end (c$::trans-unit->info tunit)))))
    (retok filepath? linkage tag?))
  :guard-hints (("Goal" :in-theory (enable c$::trans-ensemble-annop)))
  :prepwork
  ((defrulel trans-unit-infop-of-assoc-tunits
     (implies (and (filepath-trans-unit-mapp tunits)
                   (c$::filepath-trans-unit-map-annop tunits)
                   (omap::assoc filepath tunits))
              (c$::trans-unit-infop
                (c$::trans-unit->info
                  (cdr (omap::assoc filepath tunits)))))
     :induct t
     :enable (omap::assoc
              c$::filepath-trans-unit-map-annop
              c$::trans-unit-annop))))

(defrulel assoc-of-get-gso-filepath-linkage.filepath
  (implies
    (and (trans-ensemblep tunits)
         (not (mv-nth 0 (get-gso-filepath-linkage filepath? ident tunits))))
    (omap::assoc (mv-nth 1 (get-gso-filepath-linkage filepath? ident tunits))
                 (trans-ensemble->units tunits)))
  :enable get-gso-filepath-linkage)

(define get-gso-info
  ((filepath? c$::filepath-optionp)
   (ident identp)
   (tunits trans-ensemblep))
  :guard (c$::trans-ensemble-annop tunits)
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
    (and (trans-ensemblep tunits)
         (not (mv-nth 0 (get-gso-info filepath? ident tunits))))
    (omap::assoc (mv-nth 2 (get-gso-info filepath? ident tunits))
                 (trans-ensemble->units tunits)))
  :enable get-gso-info)

(local (in-theory (enable assoc-of-get-gso-info.filepath?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct type

(define struct-declor-list-get-ident
  ((structdeclors struct-declor-listp))
  :returns (mv (er? maybe-msgp)
               (ident? ident-optionp))
  (b* (((reterr) (c$::irr-ident))
       ((when (endp structdeclors))
        (retok nil))
       ((unless (endp (rest structdeclors)))
        (retmsg$ "Multiple struct declarators in a single struct declaration
                  are unsupported: ~x0"
                 structdeclors))
       ((struct-declor structdeclor) (first structdeclors)))
    (retok (and structdeclor.declor?
                (declor->ident structdeclor.declor?)))))

(define struct-declon-member-in-listp
  ((names ident-listp)
   (struct-declon struct-declonp))
  :returns (mv (er? maybe-msgp)
               (yes/no booleanp
                       :rule-classes :type-prescription))
  (b* (((reterr) nil))
    (struct-declon-case
      struct-declon
      ;; TODO: properly handle struct declarations with multiple declarators
      ;;   instead of returning error.
      :member (b* (((erp ident?)
                    (struct-declor-list-get-ident struct-declon.declors))
                   ((unless ident?)
                    (retok nil)))
                (retok (and (member-equal ident? names) t)))
      :statassert (retmsg$ "Static assertion structure declaration unsupported:
                            ~x0"
                           struct-declon.statassert)
      :empty (retok nil))))

(define split-struct-declon-list
  ((split-members ident-listp)
   (struct-declons struct-declon-listp))
  :returns (mv (er? maybe-msgp)
               (struct-declons1 struct-declon-listp)
               (struct-declons2 struct-declon-listp))
  (b* (((reterr) nil nil)
       ((when (endp struct-declons))
        (retok nil nil))
       (struct-declon (struct-declon-fix (first struct-declons)))
       ((erp split)
        (struct-declon-member-in-listp split-members struct-declon))
       ((erp struct-declons1 struct-declons2)
        (split-struct-declon-list split-members (rest struct-declons))))
    (if split
        (retok struct-declons1 (cons struct-declon struct-declons2))
      (retok (cons struct-declon struct-declons1) struct-declons2))))

(define all-no-init
  ((initdeclors init-declor-listp))
  (declare (xargs :type-prescription (booleanp (all-no-init initdeclors))))
  (or (endp initdeclors)
      (and (null (c$::init-declor->initer? (first initdeclors)))
           (all-no-init (rest initdeclors)))))

(define any-incomplete-struct
  ((specs decl-spec-listp))
  (declare (xargs :type-prescription (booleanp (any-incomplete-struct specs))))
  (and (consp specs)
       (let ((spec (first specs)))
         (or (decl-spec-case
               spec
               :typespec (type-spec-case
                           spec.spec
                           :struct (b* (((struni-spec struni-spec) spec.spec.spec))
                                     (endp struni-spec.members))
                           :otherwise nil)
               :otherwise nil)
             (any-incomplete-struct (rest specs))))))

(define incomplete-typedef
  ((specs decl-spec-listp))
  (declare (xargs :type-prescription (booleanp (incomplete-typedef specs))))
  (and (consp specs)
       (let ((spec (first specs)))
         (and (decl-spec-case
                spec
                :stoclass (c$::stor-spec-case spec.spec :typedef)
                :otherwise nil)
              (any-incomplete-struct (rest specs))))))

(define dup-split-struct-type-declon
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (declon declonp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (declons declon-listp))
  (b* (((reterr) nil nil nil))
    (declon-case
      declon
      :declon
      (b* ((type-spec? (type-spec-from-decl-specs declon.specs))
           ((erp type-match new1 new2 remanining-struct-decls split-struct-decls)
            (b* (((reterr) nil nil nil nil nil)
                 ((unless (and type-spec?
                               (all-no-init declon.declors)
                               (not (incomplete-typedef declon.specs))))
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
                              (split-struct-declon-list split-members
                                                        struni-spec.members))
                             (new1 (or new1 struni-spec.name? (ident "new_struct")))
                             (new2 (or new2 struni-spec.name? (ident "new_struct")))
                             ((list new1 new2)
                              (fresh-idents (list new1 new2) blacklist)))
                          (retok t new1 new2 remanining-struct-decls split-struct-decls))
                :otherwise (retok nil nil nil nil nil))))
           ((unless type-match)
            (retok nil nil (list (declon-fix declon)))))
        ;; TODO: get struct-type
        (retok new1
               new2
               (list (declon-fix declon)
                     (c$::make-declon-declon
                       :specs (list (c$::decl-spec-typespec
                                      (c$::make-type-spec-struct
                                        :spec
                                        (c$::make-struni-spec
                                          :attribs nil
                                          :name? new1
                                          :members remanining-struct-decls)
                                        :info nil))))
                     (c$::make-declon-declon
                       :specs (list (c$::decl-spec-typespec
                                      (c$::make-type-spec-struct
                                        :spec
                                        (c$::make-struni-spec
                                          :attribs nil
                                          :name? new2
                                          :members split-struct-decls)
                                        :info nil)))))))
      :statassert (retok nil nil (list (declon-fix declon)))))
  ///

  (defret identp-of-dup-split-struct-type-declon.new2$
    (equal (identp new2$)
           (identp new1$))))

(define declon-list-to-ext-declon-list
  ((declons declon-listp))
  :returns (extdecls ext-declon-listp)
  (if (endp declons)
      nil
    (cons (c$::ext-declon-declon (first declons))
          (declon-list-to-ext-declon-list (rest declons)))))

(define dup-split-struct-type-ext-declon
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (extdecl ext-declonp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (extdecls ext-declon-listp))
  (b* (((reterr) nil nil nil))
    (ext-declon-case
      extdecl
      :fundef (retok nil nil (list (ext-declon-fix extdecl)))
      :declon (b* (((erp new1 new2 decls)
                    (dup-split-struct-type-declon
                     original
                     new1
                     new2
                     blacklist
                     split-members
                     extdecl.declon)))
                (retok new1
                       new2
                       (declon-list-to-ext-declon-list decls)))
      :empty (retok nil nil (list (ext-declon-fix extdecl)))
      :asm (retok nil nil (list (ext-declon-fix extdecl)))))
  ///

  (defret identp-of-dup-split-struct-type-ext-declon.new2$
    (equal (identp new2$)
           (identp new1$)))

  (defret dup-split-struct-type-extdecl.ext-declons-type-prescription
    (true-listp extdecls)
    :rule-classes :type-prescription))

(define dup-split-struct-type-trans-item
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (item trans-itemp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (items trans-item-listp))
  (b* (((reterr) nil nil nil))
    (trans-item-case
      item
      :declon (b* (((erp new1 new2 extdecls)
                    (dup-split-struct-type-ext-declon
                     original
                     new1
                     new2
                     blacklist
                     split-members
                     item.declon)))
                (retok new1
                       new2
                       (c$::trans-item-list-declon extdecls)))
      :include (retmsg$ "#include directives not supported.")
      :define (retmsg$ "#define directives not supported.")
      :undef (retmsg$ "#undef directives not supported.")
      :cond (retmsg$ "Conditional directives not supported.")
      :line-comment (retok nil nil (list (trans-item-fix item)))))
  ///

  (defret identp-of-dup-split-struct-type-trans-item.new2$
    (equal (identp new2$)
           (identp new1$)))

  (defret dup-split-struct-type-extdecl.trans-items-type-prescription
    (true-listp items)
    :rule-classes :type-prescription))

(define dup-split-struct-type-trans-item-list
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (items trans-item-listp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (items$ trans-item-listp))
  (b* (((reterr) nil nil nil)
       ((when (endp items))
        (retok nil nil nil))
       ((erp new1$ new2$ new-items1)
        (dup-split-struct-type-trans-item
          original
          new1
          new2
          blacklist
          split-members
          (first items)))
       ((when new1$)
        (retok new1$
               new2$
               (append new-items1
                       (trans-item-list-fix (rest items)))))
       ((erp new1 new2 new-items2)
        (dup-split-struct-type-trans-item-list
          original
          new1
          new2
          blacklist
          split-members
          (rest items))))
    (retok new1 new2 (append new-items1 new-items2)))

  :measure (acl2-count items)
  ///

  (defret identp-of-dup-split-struct-type-trans-item-list.new2$
    (equal (identp new2$)
           (identp new1$))
    :hints (("Goal" :induct t))))

(define dup-split-struct-type-trans-unit
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (tunit trans-unitp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (tunit$ trans-unitp))
  (b* (((reterr) nil nil (c$::irr-trans-unit))
       ((trans-unit tunit) tunit)
       ((erp new1 new2 items)
        (dup-split-struct-type-trans-item-list
          original
          new1
          new2
          blacklist
          split-members
          tunit.items)))
    (retok new1
           new2
           (make-trans-unit :items items
                           :info tunit.info)))
    ///

    (defret identp-of-dup-split-struct-type-trans-unit.new2$
      (equal (identp new2$)
             (identp new1$))))

(define dup-split-struct-type-filepath-trans-unit-map
  ((original identp)
   (new1 ident-optionp)
   (new2 ident-optionp)
   (blacklist ident-setp)
   (split-members ident-listp)
   (map filepath-trans-unit-mapp))
  :returns (mv (er? maybe-msgp)
               (new1$ ident-optionp)
               (new2$ ident-optionp)
               (map$ filepath-trans-unit-mapp))
  (b* (((reterr) nil nil nil)
       ((when (omap::emptyp map))
        (retok nil nil nil))
       ((erp new1$ new2$ tunit)
        (dup-split-struct-type-trans-unit
          original
          new1
          new2
          blacklist
          split-members
          (omap::head-val map)))
       ((erp new1 new2 map$)
        (dup-split-struct-type-filepath-trans-unit-map
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

  (defret identp-of-dup-split-struct-type-filepath-trans-unit-map.new2$
    (equal (identp new2$)
           (identp new1$))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct object

(define make-desiniter-explicit
  ((desiniter desiniterp))
  :returns (mv (er? maybe-msgp)
               (desiniter$ desiniterp))
  :parents (split-gso-implementation)
  :short "Add an explicit designation to an initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the initializer does not have a designator,
     the annotation is checked.
     If a designator is present in the annotation, we use that.
     Otherwise, this function fails.")
   (xdoc::p
    "We may consider adding a guard of @('(desiniter-annop desiniter)')
     at some point in the future.
     Currently, we do not have a proof that the necessary annotations
     are present after the first pass of the transformation."))
  (b* (((reterr) (c$::irr-desiniter))
       ((desiniter desiniter) desiniter)
       ((unless (endp desiniter.designors))
        (retok (desiniter-fix desiniter)))
       ((unless (desiniter-annop desiniter))
        (retmsg$ "Cannot infer designation from initializer: ~x0"
                 (desiniter-fix desiniter)))
       ((c$::desiniter-info info) desiniter.info)
       ((when (endp info.designors))
        (retmsg$ "Cannot infer designation from initializer: ~x0"
                 (desiniter-fix desiniter))))
    (retok (c$::change-desiniter
             desiniter
             :designors info.designors)))
  ///

  (defret desiniter->designors-of-make-desiniter-explicit.desiniter$-type-prescription
    (implies (not er?)
             (consp (c$::desiniter->designors desiniter$)))
    :rule-classes :type-prescription))

(define explicit-desiniter-listp
  ((desiniters desiniter-listp))
  :returns (yes/no booleanp)
  :parents (split-gso-implementation)
  :short "Recognizer of lists of initializers with required designations."
  (or (endp desiniters)
      (and (not (endp (c$::desiniter->designors (first desiniters))))
           (explicit-desiniter-listp (rest desiniters)))))

(define make-desiniters-explicit
  ((desiniters desiniter-listp))
  :returns (mv (er? maybe-msgp)
               (desiniters$ desiniter-listp))
  (b* (((reterr) nil)
       ((when (endp desiniters))
        (retok nil))
       ((erp first) (make-desiniter-explicit (first desiniters)))
       ((erp rest) (make-desiniters-explicit (rest desiniters))))
    (retok (cons first rest)))
  ///

  (more-returns
   (desiniters$ explicit-desiniter-listp
                :hints (("Goal" :induct t
                                :in-theory (enable explicit-desiniter-listp))))))

(define designors-is-dot-any-ident
  ((designors designor-listp)
   (split-members ident-listp))
  :guard (not (endp designors))
  (and (endp (rest designors))
       (let ((designor (first designors)))
         (designor-case
           designor
           :sub nil
           :dot (and (member-equal designor.name
                                   (c$::ident-list-fix split-members))
                     t)))))

(define split-explicit-desiniters
  ((split-members ident-listp)
   (desiniters desiniter-listp))
  :guard (explicit-desiniter-listp desiniters)
  :returns (mv (desiniters1 desiniter-listp)
               (desiniters2 desiniter-listp))
  (b* (((when (endp desiniters))
        (mv nil nil))
       ((desiniter first-desiniter) (first desiniters))
       (rightp (designors-is-dot-any-ident
                first-desiniter.designors split-members))
       ((mv rest-desiniters1 rest-desiniters2)
        (split-explicit-desiniters split-members (rest desiniters))))
    (if rightp
        (mv rest-desiniters1
            (cons (desiniter-fix first-desiniter) rest-desiniters2))
      (mv (cons (desiniter-fix first-desiniter) rest-desiniters1)
          rest-desiniters2)))
  :guard-hints (("Goal" :in-theory (enable explicit-desiniter-listp)))
  ///

  (more-returns
   (desiniters1 true-listp :rule-classes :type-prescription)
   (desiniters2 true-listp :rule-classes :type-prescription)))

(define split-struct-global-initer
  ((split-members ident-listp)
   (initer initerp))
  :returns (mv (er? maybe-msgp)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((reterr) nil nil))
    (initer-case
      initer
      :single (retmsg$ "Internal error: non-brace-enclosed initializer ~
                        is illegal for a file-scope ~
                        struct initializer declarators:
                        ~x0."
                       (initer-fix initer))
      :list (b* (((erp explicit-elems)
                  (make-desiniters-explicit initer.elems))
                 ((mv elems1 elems2)
                  (split-explicit-desiniters split-members explicit-elems))
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
  :parents (split-gso-implementation)
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
    :measure (dirdeclor-count dirdeclor)))

(define split-struct-global-init-declor
  ((target identp)
   (split-members ident-listp)
   (initdeclor init-declorp))
  :returns (mv (er? maybe-msgp)
               (match booleanp :rule-classes :type-prescription)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((reterr) nil nil nil)
       ((init-declor initdeclor) initdeclor)
       ((unless (match-simple-declor-ident initdeclor.declor target))
        (retok nil nil nil))
       ((unless initdeclor.initer?)
        (retok t nil nil))
       ((erp initer-option1 initer-option2)
        (split-struct-global-initer split-members initdeclor.initer?)))
    (retok t initer-option1 initer-option2)))

(define split-struct-global-init-declors
  ((target identp)
   (split-members ident-listp)
   (initdeclors init-declor-listp))
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
    (split-struct-global-init-declor target
                                     split-members
                                     (first initdeclors))))

(define has-extern-p ((specs decl-spec-listp))
  (and (not (endp specs))
       (or (let ((spec (first specs)))
             (decl-spec-case
               spec
               :stoclass (c$::stor-spec-case spec.spec :extern)
               :otherwise nil))
           (has-extern-p (rest specs)))))

(define split-gso-split-object-declon
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (declon declonp))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (declons declon-listp))
  (b* (((reterr) nil nil))
    (declon-case
      declon
      :declon
      (b* ((type-spec? (type-spec-from-decl-specs declon.specs))
           ((unless type-spec?)
            (retok nil (list (declon-fix declon))))
           ;; TODO: check that the object is indeed file-scope, as assumed
           ((erp match initer-option1 initer-option2)
            (type-spec-case
              type-spec?
              :struct (split-struct-global-init-declors
                        original split-members declon.declors)
              :typedef (split-struct-global-init-declors
                         original split-members declon.declors)
              :otherwise (mv nil nil nil nil)))
           ((unless match)
            (retok nil (list (declon-fix declon))))
           (explicit-extern (has-extern-p declon.specs))
           (decl-new1-type
             (c$::decl-spec-typespec
               (c$::make-type-spec-struct
                 :spec
                 (c$::make-struni-spec
                    :attribs nil
                    :name? new1-type
                    :members nil)
                 :info nil)))
           (decl-new2-type
             (c$::decl-spec-typespec
               (c$::make-type-spec-struct
                 :spec
                 (c$::make-struni-spec
                   :attribs nil
                   :name? new2-type
                   :members nil)
                 :info nil))))
        (retok
          t
          (list (c$::make-declon-declon
                  :specs (c$::linkage-case
                           linkage
                           :internal (list (c$::decl-spec-stoclass
                                             (c$::stor-spec-static))
                                           decl-new1-type)
                           :otherwise (if explicit-extern
                                          (list (c$::decl-spec-stoclass
                                                  (c$::stor-spec-extern))
                                                decl-new1-type)
                                        (list decl-new1-type)))
                  :declors (list (c$::make-init-declor
                                  :declor (c$::make-declor
                                           :direct (c$::dirdeclor-ident new1))
                                  :initer? initer-option1)))
                (c$::make-declon-declon
                  :specs (c$::linkage-case
                           linkage
                           :internal (list (c$::decl-spec-stoclass
                                             (c$::stor-spec-static))
                                           decl-new2-type)
                           :otherwise (if explicit-extern
                                          (list (c$::decl-spec-stoclass
                                                  (c$::stor-spec-extern))
                                                decl-new2-type)
                                        (list decl-new2-type)))
                  :declors (list (c$::make-init-declor
                                  :declor (c$::make-declor
                                           :direct (c$::dirdeclor-ident new2))
                                  :initer? initer-option2))))))
      :statassert (retok nil (list (declon-fix declon))))))

(define split-gso-split-object-ext-declon
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecl ext-declonp))
  :returns (mv (er? maybe-msgp)
               (found booleanp
                      :rule-classes :type-prescription)
               (extdecls ext-declon-listp))
  (b* (((reterr) nil nil))
    (ext-declon-case
      extdecl
      :fundef (retok nil (list (ext-declon-fix extdecl)))
      :declon (b* (((erp found declons)
                    (split-gso-split-object-declon
                     original
                     linkage
                     new1
                     new2
                     new1-type
                     new2-type
                     split-members
                     extdecl.declon)))
                (retok found
                       (declon-list-to-ext-declon-list declons)))
      :empty (retok nil (list (ext-declon-fix extdecl)))
      :asm (retok nil (list (ext-declon-fix extdecl)))))
  ///

  (more-returns
   (extdecls true-listp :rule-classes :type-prescription)))

(define split-gso-split-object-trans-item
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (item trans-itemp))
  :returns (mv (er? maybe-msgp)
               (found booleanp :rule-classes :type-prescription)
               (items trans-item-listp))
  (b* (((reterr) nil nil))
    (trans-item-case
      item
      :declon (b* (((erp found extdecls)
                    (split-gso-split-object-ext-declon
                     original
                     linkage
                     new1
                     new2
                     new1-type
                     new2-type
                     split-members
                     item.declon)))
                (retok found
                       (c$::trans-item-list-declon extdecls)))
      :include (retmsg$ "#include directives not supported.")
      :define (retmsg$ "#define directives not supported.")
      :undef (retmsg$ "#undef directives not supported.")
      :cond (retmsg$ "Conditional directives not supported.")
      :line-comment (retok nil (list (trans-item-fix item)))))
  ///

  (more-returns
   (items true-listp :rule-classes :type-prescription)))

(define split-gso-split-object-trans-item-list
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (items trans-item-listp))
  :returns (mv (er? maybe-msgp)
               (items$ trans-item-listp))
  (b* (((reterr) nil)
       ((when (endp items))
        (retok nil))
       ((erp - new-items1)
        (split-gso-split-object-trans-item
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (first items)))
       ((erp new-items2)
        (split-gso-split-object-trans-item-list
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (rest items))))
    (retok (append new-items1 new-items2))))

(define split-gso-split-object-trans-unit
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (tunit trans-unitp))
  :returns (mv (er? maybe-msgp)
               (tunit$ trans-unitp))
  (b* (((reterr) (c$::irr-trans-unit))
       ((trans-unit tunit) tunit)
       ((erp items)
        (split-gso-split-object-trans-item-list
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          tunit.items)))
    (retok (make-trans-unit :items items :info tunit.info))))

(define split-gso-split-object-filepath-trans-unit-map
  ((original identp)
   (linkage c$::linkagep)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (map filepath-trans-unit-mapp))
  :returns (mv (er? maybe-msgp)
               (map$ filepath-trans-unit-mapp))
  (b* (((reterr) nil)
       ((when (omap::emptyp map))
        (retok nil))
       ((erp tunit)
        (split-gso-split-object-trans-unit
          original
          linkage
          new1
          new2
          new1-type
          new2-type
          split-members
          (omap::head-val map)))
       ((erp map$)
        (split-gso-split-object-filepath-trans-unit-map
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
  (std::make-define-config :no-function nil)

  (fty::deffold-map replace-field-access
    :types #!c$(exprs/decls/stmts
                fundef
                ext-declon
                ext-declon-list
                hash-if/elif-expr
                hash-if/ifdef/ifndef
                trans-items
                trans-unit
                filepath-trans-unit-map)
    :extra-args
    ((original identp)
     (linkage c$::linkagep)
     (new1 identp)
     (new2 identp)
     (split-members ident-listp))
    :parents (split-gso-implementation)
    :override
    ((c$::expr
       :ident
       (b* ((original (ident-fix original))
            (linkage (c$::linkage-fix linkage))
            ((unless (equal expr.ident original))
             (expr-fix c$::expr))
            (ident-linkage
              (c$::var-vinfo->linkage
                (c$::coerce-var-vinfo expr.info)))
            (- (and (equal linkage ident-linkage)
                    (raise "SPLIT-GSO ERROR: ~
                            Global struct object ~x0 occurs in illegal
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
                              (c$::var-vinfo->linkage
                                (c$::coerce-var-vinfo expr.arg.info))))
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
                    (equal expr.op (c$::unop-sizeof))
                    (equal (c$::unop-kind expr.op) :alignof))
                (expr-case
                  expr.arg
                  :member (expr-case
                            expr.arg
                            :ident (b* ((original (ident-fix original))
                                        (linkage (c$::linkage-fix linkage))
                                        ((unless (equal expr.arg.ident original))
                                         nil)
                                        (ident-linkage
                                          (c$::var-vinfo->linkage
                                            (c$::coerce-var-vinfo expr.arg.info))))
                                     (equal linkage ident-linkage))
                            :otherwise nil)
                  :otherwise nil))
           (raise "SPLIT-GSO ERROR: ~
                   Global struct object ~x0 occurs in illegal expression."
                  original)
         (make-expr-unary
           :op expr.op
           :arg (expr-replace-field-access
                  expr.arg original linkage new1 new2 split-members)
           :info nil))))
    :name abstract-syntax-replace-field-access))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-gso-rename-filepaths
  ((map filepath-trans-unit-mapp))
  :returns (map$ filepath-trans-unit-mapp)
  (b* (((when (omap::emptyp map)) nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (c$::filepath-fix path)
                  (c$::trans-unit-fix tunit)
                  (split-gso-rename-filepaths (omap::tail map))))
  :verify-guards :after-returns)

;; TODO: add `:fragment` argument indicate the map does not represent a
;;   complete program. In such cases, fail if the gso is external.
(define split-gso-filepath-trans-unit-map
  ((struct-tag identp)
   (filepath filepathp)
   (linkage c$::linkagep)
   (orig-struct identp)
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (map filepath-trans-unit-mapp))
  :guard (omap::assoc filepath map)
  :returns (mv (er? maybe-msgp)
               (map$ filepath-trans-unit-mapp))
  (b* (((reterr) nil)
       (map (c$::filepath-trans-unit-map-fix map))
       ((when (equal linkage (c$::linkage-none)))
        (retmsg$ "Invalid struct object linkage: ~x0" linkage))
       (ident-blacklist (filepath-trans-unit-map-collect-idents map))
       (new-struct1 (or new-struct1 orig-struct))
       (new-struct2 (or new-struct2 orig-struct))
       ((when (equal linkage (c$::linkage-external)))
        (b* (((erp new-struct-tag1 new-struct-tag2 map)
              (dup-split-struct-type-filepath-trans-unit-map
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
              (split-gso-split-object-filepath-trans-unit-map
                orig-struct
                linkage
                new-struct1
                new-struct2
                new-struct-tag1
                new-struct-tag2
                split-members
                map))
             (map
               (filepath-trans-unit-map-replace-field-access
                 map
                 orig-struct
                 linkage
                 new-struct1
                 new-struct2
                 split-members)))
          (retok map)))
       (tunit (omap::lookup filepath map))
       ((erp new-struct-tag1 new-struct-tag2 tunit)
        (dup-split-struct-type-trans-unit
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
        (split-gso-split-object-trans-unit
          orig-struct
          linkage
          new-struct1
          new-struct2
          new-struct-tag1
          new-struct-tag2
          split-members
          tunit))
       (tunit
         (trans-unit-replace-field-access
           tunit
           orig-struct
           linkage
           new-struct1
           new-struct2
           split-members)))
    (retok (omap::update (c$::filepath-fix filepath)
                         tunit
                         map))))

(define split-gso-trans-ensemble
  ((filepath? c$::filepath-optionp)
   (orig-struct identp)
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (tunits trans-ensemblep))
  :guard (c$::trans-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (tunits$ trans-ensemblep))
  (b* (((reterr) (c$::trans-ensemble-fix tunits))
       ((erp struct-tag filepath linkage)
        (get-gso-info filepath? orig-struct tunits))
       (map (trans-ensemble->units tunits))
       ((erp map)
        (split-gso-filepath-trans-unit-map
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
      (c$::make-trans-ensemble :units (split-gso-rename-filepaths map)))))

(define split-gso-code-ensemble
  ((filepath? c$::filepath-optionp)
   (orig-struct identp)
   (new-struct1 ident-optionp)
   (new-struct2 ident-optionp)
   (new-struct-tag1 ident-optionp)
   (new-struct-tag2 ident-optionp)
   (split-members ident-listp)
   (code code-ensemblep))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (code$ code-ensemblep))
  (b* (((reterr) (irr-code-ensemble))
       ((code-ensemble code) code)
       ((erp tunits) (split-gso-trans-ensemble filepath?
                                               orig-struct
                                               new-struct1
                                               new-struct2
                                               new-struct-tag1
                                               new-struct-tag2
                                               split-members
                                               code.trans-units)))
    (retok (change-code-ensemble code :trans-units tunits)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing split-gso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-gso-process-inputs (const-old
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
               (code code-ensemblep)
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
       ((unless (code-ensemble-annop code))
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
       (split-members (c$::string-list-map-ident split-members))
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
           const-new))
  ///

  (defret code-ensemble-annop-of-split-gso-process-inputs.code
    (implies (not er?)
             (code-ensemble-annop code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation split-gso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-gso-gen-everything
  ((code code-ensemblep)
   (object-ident identp)
   (filepath? c$::filepath-optionp)
   (new-object1 ident-optionp)
   (new-object2 ident-optionp)
   (new-type1 ident-optionp)
   (new-type2 ident-optionp)
   (split-members ident-listp)
   (const-new symbolp))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp code)
        (split-gso-code-ensemble
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

(define split-gso-process-inputs-and-gen-everything
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
  :parents (split-gso-implementation)
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
        (split-gso-process-inputs const-old
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
        (split-gso-gen-everything code
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

(define split-gso-fn (const-old
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
  :parents (split-gso-implementation)
  :short "Event expansion of @(tsee split-gso)."
  (b* (((mv erp event)
        (split-gso-process-inputs-and-gen-everything const-old
                                                     const-new
                                                     object-name
                                                     object-filepath
                                                     new-object1
                                                     new-object2
                                                     new-type1
                                                     new-type2
                                                     split-members
                                                     (w state)))
       ((when erp) (er-soft+ ctx t '(_) "SPIT-GSO ERROR: ~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection split-gso-macro-definition
  :parents (split-gso-implementation)
  :short "Definition of @(tsee split-gso)."
  (defmacro split-gso
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
    `(make-event (split-gso-fn ',const-old
                               ',const-new
                               ',object-name
                               ',object-filepath
                               ',new-object1
                               ',new-object2
                               ',new-type1
                               ',new-type2
                               ',split-members
                               'split-gso
                               state))))
