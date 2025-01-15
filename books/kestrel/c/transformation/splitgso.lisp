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
     References to (members of) the original object
     are replaced with references to one or the other object.")
   (xdoc::p
    "Currently this transformation operates on a single translation unit.")
   (xdoc::section
    "Status"
    (xdoc::p
     "This transformation is a work in progress. It makes a number of
      simplifying assumptions, some of which are still not checked. In
      particular, it assumes:")
    (xdoc::ul
     (xdoc::li "members of the struct type are each declared independently.")
     (xdoc::li "each element of a struct initializer list features just one designation.")
     (xdoc::li "the file-scope struct variable is not shadowed."))
    (xdoc::p
     "Other assumptions are noted in inline comments within the source.")))
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

(define get-decl-specs-of-global-extdecl
  ((ident identp)
   (extdecl extdeclp))
  :returns (mv found
               (type decl-spec-listp))
  (extdecl-case
   extdecl
   ;; TODO: generalize to include functions?
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

(define get-decl-specs-of-global-extdecl-list
  ((ident identp)
   (extdecls extdecl-listp))
  :returns (mv er
               (type decl-spec-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (reterr (msg "No object found")))
       ((mv found type)
        (get-decl-specs-of-global-extdecl ident (first extdecls))))
    (if found
        (retok type)
      (get-decl-specs-of-global-extdecl-list ident (rest extdecls)))))

(define get-decl-specs-of-global-transunit
  ((ident identp)
   (tunit transunitp))
  :returns (mv er
               (type decl-spec-listp))
  (b* (((transunit tunit) tunit))
    (get-decl-specs-of-global-extdecl-list ident tunit.decls)))

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

(define get-type-spec-of-global-transunit
  ((ident identp)
   (tunit transunitp))
  :returns (mv er
               (type type-specp))
  (b* (((reterr) (irr-type-spec))
       ((erp decl-specs)
        (get-decl-specs-of-global-transunit ident tunit))
       (type?
         (type-spec-from-dec-specs decl-specs)))
    (if type?
        (retok type?)
      (reterr (msg "Could not convert declaration specifiers to type")))))

(define get-struct-type-name-of-global-transunit
  ((ident identp)
   (tunit transunitp))
  :returns (mv er
               (name identp))
  (b* (((reterr) (c$::irr-ident))
       ((erp type-spec)
        (get-type-spec-of-global-transunit ident tunit)))
    (type-spec-case
      type-spec
      :struct (b* (((strunispec strunispec) type-spec.spec)
                   (ident? strunispec.name))
                (if ident?
                    (retok ident?)
                  (reterr (msg "Struct type is anonymous"))))
      :otherwise (reterr (msg "Type is not a struct")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct type

;; TODO: get all idents, not just the first
(define structdeclor-list-get-ident
  ((structdeclors structdeclor-listp))
  :returns (ident? ident-optionp)
  (b* (((when (endp structdeclors))
        nil)
       ((structdeclor structdeclor) (first structdeclors))
       ((unless structdeclor.declor?)
        (structdeclor-list-get-ident (rest structdeclors)))
       (ident? (declor->ident structdeclor.declor?)))
    (or ident?
        (structdeclor-list-get-ident (rest structdeclors)))))

(define structdecl-member-in-listp
  ((names ident-listp)
   (structdecl structdeclp))
  (declare (xargs :type-prescription
                  (booleanp (structdecl-member-in-listp names structdecl))))
  (structdecl-case
   structdecl
   ;; TODO: need to check if the member has more than one ident, and handle
   ;;   appropriately (or at least error).
   :member (b* ((ident? (structdeclor-list-get-ident structdecl.declor)))
             (and ident?
                  (member-equal ident? names)
                  t))
   :otherwise nil))

(define split-structdecl-list
  ((split-members ident-listp)
   (structdecls structdecl-listp))
  :returns (mv (structdecls1 structdecl-listp)
               (structdecls2 structdecl-listp))
  (b* (((when (endp structdecls))
        (mv nil nil))
       (structdecl (structdecl-fix (first structdecls)))
       (split
         (structdecl-member-in-listp split-members structdecl))
       ((mv structdecls1 structdecls2)
        (split-structdecl-list split-members (rest structdecls))))
    (if split
        (mv structdecls1 (cons structdecl structdecls2))
      (mv (cons structdecl structdecls1) structdecls2))))

(define split-global-struct-type-decl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (decl declp))
  :returns (mv found
               (decls decl-listp))
  (decl-case
   decl
   :decl
   (b* ((type-spec? (type-spec-from-dec-specs decl.specs))
        ((mv type-match remanining-struct-decls split-struct-decls)
         (if (and type-spec?
                  (endp decl.init))
             (type-spec-case
               type-spec?
               :struct (b* (((strunispec strunispec) type-spec?.spec)
                            (match
                              (equal strunispec.name original))
                            ((unless match)
                             (mv nil nil nil))
                            ((mv remanining-struct-decls split-struct-decls)
                             ;; TODO: also check that split-members are
                             ;;   all in the struct.
                             (split-structdecl-list split-members strunispec.members)))
                         (mv t remanining-struct-decls split-struct-decls))
               :otherwise (mv nil nil nil))
           (mv nil nil nil))))
     (if type-match
         (mv t
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
                                        :members split-struct-decls)))))))
       (mv nil (list (decl-fix decl)))))
   :statassert (mv nil (list (decl-fix decl)))))

(define decl-list-to-extdecl-list
  ((decls decl-listp))
  :returns (extdecls extdecl-listp)
  (if (endp decls)
      nil
    (cons (c$::extdecl-decl (first decls))
          (decl-list-to-extdecl-list (rest decls)))))

(define split-global-struct-type-extdecl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (extdecl extdeclp))
  :returns (mv found
               (extdecls extdecl-listp))
  (extdecl-case
   extdecl
   :fundef (mv nil (list (extdecl-fix extdecl)))
   :decl (b* (((mv found decls)
               (split-global-struct-type-decl
                 original
                 new1
                 new2
                 split-members
                 extdecl.unwrap)))
           (mv found
               (decl-list-to-extdecl-list decls)))
   :empty (mv nil (list (extdecl-fix extdecl)))
   :asm (mv nil (list (extdecl-fix extdecl)))))

(define split-global-struct-type-extdecl-list
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv er
               (extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((mv found new-extdecls1)
        (split-global-struct-type-extdecl
          original
          new1
          new2
          split-members
          (first extdecls)))
       ((when found)
        (retok (append new-extdecls1
                       (extdecl-list-fix (rest extdecls)))))
       ((erp new-extdecls2)
        (split-global-struct-type-extdecl-list
          original
          new1
          new2
          split-members
          (rest extdecls))))
    (retok (append new-extdecls1 new-extdecls2))))

(define split-global-struct-type-transunit
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv er
               (new-tunit transunitp))
  (b* (((reterr) (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp extdecls)
        (split-global-struct-type-extdecl-list
          original
          new1
          new2
          split-members
          tunit.decls)))
    (retok (transunit extdecls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split global struct object

;; TODO: qualifiers are dropped from split global struct object
;; e.g.
;;   static struct S s =;
;; becomes
;;   struct S1 s1;
;;   struct S2 s2;

(define match-designors
  ((split-members ident-listp)
   (designors designor-listp))
  (declare (xargs :type-prescription (booleanp (match-designors split-members designors))))
  ;; TODO: right now this only handles single-designation initializers. Needs
  ;;   to be expanded to separate multi-designation initializers.
  ;;   - Also, what about non-dot initializers?
  (b* (((when (or (endp designors)
                  (not (endp (rest designors)))))
        nil)
       (designor (first designors)))
    (designor-case
      designor
      :sub nil
      :dot (and (member-equal designor.name split-members) t))))

(define split-desiniter-list
  ((split-members ident-listp)
   (desiniters desiniter-listp))
  :returns (mv (desiniter-list1 desiniter-listp)
               (desiniter-list2 desiniter-listp))
  (b* (((when (endp desiniters))
        (mv nil nil))
       ((mv desiniters1 desiniters2)
        (split-desiniter-list split-members (rest desiniters)))
       ((desiniter desiniter) (desiniter-fix (first desiniters))))
    (if (match-designors split-members desiniter.designors)
        (mv desiniters1 (cons desiniter desiniters2))
      (mv (cons desiniter desiniters1) desiniters2))))

(define split-struct-initer
  ((split-members ident-listp)
   (initer initerp))
  :returns (mv (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (initer-case
   initer
   ;; TODO
   :single (mv nil nil)
   :list (b* (((mv elems1 elems2)
               (split-desiniter-list split-members initer.elems)))
           (mv (c$::make-initer-list
                 :elems elems1
                 :final-comma initer.final-comma)
               (c$::make-initer-list
                 :elems elems2
                 :final-comma initer.final-comma)))))

(define split-struct-initdeclor
  ((target identp)
   (split-members ident-listp)
   (initdeclor initdeclorp))
  :returns (mv (match booleanp
                      :rule-classes :type-prescription)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  (b* (((initdeclor initdeclor) initdeclor)
       ;; TODO: check initdeclor.declor.pointers is nil?
       (ident (declor->ident initdeclor.declor))
       ((unless (equal ident target))
        (mv nil nil nil))
       ((unless initdeclor.init?)
        (mv t nil nil))
       ((mv initer-option1 initer-option2)
        (split-struct-initer split-members initdeclor.init?)))
    (mv t initer-option1 initer-option2)))

(define split-struct-initdeclors
  ((target identp)
   (split-members ident-listp)
   (initdeclors initdeclor-listp))
  :returns (mv (match booleanp
                      :rule-classes :type-prescription)
               (initer-option1 initer-optionp)
               (initer-option2 initer-optionp))
  ;; Only accepts singletons for now
  ;; TODO: broaden this
  (if (or (endp initdeclors)
          (not (endp (rest initdeclors))))
      (mv nil nil nil)
    (split-struct-initdeclor target
                             split-members
                             (first initdeclors))))

(define split-global-struct-obj-decl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (decl declp))
  :returns (mv found
               (decls decl-listp))
  (decl-case
   decl
   :decl (b* ((type-spec? (type-spec-from-dec-specs decl.specs))
              ((unless type-spec?)
               (mv nil (list (decl-fix decl))))
              ;; TODO: check that the object is indeed file-scope, as assumed
              ((mv match initer-option1 initer-option2)
               (type-spec-case
                 type-spec?
                 :struct (split-struct-initdeclors original split-members decl.init)
                 :otherwise (mv nil nil nil)))
              ((unless match)
               (mv nil (list (decl-fix decl)))))
           (mv t
               (list (c$::make-decl-decl
                       :specs (list (c$::decl-spec-stoclass
                                      (c$::stor-spec-static))
                                    (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-strunispec
                                          :name new1-type))))
                       :init (list (c$::make-initdeclor
                                     :declor (c$::make-declor
                                               :direct (c$::dirdeclor-ident new1))
                                     :init? initer-option1)))
                     (c$::make-decl-decl
                       :specs (list (c$::decl-spec-stoclass
                                      (c$::stor-spec-static))
                                    (c$::decl-spec-typespec
                                      (c$::type-spec-struct
                                        (c$::make-strunispec
                                          :name new2-type))))
                       :init (list (c$::make-initdeclor
                                     :declor (c$::make-declor
                                               :direct (c$::dirdeclor-ident new2))
                                     :init? initer-option2))))))
   :statassert (mv nil (list (decl-fix decl)))))

(define split-global-struct-obj-extdecl
  ((original identp)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecl extdeclp))
  :returns (mv found
               (extdecls extdecl-listp))
  (extdecl-case
   extdecl
   :fundef (mv nil (list (extdecl-fix extdecl)))
   :decl (b* (((mv found decls)
               (split-global-struct-obj-decl
                 original
                 new1
                 new2
                 new1-type
                 new2-type
                 split-members
                 extdecl.unwrap)))
           (mv found
               (decl-list-to-extdecl-list decls)))
   :empty (mv nil (list (extdecl-fix extdecl)))
   :asm (mv nil (list (extdecl-fix extdecl)))))

(define split-global-struct-obj-extdecl-list
  ((original identp)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (extdecls extdecl-listp))
  :returns (mv er
               (extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((mv found new-extdecls1)
        (split-global-struct-obj-extdecl
          original
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
        (split-global-struct-obj-extdecl-list
          original
          new1
          new2
          new1-type
          new2-type
          split-members
          (rest extdecls))))
    (retok (append new-extdecls1 new-extdecls2))))

(define split-global-struct-obj-transunit
  ((original identp)
   (new1 identp)
   (new2 identp)
   (new1-type identp)
   (new2-type identp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv er
               (new-tunit transunitp))
  (b* (((reterr) (c$::irr-transunit))
       ((transunit tunit) tunit)
       ((erp extdecls)
        (split-global-struct-obj-extdecl-list
          original
          new1
          new2
          new1-type
          new2-type
          split-members
          tunit.decls)))
    (retok (transunit extdecls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; replace all instances of `s.field` with `s1.field` or `s2.field`.

;; TODO: detect if global object is shadowed (via linkage information)
;;   - also, check replacement identifiers for the same
(deftrans replace-field-access
  ;; Need the
  :extra-args
  ((original identp)
   (new1 identp)
   (new2 identp)
   (split-members ident-listp))
  :expr
  (lambda (expr original new1 new2 split-members)
    (expr-case
      expr
      :ident (b* (((unless (equal expr.ident original))
                   (expr-fix expr))
                  (linkage (c$::var-info->linkage
                             (c$::coerce-var-info expr.info))))
               (c$::linkage-case
                 linkage
                 :internal (prog2$ (raise "Global struct object ~x0 occurs in
                                           illegal expression."
                                          original)
                                   (expr-fix expr))
                 :otherwise (expr-fix expr)))
      :const (expr-fix expr)
      :string (expr-fix expr)
      :paren (expr-paren (replace-field-access-expr
                           expr.inner
                           original
                           new1
                           new2
                           split-members))
      :gensel (make-expr-gensel
                :control (replace-field-access-expr
                           expr.control
                           original
                           new1
                           new2
                           split-members)
                :assocs (replace-field-access-genassoc-list
                          expr.assocs
                          original
                          new1
                          new2
                          split-members))
      :arrsub (make-expr-arrsub
                :arg1 (replace-field-access-expr
                        expr.arg1
                        original
                        new1
                        new2
                        split-members)
                :arg2 (replace-field-access-expr
                        expr.arg2
                        original
                        new1
                        new2
                        split-members))
      :funcall (make-expr-funcall
                 :fun (replace-field-access-expr
                        expr.fun
                        original
                        new1
                        new2
                        split-members)
                 :args (replace-field-access-expr-list
                         expr.args
                         original
                         new1
                         new2
                         split-members))
      ;; TODO: handle when arg is a paren (and perhaps generic selection?)
      :member (b* ((match
                     (expr-case
                       expr.arg
                       :ident (b* (((unless (equal expr.arg.ident original))
                                    nil)
                                   (linkage (c$::var-info->linkage
                                              (c$::coerce-var-info expr.arg.info))))
                                (c$::linkage-case
                                  linkage
                                  :internal t
                                  :otherwise nil))
                       :otherwise nil))
                   ((unless match)
                    (make-expr-member
                      :arg (replace-field-access-expr
                             expr.arg
                             original
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
                        new1
                        new2
                        split-members)
                 :name expr.name)
      :complit (make-expr-complit
                 :type (replace-field-access-tyname
                         expr.type
                         original
                         new1
                         new2
                         split-members)
                 :elems (replace-field-access-desiniter-list
                          expr.elems
                          original
                          new1
                          new2
                          split-members)
                 :final-comma expr.final-comma)
      :unary (make-expr-unary
               :op expr.op
               :arg (replace-field-access-expr
                      expr.arg
                      original
                      new1
                      new2
                      split-members))
      :sizeof (expr-sizeof (replace-field-access-tyname
                             expr.type
                             original
                             new1
                             new2
                             split-members))
      :sizeof-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr))
      :alignof (make-expr-alignof :type (replace-field-access-tyname
                                          expr.type
                                          original
                                          new1
                                          new2
                                          split-members)
                                  :uscores expr.uscores)
      :cast (make-expr-cast
              :type (replace-field-access-tyname
                      expr.type
                      original
                      new1
                      new2
                      split-members)
              :arg (replace-field-access-expr
                     expr.arg
                     original
                     new1
                     new2
                     split-members))
      :binary (make-expr-binary
                :op expr.op
                :arg1 (replace-field-access-expr
                        expr.arg1
                        original
                        new1
                        new2
                        split-members)
                :arg2 (replace-field-access-expr
                        expr.arg2
                        original
                        new1
                        new2
                        split-members))
      :cond (make-expr-cond
              :test (replace-field-access-expr
                      expr.test
                      original
                      new1
                      new2
                      split-members)
              :then (replace-field-access-expr-option
                      expr.then
                      original
                      new1
                      new2
                      split-members)
              :else (replace-field-access-expr
                      expr.else
                      original
                      new1
                      new2
                      split-members))
      :comma (make-expr-comma
               :first (replace-field-access-expr
                        expr.first
                        original
                        new1
                        new2
                        split-members)
               :next (replace-field-access-expr
                       expr.next
                       original
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
                         new1
                         new2
                         split-members))
      :tycompat (make-expr-tycompat
                  :type1 (replace-field-access-tyname
                           expr.type1
                           original
                           new1
                           new2
                           split-members)
                  :type2 (replace-field-access-tyname
                           expr.type2
                           original
                           new1
                           new2
                           split-members))
      :offsetof (make-expr-offsetof
                  :type (replace-field-access-tyname
                          expr.type
                          original
                          new1
                          new2
                          split-members)
                  :member (replace-field-access-member-designor
                            expr.member
                            original
                            new1
                            new2
                            split-members))
      :va-arg (make-expr-va-arg
                :list (replace-field-access-expr
                        expr.list
                        original
                        new1
                        new2
                        split-members)
                :type (replace-field-access-tyname
                        expr.type
                        original
                        new1
                        new2
                        split-members))
      :extension (expr-extension (replace-field-access-expr
                                   expr.expr
                                   original
                                   new1
                                   new2
                                   split-members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: check if validated and, if not, validate
;; (include-book "../syntax/validator")
;; (valid-transunit tunit t (c$::ienv-default))
(define splitgso-transunit
  ((orig-struct identp)
   (new-struct1 identp)
   (new-struct2 identp)
   (new-struct-type1 identp)
   (new-struct-type2 identp)
   (split-members ident-listp)
   (tunit transunitp))
  :returns (mv er
               (new-tunit transunitp))
  (b* (((reterr) (c$::transunit-fix tunit))
       ((erp struct-name)
        (get-struct-type-name-of-global-transunit orig-struct tunit))
       ((erp tunit)
        (split-global-struct-type-transunit
          struct-name
          new-struct-type1
          new-struct-type2
          split-members
          tunit))
       ((erp tunit)
        (split-global-struct-obj-transunit
          orig-struct
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
           new-struct1
           new-struct2
           split-members)))
    (retok tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that const-old is a symbol that denotes a named constant
; whole value is a translation unit ensemble with a single translation unit.
; Return its file path and translation unit if successful.

; Check that const-new is a symbol usable as a new named constant.
; (At least check that it is a symbol at all.)
; Return it unchanged, but with type symbolp for further use
; (or use suitable theorems).

; Check that object-name is an ACL2 string that is the name of
; a file-scope object with a single declaration in the translation unit,
; and satisfying additional conditions.
; Return it as an identifier, or more likely return more information,
; such as the whole declaration, or better its key constituents,
; maybe also the key constituents of the struct type.

; Probably add separate functions splitgso-process-<name-of-input>,
; which the following function calls.

(define ident-map
  ((strings string-listp))
  :returns (idents ident-listp)
  (if (endp strings)
      nil
    (cons (ident (first strings))
          (ident-map (rest strings))))
  :guard-hints (("Goal" :in-theory (enable string-listp))))

(define splitgso-process-inputs (const-old
                                 const-new
                                 object-name
                                 new-object1
                                 new-object2
                                 new-type1
                                 new-type2
                                 split-members
                                 (wrld plist-worldp))
  :returns (mv erp
               (filepath filepathp)
               (tunit transunitp)
               (object-ident identp)
               (new-object1 identp)
               (new-object2 identp)
               (new-type1 identp)
               (new-type2 identp)
               (split-members ident-listp)
               (const-new$ symbolp))
  :short "Process the inputs."
  (b* (((reterr)
        (filepath :irrelevant)
        (c$::irr-transunit)
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-ident)
        nil
        nil)
       ((unless (symbolp const-old))
        (reterr (msg "~x0 must be a symbol" const-old)))
       (tunits-old (acl2::constant-value const-old wrld))
       ((unless (transunit-ensemblep tunits-old))
        (reterr (msg "~x0 must be a translation unit ensemble." const-old)))
       ((unless (c$::transunit-ensemble-annop tunits-old))
        (reterr (msg "~x0 must be an annotated with validation information." const-old)))
       (tunits-map (transunit-ensemble->unwrap tunits-old))
       ((when (or (omap::emptyp tunits-map)
                  (not (omap::emptyp (omap::tail tunits-map)))))
        (reterr (msg "~x0 must be a translation unit ensemble with at exactly
                      one translation unit"
                     const-old)))
       (filepath (deftrans-filepath
                   (omap::head-key tunits-map)
                   "SPLITGSO"))
       (tunit (omap::head-val tunits-map))
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
    (retok filepath
           tunit
           object-ident
           new-object1
           new-object2
           new-type1
           new-type2
           split-members
           const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate a defconst event with name const-new
; and value a translation unit ensemble consisting of
; a single translation unit with the given filepath.
; That single translation unit is the result of transforming tunit-old
; according to the design of the transformation.

(define splitgso-gen-everything ((filepath filepathp)
                                 (tunit transunitp)
                                 (object-ident identp)
                                 (new-object1 identp)
                                 (new-object2 identp)
                                 (new-type1 identp)
                                 (new-type2 identp)
                                 (split-members ident-listp)
                                 (const-new symbolp))
  :returns (mv erp (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp tunit)
        (splitgso-transunit
          object-ident
          new-object1
          new-object2
          new-type1
          new-type2
          split-members
          tunit))
       (defconst-event
         `(defconst ,const-new
            (transunit-ensemble
              (omap::update ',filepath
                            ',tunit
                            nil)))))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-process-inputs-and-gen-everything (const-old
                                                    const-new
                                                    object-name
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
       ((erp filepath
             tunit
             object-ident
             new-object1
             new-object2
             new-type1
             new-type2
             split-members
             const-new)
        (splitgso-process-inputs const-old
                                 const-new
                                 object-name
                                 new-object1
                                 new-object2
                                 new-type1
                                 new-type2
                                 split-members
                                 wrld))
       ((erp event)
        (splitgso-gen-everything filepath
                                 tunit
                                 object-ident
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
     new-object1
     new-object2
     new-type1
     new-type2
     split-members)
    `(make-event (splitgso-fn ',const-old
                              ',const-new
                              ',object-name
                              ',new-object1
                              ',new-object2
                              ',new-type1
                              ',new-type2
                              ',split-members
                              'splitgso
                              state))))
