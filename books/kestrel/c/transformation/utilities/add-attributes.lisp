; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "std/util/error-value-tuples" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/deffold-map" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
(include-book "../../syntax/validation-information")

(include-book "qualified-ident")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ add-attributes
  :parents (utilities)
  :short "Utilities to add attributes to C ASTs."
  :long
  (xdoc::topstring
    (xdoc::p
      "Attributes may either be associated to @(see qualified-ident)s, or to
       @(see c$::UID)s directly
       (see @(tsee transunit-ensemble-add-attributes-with-qualified-idents)
       and @(tsee transunit-ensemble-add-attributes), respectively).")
    (xdoc::p
      "When adding attributes to declaration, it is not clear whether it is
       necessary to add the attribute to <i>each</i> declaration of the same
       function or object. The GCC manual says:")
    (xdoc::blockquote
      "Compatible attribute specifications on distinct declarations of the
       same function are merged. An attribute specification that is not
       compatible with attributes already applied to a declaration of the same
       function is ignored with a warning.")
    (xdoc::p
      (xdoc::ahref
        "https://gcc.gnu.org/onlinedocs/gcc/Function-Attributes.html"
        "[GCCM:6.4.1]")
      ". This implies that it is not necessary to add the attribute to each
       declaration, but also that it does not hurt to do so. The above quote is
       specific to functions. No corresponding statement seems to be made for
       other kinds of attributes.")
    (xdoc::p
      "Currently, attributes are added to:")
    (xdoc::ul
      (xdoc::li
        "Declaration occurring in external declarations.")
      (xdoc::li
        "Function definitions.")
      (xdoc::li
        "Declarations occurring in blocks item lists.")
      (xdoc::li
        "Declarations made for parameter types in old-style function
         definitions."))
    (xdoc::p
      "Attributes are not yet added to:")
    (xdoc::ul
      (xdoc::li
        "For statements with a declaration initializer.")
      (xdoc::li
        "Function parameter declarations."))
    (xdoc::p
      "and perhaps others."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap qualified-ident-attrib-spec-list-map
  :key-type qualified-ident
  :val-type c$::attrib-spec-list
  :fix qualified-ident-attrib-spec-list-mfix
  :pred qualified-ident-attrib-spec-list-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap uid-attrib-spec-list-map
  :key-type c$::uid
  :val-type c$::attrib-spec-list
  :fix uid-attrib-spec-list-mfix
  :pred uid-attrib-spec-list-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resolve-qualified-ident-attrib-spec-list-map
  ((map qualified-ident-attrib-spec-list-mapp)
   (ensemble transunit-ensemblep))
  :guard (transunit-ensemble-annop ensemble)
  :returns (mv (er? maybe-msgp)
               (map$ uid-attrib-spec-list-mapp))
  (b* (((reterr) nil)
       (map (qualified-ident-attrib-spec-list-mfix map))
       ((when (omap::emptyp map))
        (retok nil))
       ((erp uid)
        (resolve-qualified-ident (omap::head-key map) ensemble))
       ((erp tail)
        (resolve-qualified-ident-attrib-spec-list-map (omap::tail map)
                                                      ensemble)))
    (retok (omap::update uid
                         (omap::head-val map)
                         tail)))
  :measure (acl2-count (qualified-ident-attrib-spec-list-mfix map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define map-decl-spec-attrib
  ((attrib-specs attrib-spec-listp))
  :returns (decl-specs decl-spec-listp)
  (if (endp attrib-specs)
      nil
    (cons (decl-spec-attrib (first attrib-specs))
          (map-decl-spec-attrib (rest attrib-specs)))))

(define map-block-item-declon
  ((declons declon-listp))
  :returns (block-items block-item-listp)
  (if (endp declons)
      nil
    (cons (make-block-item-declon :declon (first declons))
          (map-block-item-declon (rest declons)))))

(define map-ext-declon-declon
  ((declons declon-listp))
  :returns (ext-declons ext-declon-listp)
  (if (endp declons)
      nil
    (cons (ext-declon-declon (first declons))
          (map-ext-declon-declon (rest declons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod attrib-spec-list+init-declor-list
  ((attribs c$::attrib-spec-list)
   (declors c$::init-declor-list))
  :pred attrib-spec-list+init-declor-listp
  :layout :fulltree)

(fty::deflist attrib-spec-list+init-declor-list-list
  :elt-type attrib-spec-list+init-declor-list
  :true-listp t
  :elementp-of-nil nil
  :pred attrib-spec-list+init-declor-list-listp)

;; MOVE
(defrulel attrib-spec-listp-of-cdr-assoc-when-uid-attrib-spec-list-mapp
  (implies (uid-attrib-spec-list-mapp map)
           (attrib-spec-listp (cdr (omap::assoc uid map))))
  :induct t
  :enable omap::assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-declor-list-add-attrib-split
  ((declors init-declor-listp)
   (attrs uid-attrib-spec-list-mapp))
  :returns (attribs+declors-list attrib-spec-list+init-declor-list-listp)
  (b* ((declors (init-declor-list-fix declors))
       ((when (endp declors))
        nil)
       (attrs (uid-attrib-spec-list-mfix attrs))
       ((init-declor declor) (first declors))
       ((unless (c$::init-declor-infop declor.info))
        (er hard? 'add-attributes
            "Initializer declarator info is not well-formed."))
       (uid? (c$::init-declor-info->uid? declor.info))
       (attribs (if uid? (cdr (omap::assoc uid? attrs)) nil))
       (rest-attribs+declors
         (init-declor-list-add-attrib-split (rest declors) attrs))
       ((unless (and (consp rest-attribs+declors)
                     (equal (attrib-spec-list+init-declor-list->attribs
                              (first rest-attribs+declors))
                            attribs)))
        (cons (make-attrib-spec-list+init-declor-list
                :attribs attribs
                :declors (list declor))
              rest-attribs+declors))
       ((attrib-spec-list+init-declor-list first-rest)
        (first rest-attribs+declors)))
    (cons (change-attrib-spec-list+init-declor-list
            first-rest
            :declors (cons declor first-rest.declors))
          (rest rest-attribs+declors)))
  :measure (acl2-count (init-declor-list-fix declors))
  ;; TODO: this shouldn't be necessary.
  :hints (("Goal" :in-theory (enable init-declor-list-fix)))
  :verify-guards :after-returns)

(define declons-from-attrib-spec-list+init-declor-list-list
  ((extension booleanp)
   (specs decl-spec-listp)
   (attribs+declors-list attrib-spec-list+init-declor-list-listp))
  :returns (declons declon-listp)
  (b* ((attribs+declors-list
         (attrib-spec-list+init-declor-list-list-fix attribs+declors-list))
       ((when (endp attribs+declors-list))
        nil)
       ((attrib-spec-list+init-declor-list attribs+declors)
        (first attribs+declors-list))
       (declon (make-declon-declon
                 :extension extension
                 :specs (append (map-decl-spec-attrib attribs+declors.attribs)
                                specs)
                 :declors attribs+declors.declors)))
    (cons declon
          (declons-from-attrib-spec-list+init-declor-list-list
            extension
            specs
            (rest attribs+declors-list))))
  :measure (acl2-count
            (attrib-spec-list+init-declor-list-list-fix attribs+declors-list))
  :hints (("Goal"
            :in-theory (enable attrib-spec-list+init-declor-list-list-fix))))

(define declon-add-attrib-split
  ((declon declonp)
   (attrs uid-attrib-spec-list-mapp))
  :returns (declons declon-listp)
  (declon-case
    declon
    :declon (declons-from-attrib-spec-list+init-declor-list-list
              declon.extension
              declon.specs
              (init-declor-list-add-attrib-split declon.declors attrs))
    :statassert (list (declon-fix declon)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Check :for-declon (even though can't support it in general)
(fty::deffold-map add-attributes
  :types #!c$(exprs/decls/stmts
              fundef
              ext-declon
              ext-declon-list
              transunit
              filepath-transunit-map
              transunit-ensemble)
  :extra-args
  ((attrs uid-attrib-spec-list-mapp))
  :override
  ((c$::declon-list
     (b* (((when (endp c$::declon-list))
           nil)
          (declon (declon-add-attributes (first c$::declon-list) attrs))
          (split-declons (declon-add-attrib-split declon attrs)))
       (append split-declons
               (declon-list-add-attributes (rest c$::declon-list) attrs))))
   (c$::block-item-list
     (b* (((when (endp c$::block-item-list))
           nil)
          (item (block-item-add-attributes (first c$::block-item-list) attrs))
          (split-block-items
            (block-item-case
              item
              :declon (map-block-item-declon
                        (declon-add-attrib-split item.declon attrs))
              :otherwise (list item))))
       (append split-block-items
               (block-item-list-add-attributes (rest c$::block-item-list) attrs))))
   (c$::fundef
     (b* (((fundef fundef) c$::fundef)
          ((unless (fundef-infop fundef.info))
           (er hard? 'add-attributes
               "Function definition info is not well-formed.")
           (fundef-fix c$::fundef))
          ((fundef fundef$)
           (c$::change-fundef
             fundef
             :specs (decl-spec-list-add-attributes fundef.specs attrs)
             :declor (declor-add-attributes fundef.declor attrs)
             :attribs (attrib-spec-list-add-attributes fundef.attribs attrs)
             :declons (declon-list-add-attributes fundef.declons attrs)
             :body (comp-stmt-add-attributes fundef.body attrs)))
          (uid (c$::fundef-info->uid fundef.info))
          (attrib-specs?
            (omap::assoc uid (uid-attrib-spec-list-mfix attrs)))
          ((unless attrib-specs?)
           (fundef-fix fundef$))
          (decl-specs (map-decl-spec-attrib (cdr attrib-specs?))))
       (c$::change-fundef
         fundef$
         :specs (append decl-specs fundef$.specs))))
   (c$::ext-declon-list
     (b* (((when (endp c$::ext-declon-list))
           nil)
          (ext-declon (ext-declon-add-attributes (first c$::ext-declon-list) attrs))
          (split-ext-declons
            (ext-declon-case
              ext-declon
              :declon (map-ext-declon-declon
                        (declon-add-attrib-split ext-declon.declon attrs))
              :otherwise (list ext-declon))))
       (append split-ext-declons
               (ext-declon-list-add-attributes (rest c$::ext-declon-list) attrs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-add-attributes-with-qualified-idents
  ((ensemble transunit-ensemblep)
   (attrs qualified-ident-attrib-spec-list-mapp))
  :guard (transunit-ensemble-annop ensemble)
  :returns (mv (er? maybe-msgp)
               (ensemble$ transunit-ensemblep))
  (b* (((reterr) (irr-transunit-ensemble))
       ((erp attrs$)
        (resolve-qualified-ident-attrib-spec-list-map attrs ensemble)))
    (retok (transunit-ensemble-add-attributes ensemble attrs$))))
