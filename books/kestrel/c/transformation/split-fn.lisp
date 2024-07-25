; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/std/util/defirrelevant" :dir :system)
(include-book "kestrel/std/util/error-value-tuples" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "deftrans")
(include-book "utilities/free-vars")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ split-fn
  :parents (transformation-tools)
  :short "A C-to-C transformation to split a function in two."
  :long
  (xdoc::topstring
    (xdoc::p
      "This transformation takes the identifier of the function it is to split,
       the name of the new function to be generated, and the location of the
       split, represented as a natural number corresponding to the number of
       statements in the function body before the split.")
    (xdoc::p
      "This transformation is a work in progress, and may fail in certain
       cases. For one, it does not currently recognize multiple variables
       declared at once (e.g. @('int x, y;')). It may also fail on variables
       which have been declared but not yet initialized at the split point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ident-listp-when-ident-setp
  (implies (ident-setp set)
           (ident-listp set))
  :induct t
  :enable ident-setp)

(local (in-theory (enable ident-listp-when-ident-setp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (set-induction-depth-limit 1)

  (fty::defomap ident-decl-map
    :key-type ident
    :val-type decl
    :pred ident-decl-mapp))

(defrulel decl-listp-of-strip-cdrs-when-ident-decl-mapp
  (implies (ident-decl-mapp map)
           (decl-listp (strip-cdrs map)))
  :induct t
  :enable (strip-cdrs
           ident-decl-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-decls-map-filter
  ((map ident-decl-mapp)
   (idents ident-setp))
  :returns (new-map ident-decl-mapp)
  (b* ((map (ident-decl-map-fix map))
       ((when (omap::emptyp map))
        nil)
       ((mv key val)
        (omap::head map)))
    (if (in key idents)
        (omap::update key
                      val
                      (ident-decls-map-filter (omap::tail map) idents))
      (ident-decls-map-filter
        (omap::tail map)
        idents)))
  :measure (acl2-count (ident-decl-map-fix map))
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-to-paramdecl
  ((decl declp))
  :returns (mv erp
               (paramdecl paramdeclp))
  (b* (((reterr) (c$::irr-paramdecl)))
    (decl-case
      decl
      :decl (b* (((when (endp decl.init))
                  (reterr t))
                 ((initdeclor initdeclor) (first decl.init)))
              (retok
                (make-paramdecl
                  :spec decl.specs
                  :decl (paramdeclor-declor initdeclor.declor))))
      :statassert (reterr t))))

(define decl-list-to-paramdecl-list
  ((decls decl-listp))
  :returns (paramdecls paramdecl-listp)
  (b* (((when (endp decls))
        nil)
       ((mv erp paramdecl)
        (decl-to-paramdecl (first decls))))
    (if erp
        (decl-list-to-paramdecl-list (rest decls))
      (cons paramdecl
            (decl-list-to-paramdecl-list (rest decls))))))

(define paramdecl-to-decl
  ((paramdecl paramdeclp))
  :returns (mv erp
               (decl declp))
  (b* (((reterr) (c$::irr-decl))
       ((paramdecl paramdecl) paramdecl))
    (paramdeclor-case
      paramdecl.decl
      :declor (retok (make-decl-decl
                       :specs paramdecl.spec
                       :init (list (make-initdeclor
                                     :declor paramdecl.decl.unwrap))))
      :otherwise (reterr t))))

(define paramdecl-list-to-decl-list
  ((paramdecls paramdecl-listp))
  :returns (decls decl-listp)
  (b* (((when (endp paramdecls))
        nil)
       ((mv erp decl)
        (paramdecl-to-decl (first paramdecls))))
    (if erp
        (paramdecl-list-to-decl-list (rest paramdecls))
      (cons decl
            (paramdecl-list-to-decl-list (rest paramdecls))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abstract-fn
  ((new-fn-name identp)
   (spec declspec-listp)
   (pointers tyqual-list-listp)
   (items block-item-listp)
   (decls ident-decl-mapp))
  :returns (mv er
               (idents ident-listp)
               (new-fn fundefp))
  (b* (((reterr) nil (c$::irr-fundef))
       (idents (free-vars-block-item-list items nil))
       (decls (ident-decls-map-filter decls idents))
       (params (decl-list-to-paramdecl-list (strip-cdrs decls))))
    (retok
      idents
      (make-fundef
        :spec spec
        :declor (make-declor
                  :pointers pointers
                  :decl (make-dirdeclor-function-params
                          :decl (dirdeclor-ident new-fn-name)
                          :params params))
        :body (stmt-compound items)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initdeclor-get-idents
  ((initdeclor initdeclorp))
  :returns (idents ident-setp
                   :hints (("Goal" :in-theory (enable identp-of-declor-get-ident-under-iff))))
  (b* (((initdeclor initdeclor) initdeclor)
       (ident? (declor-get-ident initdeclor.declor)))
    (if ident?
        (insert ident? nil)
      nil)))

(define initdeclor-list-get-idents
  ((initdeclors initdeclor-listp))
  :returns (idents ident-setp)
  (if (endp initdeclors)
      nil
    (union (initdeclor-get-idents (first initdeclors))
           (initdeclor-list-get-idents (rest initdeclors))))
  :verify-guards :after-returns)

(define decl-get-idents
  ((decl declp))
  :returns (idents ident-setp)
  (decl-case
   decl
   :decl (initdeclor-list-get-idents decl.init)
   :statassert nil))

(define split-fn-decl
  ((decl declp)
   (map ident-decl-mapp))
  :returns (mv er
               (new-map ident-decl-mapp))
  (b* ((map (ident-decl-map-fix map))
       ((reterr) map)
       (idents (decl-get-idents decl)))
    (if (emptyp idents)
        (retok map)
      ;; TODO: either reterr on more than one ident, or else add all to the alist
      (retok (omap::update (head idents)
                           (decl-fix decl)
                           map)))))

(define split-fn-decl-list
  ((decls decl-listp)
   (map ident-decl-mapp))
  :returns (new-map ident-decl-mapp)
  (b* (((when (endp decls))
        (ident-decl-map-fix map))
       ((mv er split-map)
        (split-fn-decl (first decls) map)))
    (split-fn-decl-list (rest decls)
                        (if er
                            map
                          split-map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-ident-list
  ((idents ident-listp))
  :returns (exprs expr-listp)
  (if (endp idents)
      nil
    (cons (expr-ident (first idents))
          (expr-ident-list (rest idents)))))

(define split-fn-block-item-list
  ((new-fn-name identp)
   (items block-item-listp)
   (spec declspec-listp)
   (pointers tyqual-list-listp)
   (decls ident-decl-mapp)
   (split-point natp))
  :returns (mv er
               (new-fn fundefp)
               (truncated-items block-item-listp))
  (b* ((items (block-item-list-fix items))
       ((reterr) (c$::irr-fundef) items)
       ((when (zp split-point))
        (b* (((erp idents new-fn)
              (abstract-fn new-fn-name spec pointers items decls)))
          (retok new-fn
                 (list
                   (block-item-stmt
                     (stmt-return
                       (make-expr-funcall
                         :fun (expr-ident new-fn-name)
                         :args (expr-ident-list idents))))))))
       ((when (endp items))
        (reterr (msg "Bad split point specifier")))
       (item (first items))
       ((erp decls)
        (block-item-case
          item
          :decl (split-fn-decl item.unwrap decls)
          :otherwise (mv nil decls)))
       ((erp new-fn truncated-items)
        (split-fn-block-item-list new-fn-name
                              (rest items)
                              spec
                              pointers
                              decls
                              (- split-point 1))))
    (retok new-fn
           (cons (first items)
                 truncated-items)))
  :measure (block-item-list-count items)
  :hints (("Goal" :in-theory (enable o<
                                     o-finp
                                     block-item-list-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-fundef
  ((target-fn identp)
   (new-fn-name identp)
   (fundef fundefp)
   (split-point natp))
  :returns (mv er
               (fundef1 fundefp)
               (fundef2 fundef-optionp))
  (b* (((reterr) (c$::irr-fundef) nil)
       ((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (stmt-case
      fundef.body
      :compound
      (dirdeclor-case
        fundef.declor.decl
        :function-params
        (b* (((unless (equal target-fn (dirdeclor-get-ident fundef.declor.decl.decl)))
              (retok (fundef-fix fundef) nil))
             ((erp new-fn truncated-items)
              (split-fn-block-item-list
                new-fn-name
                fundef.body.items
                fundef.spec
                fundef.declor.pointers
                (split-fn-decl-list
                  (paramdecl-list-to-decl-list fundef.declor.decl.params)
                  nil)
                split-point)))
          (retok new-fn
                 (make-fundef
                   :extension fundef.extension
                   :spec fundef.spec
                   :declor fundef.declor
                   :decls fundef.decls
                   :body (stmt-compound truncated-items))))
        :otherwise (retok (fundef-fix fundef) nil))
      :otherwise (retok (fundef-fix fundef) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-extdecl
  ((target-fn identp)
   (new-fn-name identp)
   (extdecl extdeclp)
   (split-point natp))
  :returns (mv er
               (target-found booleanp)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil))
    (extdecl-case
      extdecl
      :fundef (b* (((erp fundef1 fundef2)
                    (split-fn-fundef
                      target-fn
                      new-fn-name
                      extdecl.unwrap
                      split-point)))
                (fundef-option-case
                  fundef2
                  :some (retok t (list (extdecl-fundef fundef1)
                                       (extdecl-fundef fundef2.val)))
                  :none (retok nil (list (extdecl-fundef fundef1)))))
      :decl (retok nil (list (extdecl-fix extdecl))))))

(define split-fn-extdecl-list
  ((target-fn identp)
   (new-fn-name identp)
   (extdecls extdecl-listp)
   (split-point natp))
  :returns (mv er
               (new-extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((erp target-found extdecls1)
        (split-fn-extdecl target-fn new-fn-name (first extdecls) split-point))
       ((when target-found)
        (retok (append extdecls1 (extdecl-list-fix (rest extdecls)))))
       ((erp extdecls2)
        (split-fn-extdecl-list target-fn new-fn-name (rest extdecls) split-point)))
    (retok (append extdecls1 extdecls2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-transunit
  ((target-fn identp)
   (new-fn-name identp)
   (tunit transunitp)
   (split-point natp))
  :returns (mv er
               (new-tunit transunitp))
  (b* (((transunit tunit) tunit)
       ((mv er extdecls)
        (split-fn-extdecl-list target-fn new-fn-name tunit.decls split-point)))
    (mv er (transunit extdecls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-filepath-transunit-map
  ((target-fn identp)
   (new-fn-name identp)
   (map filepath-transunit-mapp)
   (split-point natp))
  :returns (mv er
               (new-map filepath-transunit-mapp
                        :hyp (filepath-transunit-mapp map)))
  (b* (((reterr) nil)
       ((when (omap::emptyp map))
        (retok nil))
       ((mv path tunit) (omap::head map))
       (new-path (deftrans-filepath path "SPLIT-FN"))
       ((erp new-tunit)
        (split-fn-transunit target-fn new-fn-name tunit split-point))
       ((erp new-map)
        (split-fn-filepath-transunit-map target-fn
                                         new-fn-name
                                         (omap::tail map)
                                         split-point)))
    (retok (omap::update new-path new-tunit new-map)))
  :verify-guards :after-returns)

(define split-fn-transunit-ensemble
  ((target-fn identp)
   (new-fn-name identp)
   (tunits transunit-ensemblep)
   (split-point natp))
  :returns (mv er
               (new-tunits transunit-ensemblep))
  (b* (((transunit-ensemble tunits) tunits)
       ((mv er map)
        (split-fn-filepath-transunit-map target-fn
                                         new-fn-name
                                         tunits.unwrap
                                         split-point)))
    (mv er (transunit-ensemble map))))
