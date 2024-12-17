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
(include-book "std/util/error-value-tuples" :dir :system)

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
       block items in the function body before the split.")
    (xdoc::p
      "This transformation is a work in progress, and may fail in certain
       cases. For instance, it may fail given variables which have been
       declared but not yet initialized at the split point, or variables which
       are passed by reference after the split point."))
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

  (fty::defomap ident-paramdecl-map
    :key-type ident
    :val-type paramdecl
    :pred ident-paramdecl-mapp))

(defrulel ident-listp-of-keys-when-ident-paramdecl-mapp
  (implies (ident-paramdecl-mapp map)
           (ident-listp (omap::keys map)))
  :induct t
  :enable omap::keys)

(defrulel paramdecl-listp-of-strip-cdrs-when-ident-paramdecl-mapp
  (implies (ident-paramdecl-mapp map)
           (paramdecl-listp (strip-cdrs map)))
  :induct t
  :enable (strip-cdrs
           ident-paramdecl-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-ident-list
  ((idents ident-listp))
  :short "Map @(tsee c$::expr-list) over a list."
  :returns (exprs expr-listp)
  (if (endp idents)
      nil
    (cons (make-expr-ident :ident (first idents) :info nil)
          (expr-ident-list (rest idents)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paramdecl-to-ident-paramdecl-map
  ((paramdecl paramdeclp))
  :short "Convert a parameter declaration into a singleton omap associating the
          declared identifier to the declaration."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the parameter declaration is unnamed, or if it has not been
      disambiguated, the empty map is returned instead."))
  :returns (map ident-paramdecl-mapp)
  (b* (((paramdecl paramdecl) paramdecl))
    (paramdeclor-case
      paramdecl.decl
      :declor (omap::update (declor-get-ident paramdecl.decl.unwrap)
                            (paramdecl-fix paramdecl)
                            nil)
      :otherwise nil)))

(define paramdecl-list-to-ident-paramdecl-map
  ((paramdecls paramdecl-listp))
  :short "Fold @(tsee paramdecl-to-ident-paramdecl-map) over a list."
  :returns (map ident-paramdecl-mapp)
  (if (endp paramdecls)
        nil
    (omap::update* (paramdecl-to-ident-paramdecl-map (first paramdecls))
                   (paramdecl-list-to-ident-paramdecl-map (rest paramdecls))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-to-ident-paramdecl-map
  ((decl declp))
  :short "Convert a regular declaration into an omap of identifiers to
          parameter declarations."
  :long
  (xdoc::topstring
   (xdoc::p
     "The resulting parameter declarations represent the same variables, with
      the same types and qualifiers. The keys to the omap are the identifiers
      bound by each parameter declaration.")
   (xdoc::p
     "A declaration which introduces multiple variables is converted to an omap
      of equal length to the number of identifiers. For instance, the
      declaration @('int x = 0, y = 0;') is converted to the omap associating
      @('x') to parameter declaration @('int x'), and @('y') to @('int y').")
   (xdoc::p
     "Only variable declarations are converted. Static assertions result in
     @('nil').")
   (xdoc::p
     "This is used by @(tsee split-fn) to track declared variables and to
      create parameters for the newly generated function (with the subset of
      declared variables which are used)."))
  :returns (map ident-paramdecl-mapp)
  (decl-case
   decl
   :decl (decl-to-ident-paramdecl-map0 decl.specs decl.init)
   :statassert nil)
  :prepwork
  ((define decl-to-ident-paramdecl-map0
     ((declspecs decl-spec-listp)
      (initdeclors initdeclor-listp))
     :returns
     (map ident-paramdecl-mapp)
     (b* (((when (endp initdeclors))
           nil)
          ((initdeclor initdeclor) (first initdeclors))
          (ident? (declor-get-ident initdeclor.declor)))
       (if ident?
           (omap::update
             ident?
             (make-paramdecl
               :spec declspecs
               :decl (paramdeclor-declor initdeclor.declor))
             (decl-to-ident-paramdecl-map0 declspecs (rest initdeclors)))
         (decl-to-ident-paramdecl-map0 declspecs (rest initdeclors))))
     :verify-guards :after-returns)))

(define decl-list-to-ident-paramdecl-map
  ((decls decl-listp))
  :short "Fold @(tsee decl-to-ident-paramdecl-map) over a list."
  :returns (map ident-paramdecl-mapp)
  (if (endp decls)
        nil
    (omap::update* (decl-to-ident-paramdecl-map (first decls))
                   (decl-list-to-ident-paramdecl-map (rest decls))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abstract-fn
  ((new-fn-name identp)
   (spec decl-spec-listp)
   (pointers typequal/attribspec-list-listp)
   (items block-item-listp)
   (decls ident-paramdecl-mapp))
  :short "Create a new function from the block items following the @(tsee
          split-fn) split point."
  :long
  (xdoc::topstring
   (xdoc::p
     "The new function will be created with same return type as the original.")
   (xdoc::p
     "Arguments to the function are determined by taking the variable
      declarations of the original function which appear free in the block
      items, which will constitute the body of the new function. (Note that
      arguments are not currently taken by reference, but this may be necessary
      for general equivalence. It may be sufficient to take an argument by
      reference when its address is taken in an expression of the new function
      body.)"))
  :returns (mv er
               (idents ident-listp
                       "The identifiers appearing in argument @('decls')
                        corresponding to the function parameters (in the same
                        order).")
               (new-fn fundefp
                       "The new function definition."))
  (b* (((reterr) nil (c$::irr-fundef))
       (idents (free-vars-block-item-list items nil))
       (decls (ident-paramdecls-map-filter decls idents))
       (idents (omap::keys decls))
       ;; We use strip-cdrs instead of omap::values because we need these in
       ;; the same order as idents.
       (params (strip-cdrs decls)))
    (retok
      idents
      (make-fundef
        :spec spec
        :declor (make-declor
                  :pointers pointers
                  :direct (make-dirdeclor-function-params
                            :decl (dirdeclor-ident new-fn-name)
                            :params params))
        :body (stmt-compound items))))
  :prepwork
  ((define ident-paramdecls-map-filter
     ((map ident-paramdecl-mapp)
      (idents ident-setp))
     :returns (new-map ident-paramdecl-mapp)
     (b* ((map (ident-paramdecl-map-fix map))
          ((when (omap::emptyp map))
           nil)
          ((mv key val)
           (omap::head map)))
       (if (in key idents)
           (omap::update key
                         val
                         (ident-paramdecls-map-filter (omap::tail map) idents))
         (ident-paramdecls-map-filter
           (omap::tail map)
           idents)))
     :measure (acl2-count (ident-paramdecl-map-fix map))
     :hints (("Goal" :in-theory (enable o< o-finp)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-block-item-list
  ((new-fn-name identp)
   (items block-item-listp)
   (spec decl-spec-listp)
   (pointers typequal/attribspec-list-listp)
   (decls ident-paramdecl-mapp)
   (split-point natp))
  :short "Transform a list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function will walk over a list of block items until it reaches the
      designated split point. Until then, it processes each declaration,
      associating locally introduced identifers to parameter declarations
      compatible with their original declaration. When the split point is
      reached, @(tsee abstract-fn) is invoked to generate the new function with
      parameters derived from this parameter declaration map. The previous
      function is truncated at this point, and a return statement added calling
      the newly split-out function."))
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
                         :fun (make-expr-ident :ident new-fn-name :info nil)
                         :args (expr-ident-list idents))))))))
       ((when (endp items))
        (reterr (msg "Bad split point specifier")))
       (item (first items))
       (decls
        (block-item-case
          item
          :decl (omap::update* (decl-to-ident-paramdecl-map item.unwrap)
                               (ident-paramdecl-map-fix decls))
          :otherwise decls))
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
  :short "Transform a function definition, splitting it if matches the target
          identifier, or else leaving it untouched."
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
        fundef.declor.direct
        :function-params
        (b* (((unless (equal target-fn (dirdeclor-get-ident fundef.declor.direct.decl)))
              (retok (fundef-fix fundef) nil))
             ((erp new-fn truncated-items)
              (split-fn-block-item-list
                new-fn-name
                fundef.body.items
                fundef.spec
                fundef.declor.pointers
                (paramdecl-list-to-ident-paramdecl-map fundef.declor.direct.params)
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
  :short "Transform an external declaration."
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
      :decl (retok nil (list (extdecl-fix extdecl)))
      :empty (retok nil (list (extdecl-fix extdecl)))
      :asm (retok nil (list (extdecl-fix extdecl))))))

(define split-fn-extdecl-list
  ((target-fn identp)
   (new-fn-name identp)
   (extdecls extdecl-listp)
   (split-point natp))
  :short "Transform a list of external declarations."
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
  :short "Transform a translation unit."
  :returns (mv er
               (new-tunit transunitp))
  (b* (((transunit tunit) tunit)
       ((mv er extdecls)
        (split-fn-extdecl-list target-fn new-fn-name tunit.decls split-point)))
    (mv er (transunit extdecls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-filepath-transunit-map
  ((target-fn identp)
   (new-fn-name identp)
   (map filepath-transunit-mapp)
   (split-point natp))
  :short "Transform a filepath."
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
  :short "Transform a translation unit ensemble."
  :returns (mv er
               (new-tunits transunit-ensemblep))
  (b* (((transunit-ensemble tunits) tunits)
       ((mv er map)
        (split-fn-filepath-transunit-map target-fn
                                         new-fn-name
                                         tunits.unwrap
                                         split-point)))
    (mv er (transunit-ensemble map))))
