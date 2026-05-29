; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod, due to regression failure 9/4/2025 using Allegro CL 10.1:
; cert_param: (non-allegro)

(in-package "C$")

(include-book "built-in")
(include-book "unambiguity")
(include-book "type-specifier-lists")
(include-book "storage-specifier-lists")
(include-book "validation-information")
(include-book "translation-unit-comparison")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator
  :parents (validation)
  :short "Validator of the C abstract syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides syntactic validity,
     C code must satisfy a number of additional constraints
     in order to be compiled.
     These constraints form the static semantics of C.
     C compilers check that the code satisfies these constraints
     prior to translating it.")
   (xdoc::p
    "Here we provide a validator of C code,
     whose purpose is to check those constraints,
     i.e. to check whether the C code is valid and compilable.")
   (xdoc::p
    "If successful, the validator adds information to the abstract syntax,
     which downstream tools (e.g. C-to-C transformations) can make use of.")
   (xdoc::p
    "We start with an approximate validator
     that should accept all valid C code
     but also some invalid C code (due to the approximation).
     Even in its approximate form,
     this is useful to perform some validation,
     and to calculate information (approximate types)
     useful for manipulating the abstract syntax
     (e.g. for C-to-C transformations).")
   (xdoc::p
    "In a sense, the validator extends the @(see disambiguator),
     which performs an even more approximate validation,
     just enough to disambiguate the abstract syntax.
     Thus, there are structural similarities between
     the validator and the disambiguator.")
   (xdoc::p
    "Similarly to a compiler, the validator makes use of a symbol table,
     which tracks information about the symbols (identifiers) in the code.
     These symbol tables, called `validation tables', are, in some sense,
     an extension of the disambiguation tables used by the disambiguator.
     See @(tsee valid-table).")
   (xdoc::p
    "We use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to handle errors in the validator.")
   (xdoc::p
    "The ACL2 functions that validate
     the various constructs of the abstract syntax
     follow the @('valid-<fixtype>') naming scheme,
     where @('<fixtype>') is the name of
     the fixtype of the abstract syntax construct,
     and where @('valid') is best read as an abbreviation of `validate'
     rather than as the adjective `valid'.")
   (xdoc::p
    "We are extending our validator
     to try and preserve @('#include') directives when possible,
     as in our @(see preprocessor) and @(see disambiguator).
     The approach should be the same as in the disambiguator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty-valid-scope ()
  :returns (scope valid-scopep)
  :short "Empty validator scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scopes always start empty, i.e. with no identifiers.
     This function returns the empty scope."))
  (make-valid-scope :ord nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-valid-table ((filepath filepathp)
                          (dialect c::dialectp))
  :returns (table valid-tablep)
  :short "Initial validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains one empty scope (the initial file scope),
     and the initial macro table for the given dialect."))
  (make-valid-table :filepath filepath
                    :scopes (list (empty-valid-scope))
                    :macros (macro-init dialect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-table-num-scopes ((table valid-tablep))
  :returns (num natp)
  :short "Number of scopes in a validation table."
  (len (valid-table->scopes table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-push-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Push a scope onto the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The newly pushed scope is always empty."))
  (b* ((scopes (valid-table->scopes table))
       (new-scopes (cons (empty-valid-scope) scopes)))
    (change-valid-table table :scopes new-scopes))
  ///

  (defret valid-table-num-scopes-of-valid-push-scope
    (equal (valid-table-num-scopes new-table)
           (1+ (valid-table-num-scopes table)))
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-pop-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Pop a scope from the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The popped scope is discarded."))
  (b* (((valid-table table) table)
       ((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (new-scopes (cdr table.scopes)))
    (change-valid-table table :scopes new-scopes))
  :no-function nil
  ///

  (defret valid-table-num-scopes-of-valid-pop-scope
    (equal (valid-table-num-scopes new-table)
           (1- (valid-table-num-scopes table)))
    :hyp (> (valid-table-num-scopes table) 0)
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len max fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord ((ident identp) (table valid-tablep))
  :returns (mv (info? valid-ord-info-optionp) (currentp booleanp))
  :short "Look up an ordinary identifier in a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the visibility and hiding rules [C17:6.2.1/2],
     we look up the identifier starting from the innermost scope.
     We stop as soon as we find a match.
     We return @('nil') if we reach the outermost scope
     without finding a match.")
   (xdoc::p
    "We also return a flag saying whether the identifier was found
     in the current (i.e. innermost) scope or in some other scope.
     We initialize this flag to @('t'),
     and we set to @('nil') when we perform the recursive call.
     The flag is irrelevant if the first result is @('nil'),
     but in this case the returned flag is @('nil') too."))
  (valid-lookup-ord-loop ident (valid-table->scopes table) t)

  :prepwork
  ((define valid-lookup-ord-loop ((ident identp)
                                  (scopes valid-scope-listp)
                                  (currentp booleanp))
     :returns (mv (info? valid-ord-info-optionp) (updated-currentp booleanp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil))
          (scope (car scopes))
          (ord-scope (valid-scope->ord scope))
          (ident+info (assoc-equal (ident-fix ident) ord-scope))
          ((when ident+info) (mv (cdr ident+info) (bool-fix currentp))))
       (valid-lookup-ord-loop ident (cdr scopes) nil)))))

;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord-file-scope ((ident identp) (table valid-tablep))
  :returns (info? valid-ord-info-optionp)
  :short "Look up an ordinary identifier
          in the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee valid-lookup-ord), this skips any block scopes,
     and directly looks up the identifier in the file scope.
     It is used in some situations."))
  (b* ((scopes (valid-table->scopes table))
       ((when (endp scopes)) (raise "Internal error: no scopes."))
       (scope (car (last scopes)))
       (ident+info (assoc-equal (ident-fix ident)
                                (valid-scope->ord scope)))
       ((when ident+info) (cdr ident+info)))
    nil)
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-tag ((ident identp) (table valid-tablep))
  :returns (mv (info? valid-tag-info-optionp) (currentp booleanp))
  :short "Look up a tag in a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This functions behaves just as @('valid-lookup-ord'),
     but for tags instead of ordinary identifiers."))
  (valid-lookup-tag-loop ident (valid-table->scopes table) t)

  :prepwork
  ((define valid-lookup-tag-loop ((ident identp)
                                  (scopes valid-scope-listp)
                                  (currentp booleanp))
     :returns (mv (info? valid-tag-info-optionp) (updated-currentp booleanp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil))
          (scope (car scopes))
          (tag-scope (valid-scope->tag scope))
          (ident+info (assoc-equal (ident-fix ident) tag-scope))
          ((when ident+info) (mv (cdr ident+info) (bool-fix currentp))))
       (valid-lookup-tag-loop ident (cdr scopes) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-add-tag ((ident identp)
                       (info valid-tag-infop)
                       (table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Add a tag to the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Just as in @(tsee vstate-add-ord),
     the tag is added to the first (i.e. innermost) scope.
     If the tag is already present in the current scope,
     its information is overwritten."))
  (b* (((valid-table table) table)
       ((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (scope (car table.scopes))
       (tag-scope (valid-scope->tag scope))
       (new-tag-scope (acons (ident-fix ident)
                             (valid-tag-info-fix info)
                             tag-scope))
       (new-scope (change-valid-scope scope :tag new-tag-scope))
       (new-scopes (cons new-scope (cdr table.scopes)))
       (table (change-valid-table table :scopes new-scopes)))
    table)
  :guard-hints (("Goal" :in-theory (enable valid-table-num-scopes acons)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-has-internalp ((ident identp) (table valid-tablep))
  :returns (has-internalp booleanp :rule-classes :type-prescription)
  :short "Check whether an identifier has been declared with internal linkage
          in the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks whether the identifier has been declared with internal linkage
     anywhere in the translation unit, not just the visible declaration
     (if it exists).")
   (xdoc::p
    "We perform this check by looking through declarations in the file scope.
     We are able to avoid looking through block scopes because
     an identifier may only be declared with internal linkage in a block scope
     if it has been previously declared with internal linkage in the file scope
     [C17:6.2.2/4] [C17:6.2.2/6]."))
  (b* ((info? (valid-lookup-ord-file-scope ident table)))
    (and info?
         (valid-ord-info-case
          info?
          :objfun (linkage-case
                   info?.linkage
                   :internal t
                   :otherwise nil)
          :otherwise nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod vstate
  :short "Fixtype of validator states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     a validation table,
     an information map for identifiers with external linkage,
     a type completion map,
     the next unused"
    (xdoc::seetopic "uid" "unique identifier")
    ", and an implementation environment.
     It is analogous to @(tsee dstate).")
   (xdoc::p
    "The implementation environment is constant &mdash;
     i.e. it is never updated once set.
     The validation table is reset for each translation unit,
     and only contains information for the current translation unit.
     The remaining fields,
     @('externals'), @('completions'), and @('next-uid'),
     accumulate over the entire validation process,
     and their contents apply to all translation units in the ensemble."))
  ((table valid-table)
   (externals valid-externals)
   (completions type-completions)
   (next-uid uidp)
   (ienv ienv))
  :pred vstatep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-vstate
  :short "An irrelevant validator state."
  :type vstatep
  :body (vstate (irr-valid-table)
                nil
                nil
                (irr-uid)
                (irr-ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-vstate ((ienv ienvp)
                     (filepath filepathp)
                     &optional
                     (externals valid-externalsp)
                     ((completions type-completions-p) 'nil)
                     ((next-uid uidp) '(uid 0)))
  :returns (vstate vstatep)
  :short "Initial validator state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains one empty scope (the initial file scope)."))
  (make-vstate :table (init-valid-table filepath (ienv->dialect ienv))
               :externals externals
               :completions completions
               :next-uid next-uid
               :ienv ienv)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate->filepath ((vstate vstatep))
  :returns (filepath filepathp)
  :short "Wrapper of @(tsee valid-table->filepath)."
  (valid-table->filepath (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-num-scopes ((vstate vstatep))
  :returns (num natp)
  :short "Wrapper of @(tsee valid-table-num-scopes)."
  (valid-table-num-scopes (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-push-scope ((vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Wrapper of @(tsee valid-push-scope)."
  (change-vstate vstate :table (valid-push-scope (vstate->table vstate)))
  :inline t

  ///

  (defret vstate-num-scopes-of-vstate-push-scope
    (equal (vstate-num-scopes new-vstate)
           (1+ (vstate-num-scopes vstate)))
    :hints (("Goal" :in-theory (enable vstate-num-scopes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-pop-scope ((vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Wrapper of @(tsee valid-pop-scope)."
  (change-vstate vstate :table (valid-pop-scope (vstate->table vstate)))
  :inline t

  ///

  (defret vstate-num-scopes-of-vstate-pop-scope
    (equal (vstate-num-scopes new-vstate)
           (1- (vstate-num-scopes vstate)))
    :hyp (> (vstate-num-scopes vstate) 0)
    :hints (("Goal" :in-theory (enable vstate-num-scopes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-lookup-ord ((ident identp) (vstate vstatep))
  :returns (mv (info? valid-ord-info-optionp) (currentp booleanp))
  :short "Wrapper of @(tsee valid-lookup-ord)."
  (valid-lookup-ord ident (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(define vstate-lookup-ord-file-scope ((ident identp) (vstate vstatep))
  :returns (info? valid-ord-info-optionp)
  :short "Wrapper of @(tsee valid-lookup-ord-file-scope)."
  (valid-lookup-ord-file-scope ident (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-lookup-tag ((ident identp) (vstate vstatep))
  :returns (mv (info? valid-tag-info-optionp) (currentp booleanp))
  :short "Wrapper of @(tsee valid-lookup-tag)."
  (valid-lookup-tag ident (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-add-tag ((ident identp)
                        (info valid-tag-infop)
                        (vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Wrapper of @(tsee valid-add-tag)."
  (b* ((table (vstate->table vstate))
       (new-table (valid-add-tag ident info table)))
    (change-vstate vstate :table new-table))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-has-internalp ((ident identp) (vstate vstatep))
  :returns (has-internalp booleanp :rule-classes :type-prescription)
  :short "Wrapper of @(tsee valid-has-internalp)."
  (valid-has-internalp ident (vstate->table vstate))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-lookup-ext ((ident identp) (vstate vstatep))
  :returns (info? valid-ext-info-optionp)
  :short "Look up the validation information of an identifier in the
          @('externals') map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds the validation information
     for an identifier with external linkage
     which has been declared in any scope or translation unit.
     See @(see valid-table)."))
  (b* (((vstate vstate) vstate))
    (cdr (omap::assoc (ident-fix ident) vstate.externals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-get-fresh-uid ((ident identp)
                              (linkage linkagep)
                              (vstate vstatep))
  :returns (mv (uid uidp)
               (new-vstate vstatep))
  :short "Get a fresh @(tsee UID) and update the vstate accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('next-uid') field of the @(see vstate) is incremented to record
     that the returned @(tsee UID) is now taken."))
  (b* (((vstate vstate) vstate))
    (linkage-case
     linkage
     :external (b* ((info? (vstate-lookup-ext ident vstate)))
                 (valid-ext-info-option-case
                  info?
                  :some (mv (valid-ext-info->uid info?.val)
                            (vstate-fix vstate))
                  :none (mv vstate.next-uid
                            (change-vstate
                             vstate
                             :next-uid (uid-increment vstate.next-uid)))))
     :otherwise (mv vstate.next-uid
                    (change-vstate
                     vstate
                     :next-uid (uid-increment vstate.next-uid)))))

  ///

  (defret vstate-get-fresh-uid.uid-under-iff
    uid))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-update-ext ((ident identp)
                           (type typep)
                           (uid uidp)
                           (vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Update the @('externals') map with an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "If no entry exists for the identifier,
     add a new @(tsee valid-ext-info).
     If an entry does exist, update the @('declared-in') field to include
     the name of the current translation unit.")
   (xdoc::p
    "When an existing entry already exists,
     type compatibility is not checked, nor is the UID.
     Instead, the caller should check compatibility and ensure a proper UID
     before updating."))
  (b* (((vstate vstate) vstate)
       ((valid-table table) vstate.table)
       (info? (vstate-lookup-ext ident vstate))
       (new-info
        (valid-ext-info-option-case
         info?
         :some (change-valid-ext-info
                info?
                :declared-in (insert table.filepath
                                     (valid-ext-info->declared-in
                                      info?.val)))
         :none (make-valid-ext-info
                :type type
                :declared-in (insert table.filepath nil)
                :uid uid)))
       (new-externals
        (omap::update (ident-fix ident) new-info vstate.externals)))
    (change-vstate vstate :externals new-externals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-add-ord ((ident identp)
                        (info valid-ord-infop)
                        (vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Add an ordinary identifier to the validation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the information to associate to the identifier.")
   (xdoc::p
    "The identifier is always added to
     the first (i.e. innermost, i.e. current) scope of the validation table.
     We check the existence of at least one scope;
     recall that there must be always a file scope.")
   (xdoc::p
    "If the identifier is already present in the current scope,
     its information is overwritten,
     but we only call this function after checking that
     this overwriting is acceptable,
     i.e. when it ``refines'' the validation information for the identifier.
     We could consider adding a guard to this function
     that characterizes the acceptable overwriting.")
   (xdoc::p
    "If @('info') indicates external linkage, we update the @('externals') map.
     See @(tsee vstate-update-ext)."))
  (b* (((vstate vstate) vstate)
       ((valid-table table) vstate.table)
       ((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (vstate-fix vstate))
       (scope (car table.scopes))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (cons new-scope (cdr table.scopes)))
       (table (change-valid-table table :scopes new-scopes))
       (vstate (change-vstate vstate :table table))
       (vstate
         (valid-ord-info-case
          info
          :objfun (linkage-case
                   info.linkage
                   :external
                   (vstate-update-ext ident info.type info.uid vstate)
                   :otherwise vstate)
          :otherwise vstate)))
    vstate)
  :guard-hints (("Goal" :in-theory (enable valid-table-num-scopes acons)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define vstate-add-ord-file-scope ((ident identp)
                                   (info valid-ord-infop)
                                   (vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Add an ordinary identifier
          to the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee vstate-add-ord), this skips any block scopes,
     and directly updates the file scope at the bottom of the stack.
     It is used in some situations.")
   (xdoc::p
    "As in @(tsee vstate-add-ord), we update the @('externals') map
     if @('info') indicates external linkage."))
  (b* (((vstate vstate) vstate)
       ((valid-table table) vstate.table)
       (scopes (valid-table->scopes table))
       ((when (endp scopes))
        (raise "Internal error: no scopes.")
        (irr-vstate))
       (scope (car (last scopes)))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (append (butlast scopes 1) (list new-scope)))
       (table (change-valid-table table :scopes new-scopes))
       (vstate (change-vstate vstate :table table))
       (vstate
         (valid-ord-info-case
          info
          :objfun (linkage-case
                   info.linkage
                   :external
                   (vstate-update-ext ident info.type info.uid vstate)
                   :otherwise vstate)
          :otherwise vstate)))
    vstate)
  :guard-hints (("Goal" :in-theory (enable acons)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

(define vstate-add-ord-objfuns-file-scope ((idents ident-listp)
                                           (type typep)
                                           (linkage linkagep)
                                           (defstatus valid-defstatusp)
                                           (vstate vstatep))
  :returns (new-vstate vstatep)
  :short "Add a list of ordinary identifiers
          corresponding to objects or functions
          to the file scope of a validation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee vstate-add-ord-file-scope)."))
  (b* (((when (endp idents))
        (vstate-fix vstate))
       ((mv uid vstate) (vstate-get-fresh-uid (first idents) linkage vstate)))
    (vstate-add-ord-objfuns-file-scope
     (rest idents)
     type
     linkage
     defstatus
     (vstate-add-ord-file-scope (first idents)
                                (make-valid-ord-info-objfun
                                  :type type
                                  :linkage linkage
                                  :defstatus defstatus
                                  :uid uid)
                                vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vstate-make-type-composite ((x typep)
                                    (y typep)
                                    (vstate vstatep))
  :returns (mv (composite typep)
               (new-vstate vstatep))
  :short "Construct a composite @(see type) with a validation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This wraps @(tsee type-composite),
     extracting the @('completions') @('next-uid') from the validation state,
     and updating the values accordingly."))
  (b* (((vstate vstate) vstate)
       ((mv composite completions next-uid)
        (type-composite x y vstate.completions vstate.next-uid vstate.ienv)))
    (mv composite
        (change-vstate
          vstate
          :completions completions
          :next-uid next-uid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-dec/oct/hex-const ((const dec/oct/hex-constp))
  :returns (value natp)
  :short "Validate a decimal, octal, or hexadecimal constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of constant is always valid,
     but for this function we use the naming scheme @('valid-...')
     for uniformity with the other validator's functions.")
   (xdoc::p
    "This function actually evaluates the constant, to a natural number.
     This is needed by the validator in order to assign
     types to integer constants.
     This function returns a natural number,
     which can be arbitrarily large;
     whether an integer constant is too large is checked elsewhere."))
  (dec/oct/hex-const->value const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-iconst ((iconst iconstp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (new-iconst iconstp) (type typep))
  :short "Validate an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer constant is valid iff
     it has a type according to the table in [C17:6.4.4.1/5].
     We formalize that table here, and we return the type of the constant.
     If the constant is too large,
     it does not have a type, and it is invalid."))
  (b* (((reterr) (irr-iconst) (irr-type))
       ((iconst iconst) iconst)
       (value (valid-dec/oct/hex-const iconst.core))
       ((erp type)
        (b* (((reterr) (irr-type)))
          (cond
           ((not iconst.suffix?)
            (if (dec/oct/hex-const-case iconst.core :dec)
                (cond ((ienv-sint-rangep value ienv) (retok (type-sint)))
                      ((ienv-slong-rangep value ienv) (retok (type-slong)))
                      ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))
              (cond ((ienv-sint-rangep value ienv) (retok (type-sint)))
                    ((ienv-uint-rangep value ienv) (retok (type-uint)))
                    ((ienv-slong-rangep value ienv) (retok (type-slong)))
                    ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                    ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                    ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                    (t (retmsg$ "The constant ~x0 is too large."
                                (iconst-fix iconst))))))
           ((isuffix-case iconst.suffix? :u)
            (cond ((ienv-uint-rangep value ienv) (retok (type-uint)))
                  ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                  ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           ((isuffix-case iconst.suffix? :l)
            (cond
             ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                         '(:locase-l :upcase-l))
              (if (dec/oct/hex-const-case iconst.core :dec)
                  (cond ((ienv-slong-rangep value ienv) (retok (type-slong)))
                        ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                        (t (retmsg$ "The constant ~x0 is too large."
                                    (iconst-fix iconst))))
                (cond ((ienv-slong-rangep value ienv) (retok (type-slong)))
                      ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                      ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))))
             ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                         '(:locase-ll :upcase-ll))
              (if (dec/oct/hex-const-case iconst.core :dec)
                  (cond ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                        (t (retmsg$ "The constant ~x0 is too large."
                                    (iconst-fix iconst))))
                (cond ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))))
             (t (prog2$ (impossible) (retmsg$ "")))))
           ((or (and (isuffix-case iconst.suffix? :ul)
                     (member-eq (lsuffix-kind
                                 (isuffix-ul->length iconst.suffix?))
                                '(:locase-l :upcase-l)))
                (and (isuffix-case iconst.suffix? :lu)
                     (member-eq (lsuffix-kind
                                 (isuffix-lu->length iconst.suffix?))
                                '(:locase-l :upcase-l))))
            (cond ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                  ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           ((or (and (isuffix-case iconst.suffix? :ul)
                     (member-eq (lsuffix-kind
                                 (isuffix-ul->length iconst.suffix?))
                                '(:locase-ll :upcase-ll)))
                (and (isuffix-case iconst.suffix? :lu)
                     (member-eq (lsuffix-kind
                                 (isuffix-lu->length iconst.suffix?))
                                '(:locase-ll :upcase-ll))))
            (cond ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           (t (prog2$ (impossible) (retmsg$ ""))))))
       (info (make-iconst-info :type type :value value))
       (new-iconst (change-iconst iconst :info info)))
    (retok new-iconst type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fconst ((fconst fconstp))
  :returns (type typep)
  :short "Validate a floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "A floating constant is always valid:
     [C17:6.4.4.2] states no restrictions,
     except for a recommended practice
     to provide a diagnostic message in certain cases,
     which also instructs to proceed with compilation nonetheless,
     suggesting that it should be only a warning, not an error.")
   (xdoc::p
    "The type is determined solely by the suffix, including its absence
     [C17:6.4.4.2/4]."))
  (b* ((suffix? (fconst-case fconst
                             :dec fconst.suffix?
                             :hex fconst.suffix?)))
    (cond ((not suffix?) (type-double))
          ((or (fsuffix-case suffix? :locase-f)
               (fsuffix-case suffix? :upcase-f))
           (type-float))
          ((or (fsuffix-case suffix? :locase-l)
               (fsuffix-case suffix? :upcase-l))
           (type-ldouble))
          (t (type-unknown)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-univ-char-name ((ucn univ-char-name-p) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate a universal character name."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the numeric code of the character.")
   (xdoc::p
    "[C17:6.4.3/2] states some restriction on the character code.
     [C17:6.4.4.4/4] and (implicitly) [C17:6.4.5/4]
     state type-based restrictions on
     the character codes of octal and hexadecimal escapes,
     based on the (possibly absent) prefix of
     the character constant or string literal.
     But it seems reasonable that the same range restrictions
     should also apply to universal character names;
     some experiments with the C compiler on Mac confirms this."))
  (b* (((reterr) 0)
       (code (univ-char-name-case
              ucn
              :locase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad)
                               (hex-quad->2nd ucn.quad)
                               (hex-quad->3rd ucn.quad)
                               (hex-quad->4th ucn.quad)))
              :upcase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad1)
                               (hex-quad->2nd ucn.quad1)
                               (hex-quad->3rd ucn.quad1)
                               (hex-quad->4th ucn.quad1)
                               (hex-quad->1st ucn.quad2)
                               (hex-quad->2nd ucn.quad2)
                               (hex-quad->3rd ucn.quad2)
                               (hex-quad->4th ucn.quad2)))))
       ((when (and (< code #xa0)
                   (not (= code #x24))
                   (not (= code #x40))
                   (not (= code #x60))))
        (retmsg$ "The universal character name ~x0 has a code ~x1
                  that is below A0h but is not 24h or 40h or 60h."
                 (univ-char-name-fix ucn) code))
       ((when (and (<= #xd800 code)
                   (<= code #xdfff)))
        (retmsg$ "The universal character name ~x0 has a code ~x1
                  between D800h and DFFFh."
                 (univ-char-name-fix ucn) code))
       ((when (> code (nfix max)))
        (retmsg$ "The universal character name ~x0 has a code ~x1 above ~x2."
                 (univ-char-name-fix ucn) code (nfix max))))
    (retok code)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-simple-escape ((esc simple-escapep))
  :returns (code natp)
  :short "Validate a simple escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Simple escapes are always valid.
     This function returns their ASCII codes.
     Note that these always fit in any of the types
     mentioned in [C17:6.4.4.4/4].
     The GCC escape @('\\%') is like the character @('%')."))
  (simple-escape-case
   esc
   :squote (char-code #\')
   :dquote (char-code #\")
   :qmark (char-code #\?)
   :bslash (char-code #\\)
   :a 7
   :b 8
   :f 12
   :n 10
   :r 13
   :t 9
   :v 11
   :percent (char-code #\%)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-oct-escape ((esc oct-escapep) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate an octal escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.4.4.4/9] states restrictions on
     the numeric value of an octal escape used in a character constant,
     based on the prefix of the character constant;
     similarly restrictions apply to octal escapes in string literals
     [C17:6.4.5/4].
     This ACL2 function is used to check
     both octal escapes in character constants
     and octal escapes in string literals:
     we pass as input the maximum allowed character code,
     which is determined from the character constant or string literal prefix
     if present (see callers),
     and suffices to express the applicable restrictions."))
  (b* (((reterr) 0)
       (code (oct-escape-case
              esc
              :one (str::oct-digit-char-value esc.digit)
              :two (str::oct-digit-chars-value (list esc.digit1
                                                     esc.digit2))
              :three (str::oct-digit-chars-value (list esc.digit1
                                                       esc.digit2
                                                       esc.digit3)))))
    (if (<= code (nfix max))
        (retok code)
      (retmsg$ "The octal escape sequence ~x0 has value ~x1, ~
                which exceeds the maximum allowed ~x2, ~
                required in the context of where this octal escape occurs."
               (oct-escape-fix esc)
               code
               (nfix max)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-escape ((esc escapep) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the escape sequence is valid, we return its character code.
     For simple and octal escapes, and for universal character names,
     we use separate validation functions.
     For a hexadecimal escape, we calculate the numeric value,
     and we subject them to same restrictions as octal escapes
     [C17:6.4.4.4/9] [C17:6.4.5/4].")
   (xdoc::p
    "Although [C17] does not seem to state that explicitly,
     it seems reasonable that the same restriction applies to
     universal character names;
     we will revise this if that turns out to be not the case."))
  (b* (((reterr) 0))
    (escape-case
     esc
     :simple (retok (valid-simple-escape esc.escape))
     :oct (valid-oct-escape esc.escape max)
     :hex (b* ((code (str::hex-digit-chars-value esc.escape)))
            (if (<= code (nfix max))
                (retok code)
              (retmsg$ "The hexadecimal escape sequence ~x0 has value ~x1, ~
                        which exceeds the maximum allowed ~x2, ~
                        required in the context where ~
                        this hexadecimal escape occurs."
                       (escape-fix esc)
                       code
                       (nfix max))))
     :univ (valid-univ-char-name esc.escape max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char ((cchar c-char-p) (prefix? eprefix-optionp) (ienv ienvp))
  :returns (mv (erp maybe-msgp)
               (code natp
                     :hints (("Goal" :in-theory (enable natp-when-ucharp)))))
  :short "Validate a character of a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.")
   (xdoc::p
    "The grammar [C17:6.4.4.4/1] excludes (direct) character codes
     for single quote and new-line.
     For the latter, we check both line feed and carriage return.
     Note that our lexer normalizes both to line feed,
     and excludes line feed when lexing @('c-char');
     here we make an independent check,
     but in the future we could make that
     an invariant in the abstract syntax.")
   (xdoc::p
    "[C17:6.4.4.4/4] says that, based on the (possibly absent) prefix
     of the character constant of which this character is part,
     the character code of an octal or hexadecimal escape must fit in
     @('unsigned char'), or
     @('wchar_t'), or
     @('char16_t'), or
     @('char32_t').
     To properly capture the range of the latter three types,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to,
     and then use again the implementation environment
     to obtain the maximun values of such built-in types.
     For now, we just use the maximum Unicode code points,
     i.e. effectively we do not enforce any restriction."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (ienv->uchar-max ienv))))
    (c-char-case
     cchar
     :char (cond ((= cchar.code (char-code #\'))
                  (retmsg$ "Single quote cannot be used directly ~
                            in a character constant."))
                 ((= cchar.code 10)
                  (retmsg$ "Line feed cannot be used directly ~
                            in a character constant."))
                 ((= cchar.code 13)
                  (retmsg$ "Carriage return cannot be used directly ~
                            in a character constant."))
                 ((> cchar.code max)
                  (retmsg$ "The character with code ~x0 ~
                            exceed the maximum ~x1 allowed for ~
                            a character constant with prefix ~x2."
                           cchar.code max (eprefix-option-fix prefix?)))
                 (t (retok cchar.code)))
     :escape (valid-escape cchar.escape max)))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-ucharp
                                           rationalp-when-ucharp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char-list ((cchars c-char-listp)
                           (prefix? eprefix-optionp)
                           (ienv ienvp))
  :returns (mv (erp maybe-msgp) (codes nat-listp))
  :short "Validate a list of characters of a character constant."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-c-char (car cchars) prefix? ienv))
       ((erp codes) (valid-c-char-list (cdr cchars) prefix? ienv)))
    (retok (cons code codes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cconst ((cconst cconstp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the constant,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the constant.
     According to [C17:6.4.4.4/10],
     a character constant without prefix has type @('int').
     According to [C17:6.4.4.4/11],
     a character constant with a prefix has type
     @('wchar_t'), @('char16_t'), or @('char32_t');
     since for now we do not model these,
     we return an unknown type in this case.")
   (xdoc::p
    "The types @('wchar_t'), @('char16_t'), and @('char32_t')
     may vary across implementations.
     In order to handle these in a general way,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to.
     Once we do that, we will be able to perform
     a full validation of character constants here."))
  (b* (((reterr) (irr-type))
       ((cconst cconst) cconst)
       ((erp &) (valid-c-char-list cconst.cchars cconst.prefix? ienv)))
    (if cconst.prefix?
        (retok (type-unknown))
      (retok (type-sint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-enum-const ((econst identp) (vstate vstatep))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate an enumeration constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we validate an enumeration constant that occurs as an expression.
     Thus, the validation table must include that (ordinary) identifier,
     with the information of being an enumeration constant.
     Its type is always @('int') [C17:6.7.2.2/3],
     so this function always returns that type if validation succeeds;
     we could have this function return nothing if there's no error,
     but we have it return the @('int') type for uniformity and simplicity."))
  (b* (((reterr) (irr-type))
       ((mv info &) (vstate-lookup-ord econst vstate))
       ((unless info)
        (retmsg$ "The identifier ~x0, used as an enumeration constant, ~
                  is not in scope."
                 (ident-fix econst)))
       ((unless (valid-ord-info-case info :enumconst))
        (retmsg$ "The identifier ~x0, used as an enumeration constant, ~
                  is in scope, but it is not an enumeration constant: ~
                  its information is ~x1."
                 (ident-fix econst) info)))
    (retok (type-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-const ((const constp) (vstate vstatep))
  :returns (mv (erp maybe-msgp) (new-const constp) (type typep))
  :short "Validate a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the type of the constant."))
  (b* (((reterr) (irr-const) (irr-type))
       (ienv (vstate->ienv vstate)))
    (const-case
     const
     :int (b* (((erp iconst type) (valid-iconst const.iconst ienv)))
            (retok (const-int iconst) type))
     :float (b* ((type (valid-fconst const.fconst)))
              (retok (const-fix const) type))
     :enum (b* (((erp type) (valid-enum-const const.ident vstate)))
             (retok (const-fix const) type))
     :char (b* (((erp type) (valid-cconst const.cconst ienv)))
             (retok (const-fix const) type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char ((schar s-char-p) (prefix? eprefix-optionp) (ienv ienvp))
  :returns (mv (erp maybe-msgp)
               (code natp
                     :hints (("Goal" :in-theory (enable natp-when-ucharp)))))
  :short "Validate a character of a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.
     [C17:6.4.5/4] says that the same restrictions that apply
     to @('c-char')s in character constants
     also apply to @('s-char')s in string literals.
     So this function is similar to @(tsee valid-c-char),
     except that we prohibit double quote instead of single quote,
     based on the grammar in [C17:6.4.5/1]."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (ienv->uchar-max ienv))))
    (s-char-case
     schar
     :char (cond ((= schar.code (char-code #\"))
                  (retmsg$ "Double quote cannot be used directly ~
                            in a string literal."))
                 ((= schar.code 10)
                  (retmsg$ "Line feed cannot be used directly ~
                            in a character constant."))
                 ((= schar.code 13)
                  (retmsg$ "Carriage return cannot be used directly ~
                            in a character constant."))
                 ((> schar.code max)
                  (retmsg$ "The character with code ~x0 ~
                            exceeds the maximum ~x1 allowed for ~
                            a character constant with prefix ~x2."
                           schar.code max (eprefix-option-fix prefix?)))
                 (t (retok schar.code)))
     :escape (valid-escape schar.escape max)))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-ucharp
                                           rationalp-when-ucharp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char-list ((cchars s-char-listp)
                           (prefix? eprefix-optionp)
                           (ienv ienvp))
  :returns (mv (erp maybe-msgp) (codes nat-listp))
  :short "Validate a list of characters of a string literal."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-s-char (car cchars) prefix? ienv))
       ((erp codes) (valid-s-char-list (cdr cchars) prefix? ienv)))
    (retok (cons code codes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit ((strlit stringlitp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the string literal,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the string literal.
     If the literal is a character string literal
     (i.e. it has no encoding prefix)
     or a UTF-8 string literal
     (i.e. it has the @('u8') prefix),
     it has an array type with element type @('char').
     If an encoding prefix is present,
     the literal may have type @('wchar_t') or @('char16_t') or @('char32_t').
     Since we do not yet model the values of these type definitions,
     we return an array type with an unknown element type in these cases."))
  (b* (((reterr) (make-type-array :of (irr-type) :size nil))
       ((stringlit strlit) strlit)
       ((erp &) (valid-s-char-list strlit.schars strlit.prefix? ienv)))
    (retok (make-type-array
            :of (if (or (not strlit.prefix?)
                        (eprefix-case strlit.prefix? :locase-u8))
                    (type-char)
                  (type-unknown))
            :size nil))) ; TODO: size

  ///

  (defret type-kind-of-valid-stringlit.type
    (equal (type-kind type)
           :array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit-list ((strlits stringlit-listp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a list of string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax preserves information about
     adjacent string literals [C17:5.1.1.2/6],
     by using lists of string literals, instead of single string literals,
     in various places.
     So the validator also operates on such lists of string literals.")
   (xdoc::p
    "One basic requirement is that the list is not empty,
     because there must be at least one string literal;
     in the future we could built that constraint into the abstract syntax,
     but for now we put that as a check in the validator.")
   (xdoc::p
    "Another requirement is that
     there cannot be both UTF-8 and wide prefixes [C17:6.4.5/2],
     where these kinds of prefixes are defined in [C17:6.4.5/3].
     We check that by projecting the optional prefixes
     and checking for incompatible occurrences.")
   (xdoc::p
    "Whether string literals with different prefixes
     (satisfying the requirement just mentioned)
     can be concatenated, and what their combined type is,
     is implementation-defined [C17:6.4.5/5].
     We plan to extend our implementation environments
     with information about how to treat those cases,
     but for now we allow all concatenations.")
   (xdoc::p
    "If all literals in the concatenation are character string literals
     or UTF-8 string literals,
     the result is an array type with the element type @('char').
     Otherwise, it is an array type with an unknown element type.
     This covers both the case of well-defined wide string literals
     (whose types we do not yet model),
     and the implementation-defined mixed string encoding."))
  (b* (((reterr) (make-type-array :of (irr-type) :size nil))
       ((unless (consp strlits))
        (retmsg$ "There must be at least one string literal."))
       ((erp prefix? conflictp) (valid-stringlit-list-loop strlits ienv))
       (prefixes (stringlit-list->prefix? strlits))
       ((when (and (member-equal (eprefix-locase-u8) prefixes)
                   (or (member-equal (eprefix-locase-u) prefixes)
                       (member-equal (eprefix-upcase-u) prefixes)
                       (member-equal (eprefix-upcase-l) prefixes))))
        (retmsg$ "Incompatible prefixes ~x0 in the list of string literals."
                 prefixes)))
    (retok (make-type-array
            :of (if (or conflictp
                        (and prefix? (not (eprefix-case prefix? :locase-u8))))
                    (type-unknown)
                  (type-char))
            :size nil))) ; TODO: size
  :prepwork
  ((define valid-stringlit-list-loop ((strlits stringlit-listp) (ienv ienvp))
     :returns (mv (erp maybe-msgp)
                  (prefix? eprefix-optionp)
                  (conflictp booleanp :rule-classes :type-prescription))
     :parents nil
     (b* (((reterr) nil nil)
          ((when (endp strlits)) (retok nil nil))
          ((erp &) (valid-stringlit (car strlits) ienv))
          (first-prefix? (stringlit->prefix? (car strlits)))
          ((erp rest-prefix? conflictp)
           (valid-stringlit-list-loop (cdr strlits) ienv))
          (prefix? (or first-prefix? rest-prefix?))
          (conflictp (or conflictp
                         (and first-prefix?
                              rest-prefix?
                              (not (equal first-prefix? rest-prefix?))))))
       (retok prefix? conflictp))))

  ///

  (defret type-kind-of-valid-stringlit-list.type
    (equal (type-kind type)
           :array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-var ((var identp) (vstate vstatep))
  :returns (mv (erp maybe-msgp) (type typep) (linkage linkagep) (uid uidp))
  :short "Validate a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to validate the @(':ident') case of the @(tsee expr) fixtype.
     This is the case of a variable, not an enumeration constant,
     which is part of the @(':const') case of @(tsee expr).
     Recall that the parser initially parses all identifiers used as expressions
     under the @(':ident') case, but the disambiguator re-classifies
     some of them under the @(':const') case, as appropriate.")
   (xdoc::p
    "A variable (i.e. identifier) is valid if
     it is found in the validation table,
     recorded as denoting an object or function
     [C17:6.5.1/2].
     The type and the linkage are obtained from the table."))
  (b* (((reterr) (irr-type) (irr-linkage) (irr-uid))
       ((mv info &) (vstate-lookup-ord var vstate))
       ((unless info)
        (retmsg$ "The variable ~x0 is not in scope." (ident-fix var)))
       ((unless (valid-ord-info-case info :objfun))
        (retmsg$ "The identifier ~x0, used as a variable,is in scope, ~
                  but does not denote an object or function."
                 (ident-fix var))))
    (retok (valid-ord-info-objfun->type info)
           (valid-ord-info-objfun->linkage info)
           (valid-ord-info-objfun->uid info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-gensel ((expr exprp)
                      (type typep)
                      (type-alist type-option-type-alistp))
  :guard (expr-case expr :gensel)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a generic selection expression,
          given the types for the components."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not perform any of the checks prescribed in [C17:6.5.1.1/2].
     We will perform them later, when we refine our validator.
     We return the unknown type."))
  (declare (ignore expr type type-alist))
  (retok (type-unknown)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-arrsub ((expr exprp) (type-arg1 typep) (type-arg2 typep))
  :guard (expr-case expr :arrsub)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate an array subscripting expression,
          given the types of the two sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting array types to pointer types,
     one sub-expression must have pointer type,
     and the other sub-expression must have integer type
     [C17:6.5.2.1/1].
     The expression has the type referenced by the pointer type.")
   (xdoc::p
    "There is no need to perform function-to-pointer conversion,
     because that would result in a pointer to function,
     which is disallowed,
     as it has to be a pointer to a complete object type [C17:6.5.2.1/1].
     So by leaving function types as such, we automatically disallow them."))
  (b* (((reterr) (irr-type))
       (type1 (type-apconvert type-arg1))
       (type2 (type-apconvert type-arg2))
       ((when (and (type-case type1 :pointer)
                   (or (type-integerp type2)
                       (type-case type2 :unknown))))
        (retok (type-pointer->to type1)))
       ((when (and (type-case type2 :pointer)
                   (or (type-integerp type1)
                       (type-case type1 :unknown))))
        (retok (type-pointer->to type2)))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown))))
    (retmsg$ "In the array subscripting expression ~x0, ~
              the first sub-expression has type ~x1, ~
              and the second sub-expression has type ~x2."
             (expr-fix expr)
             (type-fix type-arg1)
             (type-fix type-arg2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-prototype-args ((types-param type-listp)
                              (args expr-listp)
                              (types-arg type-listp)
                              (ellipsis booleanp)
                              (completions type-completions-p)
                              (ienv ienvp))
  :guard (equal (len types-arg) (len args))
  :returns (erp maybe-msgp)
  :short "Validate a function prototype parameter list against a list of
          arguments given the argument types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a function type which includes a prototype,
     two conditions must hold [C17:6.5.2.2/2]:")
   (xdoc::ol
    (xdoc::li
     "The number of arguments must be the same as the number of parameter types,
      or greater than or equal when an ellipsis is present.
      The `greater than' part does not seem to be explicitly stated in [C17],
      which just says that the number of arguments
      must agree with the number of parameters [C17:6.5.2.2/2];
      one could interpret `number of parameters' loosely as
      the ellipsis implying an unspecified number of additional parameters.
      Indeed, [C17:6.7.6.3/9] say that
      the ellipsis conveys no information about the additional parameters,
      suggesting that additional arguments are allowed.
      Simple experiments with GCC confirm the ability to pass
      more arguments than declared parameters when there is an ellipsis.")
    (xdoc::li
     "For each parameter/argument pair,
      the same restrictions apply as in the case of simple assignment.
      See @(tsee valid-binary) for details on these restrictions.
      When validating with GCC/Clang extensions enabled,
      these restrictions are slightly weakened.
      See the following section."))
   (xdoc::section
    "GCC/Clang Extensions"
    (xdoc::p
     "GCC has a type attribute @('transparent_union')
      which affects type-checking of arguments against
      some parameters with union type.
      The attribute may be attached a union type definition.
      When a function parameter has such a type,
      the constraints on the corresponding argument are weakened.
      In particular, the type of the argument
      is allowed to be any of the member types of the union,
      and a null pointer expression or void pointer type is allowed
      if any of the union members are a pointer.
      For now, we approximate this by allowing any argument type
      when the parameter type is a union and GCC/Clang extensions are enabled.
      See "
     (xdoc::ahref
      "https://gcc.gnu.org/onlinedocs/gcc/Common-Type-Attributes.html"
      "[GCCM:6.4.3.1]")
     " for more information on the @('transparent_union') attribute.")))
  (b* (((reterr))
       (types-param (type-list-fix types-param))
       (args (expr-list-fix args))
       ((ienv ienv) ienv)
       ((when (endp types-param))
        (if (or (endp types-arg) ellipsis)
            nil
          (retmsg$ "Too many arguments.")))
       ((when (endp types-arg))
        (retmsg$ "Too few arguments."))
       (type-param (first types-param))
       (arg (first args))
       (type-arg (type-fpconvert (type-apconvert (first types-arg))))
       (gcc/clang (ienv->gcc/clang ienv)))
    (if (or (type-case type-param :unknown)
            (and gcc/clang (type-case type-param :union))
            (type-case type-arg :unknown)
            (and (type-arithmeticp type-param)
                 (type-arithmeticp type-arg))
            (and (or (type-case type-param :struct)
                     (type-case type-param :union))
                 (type-compatible-p type-param type-arg completions ienv))
            (and (type-case type-param :pointer)
                 (or (and (type-case type-arg :pointer)
                          (let ((type-to-param (type-pointer->to type-param))
                                (type-to-arg (type-pointer->to type-arg)))
                            (or (type-compatible-p
                                 type-to-param type-to-arg completions ienv)
                                (and (type-case type-to-param :void)
                                     (not (type-case type-to-arg :function)))
                                (and (type-case type-to-arg :void)
                                     (not
                                      (type-case type-to-param :function))))))
                     (expr-null-pointer-constp arg type-arg ienv)))
            (and (type-case type-param :bool)
                 (type-case type-arg :pointer)))
        (valid-prototype-args (rest types-param)
                              (rest args)
                              (rest types-arg)
                              ellipsis
                              completions
                              ienv)
      (retmsg$ "Argument ~x0 with type ~x1 ~
                cannot be applied to function parameter with type ~x2."
               arg
               type-arg
               type-param)))
  :measure (len (type-list-fix types-param))
  :hints (("Goal" :in-theory (enable type-list-fix len)))
  :guard-hints (("Goal" :in-theory (enable len)))
  :hooks ((:fix
           :hints (("Goal" :induct t
                    :expand (valid-prototype-args
                             (type-list-fix types-param) args types-arg
                             ellipsis completions ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-funcall ((expr exprp)
                       (type-fun typep)
                       (types-arg type-listp)
                       (completions type-completions-p)
                       (ienv ienvp))
  :guard (and (expr-case expr :funcall)
              (equal (len types-arg)
                     (len (expr-funcall->args expr))))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a function call expression,
          given the types of the sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting function types to pointer types,
     the first sub-expression must have pointer type [C17:6.5.2.2/1];
     Furthermore, it must be a pointer to a function type.")
   (xdoc::p
    "There is no need to perform array-to-pointer conversion,
     because array types cannot have function element types,
     but only (complete) object element types [C17:6.2.5/20].
     Thus, the conversion could never result into a pointer to a function.")
   (xdoc::p
    "When the function expression is a pointer
     to a function type which includes a prototype,
     we validate the arguments
     against the prototype parameter list [C17:6.5.2.2/2]
     (see @(tsee valid-prototype-args)).
     We return the function return type."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-fun :unknown))
        (retok (type-unknown)))
       (type (type-fpconvert type-fun))
       ((unless (type-case type :pointer))
        (retmsg$ "In the function call expression ~x0, ~
                  the first sub-expression is expected to have a pointer type, ~
                  but it has type ~x1."
                 (expr-fix expr)
                 (type-fix type-fun)))
       (to-type (type-pointer->to type))
       ((when (type-case to-type :unknown))
        (retok (type-unknown)))
       ((unless (type-case to-type :function))
        (retmsg$ "In the function call expression ~x0, ~
                  the first sub-expression is expected
                  to have a function pointer or unknown pointer type,
                  but it has type ~x1."
                 (expr-fix expr)
                 (type-fix type-fun)))
       (type-params (type-function->params to-type))
       ((erp)
        (type-params-case
         type-params
         :prototype (valid-prototype-args type-params.params
                                          (expr-funcall->args expr)
                                          types-arg
                                          type-params.ellipsis
                                          completions
                                          ienv)
         :otherwise (retok))
        :iferr (msg$ "Error in function call ~x0:~%~@1" (expr-fix expr) erp)))
    (retok (type-function->ret to-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-member ((expr exprp)
                      (type-arg typep)
                      (completions type-completions-p))
  :guard (expr-case expr :member)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a member expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument type must be a structure or union type [C17:6.5.2.3/1].
     Since a pointer type is not allowed here,
     there is no need to convert arrays or functions to pointers.")
   (xdoc::p
    "The structure or union type completion
     is looked up in the @('completions') map.
     The struct must be complete;
     if there is no completion, it is a validation error [C17:6.5.2.3/1].
     The type of the member is then looked up within the completion,
     which becomes the type of the expression [C17:6.5.2.3/3].
     If there is no such member within the completion,
     it is a validation error [C17:6.5.2.3/1]."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (name (expr-member->name expr))
       ((erp uid tag/members)
        (b* (((reterr) nil nil))
          (type-case
           type-arg
           :struct (retok type-arg.uid type-arg.tag/members)
           :union (retok type-arg.uid type-arg.tag/members)
           :otherwise (retmsg$ "In the member expression ~x0, ~
                                 the sub-expression has type ~x1."
                               (expr-fix expr) (type-fix type-arg)))))
       ((mv erp members)
        (type-struni-tag/members->members tag/members uid completions))
       ((when erp)
        (retmsg$ "Cannot get member ~x0 of incomplete type ~x1. ~
                  This occurred in the expression ~x2."
                 name
                 (type-fix type-arg)
                 (expr-fix expr)))
       (type? (type-struni-member-list-lookup name members))
       ((unless type?)
        (retmsg$ "No member field ~x0 in type ~x1."
                 name
                 (type-fix type-arg))))
    (retok type?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-memberp ((expr exprp)
                       (type-arg typep)
                       (completions type-completions-p))
  :guard (expr-case expr :memberp)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a member pointer expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the sub-expression is
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "The argument type must be a pointer to a structure or union type
     [C17:6.5.2.3/2].
     We perform array-to-pointer conversion,
     then check that the type is a pointer to a struct type.
     We do not convert functions to pointers,
     because that would result into a pointer to function,
     which is not a pointer to structure or union as required;
     thus, by leaving function types unchanged, we reject them here.")
   (xdoc::p
    "The structure or union type completion
     is looked up in the @('completions') map.
     The type must be complete;
     if there is no completion, it is a validation error [C17:6.5.2.3/1].
     The type of the member is then looked up within the completion,
     which becomes the type of the expression [C17:6.5.2.3/4].
     If there is no such member within the completion,
     it is a validation error [C17:6.5.2.3/1]."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (type (type-apconvert type-arg))
       ((unless (type-case type :pointer))
        (retmsg$ "In the member pointer expression ~x0, ~
                  the sub-expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg)))
       (to-type (type-pointer->to type))
       ((when (type-case to-type :unknown))
        (retok (type-unknown)))
       (name (expr-memberp->name expr))
       ((erp uid tag/members)
        (b* (((reterr) nil nil))
          (type-case
           to-type
           :struct (retok to-type.uid to-type.tag/members)
           :union (retok to-type.uid to-type.tag/members)
           :otherwise (retmsg$ "In the member expression ~x0, ~
                                 the sub-expression has type ~x1."
                               (expr-fix expr) (type-fix type-arg)))))
       ((mv erp members)
        (type-struni-tag/members->members tag/members uid completions))
       ((when erp)
        (retmsg$ "Cannot get member ~x0 of incomplete type ~x1. ~
                  This occurred in the expression ~x2."
                 name
                 to-type
                 (expr-fix expr)))
       (type? (type-struni-member-list-lookup name members))
       ((unless type?)
        (retmsg$ "No member field ~x0 in type ~x1."
                 name
                 to-type)))
    (retok type?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-unary ((expr exprp) (op unopp) (type-arg typep) (ienv ienvp))
  :guard (expr-case expr :unary)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a unary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('&') operator requires an lvalue of any type as operand
     [C17:6.5.3.2/1] [C17:6.5.3.2/3],
     but we are not yet distinguishing lvalues from non-lvalues,
     so we allow any type of operand,
     and we return the pointer type derived from the operand type.")
   (xdoc::p
    "The @('*') unary operator requires an operand of a pointer type
     [C17:6.5.3.2/2],
     after array-to-pointer and function-to-pointer conversions;
     as always, we also need to allow the unknown type.
     The result is the referenced type.")
   (xdoc::p
    "The @('+') and @('-') unary operators
     require an operand of an arithmetic type [C17:6.5.3.3/1],
     and the result has the promoted type [C17:6.5.3.3/2].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('~') operator requires an operand of an integer type [C17:6.5.3.3/1],
     and the result has the promoted type [C17:.6.5.3.3/4].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('!') operator requires an operand of a scalar type [C17:6.5.3.3/1],
     and result is always @('signed int') [C17:6.5.3.3/5].
     Since pointers may be involved, we perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('sizeof') operator applied to an expression
     requires a non-function complete type [C17:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C17:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t').")
   (xdoc::p
    "The @('++') pre-increment and @('--') pre-decrement operators
     require a real or pointer operand [C17:6.5.3.1/1].
     Since these expressions are equivalent to assignments
     [C17:6.5.3.1/2] [C17:6.5.3.1/3],
     the type of the result must be the type of the operand.
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers,
     not lvalues as required [C17:6.5.3.1/1].")
   (xdoc::p
    "The @('++') post-increment and @('--') post-decrement operators
     require a real or pointer operand [C17:6.5.2.4/1].
     The type of the result is the same as the operand
     [C17:6.5.2.4/2] [C17:6.5.2.4/3].
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers,
     not lvalues as required [C17:6.5.2.4/1].")
   (xdoc::p
    "The @('__real__') and @('__imag__') operators (GCC extensions)
     require a complex operand and return a corresponding real operand.
     This is what the GCC documentation seems to suggest,
     although the description is not as precise as in [C17]."))
  (b* (((reterr) (irr-type))
       (msg (msg$ "In the unary expression ~x0, ~
                   the sub-expression has type ~x1."
                  (expr-fix expr) (type-fix type-arg))))
    (case (unop-kind op)
      (:address (retok (make-type-pointer :to type-arg)))
      (:indir (b* (((when (type-case type-arg :unknown))
                    (retok (type-unknown)))
                   (type (type-fpconvert (type-apconvert type-arg))))
                (type-case
                 type
                 :pointer (retok type.to)
                 :otherwise (reterr msg))))
      ((:plus :minus) (b* (((when (type-case type-arg :unknown))
                            (retok (type-unknown)))
                           ((unless (type-arithmeticp type-arg))
                            (reterr msg)))
                        (retok (type-integer-promote type-arg ienv))))
      (:bitnot (b* (((when (type-case type-arg :unknown))
                     (retok (type-unknown)))
                    ((unless (type-integerp type-arg))
                     (reterr msg)))
                 (retok (type-integer-promote type-arg ienv))))
      (:lognot (b* (((when (type-case type-arg :unknown))
                     (retok (type-unknown)))
                    (type (type-fpconvert (type-apconvert type-arg)))
                    ((unless (type-scalarp type))
                     (reterr msg)))
                 (retok (type-sint))))
      ((:preinc :predec :postinc :postdec)
       (b* (((when (type-case type-arg :unknown))
             (retok (type-unknown)))
            ((unless (or (type-realp type-arg)
                         (type-case type-arg :pointer)))
             (reterr msg)))
         (retok (type-fix type-arg))))
      (:sizeof (b* (((when (type-case type-arg :function))
                     (reterr msg)))
                 (retok (type-unknown))))
      (:alignof (b* (((when (type-case type-arg :function))
                      (reterr msg)))
                  (retok (type-unknown))))
      (:real (type-case type-arg
                        :floatc (retok (type-float))
                        :doublec (retok (type-double))
                        :ldoublec (retok (type-ldouble))
                        :unknown (retok (type-unknown))
                        :otherwise (reterr msg)))
      (:imag (type-case type-arg
                        :floatc (retok (type-float))
                        :doublec (retok (type-double))
                        :ldoublec (retok (type-ldouble))
                        :unknown (retok (type-unknown))
                        :otherwise (reterr msg)))
      (t (prog2$ (impossible) (retmsg$ ""))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-simple-assignment ((type-arg1 typep)
                                 (type-arg2 typep)
                                 (expr-arg2 exprp)
                                 (completions type-completions-p)
                                 (ienv ienvp))
  :returns (erp booleanp)
  :short "Validate two types according to the rules of simple assignment."
  :long
  (xdoc::topstring
   (xdoc::p
    "In addition to actual simple assignment expressions,
     the constraints of simple assignment are also used
     for certain initializers (see @(tsee valid-initer)).
     Therefore, we introduce a dedicated function
     for checking said type constraints.")
   (xdoc::p
    "In our currently approximate type system,
     the requirements in [C17:6.5.16.1/1] reduce
     to the following simplified cases.")
   (xdoc::ol
    (xdoc::li
     "Both operands have arithmetic types.")
    (xdoc::li
     "The left operand has a structure or union type, and the two operand types
      are compatible.")
    (xdoc::li
     "Both operands have compatible pointer types.")
    (xdoc::li
     "One operand is a pointer to an object type
      and the other is a pointer to the @('void') type.
      As a GCC/Clang extension,
      we also allow one operand to be a pointer to the @('void') type,
      and the other to be a pointer to <i>any</i> type
      (either object or function).
      We are not aware of explicit GCC documentation of this feature,
      but a related feature is listed by the standard
      as a common extension [C17:J.5.7].")
    (xdoc::li
     "The left operand is a pointer type
      and the right operand is a null pointer constant
      (approximated as anything of an integer type).")
    (xdoc::li
     "The left operand has the boolean type and the right operand has the
      pointer type."))
   (xdoc::p
    "We do not perform array-to-pointer or function-to-pointer conversion
     on the left operand, because the result would not be an lvalue."))
  (b* (((reterr))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok))
       (type1 type-arg1)
       (type2 (type-fpconvert (type-apconvert type-arg2))))
    (if (or (and (type-arithmeticp type1)
                 (type-arithmeticp type2))
            (and (or (type-case type1 :struct)
                     (type-case type1 :union))
                 (type-compatible-p type1 type2 completions ienv))
            (and (type-case type1 :pointer)
                 (or (and (type-case type2 :pointer)
                          (let ((type-to1 (type-pointer->to type1))
                                (type-to2 (type-pointer->to type2)))
                            (or (type-compatible-p
                                 type-to1 type-to2 completions ienv)
                                (and (type-case type-to1 :void)
                                     (or (ienv->gcc/clang ienv)
                                         (not (type-case type-to2
                                                         :function))))
                                (and (type-case type-to2 :void)
                                     (or (ienv->gcc/clang ienv)
                                         (not (type-case type-to1
                                                         :function)))))))
                     (expr-null-pointer-constp expr-arg2 type2 ienv)))
            (and (type-case type1 :bool)
                 (type-case type2 :pointer)))
        (retok)
      (reterr t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-binary ((expr exprp)
                      (op binopp)
                      (type-arg1 typep)
                      (type-arg2 typep)
                      (completions type-completions-p)
                      (ienv ienvp))
  :guard (expr-case expr :binary)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a binary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('*') binary and @('/') operators
     require arithmetic operands [C17:6.5.5/2].
     The result is the common type according to
     the usual arithmetic conversions [C17:6.5.5/3].
     There is no need for array-to-pointer or function-to-pointer conversions
     because those never produce arithmetic types.")
   (xdoc::p
    "The @('%') operator requires integer operands [C17:6.5.5/2].
     The result is from the usual arithmetic conversions [C17:6.5.5/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+') binary operator requires
     either two arithmetic operands
     or an integer and a pointer operand
     [C17:6.5.6/2].
     In the first case, the result is from the usual arithmetic conversions
     [C17:6.5.6/4].
     In the second case,
     the result is the type of the pointer operand [C17:6.5.6/8].
     Because of that second case, which involves pointers,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('-') binary operator requires
     either two arithmetic operands,
     or two pointer operands,
     or a pointer first operand and an integer second operand
     [C17:6.5.6/3].
     In the first case, the result is from the usual arithmetic conversions
     [C17:6.5.6/4].
     In the second case, the result has type @('ptrdiff_t') [C17:6.5.6/9],
     which has an implementation-specific definition,
     and so we return the unknown type in this case.
     In the third case,
     the result has the type of the pointer operand [C17:6.5.6/8].
     Because of the second and third cases, which involve pointers,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('<<') and @('>>') operators require integer operands [C17:6.5.7/2].
     The type of the result is the type of the promoted left operand
     [C17:6.5.7/3].
     There is no need for
     array-to-pointer or function-to-pointer conversions.")
   (xdoc::p
    "The @('<'), @('>'), @('<='), and @('>=') operators
     require real types or pointer types [C17:6.5.8/2].
     The result is always @('signed int') [C17:6.5.8/6].
     Since pointers may be involved,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to object type is required.
     When the converted types are pointer types,
     we check that they point to compatible object types.
     The standard does not allow
     a null pointer constant [C17:6.3.2.3/3] without the @('void *') cast
     to be used as an operand while the other operand has pointer type.
     But we found it accepted by practical compilers,
     so it is probably a GCC extension.
     We therefore accept this when the "
    (xdoc::seetopic "implementation-environments" "implementation-environment")
    " dialect indicates GCC/Clang extensions.
     Since we do not have code yet to recognize null pointer constants,
     we accept any integer expression;
     that is, we allow one pointer operand and one integer operand.")
   (xdoc::p
    "The @('==') and @('!=') operators require
     arithmetic types or pointer types [C17:6.5.9/2];
     When the converted types are pointer types,
     we check that they point to compatible object types,
     or that one of them points to @('void').
     Since we do not yet implement evaluation of constant expressions,
     all integer expressions are considered potential null pointer constants:
     so we allow an operand to be a pointer and the other to be an integer,
     to accommodate a null pointer constant [C17:6.3.2.3/3]
     without the @('void *') cast.
     The result is always @('signed int') [C17:6.5.9/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('&'), @('^'), and @('|') operators require integer operands
     [C17:6.5.10/2] [C17:6.5.11/2] [C17:6.5.12/2].
     The result has the type from the usual arithmetic conversions
     [C17:6.5.10/3] [C17:6.5.11/3] [C17:6.5.12/3].
     No array-to-pointer or function-to-pointer conversion is needed.")
   (xdoc::p
    "The @('&&') and @('||') operators require scalar types
     [C17:6.5.13/2] [C17:6.5.14/2].
     The result has type @('signed int') [C17:6.5.13/3] [C17:6.5.14/3].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('=') simple assignment operator requires
     an lvalue as left operand [C17:6.5.16/2],
     but currently we do not check that.
     Type constraints are checked by @(tsee valid-simple-assignment).
     The type of the result is the type of the left operand [C17:6.5.16/3].")
   (xdoc::p
    "The @('*=') and @('/=') operators require arithmetic operands
     [C17:6.5.16.2/2],
     and the result has the type of the first operand [C17:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('%=') operator requires integer operands [C17:6.5.16.2/2],
     and the result has the type of the first operand [C17:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+=') and @('-=') operands require
     either arithmetic operands
     or a first pointer operand and a second integer operand
     [C17:6.5.16.2/1].
     The result has the type of the first operand [C17:6.5.16/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('<<='), @('>>='), @('&='), @('^='), and @('|=') operators
     require integer operands [C17:6.5.13.2/2].
     The result has the type of the first operand [C17:6.5.13/3].
     No array-to-pointer or function-to-pointer conversions are needed."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown)))
       (msg (msg$ "In the binary expression ~x0, ~
                   the sub-expressions have types ~x1 and ~x2."
                  (expr-fix expr) (type-fix type-arg1) (type-fix type-arg2))))
    (case (binop-kind op)
      ((:mul :div) (b* (((unless (and (type-arithmeticp type-arg1)
                                      (type-arithmeticp type-arg2)))
                         (reterr msg)))
                     (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:rem (b* (((unless (and (type-arithmeticp type-arg1)
                               (type-arithmeticp type-arg2)))
                  (reterr msg)))
              (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:add (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((and (type-integerp type1)
                     (type-case type2 :pointer))
                (retok type2))
               ((and (type-case type1 :pointer)
                     (type-integerp type2))
                (retok type1))
               (t (reterr msg)))))
      (:sub (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((and (type-case type1 :pointer)
                     (type-integerp type2))
                (retok type1))
               ((and (type-case type1 :pointer)
                     (type-case type2 :pointer))
                (retok (type-unknown)))
               (t (reterr msg)))))
      ((:shl :shr) (b* (((unless (and (type-integerp type-arg1)
                                      (type-integerp type-arg2)))
                         (reterr msg)))
                     (retok (type-integer-promote type-arg1 ienv))))
      ((:lt :gt :le :ge)
       (b* ((type1 (type-apconvert type-arg1))
            (type2 (type-apconvert type-arg2))
            ((unless (or (and (type-realp type1)
                              (type-realp type2))
                         (if (type-case type1 :pointer)
                             (and (type-case type2 :pointer)
                                  (let ((type-to1 (type-pointer->to type1))
                                        (type-to2 (type-pointer->to type2)))
                                    (and (not (type-case type-to1 :function))
                                         (not (type-case type-to2 :function))
                                         (type-compatible-p
                                          type-to1 type-to2 completions ienv))))
                           (and (ienv->gcc/clang ienv)
                                (expr-null-pointer-constp
                                 (expr-binary->arg1 expr) type1 ienv)
                                (type-case type2 :pointer)))))
             (reterr msg)))
         (retok (type-sint))))
      ((:eq :ne)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (or (and (type-arithmeticp type1)
                              (type-arithmeticp type2))
                         (if (type-case type1 :pointer)
                             (or (type-compatible-p
                                  type1 type2 completions ienv)
                                 (and (type-case type2 :pointer)
                                      (let ((type-to1 (type-pointer->to type1))
                                            (type-to2 (type-pointer->to type2)))
                                        (or (and (type-case type-to1 :void)
                                                 (not (type-case type-to2
                                                                 :function)))
                                            (and (type-case type-to2 :void)
                                                 (not (type-case type-to1
                                                                 :function))))))
                                 (expr-null-pointer-constp
                                  (expr-binary->arg2 expr) type2 ienv))
                           (and (expr-null-pointer-constp
                                 (expr-binary->arg1 expr) type1 ienv)
                                (type-case type2 :pointer)))))
             (reterr msg)))
         (retok (type-sint))))
      ((:bitand :bitxor :bitior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      ((:logand :logor)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (and (type-scalarp type1)
                          (type-scalarp type2)))
             (reterr msg)))
         (retok (type-sint))))
      (:asg
       (b* (((erp)
             (valid-simple-assignment
              type-arg1 type-arg2 (expr-binary->arg2 expr) completions ienv)
             :iferr msg))
         (retok (type-fix type-arg1))))
      ((:asg-mul :asg-div)
       (b* (((unless (and (type-arithmeticp type-arg1)
                          (type-arithmeticp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (:asg-rem (b* (((unless (and (type-integerp type-arg1)
                                   (type-integerp type-arg2)))
                      (reterr msg)))
                  (retok (type-fix type-arg1))))
      ((:asg-add :asg-sub)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (or (and (type-arithmeticp type1)
                              (type-arithmeticp type2))
                         (and (type-case type1 :pointer)
                              (type-integerp type2))))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      ((:asg-shl :asg-shr :asg-and :asg-xor :asg-ior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (t (prog2$ (impossible) (retmsg$ ""))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-sizeof/alignof ((expr exprp) (type typep))
  :guard (or (expr-case expr :sizeof)
             (expr-case expr :alignof))
  :returns (mv (erp maybe-msgp) (type1 typep))
  :short "Validate a @('sizeof') operator applied to a type name,
          or an @('alignof') operator,
          given the type denoted by the argument type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('sizeof') operator applied to an type name
     requires a non-function complete type [C17:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C17:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t')."))
  (b* (((reterr) (irr-type))
       ((when (type-case type :function))
        (retmsg$ "In the ~s0 type expression ~x1, ~
                  the argument ~x2 is a function type."
                 (case (expr-kind expr)
                   (:sizeof "sizeof")
                   (:alignof "_Alignof")
                   (t (impossible)))
                 (expr-fix expr)
                 (type-fix type))))
    (retok (type-unknown))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cast ((expr exprp) (type-cast typep) (type-arg typep))
  :guard (expr-case expr :cast)
  :returns (mv (erp maybe-msgp) (type1 typep))
  :short "Validate a cast expression,
          given the type denoted by the type name
          and the type of the argument expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type name must denote the void type or a scalar type [C17:6.5.4/2].
     If the type name denotes a scalar type,
     the expression must also have scalar type [C17:6.5.4/2].
     Since scalar types involve pointers,
     we perform array-to-pointer and function-to-pointer conversions.
     The result is the type denoted by the type name."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-cast :unknown)
                  (type-case type-arg :unknown)))
        (retok (type-unknown)))
       (type1-arg (type-fpconvert (type-apconvert type-arg)))
       ((unless (or (type-case type-cast :void)
                    (type-scalarp type-cast)))
        (retmsg$ "In the cast expression ~x0, the cast type is ~x1."
                 (expr-fix expr) (type-fix type-cast)))
       ((unless (or (type-case type-cast :void)
                    (type-scalarp type1-arg)))
        (retmsg$ "In the cast expression ~x0, ~
                  the argument expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (retok (type-fix type-cast))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cond ((expr exprp)
                    (type-test typep)
                    (type-then typep)
                    (type-else typep)
                    (vstate vstatep))
  :guard (expr-case expr :cond)
  :returns (mv (erp maybe-msgp) (type typep) (new-vstate vstatep))
  :short "Validate a conditional expression,
          given types for its operands."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must have scalar type [C17:6.5.15/2].
     In our currently approximate type system,
     the other two operands must have
     both arithmetic type,
     or both the same structure type,
     or both the union type,
     or both the void type,
     or compatible pointer types,
     or one pointer type and the other operand a null pointer constant,
     or one pointer to an object type and one pointer to @('void')
     [C17:6.5.15/3].
     Currently, null pointer constants [C17:6.3.2.3/3] are approximated as any
     expression with an integer type.
     The type of the result is
     the one from the usual arithmetic conversions
     in the first case,
     and the common type in the other cases
     [C17:6.5.15/5].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions."))
  (b* (((reterr) (irr-type) (vstate-fix vstate))
       (ienv (vstate->ienv vstate))
       ((when (or (type-case type-test :unknown)
                  (type-case type-then :unknown)
                  (type-case type-else :unknown)))
        (retok (type-unknown) (vstate-fix vstate)))
       (type1 (type-fpconvert (type-apconvert type-test)))
       (type2 (type-fpconvert (type-apconvert type-then)))
       (type3 (type-fpconvert (type-apconvert type-else)))
       ((unless (type-scalarp type1))
        (retmsg$ "In the conditional expression ~x0, ~
                  the first operand has type ~x1."
                 (expr-fix expr) (type-fix type-test)))
       ((when (and (type-arithmeticp type2)
                   (type-arithmeticp type3)))
        (retok (type-uaconvert type2 type3 ienv) (vstate-fix vstate)))
       ((when (and (type-case type2 :struct)
                   (type-case type3 :struct)))
        (b* (((unless (type-compatible-p type2
                                         type3
                                         (vstate->completions vstate)
                                         ienv))
              (retmsg$ "Struct types ~x0 and ~x1 are incompatible."
                       type2
                       type3))
             ((mv composite vstate)
              (vstate-make-type-composite type2 type3 vstate)))
          (retok composite vstate)))
       ((when (and (type-case type2 :union)
                   (type-case type3 :union)))
        (b* (((unless (type-compatible-p type2
                                         type3
                                         (vstate->completions vstate)
                                         ienv))
              (retmsg$ "Struct types ~x0 and ~x1 are incompatible."
                       type2
                       type3))
             ((mv composite vstate)
              (vstate-make-type-composite type2 type3 vstate)))
          (retok composite vstate)))
       ((when (and (type-case type2 :pointer)
                   (type-compatible-p type2
                                      type3
                                      (vstate->completions vstate)
                                      ienv)))
        (b* (((mv composite vstate)
              (vstate-make-type-composite type2 type3 vstate)))
          (retok composite vstate)))
       ((when (and (type-case type2 :pointer)
                   (expr-null-pointer-constp
                     (expr-cond->else expr) type3 ienv)))
        (retok (type-fix type2) (vstate-fix vstate)))
       ((when (and (type-case type3 :pointer)
                   (expr-cond->then expr)
                   (expr-null-pointer-constp
                     (expr-cond->then expr) type2 ienv)))
        (retok (type-fix type3) (vstate-fix vstate)))
       ((when (and (type-case type2 :pointer)
                   (type-case type3 :pointer)
                   (let ((type-to2 (type-pointer->to type2))
                         (type-to3 (type-pointer->to type3)))
                     (or (and (type-case type-to2 :void)
                              (not (type-case type-to3 :function)))
                         (and (type-case type-to3 :void)
                              (not (type-case type-to2 :function)))))))
        (retok (make-type-pointer :to (type-void)) (vstate-fix vstate))))
    (retmsg$ "In the conditional expression ~x0, ~
              the second operand has type ~x1 ~
              and the third operand has type ~x2."
             (expr-fix expr) (type-fix type-then) (type-fix type-else))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-type-spec-list-residual ((tyspecs type-spec-listp))
  :guard (and (type-spec-list-unambp tyspecs)
              (consp tyspecs))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a residual list of type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type specifiers occur as elements of
     declaration specifiers
     (see grammar rule @('declaration-specifiers'))
     and specifier and qualifier lists
     (see grammar rule @('specifier-qualifier-list')).
     As we validate those two kinds of lists,
     when we encounter type specifiers that, like for example @('void'),
     uniquely determine a type,
     and must be the only type specifier occurring in the list,
     we perform all the necessary checks on type specifiers
     as part of validating those lists.")
   (xdoc::p
    "But when instead we encounter type specifiers that
     do not uniquely and solely determine a type,
     such as @('unsigned') and @('char'),
     we collect all of them and then we call this validation function
     to validate whether this residual sequence of type specifier
     determines a unique type or not.
     If it does not, it is an error,
     because every type specifier sub-sequence
     of a sequence of declaration specifiers
     or of a sequence of specifiers and qualifiers
     must denote a type.
     Here, `residual' refers not to the list of type specifiers,
     which are in fact all the ones occurring as sub-sequence,
     but to the fact that we perform the ``residual'' validation.")
   (xdoc::p
    "Here we accept all the lists of type specifiers in [C17:6.7.2/2]
     except for those that are singletons determining a type
     and that may not be part of longer sequences.")
   (xdoc::p
    "The GCC documentation says that @('__int128')
     can be used alone for signed,
     or accompanied by @('unsigned') for unsigned.
     But we also found it accompanied by @('signed')
     (and its underscore variations)
     in practical code,
     which seems indeed consistent with other types like @('signed int');
     so we accept all three variants.
     But for now we map all of them to the unknown type."))
  (b* (((reterr) (irr-type)))
    (cond
     ((type-spec-list-char-p tyspecs)
      (retok (type-char)))
     ((type-spec-list-signed-char-p tyspecs)
      (retok (type-schar)))
     ((type-spec-list-unsigned-char-p tyspecs)
      (retok (type-uchar)))
     ((or (type-spec-list-short-p tyspecs)
          (type-spec-list-signed-short-p tyspecs)
          (type-spec-list-short-int-p tyspecs)
          (type-spec-list-signed-short-int-p tyspecs))
      (retok (type-sshort)))
     ((or (type-spec-list-unsigned-short-p tyspecs)
          (type-spec-list-unsigned-short-int-p tyspecs))
      (retok (type-ushort)))
     ((or (type-spec-list-int-p tyspecs)
          (type-spec-list-signed-p tyspecs)
          (type-spec-list-signed-int-p tyspecs))
      (retok (type-sint)))
     ((or (type-spec-list-unsigned-p tyspecs)
          (type-spec-list-unsigned-int-p tyspecs))
      (retok (type-uint)))
     ((or (type-spec-list-long-p tyspecs)
          (type-spec-list-signed-long-p tyspecs)
          (type-spec-list-long-int-p tyspecs)
          (type-spec-list-signed-long-int-p tyspecs))
      (retok (type-slong)))
     ((or (type-spec-list-unsigned-long-p tyspecs)
          (type-spec-list-unsigned-long-int-p tyspecs))
      (retok (type-ulong)))
     ((or (type-spec-list-long-long-p tyspecs)
          (type-spec-list-signed-long-long-p tyspecs)
          (type-spec-list-long-long-int-p tyspecs)
          (type-spec-list-signed-long-long-int-p tyspecs))
      (retok (type-sllong)))
     ((or (type-spec-list-unsigned-long-long-p tyspecs)
          (type-spec-list-unsigned-long-long-int-p tyspecs))
      (retok (type-ullong)))
     ((type-spec-list-float-p tyspecs)
      (retok (type-float)))
     ((type-spec-list-double-p tyspecs)
      (retok (type-double)))
     ((type-spec-list-long-double-p tyspecs)
      (retok (type-ldouble)))
     ((type-spec-list-float-complex-p tyspecs)
      (retok (type-floatc)))
     ((type-spec-list-double-complex-p tyspecs)
      (retok (type-doublec)))
     ((type-spec-list-long-double-complex-p tyspecs)
      (retok (type-ldoublec)))
     ((type-spec-list-locase-float80-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-locase-float128-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-locase-float80-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-locase-float128-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float16-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float16x-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float32-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float32x-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float64-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float64x-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float128-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float128x-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float16-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float16x-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float32-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float32x-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float64-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float64x-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float128-complex-p tyspecs)
      (retok (type-unknown)))
     ((type-spec-list-float128x-complex-p tyspecs)
      (retok (type-unknown)))
     ((or (type-spec-list-int128-p tyspecs)
          (type-spec-list-signed-int128-p tyspecs))
      (retok (type-unknown)))
     ((type-spec-list-unsigned-int128-p tyspecs)
      (retok (type-unknown)))
     (t (retmsg$ "The type specifier sequence ~x0 is invalid."
                 (type-spec-list-fix tyspecs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stor-spec-list ((storspecs stor-spec-listp)
                              (ident identp)
                              (type typep)
                              (fundefp booleanp)
                              (vstate vstatep))
  :returns (mv (erp maybe-msgp)
               (typedefp booleanp)
               (linkage linkagep)
               (lifetime? lifetime-optionp))
  :short "Validate a list of storage class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is called on the sub-list of storage class specifiers
     of a list of declaration specifiers,
     after determining the identifier being declared and its type,
     which are both passed as input to this function,
     along with the current validator state.")
   (xdoc::p
    "Only a few sequences of storage class specifiers are allowed [C17:6.7.1/2],
     also depending on whether the declaration is in a block or file scope
     [C17:6.7.1/3],
     which we can see from the validation table.
     Each allowed sequence of storage class specifiers may determine
     that a @('typedef') name is being declared,
     or that an object or function is being declared,
     with a certain linkage and lifetime.
     So we return as results
     a flag saying that a @('typedef') name is being declared,
     a linkage,
     and an optional lifetime.
     We explain all the possibilities below,
     for each allowed sequence of storage class specifiers.")
   (xdoc::p
    "If the storage class specifier sequence is @('typedef'),
     a @('typedef') name is being declared,
     so we return @('t') as the @('typedef') flag result.
     This is the only case in which this result is @('t');
     in all other cases, that result is @('nil'),
     because in all other cases we are not declaring a @('typedef') name.
     A @('typedef') name (which is an identifier) has no linkage
     [C17:6.2.2/1] [C17:6.2.2/6].
     Since lifetime (i.e. storage duration)
     only applies to objects [C17:6.2.4/1],
     we return @('nil') as lifetime, i.e. no lifetime.")
   (xdoc::p
    "If the storage class specifier sequence is @('extern'),
     linkage may be external or not,
     based on whether there is already
     a declaration of the same identifiers in scope or not
     and whether that previous declaration specifies a linkage or not
     [C17:6.2.2/4].
     So we look up the identifier in the validation table.
     If nothing is found, then the linkage is external.
     If an object or function is found with external or internal linkage,
     then the linkage of the new declaration
     is the one of that object or function;
     the two declarations must refer to the same object or function,
     but we check elsewhere that the two declarations
     are consistent with each other.
     If an object or function is found with no linkage,
     or a @('typedef') is found (which has no linkage [C17:6.2.2/6]),
     or an enumeration constant is found (which has no linkage [C17:6.2.2/6]),
     then the linkage of the new declaration is external;
     the two declarations must refer to different entities.
     In any case, the linkage is always either internal or external.
     If the type is that of a function,
     there is no lifetime, which only applies to objects [C17:6.2.4/1].
     If the type is that of an object,
     the lifetime is static [C17:6.2.4/3],
     because as mentioned above the linkage is always internal or external.")
   (xdoc::p
    "If the storage class specifier sequence is
     @('extern _Thread_local') or @('_Thread_local extern'),
     then the type must not be that of a function [C17:6.7.1/4].
     The lifetime is thread [C17:6.2.4/4],
     while the linkage is determined as in the @('extern') case above.")
   (xdoc::p
    "If the storage class specifier sequence is @('static'),
     things differ whether the identifier is declared
     in the file scope or in a block scope.
     If we are in the file scope, the linkage is internal [C17:6.2.2/3].
     If we are in a block scope, it depends on whether
     we are declaring an object or a function.
     If it is an object, it has no linkage [C17:6.2.2/6],
     because it does not have @('extern').
     If it is a function it is an error [C17:6.7.1/7].
     The lifetime is absent (i.e. @('nil')) for a function,
     since lifetimes only apply to objects [C17:6.2.4/1];
     it is static otherwise [C17:6.2.4/3].")
   (xdoc::p
    "If the storage class specifier sequence is
     @('static _Thread_local') or @('_Thread_local static'),
     then the type must not be that of a function [C17:6.7.1/4].
     Linkage is determined as in the previous case.
     The lifetime is thread.")
   (xdoc::p
    "If the storage class specifier sequence is @('_Thread_local'),
     the type must not be one of a function [C17:6.7.1/4].
     Since we must have an object, the lifetime is thread.
     If we are in a block scope, it is an error,
     because in that case there must also be @('extern') or @('static')
     [C17:6.7.1/3].
     Since we cannot be in a block scope, we must be in the file scope.
     [C17:6.2.2] does not seem to specify the linkage for this case,
     perhaps because @('_Thread_local') was added at some point,
     but [C17:6.2.2] was not updated accordingly:
     [C17:6.2.2/5] specifies external linkage
     for the case of an object in a file scope without storage class specifiers,
     but this should be probably interpreted as
     including the @('_Thread_local') case,
     which makes sense, and is consistent with some clearer wording
     in the newly released C23 standard.")
   (xdoc::p
    "If the storage class specifier sequence is @('auto') or @('register'),
     we must not be in a file scope [C17:6.9/2];
     so we must be in a block scope.
     The type must not be one of a function.
     Thus, it has no linkage [C17:6.2.2/6].
     The lifetime is automatic [C17:6.2.4/5].")
   (xdoc::p
    "As a GCC extension, we allow the @('register') storage class specifier
     for file-scope declarations when GCC/Clang extensions are enabled
     by the implementation environment.
     This allows for the ``global register variables'' extension "
    (xdoc::ahref
     "https://gcc.gnu.org/onlinedocs/gcc/Global-Register-Variables.html"
     "[GCCM:6.11.6.1]")
    ". In this case, the linkage and lifetime are
     the same as if we had no storage class specifiers.")
   (xdoc::p
    "If there are no storage class specifiers (i.e. the sequence is empty),
     things differ based on
     whether the identifier declares an object or a function,
     and whether we are in the file scope or a block scope.
     If the type is that of a function,
     linkage is determined as if it had the @('extern') specifier [C17:6.2.2/5];
     in this case, there is no lifetime.
     For an object with file scope,
     the linkage is external [C17:6.2.2/5],
     and thus the lifetime is static [C17:6.2.4/3].
     For an object block scope, there is no linkage [C17:6.2.2/6],
     and the lifetime is automatic [C17:6.2.4/5].")
   (xdoc::p
    "We prove that if @('typedefp') is @('t')
     then @('lifetime?') is @('nil') and there is no linkage.
     We prove that if a function is being declared,
     then the linkage is always external or internal,
     and that the only possible sequences of storage class specifiers
     are @('extern'), @('static'), and nothing.
     We prove that if an object is declared in the file scope,
     then the linkage is always external or internal.")
   (xdoc::p
    "The @('fundefp') input is @('t') when this function is called on
     the storage class specifiers of a function definition.
     The reason is that, when this function is called in that situation,
     the validation table contains a block scope for the function body,
     but the storage class specifiers checked here are in the file scope:
     so checking the validation table to determine,
     for the purpose of validating the storage class specifiers,
     whether we are in a block or file scope,
     would give an incorrect result.
     So we use the @('fundefp') flag to adjust the check.
     This flag is @('nil') in all other situations."))
  (b* (((reterr) nil (irr-linkage) nil)
       (ienv (vstate->ienv vstate)))
    (cond
     ((stor-spec-list-typedef-p storspecs)
      (retok t (linkage-none) nil))
     ((stor-spec-list-extern-p storspecs)
      (b* ((linkage
            (b* (((mv info? &) (vstate-lookup-ord ident vstate))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-extern-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (linkage
            (b* (((mv info? &) (vstate-lookup-ord ident vstate))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage))))
        (retok nil linkage (lifetime-thread))))
     ((stor-spec-list-static-p storspecs)
      (b* ((block-scope-p (and (> (vstate-num-scopes vstate) 1)
                               (not fundefp)))
           ((when (and block-scope-p
                       (type-case type :function)))
            (retmsg$ "The storage class specifier 'static' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-static-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (block-scope-p (and (> (vstate-num-scopes vstate) 1)
                               (not fundefp)))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (lifetime-thread)))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           ((when (and (> (vstate-num-scopes vstate) 1)
                       (not fundefp)))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in a block scope ~
                      without 'extern' or 'static', ~
                      for the declaration of the object ~x0."
                     (ident-fix ident))))
        (retok nil (linkage-external) (lifetime-thread))))
     ((or (stor-spec-list-auto-p storspecs)
          (stor-spec-list-register-p storspecs))
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '~s0' ~
                      cannot be used in the declaration of the function ~x1."
                     (if (stor-spec-list-auto-p storspecs)
                         "auto"
                       "register")
                     (ident-fix ident)))
           ((unless (and (or (> (vstate-num-scopes vstate) 1)
                             (ienv->gcc/clang ienv))
                         (not fundefp)))
            (retmsg$ "The storage class specifier '~s0' ~
                      cannot be used in the file scope, for identifier ~x1."
                     (if (stor-spec-list-auto-p storspecs)
                         "auto"
                       "register")
                     (ident-fix ident))))
        (if (> (vstate-num-scopes vstate) 1)
            (retok nil (linkage-none) (lifetime-auto))
          (retok nil (linkage-external) (lifetime-static)))))
     ((endp storspecs)
      (if (type-case type :function)
          (b* (((mv info? &) (vstate-lookup-ord ident vstate))
               ((unless info?)
                (retok nil (linkage-external) nil))
               ((unless (valid-ord-info-case info? :objfun))
                (retok nil (linkage-external) nil))
               (previous-linkage (valid-ord-info-objfun->linkage info?)))
            (if (linkage-case previous-linkage :none)
                (retok nil (linkage-external) nil)
              (retok nil previous-linkage nil)))
        (if (and (> (vstate-num-scopes vstate) 1)
                 (not fundefp))
            (retok nil (linkage-none) (lifetime-auto))
          (retok nil (linkage-external) (lifetime-static)))))
     (t (retmsg$ "The storage class specifier sequence ~x0 is invalid."
                 (stor-spec-list-fix storspecs)))))

  ///

  (defret no-lifetime-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (not lifetime?)))

  (defret no-linkage-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (equal (linkage-kind linkage) :none)))

  (defret ext/int-linkage-of-valid-stor-spec-when-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (not (equal (linkage-kind linkage)
                         :none))))

  (defret ext/int-linkage-of-valid-stor-spec-list-when-file-object
    (implies (and (not erp)
                  (not typedefp)
                  (not (type-case type :function))
                  (equal (vstate-num-scopes vstate) 1))
             (not (equal (linkage-kind linkage)
                         :none))))

  (defret lifetime-of-valid-stor-spec-when-object
    (implies (and (not erp)
                  (not typedefp)
                  (not (type-case type :function)))
             lifetime?))

  (defret extern/static/none-when-valid-stor-spec-list-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (or (stor-spec-list-extern-p storspecs)
                 (stor-spec-list-static-p storspecs)
                 (endp storspecs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines valid-exprs/decls/stmts
  :short "Validate expressions, declarations, statements,
          and related artifacts."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since we currently have an approximate model of types,
     with the `unknown type' among them (see @(tsee type)),
     wherever a certain kind of type is required (e.g. an integer type),
     we also need to allow the unknown type,
     because that could be the required kind of type.
     Our currently approximate validator must not reject valid programs,
     because it needs to deal with any practical programs we encounter.
     Eventually, when we refine our validator and our model of types
     to no longer be approximate and include the unknown type,
     we will rescind this extra allowance for the unknown type.")
   (xdoc::p
    "Each validation function takes and returns
     an abstract syntax entity (of the appropriate kind)
     and returns a transformed one (of the same kind).
     Currently there is no change,
     but soon we will be adding information to the abstract syntax."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr ((expr exprp) (vstate vstatep))
    :guard (expr-unambp expr)
    :returns (mv (erp maybe-msgp)
                 (new-expr exprp)
                 (type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type of the expression,
       the set of types returned by @('return') statements in the expression,
       and a possibly updated validator state.
       The reason for the set of @('return') types
       is that, as a GCC extension, an expression may consist of a statement,
       and the validation of statements involves sets of @('return') types:
       see @(tsee valid-stmt).
       In case of successful validation,
       we also return a possibly enriched expression:
       the enrichment consists of a type added as
       information for identifier expression;
       that is the type of the identifier expression,
       calculated by the validator.")
     (xdoc::p
      "For now we do not distinguish lvalues [C17:6.3.2.1/1].
       To do that, we will introduce a richer notion of expression type
       that includes a type and also
       an indication of whether the expression is an lvalue;
       we will also perform lvalue conversion where needed.
       This is already done in @(see c::static-semantics),
       for the subset of C that is formalized.")
     (xdoc::p
      "We use separate functions to validate the various kinds of expressions,
       to minimize case splits in the mutually recursive clique of functions.
       But we need to calculate types for sub-expressions recursively here,
       and pass the types to those separate functions.")
     (xdoc::p
      "Expressions without subexpressions return
       the empty set of @('return') types.
       Other expressions return the union of the sets
       obtained from validating the sub-constructs.")
     (xdoc::p
      "To validate a compound literal, first we validate the type name,
       obtaining a type if that validation is successful.
       The type of the compound literal is the one denoted by the type name.
       We also retrieve
       the storage duration (i.e. lifetime) of the object,
       which is either static or automatic,
       based on whether the compound literal occurs
       outside or inside the body of a function [C17:6.5.2.5/5],
       which we can see based on whether
       the number of scopes in the validation table is 1 or not
       (recall that this number is never 0).
       We then check all the same constraints and semantic rules
       as in initializer lists occurring in an initializer
       [C17:6.5.2.5/2] [C17:6.5.2.5/6].
       See @(tsee valid-initer) for a description of those checks.")
     (xdoc::p
      "A unary @('&&') expression has type @('void *'),
       according to the GCC documentation.")
     (xdoc::p
      "In a conditional expression, the second operand may be absent;
       this is a GCC extension.
       However, for validation, we normalize the situation
       by replicating the type of the first operand for the second operand,
       when there is no second operand,
       according to the semantics of the absence of the second operand.")
     (xdoc::p
      "For the comma operator, we validate both sub-expressions,
       and the resulting type is the one of the second sub-expression
       [C17:6.5.17/2].")
     (xdoc::p
      "For a statement expression, we push a new scope for the block
       and we validate the block items. We then pop the scope.
       If a type is returned, that is the type of the expression.
       Otherwise, the expression has type @('void'),
       as described in the GCC documentation of statement expressions.")
     (xdoc::p
      "The GCC extension @('__builtin_types_compatible_p')
       is validated by validating its argument type names.
       The result is @('signed int'), according to the GCC manual.")
     (xdoc::p
      "For the GCC extension @('__builtin_offsetof'),
       for now we just validate
       its component type names and expressions (if any),
       but without checking that the member designators are valid;
       for that, we need a more refined type system.
       The result has type @('size_t') [C17:7.19],
       whose definition is implementation-dependent,
       and thus for now we return the unknown type."))
    (b* (((reterr) (irr-expr) (irr-type) nil (irr-vstate))
         (ienv (vstate->ienv vstate)))
      (expr-case
       expr
       :ident (b* (((erp type linkage uid) (valid-var expr.ident vstate))
                   (info (make-var-info :type type
                                        :linkage linkage
                                        :uid uid)))
                (retok (make-expr-ident :ident expr.ident
                                        :info info)
                       type
                       nil
                       (vstate-fix vstate)))
       :const (b* (((erp const type) (valid-const expr.const vstate))
                   (info (make-expr-const-info :type type)))
                (retok (make-expr-const :const const
                                        :info info)
                       type
                       nil
                       (vstate-fix vstate)))
       :string (b* (((erp type) (valid-stringlit-list expr.strings ienv))
                    (info (make-expr-string-info :type type)))
                 (retok (change-expr-string expr :info info)
                        type
                        nil
                        (vstate-fix vstate)))
       :paren (b* (((erp new-inner type types vstate)
                    (valid-expr expr.inner vstate)))
                (retok (expr-paren new-inner) type types vstate))
       :gensel (b* (((erp new-control type-control types-control vstate)
                     (valid-expr expr.control vstate))
                    ((erp new-assocs type-alist types-assoc vstate)
                     (valid-genassoc-list expr.assocs vstate))
                    ((erp type) (valid-gensel expr type-control type-alist)))
                 (retok (make-expr-gensel :control new-control
                                          :assocs new-assocs)
                        type
                        (set::union types-control types-assoc)
                        vstate))
       :arrsub (b* (((erp new-arg1 type-arg1 types-arg1 vstate)
                     (valid-expr expr.arg1 vstate))
                    ((erp new-arg2 type-arg2 types-arg2 vstate)
                     (valid-expr expr.arg2 vstate))
                    ((erp type) (valid-arrsub expr type-arg1 type-arg2))
                    (info (make-expr-arrsub-info :type type)))
                 (retok (make-expr-arrsub :arg1 new-arg1
                                          :arg2 new-arg2
                                          :info info)
                        type
                        (set::union types-arg1 types-arg2)
                        vstate))
       :funcall (b* (((erp new-fun type-fun types-fun vstate)
                      (valid-expr expr.fun vstate))
                     ((erp new-args types-arg rtypes-arg vstate)
                      (valid-expr-list expr.args vstate))
                     ((erp type)
                      (valid-funcall expr
                                     type-fun
                                     types-arg
                                     (vstate->completions vstate)
                                     ienv))
                     (info (make-expr-funcall-info :type type)))
                  (retok (make-expr-funcall :fun new-fun
                                            :args new-args
                                            :info info)
                         type
                         (set::union types-fun rtypes-arg)
                         vstate))
       :member (b* (((erp new-arg type-arg types-arg vstate)
                     (valid-expr expr.arg vstate))
                    ((erp type)
                     (valid-member expr
                                   type-arg
                                   (vstate->completions vstate))))
                 (retok (make-expr-member :arg new-arg :name expr.name)
                        type
                        types-arg
                        vstate))
       :memberp (b* (((erp new-arg type-arg types-arg vstate)
                      (valid-expr expr.arg vstate))
                     ((erp type)
                      (valid-memberp expr
                                     type-arg
                                     (vstate->completions vstate))))
                  (retok (make-expr-memberp :arg new-arg :name expr.name)
                         type
                         types-arg
                         vstate))
       :complit (b* (((erp new-type target-type types-type vstate)
                      (valid-tyname expr.type vstate))
                     (lifetime (if (> (vstate-num-scopes vstate) 1)
                                   (lifetime-auto)
                                 (lifetime-static))))
                  (cond
                   ((type-case target-type :unknown)
                    (b* (((erp new-elems types-desiniters vstate)
                          (valid-desiniter-list
                           expr.elems
                           (type-unknown)
                           (initer-subobjects-stack-unknown)
                           lifetime
                           vstate)))
                      (retok (make-expr-complit :type new-type
                                                :elems new-elems
                                                :final-comma expr.final-comma)
                             target-type
                             (set::union types-type types-desiniters)
                             vstate)))
                   ((type-scalarp target-type)
                    (b* (((unless (and (consp expr.elems)
                                       (endp (cdr expr.elems))))
                          (retmsg$ "The initializer list ~x0 ~
                                     for the target type ~x1 ~
                                     is not a singleton."
                                   expr.elems
                                   target-type))
                         ((desiniter desiniter) (car expr.elems))
                         ((unless (endp desiniter.designors))
                          (retmsg$ "The initializer list ~x0 ~
                                     for the target type ~x1 ~
                                     is a singleton ~
                                     but it has designators."
                                   expr.elems
                                   target-type))
                         ((unless (initer-case desiniter.initer :single))
                          (retmsg$ "The initializer list ~x0 ~
                                     for the target type ~x1 ~
                                     is a singleton without designators ~
                                     but the inner initializer ~
                                     is not a single expression."
                                   expr.elems
                                   target-type))
                         (init-expr (initer-single->expr desiniter.initer))
                         ((erp new-init-expr init-type types-init-expr vstate)
                          (valid-expr init-expr vstate))
                         ((erp)
                          (valid-simple-assignment target-type
                                                   init-type
                                                   init-expr
                                                   (vstate->completions vstate)
                                                   ienv)
                          :iferr (msg$ "The compound literal ~x0 ~
                                         for the target type ~x1 ~
                                         has type ~x2."
                                       (expr-fix expr)
                                       target-type
                                       init-type))
                         (new-complit
                          (make-expr-complit
                           :type new-type
                           :elems (list (make-desiniter
                                         :designors nil
                                         :initer (initer-single new-init-expr)))
                           :final-comma expr.final-comma)))
                      (retok new-complit
                             target-type
                             (set::union types-type types-init-expr)
                             vstate)))
                   ((and (type-case target-type :array)
                         (and (consp expr.elems)
                              (endp (rest expr.elems))
                              (endp (desiniter->designors
                                     (first expr.elems)))
                              (let ((inner-initer (desiniter->initer
                                                   (first expr.elems))))
                                (initer-case
                                 inner-initer
                                 :single (expr-case inner-initer.expr
                                                    :string)
                                 :list nil))))
                    (b* ((str-expr (initer-single->expr
                                    (desiniter->initer (first expr.elems))))
                         ((erp str-type)
                          (valid-stringlit-list
                           (expr-string->strings str-expr) ienv))
                         ((unless (and (type-compatible-p
                                        (type-array->of target-type)
                                        (type-array->of str-type)
                                        (vstate->completions vstate)
                                        ienv)
                                       ;; The element type of the str-type
                                       ;; array may be unknown, representing
                                       ;; one of the wide character types we
                                       ;; are not modeling precisely. However,
                                       ;; we know that these types must be
                                       ;; integer types.
                                       (type-integerp
                                        (type-array->of target-type))))
                          (retmsg$ "Cannot initialize type ~x0 ~
                                     with string literal ~x1 ~
                                     of type ~x2."
                                   target-type
                                   str-expr
                                   str-type))
                         (info (make-expr-string-info :type str-type))
                         (new-complit
                          (make-expr-complit
                           :type new-type
                           :elems
                           (list
                            (make-desiniter
                             :designors nil
                             :initer (initer-single
                                      (make-expr-string
                                       :strings (expr-string->strings
                                                 str-expr)
                                       :info info))))
                           :final-comma expr.final-comma)))
                      (retok new-complit
                             target-type
                             types-type
                             (vstate-fix vstate))))
                   ((or (type-aggregatep target-type)
                        (type-case target-type :union))
                    (b* (((erp subobjects-stack)
                          (initer-context-enter
                           (initer-context-top target-type)
                           (vstate->completions vstate)))
                         ((erp new-elems types-desiniters vstate)
                          ;; TODO: ... how can this possibly be failing in the
                          ;; measure conjecture?
                          ;; Is something rewriting away the obvious
                          ;; conclusion?
                          ;; We can deal with it be addressing the
                          ;; expr-count = 1 hyp.
                          (valid-desiniter-list expr.elems
                                                target-type
                                                subobjects-stack
                                                lifetime
                                                vstate)))
                      (retok (make-expr-complit
                              :type new-type
                              :elems new-elems
                              :final-comma expr.final-comma)
                             target-type
                             (set::union types-type types-desiniters)
                             vstate)))
                   (t (retmsg$ "The compound literal ~x0 ~
                                 for the target type ~x1 is disallowed."
                               (expr-fix expr)
                               (type-fix target-type)))))
       :unary (b* (((erp new-arg type-arg types-arg vstate)
                    (valid-expr expr.arg vstate))
                   ((erp type) (valid-unary expr expr.op type-arg ienv))
                   (info (make-expr-unary-info :type type)))
                (retok (make-expr-unary :op expr.op
                                        :arg new-arg
                                        :info info)
                       type
                       types-arg
                       vstate))
       :label-addr (retok (expr-label-addr expr.arg)
                          (type-pointer (type-void))
                          nil
                          (vstate-fix vstate))
       :sizeof (b* (((erp new-type type types vstate)
                     (valid-tyname expr.type vstate))
                    ((erp type1) (valid-sizeof/alignof expr type)))
                 (retok (expr-sizeof new-type) type1 types vstate))
       :alignof (b* (((erp new-type type types vstate)
                      (valid-tyname expr.type vstate))
                     ((erp type1) (valid-sizeof/alignof expr type)))
                  (retok (make-expr-alignof :type new-type
                                            :uscores expr.uscores)
                         type1
                         types
                         vstate))
       :cast (b* (((erp new-type type-cast types-cast vstate)
                   (valid-tyname expr.type vstate))
                  ((erp new-arg type-arg types-arg vstate)
                   (valid-expr expr.arg vstate))
                  ((erp type) (valid-cast expr type-cast type-arg)))
               (retok (make-expr-cast :type new-type :arg new-arg)
                      type
                      (set::union types-cast types-arg)
                      vstate))
       :binary (b* (((erp new-arg1 type-arg1 types-arg1 vstate)
                     (valid-expr expr.arg1 vstate))
                    ((erp new-arg2 type-arg2 types-arg2 vstate)
                     (valid-expr expr.arg2 vstate))
                    ((erp type)
                     (valid-binary expr
                                   expr.op
                                   type-arg1
                                   type-arg2
                                   (vstate->completions vstate)
                                   ienv))
                    (info (make-expr-binary-info :type type)))
                 (retok (make-expr-binary :op expr.op
                                          :arg1 new-arg1
                                          :arg2 new-arg2
                                          :info info)
                        type
                        (set::union types-arg1 types-arg2)
                        vstate))
       :cond (b* (((erp new-test type-test types-test vstate)
                   (valid-expr expr.test vstate))
                  ((erp new-then type-then? types-then vstate)
                   (valid-expr-option expr.then vstate))
                  (type-then (or type-then? type-test))
                  ((erp new-else type-else types-else vstate)
                   (valid-expr expr.else vstate))
                  ((erp type vstate)
                   (valid-cond expr type-test type-then type-else vstate)))
               (retok (make-expr-cond  :test new-test
                                       :then new-then
                                       :else new-else)
                      type
                      (set::union types-test (set::union types-then types-else))
                      vstate))
       :comma (b* (((erp new-first & types1 vstate)
                    (valid-expr expr.first vstate))
                   ((erp new-next type types2 vstate)
                    (valid-expr expr.next vstate)))
                (retok (make-expr-comma :first new-first :next new-next)
                       type
                       (set::union types1 types2)
                       vstate))
       :stmt (b* (((erp new-cstmt types type? vstate)
                   (valid-comp-stmt expr.stmt nil vstate))
                  (type (or type? (type-void))))
               (retok (expr-stmt new-cstmt) type types vstate))
       :tycompat (b* (((erp new-type1 & types1 vstate)
                       (valid-tyname expr.type1 vstate))
                      ((erp new-type2 & types2 vstate)
                       (valid-tyname expr.type2 vstate)))
                   (retok (make-expr-tycompat :type1 new-type1
                                              :type2 new-type2)
                          (type-sint)
                          (set::union types1 types2)
                          vstate))
       :offsetof (b* (((erp new-type & types vstate)
                       (valid-tyname expr.type vstate))
                      ((erp new-member more-types vstate)
                       (valid-member-designor expr.member vstate)))
                   (retok (make-expr-offsetof :type new-type
                                              :member new-member)
                          (type-unknown)
                          (set::union types more-types)
                          vstate))
       :va-arg (b* (((erp new-list & list-types vstate)
                     (valid-expr expr.list vstate))
                    ((erp new-type & type-types vstate)
                     (valid-tyname expr.type vstate)))
                 (retok (make-expr-va-arg :list new-list :type new-type)
                        (type-unknown)
                        (set::union list-types type-types)
                        vstate))
       :extension (b* (((erp new-expr type types vstate)
                        (valid-expr expr.expr vstate)))
                    (retok (expr-extension new-expr) type types vstate))
       :otherwise (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (expr-count expr) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-list ((exprs expr-listp) (vstate vstatep))
    :guard (expr-list-unambp exprs)
    :returns (mv (erp maybe-msgp)
                 (new-exprs expr-listp)
                 (types type-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate all the expressions, one after the other,
       and we return the resulting types, in the same order.
       We also return the union of all the @('return') types.
       We also return a possibly updated validator state."))
    (b* (((reterr) nil nil nil (irr-vstate))
         ((when (endp exprs)) (retok nil nil nil (vstate-fix vstate)))
         ((erp new-expr type return-types vstate)
          (valid-expr (car exprs) vstate))
         ((erp new-exprs types more-return-types vstate)
          (valid-expr-list (cdr exprs) vstate)))
      (retok (cons new-expr new-exprs)
             (cons type types)
             (set::union return-types more-return-types)
             vstate))
    :measure (acl2::two-nats-measure (expr-list-count exprs) 0)

    ///

    (local
     (define induct-valid-expr-list (exprs vstate)
       (b* (((reterr) nil nil nil (irr-vstate))
            ((when (endp exprs)) (retok nil nil nil (vstate-fix vstate)))
            ((erp new-expr type return-types vstate)
             (valid-expr (car exprs) vstate))
            ((erp new-exprs types more-return-types vstate)
             (induct-valid-expr-list (cdr exprs) vstate)))
         (retok (cons new-expr new-exprs)
                (cons type types)
                (set::union return-types more-return-types)
                vstate))
       :verify-guards nil
       :measure (expr-list-count exprs)))

    (defret len-of-valid-expr-list.types
      (implies (not erp)
               (equal (len types)
                      (len exprs)))
      :fn valid-expr-list
      :hints (("Goal" :induct (induct-valid-expr-list exprs vstate)
               :in-theory (enable (:i induct-valid-expr-list)
                                  len
                                  fix)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-option ((expr? expr-optionp)
                             (vstate vstatep))
    :guard (expr-option-unambp expr?)
    :returns (mv (erp maybe-msgp)
                 (new-expr? expr-optionp)
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil nil (irr-vstate)))
      (expr-option-case
       expr?
       :some (valid-expr expr?.val vstate)
       :none (retok nil nil nil (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (expr-option-count expr?) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr ((cexpr const-exprp)
                            (vstate vstatep))
    :guard (const-expr-unambp cexpr)
    :returns (mv (erp maybe-msgp)
                 (new-cexpr const-exprp)
                 (type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides being valid expressions,
       constant expression must satisfy other requirements [C17:6.6].
       Fow now we do not check these requirements,
       but when we do we may need to extend this validation function
       to return not only a type but also a value,
       namely the value of the constant expression."))
    (b* (((reterr) (irr-const-expr) (irr-type) nil (irr-vstate))
         (ienv (vstate->ienv vstate))
         ((erp new-expr type types vstate)
          (valid-expr (const-expr->expr cexpr) vstate))
         (val (const-eval-expr new-expr ienv))
         (info (make-const-expr-info :value val)))
      (retok (make-const-expr :expr new-expr :info info) type types vstate))
    :measure (acl2::two-nats-measure (const-expr-count cexpr) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr-option ((cexpr? const-expr-optionp)
                                   (vstate vstatep))
    :guard (const-expr-option-unambp cexpr?)
    :returns (mv (erp maybe-msgp)
                 (new-cexpr? const-expr-optionp)
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no constant expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil nil (irr-vstate)))
      (const-expr-option-case
       cexpr?
       :some (valid-const-expr cexpr?.val vstate)
       :none (retok nil nil nil (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (const-expr-option-count cexpr?) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc ((genassoc genassocp)
                          (vstate vstatep))
    :guard (genassoc-unambp genassoc)
    :returns (mv (erp maybe-msgp)
                 (new-genassoc genassocp)
                 (tyname-type type-optionp)
                 (expr-type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a generic association."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the generic association has a type name,
       we validate it and return the type that it denotes.
       If the generic association has @('default'),
       we return @('nil') as the @('tyname-type') result.
       Either way, we validate the expression, and return its type."))
    (b* (((reterr) (irr-genassoc) nil (irr-type) nil (irr-vstate)))
      (genassoc-case
       genassoc
       :type (b* (((erp new-type tyname-type tyname-types vstate)
                   (valid-tyname genassoc.type vstate))
                  ((erp new-expr expr-type expr-types vstate)
                   (valid-expr genassoc.expr vstate)))
               (retok (make-genassoc-type :type new-type :expr new-expr)
                      tyname-type
                      expr-type
                      (set::union tyname-types expr-types)
                      vstate))
       :default (b* (((erp new-expr expr-type expr-types vstate)
                      (valid-expr genassoc.expr vstate)))
                  (retok (genassoc-default new-expr)
                         nil
                         expr-type
                         expr-types
                         vstate))))
    :measure (acl2::two-nats-measure (genassoc-count genassoc) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc-list ((genassocs genassoc-listp)
                               (vstate vstatep))
    :guard (genassoc-list-unambp genassocs)
    :returns (mv (erp maybe-msgp)
                 (new-genassocs genassoc-listp)
                 (type-alist type-option-type-alistp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each generic association, one after the other.
       We put the calculated types (and optional types) into an alist,
       which we return.
       There may be repeated keys in the alist: it is a feature,
       so we can separately check their uniqueness."))
    (b* (((reterr) nil nil nil (irr-vstate))
         ((when (endp genassocs)) (retok nil nil nil (vstate-fix vstate)))
         ((erp new-genassoc tyname-type? expr-type types vstate)
          (valid-genassoc (car genassocs) vstate))
         ((erp new-genassocs type-alist more-types vstate)
          (valid-genassoc-list (cdr genassocs) vstate)))
      (retok (cons new-genassoc new-genassocs)
             (acons tyname-type? expr-type type-alist)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (genassoc-list-count genassocs) 0)

    ///

    (defret alistp-of-valid-genassoc-list.type-alist
      (alistp type-alist)
      :hints
      (("Goal" :in-theory (e/d (alistp-when-type-option-type-alistp-rewrite)
                               (return-type-of-valid-genassoc-list.type-alist))
        :use return-type-of-valid-genassoc-list.type-alist))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-member-designor ((memdesign member-designorp)
                                 (vstate vstatep))
    :guard (member-designor-unambp memdesign)
    :returns (mv (erp maybe-msgp)
                 (new-memdesign member-designorp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a member designator."
    (b* (((reterr) (irr-member-designor) nil (irr-vstate)))
      (member-designor-case
       memdesign
       :ident (retok (member-designor-fix memdesign)
                     nil
                     (vstate-fix vstate))
       :dot (b* (((erp new-member types vstate)
                  (valid-member-designor memdesign.member vstate)))
              (retok (make-member-designor-dot :member new-member
                                               :name memdesign.name)
                     types
                     vstate))
       :sub (b* (((erp new-member types vstate)
                  (valid-member-designor memdesign.member vstate))
                 ((erp new-expr & more-types vstate)
                  (valid-expr memdesign.index vstate)))
              (retok (make-member-designor-sub :member new-member
                                               :index new-expr)
                     (set::union types more-types)
                     vstate))))
    :measure (acl2::two-nats-measure (member-designor-count memdesign) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-type-spec ((tyspec type-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (vstate vstatep))
    :guard (and (type-spec-unambp tyspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-tyspec type-specp)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "Type specifiers are used to specify types, as described in [C17:6.7.2/2].
       Certain type specifiers individually specify a type,
       and there cannot be other type specifiers;
       an example is @('void').
       Other type specifiers may individually specify a type,
       but they may be also combined with other type specifiers
       to specify a different type;
       an example is @('signed').
       The type specifier @('_Complex') does not individually specify any type,
       and must be always combined with other type specifiers.")
     (xdoc::p
      "Given these possibilities,
       our approach is to validate type specifiers in order,
       while going through the declaration specifiers,
       or the specifier and qualifier lists,
       where they occur.
       As we go through them, we thread through two pieces of information:
       an optional type,
       non-@('nil') when a type has been definitely determined,
       and a list of type specifiers encountered so far.
       These two cannot be non-@('nil') at the same time, as the guard requires:
       if a type has been determined,
       there is no need to keep track of the type specifiers so far;
       and if we are keeping track of the type specifiers so far,
       we must not have determined a type yet.")
     (xdoc::p
      "Initially,
       the optional type and the list of type specifiers are both @('nil'),
       because we neither have encountered any type specifiers
       nor determined a type.
       If we encounter a type specifier like @('void')
       that individually denotes a type,
       we ensure that no other type specifiers were encountered before,
       and we determine the type.
       Once a type is determined, any type specifier will cause an error.
       We may get at the end without a determined type yet,
       but we will have the list of all the type specifiers,
       which is used, in another validation function,
       to determined the type if any.")
     (xdoc::p
      "Our current type system does not model atomic types,
       so for an atomic type we validate the type name
       and we regard the atomic type as denoting the same type.")
     (xdoc::p
      "For a structure or union or enumeration type specifier,
       we recursively validate their sub-structures,
       and the type is determined in all cases.
       A struct or union type specifier with a structure declaration list
       declares a new type [C17:6.7.2.1/8].
       If the tag has already been used
       to declare a complete type in the current scope,
       this is a validation error [C17:6.7.2.3/1].
       If the tag has been used
       to declare an incomplete type in the current scope,
       the type must be of the same kind [C17:6.7.2.3/2].
       Otherwise, the new struct or union type
       is added to the current scope and completions map,
       and this new type is the type of the type specifier.
       If the struct or union type specifier
       does not have a structure declaration list,
       the tag is looked up in the tag name space.
       If the tag is in scope and has the expected tag kind,
       the type described by the tag is the type of the type specifier
       [C17:6.7.2.3/9].
       If the tag is in scope and has the wrong tag kind,
       it is a validation error
       [C17:6.7.2.3/2,9].
       Otherwise, the tag is not in scope,
       and the type specifier declares a new incomplete type [C17:6.7.2.3/8].
       We add the incomplete type declaration to the current scope,
       but we do not add an entry to the completions map.
       A structure or union type specifier must have either
       a tag or a structure declaration list [C17:6.7.2.3/1].
       Enumeration types are not yet tracked in the validation table.
       Their type is the singular enumeration type.")
     (xdoc::p
      "For @('typedef') names,
       we look up the type definition in the validation table.
       If no such entry exists in the table, validation fails.
       Otherwise, we return the type in the table entry
       as the one denoted by the @('typedef') name.
       The latter is an important point, because it means that
       we always fully expand @('typedef') names
       to their @('typedef')-name-free types
       (recall that @(tsee type) has no case for @('typedef') names).
       In a translation unit, no forward references are allowed,
       so the first @('typedef') (if any) cannot refer to others;
       later @('typedef')s may refer to previous ones,
       but since we expand their definientia through this table lookup,
       we effectively always recursively expand all @('typedef')s.
       This may be exactly what is needed for validation,
       but we will revisit this choice if needed.")
     (xdoc::p
      "For now, for simplicity, we regard
       all the type specifiers that are GCC extensions
       to determine the unknown type;
       except for an empty structure type specifier,
       which determines the structure type.
       The @('__int128') may be preceded by @('unsigned'),
       according to the GCC documentation;
       we found, in practical code,
       that it can also be preceded by @('signed') and its underscore variants;
       so @('__int128') alone does not determine a type,
       and we use @(tsee valid-type-spec-list-residual)
       to determine the type, if any, as done in other cases."))
    (b* (((reterr) (irr-type-spec) nil nil nil (irr-vstate))
         ((when type?)
          (retmsg$ "Since the type ~x0 has been determined, ~
                    there must be no more type specifiers, ~
                    but ~x1 follows instead."
                   (type-option-fix type?) (type-spec-fix tyspec)))
         (same-vstate (vstate-fix vstate))
         (ext-tyspecs (rcons (type-spec-fix tyspec)
                             (type-spec-list-fix tyspecs)))
         (msg-bad-preceding (msg$ "The type specifier ~x0 ~
                                   must not be preceded by ~x1."
                                  (type-spec-fix tyspec)
                                  (type-spec-list-fix tyspecs))))
      (type-spec-case
       tyspec
       :void (if (endp tyspecs)
                 (retok (type-spec-void)
                        (type-void)
                        nil
                        nil
                        same-vstate)
               (reterr msg-bad-preceding))
       :char (retok (type-spec-char) nil ext-tyspecs nil same-vstate)
       :short (retok (type-spec-short) nil ext-tyspecs nil same-vstate)
       :int (retok (type-spec-int) nil ext-tyspecs nil same-vstate)
       :long (retok (type-spec-long) nil ext-tyspecs nil same-vstate)
       :float (retok (type-spec-float) nil ext-tyspecs nil same-vstate)
       :double (retok (type-spec-double) nil ext-tyspecs nil same-vstate)
       :signed (retok (type-spec-signed tyspec.uscores)
                      nil
                      ext-tyspecs
                      nil
                      same-vstate)
       :unsigned (retok (type-spec-unsigned) nil ext-tyspecs nil same-vstate)
       :bool (if (endp tyspecs)
                 (retok (type-spec-bool) (type-bool) nil nil same-vstate)
               (reterr msg-bad-preceding))
       :complex (retok (type-spec-complex) nil ext-tyspecs nil same-vstate)
       :atomic (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((erp new-type type types vstate)
                     (valid-tyname tyspec.type vstate)))
                 (retok (type-spec-atomic new-type) type nil types vstate))
       :struct (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((struni-spec tyspec.spec) tyspec.spec)
                    ((when (endp tyspec.spec.members))
                     (b* (((unless tyspec.spec.name?)
                           (retmsg$ "Struct type specifier ~x0 has neither ~
                                     a tag nor a structure declaration list."
                                    (type-spec-fix tyspec)))
                          ((erp new-spec - types vstate)
                           (valid-struni-spec tyspec.spec vstate))
                          ((mv info? -)
                           (vstate-lookup-tag tyspec.spec.name? vstate))
                          ((when info?)
                           (if (equal (valid-tag-info->kind info?)
                                      (tag-kind-struct))
                               (retok (type-spec-struct new-spec)
                                      (make-type-struct
                                       :uid (valid-tag-info->uid info?)
                                       :tunit? (vstate->filepath vstate)
                                       :tag/members
                                       (type-struni-tag/members-tagged
                                        tyspec.spec.name?))
                                      nil
                                      types
                                      vstate)
                             (retmsg$ "The tag is expected ~
                                       to be of kind 'union', ~
                                       but it is of kind 'struct'. ~
                                       This occurred ~
                                       in the type specifier ~x1."
                                      tyspec.spec.name?
                                      (type-spec-fix tyspec))))
                          (uid (vstate->next-uid vstate))
                          (vstate (change-vstate
                                    vstate
                                    :next-uid (uid-increment uid)))
                          (vstate (vstate-add-tag tyspec.spec.name?
                                                  (make-valid-tag-info
                                                   :kind (tag-kind-struct)
                                                   :uid uid)
                                                  vstate)))
                       (retok (type-spec-struct new-spec)
                              (make-type-struct
                               :uid uid
                               :tunit? (vstate->filepath vstate)
                               :tag/members (type-struni-tag/members-tagged
                                             tyspec.spec.name?))
                              nil
                              types
                              vstate)))
                    ((mv current-uid? current+completep)
                     (b* (((unless tyspec.spec.name?)
                           (mv nil nil))
                          ((mv info? currentp)
                           (vstate-lookup-tag tyspec.spec.name? vstate))
                          ((unless (and info? currentp))
                           (mv nil nil))
                          (uid (valid-tag-info->uid info?))
                          (members? (hons-get (valid-tag-info->uid info?)
                                              (vstate->completions vstate))))
                       (mv uid (consp members?))))
                    ((when current+completep)
                     (retmsg$ "A type is already defined in this scope ~
                               with tag ~x0. ~
                               This occurred in the type specifier ~x1."
                              tyspec.spec.name?
                              (type-spec-fix tyspec)))
                    ((mv uid vstate)
                     (b* (((when current-uid?)
                           (mv current-uid? vstate))
                          (uid (vstate->next-uid vstate))
                          (vstate (change-vstate
                                    vstate
                                    :next-uid (uid-increment uid))))
                       (mv uid
                           (if tyspec.spec.name?
                               (vstate-add-tag tyspec.spec.name?
                                               (make-valid-tag-info
                                                :kind (tag-kind-struct)
                                                :uid uid)
                                               vstate)
                             vstate))))
                    ((erp new-spec type-struni-members types vstate)
                     (valid-struni-spec tyspec.spec vstate))
                    (type (make-type-struct
                           :uid uid
                           :tunit? (vstate->filepath vstate)
                           :tag/members (if tyspec.spec.name?
                                            (type-struni-tag/members-tagged
                                             tyspec.spec.name?)
                                          (type-struni-tag/members-untagged
                                           type-struni-members))))
                    (vstate (change-vstate
                              vstate
                              :completions (hons-acons
                                             uid
                                             type-struni-members
                                             (vstate->completions vstate)))))
                 (retok (type-spec-struct new-spec)
                        type
                        nil
                        types
                        vstate))
       :union (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                   ((struni-spec tyspec.spec) tyspec.spec)
                   ((when (endp tyspec.spec.members))
                    (b* (((unless tyspec.spec.name?)
                          (retmsg$ "Union type specifier ~x0 has neither ~
                                    a tag nor a structure declaration list."
                                   (type-spec-fix tyspec)))
                         ((erp new-spec - types vstate)
                          (valid-struni-spec tyspec.spec vstate))
                         ((mv info? -)
                          (vstate-lookup-tag tyspec.spec.name? vstate))
                         ((when info?)
                          (if (equal (valid-tag-info->kind info?)
                                     (tag-kind-union))
                              (retok (type-spec-union new-spec)
                                     (make-type-union
                                      :uid (valid-tag-info->uid info?)
                                      :tunit? (vstate->filepath vstate)
                                      :tag/members
                                      (type-struni-tag/members-tagged
                                       tyspec.spec.name?))
                                     nil
                                     types
                                     vstate)
                            (retmsg$ "The tag is expected ~
                                      to be of kind 'struct', ~
                                      but it is of kind 'union'. ~
                                      This occurred in the type specifier ~x1."
                                     tyspec.spec.name?
                                     (type-spec-fix tyspec))))
                         (uid (vstate->next-uid vstate))
                         (vstate (change-vstate
                                   vstate
                                   :next-uid (uid-increment uid)))
                         (vstate (vstate-add-tag tyspec.spec.name?
                                                 (make-valid-tag-info
                                                  :kind (tag-kind-union)
                                                  :uid uid)
                                                 vstate)))
                      (retok (type-spec-union new-spec)
                             (make-type-union
                              :uid uid
                              :tunit? (vstate->filepath vstate)
                              :tag/members (type-struni-tag/members-tagged
                                            tyspec.spec.name?))
                             nil
                             types
                             vstate)))
                   ((mv current-uid? current+completep)
                    (b* (((unless tyspec.spec.name?)
                          (mv nil nil))
                         ((mv info? currentp)
                          (vstate-lookup-tag tyspec.spec.name? vstate))
                         ((unless (and info? currentp))
                          (mv nil nil))
                         (uid (valid-tag-info->uid info?))
                         (members? (hons-get (valid-tag-info->uid info?)
                                             (vstate->completions vstate))))
                      (mv uid (consp members?))))
                   ((when current+completep)
                    (retmsg$ "A type is already defined in this scope ~
                              with tag ~x0. ~
                              This occurred in the type specifier ~x1."
                             tyspec.spec.name?
                             (type-spec-fix tyspec)))
                   ((mv uid vstate)
                    (b* (((when current-uid?)
                          (mv current-uid? vstate))
                         (uid (vstate->next-uid vstate))
                         (vstate (change-vstate
                                   vstate
                                   :next-uid (uid-increment uid))))
                      (mv uid
                          (if tyspec.spec.name?
                              (vstate-add-tag tyspec.spec.name?
                                              (make-valid-tag-info
                                               :kind (tag-kind-union)
                                               :uid uid)
                                              vstate)
                            vstate))))
                   ((erp new-spec type-struni-members types vstate)
                    (valid-struni-spec tyspec.spec vstate))
                   (type (make-type-union
                          :uid uid
                          :tunit? (vstate->filepath vstate)
                          :tag/members (if tyspec.spec.name?
                                           (type-struni-tag/members-tagged
                                            tyspec.spec.name?)
                                         (type-struni-tag/members-untagged
                                          type-struni-members))))
                   (vstate (change-vstate
                              vstate
                              :completions (hons-acons
                                             uid
                                             type-struni-members
                                             (vstate->completions vstate)))))
                (retok (type-spec-union new-spec)
                       type
                       nil
                       types
                       vstate))
       :enum (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                  ((erp new-spec types vstate)
                   (valid-enum-spec tyspec.spec vstate)))
               (retok (type-spec-enum new-spec) (type-enum) nil types vstate))
       :typedef (b* (((unless (endp tyspecs))
                      (reterr msg-bad-preceding))
                     ((mv info? -)
                      (vstate-lookup-ord tyspec.name vstate))
                     ((unless info?)
                      (retmsg$ "The identifier ~x0 is not an in-scope ~
                                ordinary identifier."
                               (ident->unwrap tyspec.name))))
                  (valid-ord-info-case
                   info?
                   :typedef (retok (type-spec-typedef tyspec.name)
                                   info?.def
                                   nil
                                   nil
                                   same-vstate)
                   :otherwise (retmsg$ "The identifier ~x0 does not ~
                                        represent a typedef.")))
       :int128 (retok (make-type-spec-int128 :uscoret tyspec.uscoret)
                      nil
                      ext-tyspecs
                      nil
                      same-vstate)
       :locase-float80 (retok (type-spec-locase-float80)
                              nil ext-tyspecs nil same-vstate)
       :locase-float128 (retok (type-spec-locase-float128)
                               nil ext-tyspecs nil same-vstate)
       :float16 (retok (type-spec-float16) nil ext-tyspecs nil same-vstate)
       :float16x (retok (type-spec-float16x) nil ext-tyspecs nil same-vstate)
       :float32 (retok (type-spec-float32) nil ext-tyspecs nil same-vstate)
       :float32x (retok (type-spec-float32x) nil ext-tyspecs nil same-vstate)
       :float64 (retok (type-spec-float64) nil ext-tyspecs nil same-vstate)
       :float64x (retok (type-spec-float64x) nil ext-tyspecs nil same-vstate)
       :float128 (retok (type-spec-float128) nil ext-tyspecs nil same-vstate)
       :float128x (retok (type-spec-float128x) nil ext-tyspecs nil same-vstate)
       :builtin-va-list (if (endp tyspecs)
                            (retok (type-spec-builtin-va-list)
                                   (type-unknown)
                                   nil
                                   nil
                                   same-vstate)
                          (reterr msg-bad-preceding))
       :struct-empty (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                          ((mv current-uid? current+completep)
                           (b* (((unless tyspec.name?)
                                 (mv nil nil))
                                ((mv info? currentp)
                                 (vstate-lookup-tag tyspec.name? vstate))
                                ((unless (and info? currentp))
                                 (mv nil nil))
                                (uid (valid-tag-info->uid info?))
                                (members?
                                 (hons-get (valid-tag-info->uid info?)
                                           (vstate->completions vstate))))
                             (mv uid (consp members?))))
                          ((when current+completep)
                           (retmsg$ "A type is already defined in this scope ~
                                     with tag ~x0.
                                     This occurred in the type specifier ~x1."
                                    tyspec.name?
                                    (type-spec-fix tyspec)))
                          ((mv uid vstate)
                           (b* (((when current-uid?)
                                 (mv current-uid? vstate))
                                (uid (vstate->next-uid vstate))
                                (vstate (change-vstate
                                          vstate
                                          :next-uid (uid-increment uid))))
                             (mv uid
                                 (if tyspec.name?
                                     (vstate-add-tag tyspec.name?
                                                     (make-valid-tag-info
                                                      :kind (tag-kind-struct)
                                                      :uid uid)
                                                     vstate)
                                   vstate))))
                          (type (make-type-struct
                                 :uid uid
                                 :tunit? (vstate->filepath vstate)
                                 :tag/members
                                 (if tyspec.name?
                                     (type-struni-tag/members-tagged
                                      tyspec.name?)
                                   (type-struni-tag/members-untagged
                                    nil))))
                          (vstate
                            (change-vstate
                              vstate
                              :completions (hons-acons
                                             uid
                                             nil
                                             (vstate->completions vstate)))))
                       (retok (make-type-spec-struct-empty
                               :attribs tyspec.attribs
                               :name? tyspec.name?)
                              type
                              nil
                              nil
                              vstate))
       :typeof-expr (if (endp tyspecs)
                        (retok (type-spec-fix tyspec)
                               (type-unknown)
                               nil
                               nil
                               same-vstate)
                      (reterr msg-bad-preceding))
       :typeof-type (if (endp tyspecs)
                        (retok (type-spec-fix tyspec)
                               (type-unknown)
                               nil
                               nil
                               same-vstate)
                      (reterr msg-bad-preceding))
       :auto-type (if (endp tyspecs)
                      (retok (type-spec-fix tyspec)
                             (type-unknown)
                             nil
                             nil
                             same-vstate)
                    (reterr msg-bad-preceding))
       :otherwise (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (type-spec-count tyspec) 0)

    ///

    (defret type-spec-list-unambp-of-valid-type-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-type-spec tyspec type? tyspecs vstate))))

    (defret not-type-and-type-specs-of-valid-type-spec
      (not (and new-type? new-tyspecs))
      :hints
      (("Goal"
        :expand (valid-type-spec tyspec type? tyspecs vstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual ((specqual spec/qual-p)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (vstate vstatep))
    :guard (and (spec/qual-unambp specqual)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-specqual spec/qual-p)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a specifier or qualifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore type qualifiers [C17:6.7.3],
       as they do not have any impact on our approximate type system.
       We validate alignment specifiers (in a separate validation function),
       but make no use of them in our approximate type system.
       Thus, the validation of a specifier or qualifier
       returns the same results as
       the validation of a type specifier (see @(tsee valid-type-spec)).
       For now we also skip over attributes completely;
       see the ABNF grammar for @('specifier-qualifier-list')."))
    (b* (((reterr) (irr-spec/qual) nil nil nil (irr-vstate)))
      (spec/qual-case
       specqual
       :typespec (b* (((erp new-spec type? tyspecs types vstate)
                       (valid-type-spec
                        specqual.spec type? tyspecs vstate)))
                   (retok (spec/qual-typespec new-spec)
                          type?
                          tyspecs
                          types
                          vstate))
       :typequal (retok (spec/qual-typequal specqual.qual)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        nil
                        (vstate-fix vstate))
       :align (b* (((erp new-spec types vstate)
                    (valid-align-spec specqual.spec vstate)))
                (retok (spec/qual-align new-spec)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       types
                       vstate))
       :attrib (retok (spec/qual-attrib specqual.spec)
                      (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      nil
                      (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (spec/qual-count specqual) 0)

    ///

    (defret type-spec-list-unambp-of-valid-spec/qual
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-spec/qual specqual type? tyspecs vstate))))

    (defret not-type-and-type-specs-of-valid-spec/qual
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-spec/qual specqual nil tyspecs vstate)
                 (valid-spec/qual specqual type? nil vstate)))))

    (defret not-type-specs-of-valid-spec/qual-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-spec/qual))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual-list ((specquals spec/qual-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (vstate vstatep))
    :guard (and (spec/qual-list-unambp specquals)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-specquals spec/qual-listp)
                 (type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of specifiers and qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type determined by
       the type specifiers in the sequence.")
     (xdoc::p
      "We validate specifiers and qualifiers from left to right,
       threading the partial results through.
       When we reach the end, if the type has not been determined yet,
       we look at the collected type specifiers and determine the type,
       via a separate validation function.
       If there are no type specifiers, but no type has been determined,
       it means that there were no type specifiers at all [C17:6.7.2/2]."))
    (b* (((reterr) nil (irr-type) nil (irr-vstate))
         ((when (endp specquals))
          (cond
           (type?
            (retok nil (type-option-fix type?) nil (vstate-fix vstate)))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok nil type nil (vstate-fix vstate))))
           (t (retmsg$ "The specifier and qualifier list ~x0 ~
                        contains no type specifiers."
                       (spec/qual-list-fix specquals)))))
         ((erp new-specqual type? tyspecs types vstate)
          (valid-spec/qual (car specquals) type? tyspecs vstate))
         ((erp new-specquals type more-types vstate)
          (valid-spec/qual-list (cdr specquals) type? tyspecs vstate)))
      (retok (cons new-specqual new-specquals)
             type
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (spec/qual-list-count specquals) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-align-spec ((align align-specp)
                            (vstate vstatep))
    :guard (align-spec-unambp align)
    :returns (mv (erp maybe-msgp)
                 (new-align align-specp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an alignment specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we just validate the type name or expression,
       possibly extending the validation table,
       but we do not check whether the alignment specifier
       is appropriate for the place where it occurs [C17:6.7.5].")
     (xdoc::p
      "In the version with the expression,
       the latter must have integer type [C17:6.7.5/3].
       The version with the type name
       is equivalent to @('_Alignas(_Alignof(typename))'),
       and thus we perform the same checks as in
       the @(':alignof') case of @(tsee valid-expr),
       including @(tsee valid-sizeof/alignof)."))
    (b* (((reterr) (irr-align-spec) nil (irr-vstate)))
      (align-spec-case
       align
       :alignas-type
       (b* (((erp new-type type types vstate)
             (valid-tyname align.type vstate))
            ((when (type-case type :function))
             (retmsg$ "In the alignment specifier ~x0, ~
                       the argument ~x2 is a function type."
                      (align-spec-fix align) type)))
         (retok (align-spec-alignas-type new-type) types vstate))
       :alignas-expr
       (b* (((erp new-expr type types vstate)
             (valid-const-expr align.expr vstate))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (retmsg$ "In the alignment specifier ~x0, ~
                       the argument has type ~x1."
                      (align-spec-fix align) type)))
         (retok (align-spec-alignas-expr new-expr) types vstate))
       :alignas-ambig (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (align-spec-count align) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec ((declspec decl-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (storspecs stor-spec-listp)
                           (vstate vstatep))
    :guard (and (decl-spec-unambp declspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-declspec decl-specp)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (new-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore
       type qualifiers,
       function specifiers,
       and attributes.
       We validate alignment specifiers but we do not make any use of them
       in our currently approximate type system.
       We handle type specifiers similarly to @(tsee valid-spec/qual).
       In addition, we collect all the storage class specifiers
       encountered as we go through the declaration specifiers."))
    (b* (((reterr) (irr-decl-spec) nil nil nil nil (irr-vstate)))
      (decl-spec-case
       declspec
       :stoclass (retok (decl-spec-stoclass declspec.spec)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (rcons declspec.spec (stor-spec-list-fix storspecs))
                        nil
                        (vstate-fix vstate))
       :typespec (b* (((erp new-spec type? tyspecs types vstate)
                       (valid-type-spec
                        declspec.spec type? tyspecs vstate)))
                   (retok (decl-spec-typespec new-spec)
                          type?
                          tyspecs
                          (stor-spec-list-fix storspecs)
                          types
                          vstate))
       :typequal (retok (decl-spec-typequal declspec.qual)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (vstate-fix vstate))
       :function (retok (decl-spec-function declspec.spec)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (vstate-fix vstate))
       :align (b* (((erp new-spec types vstate)
                    (valid-align-spec declspec.spec vstate)))
                (retok (decl-spec-align new-spec)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       types
                       vstate))
       :attrib (retok (decl-spec-attrib declspec.spec)
                      (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      (stor-spec-list-fix storspecs)
                      nil
                      (vstate-fix vstate))
       :stdcall (retok (decl-spec-stdcall)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       nil
                       (vstate-fix vstate))
       :declspec (retok (decl-spec-declspec declspec.arg)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (decl-spec-count declspec) 0)

    ///

    (defret type-spec-list-unambp-of-valid-decl-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal"
        :expand (valid-decl-spec declspec type? tyspecs storspecs vstate))))

    (defret not-type-and-type-specs-of-valid-decl-spec
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-decl-spec declspec nil tyspecs storspecs vstate)
                 (valid-decl-spec declspec type? nil storspecs vstate)))))

    (defret not-type-specs-of-valid-decl-spec-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-decl-spec)))

    (defret valid-decl-spec.new-storspecs-type-prescription
      (true-listp new-storspecs)
      :rule-classes :type-prescription
      :hints
      (("Goal"
        :expand (valid-decl-spec declspec type? tyspecs storspecs vstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec-list ((declspecs decl-spec-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (storspecs stor-spec-listp)
                                (vstate vstatep))
    :guard (and (decl-spec-list-unambp declspecs)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-declspecs decl-spec-listp)
                 (type typep)
                 (all-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return
       the type determined by the type specifiers,
       and the list of storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We go through each element of the list,
       threading the partial results through.
       When we reach the end of the list,
       if a type has been determined, we return it.
       Otherwise, we use a separate function to attempt to determine it
       from the collected type specifiers."))
    (b* (((reterr) nil (irr-type) nil nil (irr-vstate))
         ((when (endp declspecs))
          (cond
           (type? (retok nil
                         (type-option-fix type?)
                         (stor-spec-list-fix storspecs)
                         nil
                         (vstate-fix vstate)))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok nil
                     type
                     (stor-spec-list-fix storspecs)
                     nil
                     (vstate-fix vstate))))
           (t (retmsg$ "The declaration specifiers ~x0 ~
                        contain no type specifiers."
                       (decl-spec-list-fix declspecs)))))
         ((erp new-declspec type? tyspecs storspecs types vstate)
          (valid-decl-spec (car declspecs) type? tyspecs storspecs vstate))
         ((erp new-declspecs type storspecs more-types vstate)
          (valid-decl-spec-list
           (cdr declspecs) type? tyspecs storspecs vstate)))
      (retok (cons new-declspec new-declspecs)
             type
             storspecs
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (decl-spec-list-count declspecs) 0)

    ///

    (defret valid-decl-spec-list.all-storspecs-type-prescription
      (true-listp all-storspecs)
      :rule-classes :type-prescription
      :hints
      (("Goal"
        :in-theory (disable return-type-of-valid-decl-spec-list.all-storspecs)
        :use return-type-of-valid-decl-spec-list.all-storspecs))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer ((initer initerp)
                        (ctx initer-context-p)
                        (lifetime lifetimep)
                        (vstate vstatep)
                        (steps natp))
    :guard (initer-unambp initer)
    :returns (mv (erp maybe-msgp)
                 (new-initer initerp)
                 (new-ctx initer-context-p)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "The initializer context passed as input provides
       the necessary type and position information to validate the initializer.
       It either indicates that we are at the outermost initializer,
       in which case we have just the target type of the initializer,
       or we are at some nested initializer,
       in which case we have a stack of subobject frames.
       In this case, the target type is
       the type of the ``current'' subobject.")
     (xdoc::p
      "The lifetime kind passed as input is
       the one of the object being initialized.")
     (xdoc::p
      "If the target type is unknown, no constraints are checked.
       If the initializer consists of an initialization list,
       the list is validated under an unknown initializer context.")
     (xdoc::p
      "If the target type is a scalar,
       the initializer must be either a single expression,
       or a singleton initializer list without designators
       [C17:6.7.9/11].
       The latter is an expression enclosed in braces;
       experiments show that the final comma is allowed.
       The same constraints as in assignments apply here
       [C17:6.7.9/11] [C17:6.5.16.1/1]:
       see @(tsee valid-simple-assignment)
       for how we currently approximate the checks.")
     (xdoc::p
      "We then check a number of cases, each of which is permitted to fail.")
     (xdoc::ul
      (xdoc::li
       "If the initializer is a single string literal expression
        and the target type is an array, we validate the string literal.
        If the string literal is
        a character string literal or a UTF-8 string literal,
        the element type of the target array type must be a character type
        [C17:6.7.9/14].
        Otherwise, the string literal is a wide string literal
        and the element type of the target array type must be compatible
        [C17:6.7.9/15].")
      (xdoc::li
       "If the initializer is a singleton list without designators,
        the same rules as above apply [C17:6.7.9/14] [C17:6.7.9/15].
        However, we also check whether
        the string literal element type is unknown.
        In this case, the compatibilty check is not sufficient
        to establish that this is the proper case
        (it could be that the target array element type is actually
        an aggregate, and we should instead recurse).
        Therefore, if the element type is unknown,
        we proceed with the unknown initializer context
        to reflect this uncertainty.")
      (xdoc::li
       "If the target type is either a structure or union
        with automatic storage duration
        and the initializer is a single expression,
        the expression may be any compatible structure or union
        [C17:6.7.9/13]."))
     (xdoc::p
      "If any of the listed cases fails
       and the target type is an aggregate or union,
       we expand the subobjects at the head of the stack
       and recurse [C17:6.7.9/20].
       This recursion is always expected to terminate, but for the moment,
       we explicitly limit recursion with a step counter.
       The reason the recursion should terminate regardless
       is that the size of the type corresponding to the initializer context
       decreases at every call.
       When we expand subobjects at the head of the stack,
       the new type becomes an immediate sub-type of the old type
       (a member of the structure or union, or an element of the array).
       To prove this, we would need to know that the @(tsee type-completions)
       from the validation table is ``well-formed'',
       in that there are no circular structures or unions."))
    (b* (((reterr) (irr-initer) (irr-initer-context) nil (irr-vstate))
         (ienv (vstate->ienv vstate))
         (steps (lnfix steps))
         ((when (= (the unsigned-byte steps) 0))
          (retmsg$ "Ran out of steps in valid-initer."))
         ((when (initer-context-end-p ctx))
          (retmsg$ "Too many initializers. Unexpected initializer: ~x0"
                   (irr-initer)))
         (target-type (initer-context->type ctx))
         ((when (type-case target-type :unknown))
          (initer-case
           initer
           :single (b* (((erp new-expr & types vstate)
                         (valid-expr initer.expr vstate)))
                     (retok (initer-single new-expr)
                            (initer-context-unknown)
                            types
                            vstate))
           :list (b* (((erp new-elems types vstate)
                       (valid-desiniter-list initer.elems
                                             (type-unknown)
                                             (initer-subobjects-stack-unknown)
                                             lifetime
                                             vstate)))
                   (retok (make-initer-list :elems new-elems
                                            :final-comma initer.final-comma)
                          (initer-context-unknown)
                          types
                          vstate))))
         ((when (type-scalarp target-type))
          (b* (((erp expr)
                (b* (((reterr) (irr-expr)))
                  (initer-case
                   initer
                   :single (retok initer.expr)
                   :list (b* (((unless (and (consp initer.elems)
                                            (endp (cdr initer.elems))))
                               (retmsg$ "The initializer list ~x0 ~
                                          for the target type ~x1 ~
                                          is not a singleton."
                                        (initer-fix initer)
                                        (type-fix target-type)))
                              ((desiniter desiniter) (car initer.elems))
                              ((unless (endp desiniter.designors))
                               (retmsg$ "The initializer list ~x0 ~
                                          for the target type ~x1 ~
                                          is a singleton ~
                                          but it has designators."
                                        (initer-fix initer)
                                        (type-fix target-type)))
                              ((unless (initer-case desiniter.initer :single))
                               (retmsg$ "The initializer list ~x0 ~
                                          for the target type ~x1 ~
                                          is a singleton without designators ~
                                          but the inner initializer ~
                                          is not a single expression."
                                        (initer-fix initer)
                                        (type-fix target-type))))
                           (retok (initer-single->expr desiniter.initer))))))
               ((erp new-expr init-type types vstate)
                (valid-expr expr vstate))
               ((erp)
                (valid-simple-assignment
                 target-type init-type expr (vstate->completions vstate) ienv)
                :iferr (msg$ "The initializer ~x0 for the target type ~x1 ~
                              has type ~x2."
                             (initer-fix initer)
                             (type-fix target-type)
                             init-type))
               (new-initer
                (initer-case
                 initer
                 :single (initer-single new-expr)
                 :list (make-initer-list
                        :elems (list (make-desiniter
                                      :designors nil
                                      :initer (initer-single new-expr)))
                        :final-comma initer.final-comma))))
            (retok new-initer (initer-context-fix ctx) types vstate)))
         ((erp successp new-initer new-ctx return-types new-vstate)
          (b* (((reterr)
                nil (irr-initer) (irr-initer-context) nil (irr-vstate)))
            (cond ((and (initer-case initer :single)
                        (expr-case (initer-single->expr initer) :string)
                        (type-case target-type :array))
                   (b* (((erp str-type)
                         (valid-stringlit-list
                          (expr-string->strings (initer-single->expr initer))
                          ienv))
                        ((unless
                             (if (type-case (type-array->of str-type) :char)
                                 (or (type-characterp
                                      (type-array->of target-type))
                                     (type-case (type-array->of target-type)
                                                :unknown))
                               (type-compatible-p
                                (type-array->of target-type)
                                (type-array->of str-type)
                                (vstate->completions vstate)
                                ienv)))
                         (retok nil nil nil nil nil))
                        (info (make-expr-string-info :type str-type)))
                     (retok t
                            (initer-single
                             (make-expr-string
                              :strings (expr-string->strings
                                        (initer-single->expr initer))
                              :info info))
                            (initer-context-fix ctx)
                            nil
                            (vstate-fix vstate))))
                  ((and (type-case target-type :array)
                        (initer-case
                         initer
                         :list (and (consp initer.elems)
                                    (endp (rest initer.elems))
                                    (endp (desiniter->designors
                                           (first initer.elems)))
                                    (let ((inner-initer (desiniter->initer
                                                         (first initer.elems))))
                                      (initer-case
                                       inner-initer
                                       :single (expr-case inner-initer.expr
                                                          :string)
                                       :list nil)))
                         :otherwise nil))
                   (b* ((str-expr (initer-single->expr
                                   (desiniter->initer
                                    (first (initer-list->elems initer)))))
                        ((erp str-type)
                         (valid-stringlit-list
                          (expr-string->strings str-expr) ienv))
                        (new-ctx
                         (if (type-case (type-array->of target-type) :unknown)
                             ;; When element type of the target array is
                             ;; unknown, we can't know whether the true type
                             ;; is a character type (in which case this case
                             ;; applies) or it is an aggregate or union (in
                             ;; which case we should recurse.) Therefore, we
                             ;; must fall back to an unknown initializer
                             ;; context.
                             (initer-context-unknown)
                           (initer-context-fix ctx)))
                        ((unless (and (type-compatible-p
                                       (type-array->of target-type)
                                       (type-array->of str-type)
                                       (vstate->completions vstate)
                                       ienv)
                                      ;; The element type of the str-type array
                                      ;; may be unknown, representing one of
                                      ;; the wide character types we are not
                                      ;; modeling precisely. However, we know
                                      ;; that these types must be integer
                                      ;; types.
                                      (type-integerp
                                       (type-array->of target-type))))
                         (retok nil nil nil nil nil))
                        (info (make-expr-string-info :type str-type))
                        (new-initer
                         (make-initer-list
                          :elems
                          (list
                           (make-desiniter
                            :designors nil
                            :initer (initer-single
                                     (make-expr-string
                                      :strings (expr-string->strings
                                                str-expr)
                                      :info info))))
                          :final-comma (initer-list->final-comma initer))))
                     (retok t new-initer new-ctx nil (vstate-fix vstate))))
                  ((and (or (type-case target-type :struct)
                            (type-case target-type :union))
                        (initer-case initer :single)
                        (lifetime-case lifetime :auto))
                   (b* (((erp new-expr type types vstate)
                         (valid-expr (initer-single->expr initer) vstate))
                        ((unless (type-compatible-p type
                                                    target-type
                                                    (vstate->completions vstate)
                                                    ienv))
                         (retok nil nil nil nil nil)))
                     (retok t
                            (initer-single new-expr)
                            (initer-context-fix ctx)
                            types
                            vstate)))
                  ((and (or (type-aggregatep target-type)
                            (type-case target-type :union))
                        (initer-case initer :list))
                   (b* (((erp subobjects-stack)
                         (initer-context-enter ctx
                                               (vstate->completions vstate)))
                        ((erp new-elems types vstate)
                         (valid-desiniter-list (initer-list->elems initer)
                                               target-type
                                               subobjects-stack
                                               lifetime
                                               vstate)))
                     (retok t
                            (make-initer-list
                             :elems new-elems
                             :final-comma (initer-list->final-comma initer))
                            (initer-context-fix ctx)
                            types
                            vstate)))
                  (t (retok nil nil nil nil nil)))))
         ((when successp)
          (retok new-initer new-ctx return-types new-vstate))
         ((unless (and (or (type-aggregatep target-type)
                           (type-case target-type :union))
                       (initer-case initer :single)
                       (initer-context-case ctx :stack)))
          (retmsg$ "The initializer ~x0 for the target type ~x1 is disallowed."
                   (initer-fix initer) (type-fix target-type)))
         ((erp subobjects-stack)
          (subobjects-stack-enter (initer-context-stack->stack ctx)
                                  (vstate->completions vstate))))
      (valid-initer initer
                    (initer-context-stack subobjects-stack)
                    lifetime
                    vstate
                    (- steps 1)))
    :measure (acl2::two-nats-measure (initer-count initer) (nfix steps))

    ///

    (local
     (define induct-valid-initer (ctx vstate steps)
       (declare (irrelevant ctx vstate))
       (b* ((steps (nfix steps))
            ((when (equal (nfix steps) 0))
             nil)
            ((mv - subobjects-stack)
             (subobjects-stack-enter (initer-context-stack->stack ctx)
                                     (vstate->completions vstate))))
         (induct-valid-initer (initer-context-stack subobjects-stack)
                              vstate
                              (- (nfix steps) 1)))
       :verify-guards nil
       :measure (nfix steps)
       :hints (("Goal" :in-theory (enable nfix)))))

    (defret initer-context-kind-of-valid-initer.new-ctx-when-case-stack
      (implies (and (initer-context-case ctx :stack)
                    (not erp))
               (equal (initer-context-kind new-ctx)
                      :stack))
      :fn valid-initer
      :hints (("Goal" :induct (induct-valid-initer ctx vstate steps)
               :in-theory (e/d (induct-valid-initer)
                               (valid-expr valid-initer)))
              '(:expand ((valid-initer initer ctx lifetime vstate steps))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer-option ((initer? initer-optionp)
                               (target-type typep)
                               (lifetime? lifetime-optionp)
                               (vstate vstatep))
    :guard (and (initer-option-unambp initer?)
                (or (not initer?)
                    lifetime?))
    :returns (mv (erp maybe-msgp)
                 (new-initer? initer-optionp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no initializer, validation succeeds.
       Otherwise, we validate the initializer."))
    (b* (((reterr) nil nil (irr-vstate)))
      (initer-option-case
       initer?
       :some (b* (((erp new-initer - return-types vstate)
                   (valid-initer initer?.val
                                 (initer-context-top target-type)
                                 (lifetime-option-fix lifetime?)
                                 vstate
                                 1024)))
               (retok new-initer return-types vstate))
       :none (retok nil nil (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (initer-option-count initer?) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter ((desiniter desiniterp)
                           (current-object-type typep)
                           (subobjects-stack initer-subobjects-stack-p)
                           (lifetime lifetimep)
                           (vstate vstatep))
    :guard (desiniter-unambp desiniter)
    :returns (mv (erp maybe-msgp)
                 (new-desiniter desiniterp)
                 (new-subobjects-stack initer-subobjects-stack-p)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer with optional designation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The subobjects stack passed as input represents
       our position in the initializer.
       It is used to determine the ``current'' subobject
       when an initializer lacks a designation.")
     (xdoc::p
      "When a designation is present,
       we reset the subobjects stack and validate the designators,
       using the current object type as the base type
       to be refined by the designators [C17:6.7.9/18].
       This returns a new subobjects stack,
       reflecting the position in the objects described by the designators.
       If no designation is present, we use the existing subobjects stack
       [C17:6.7.9/17].")
     (xdoc::p
      "After validating the initializer with this subobjects stack,
       we then advance the stack forward one position
       and the return the new stack."))
    (b* (((reterr)
          (irr-desiniter) (irr-initer-subobjects-stack) nil (irr-vstate))
         ((vstate vstate) vstate)
         ((desiniter desiniter) desiniter)
         ;; (info
         ;;  (desiniter-info
         ;;    (if (and (endp desiniter.designors)
         ;;             (not (subobjects-stack-end-p subobjects-stack)))
         ;;        (subobjects-stack-to-designors subobjects-stack vstate.ienv)
         ;;      nil)))
         ((erp new-design subobjects-stack types vstate)
          (if (endp desiniter.designors)
              (retok desiniter.designors
                     subobjects-stack
                     nil
                     vstate)
            (valid-designor-list desiniter.designors
                                 current-object-type
                                 (initer-subobjects-stack-known nil)
                                 vstate)))
         ((erp new-init ctx more-types vstate)
          (valid-initer desiniter.initer
                        (initer-context-stack subobjects-stack)
                        lifetime
                        vstate
                        1024))
         (new-subobjects-stack (initer-context-stack->stack ctx))
         (info
          (desiniter-info
            (if (and (endp desiniter.designors)
                     (not (subobjects-stack-end-p new-subobjects-stack)))
                (subobjects-stack-to-designors new-subobjects-stack vstate.ienv)
              nil)))
         (new-subobjects-stack
          (if (subobjects-stack-end-p new-subobjects-stack)
              ;; TODO: this case is impossible.
              new-subobjects-stack
            (subobjects-stack-advance new-subobjects-stack))))
      (retok (make-desiniter :designors new-design :initer new-init :info info)
             new-subobjects-stack
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (desiniter-count desiniter) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter-list ((desiniters desiniter-listp)
                                (current-object-type typep)
                                (subobjects-stack initer-subobjects-stack-p)
                                (lifetime lifetimep)
                                (vstate vstatep))
    :guard (desiniter-list-unambp desiniters)
    :returns (mv (erp maybe-msgp)
                 (new-desiniters desiniter-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more
            initializers with optional designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "The subobjects stack passed as input represents
       our position in the initializer.
       We validate the first initializer with an optional designation
       according to this stack.
       This returns a new stack used for the next element of the list."))
    (b* (((reterr) nil nil (irr-vstate))
         ((when (endp desiniters)) (retok nil nil (vstate-fix vstate)))
         ((erp new-desiniter subobjects-stack types vstate)
          (valid-desiniter (car desiniters)
                           current-object-type
                           subobjects-stack
                           lifetime
                           vstate))
         ((erp new-desiniters more-types vstate)
          (valid-desiniter-list (cdr desiniters)
                                current-object-type
                                subobjects-stack
                                lifetime
                                vstate)))
      (retok (cons new-desiniter new-desiniters)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (desiniter-list-count desiniters) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor ((designor designorp)
                          (target-type typep)
                          (subobjects-stack initer-subobjects-stack-p)
                          (vstate vstatep))
    :guard (designor-unambp designor)
    :returns (mv (erp maybe-msgp)
                 (new-designor designorp)
                 (new-subobjects-stack initer-subobjects-stack-p)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the one that the designator must apply to.
       By applying the designator to the type,
       we obtain the remaining subobjects at that point in the object.
       These subobjects are pushed to the new subobject stack and returned.")
     (xdoc::p
      "A subscript designator requires an array target type,
       and must have an integer expression [C17:6.7.9/6];
       the result is the element type of the array type.
       A dotted designator requires a struct or union type [C17:6.7.9/7];
       the result is the type of the member of that name."))
    (b* (((reterr)
          (irr-designor) (irr-initer-subobjects-stack) nil (irr-vstate)))
      (designor-case
       designor
       :sub
       (b* (((erp new-index index-type index-types vstate)
             (valid-const-expr designor.index vstate))
            ((erp new-range? range?-type? range?-types vstate)
             (valid-const-expr-option designor.range? vstate))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The first or only index of the designator ~x0 ~
                       has type ~x1."
                      (designor-fix designor)
                      index-type))
            ((unless (or (not range?-type?)
                         (type-integerp range?-type?)
                         (type-case range?-type? :unknown)))
             (retmsg$ "The second index of the designator ~x0 ~
                       has type ~x1."
                      (designor-fix designor)
                      range?-type?))
            ((when (type-case target-type :unknown))
             (retok (make-designor-sub :index new-index :range? new-range?)
                    (initer-subobjects-stack-unknown)
                    (set::union index-types range?-types)
                    vstate))
            ((unless (type-case target-type :array))
             (retmsg$ "The target type of the designator ~x0 is ~x1."
                      (designor-fix designor)
                      (type-fix target-type)))
            (element-type (type-array->of target-type))
            ((unless (const-expr-infop (const-expr->info new-index)))
             (retmsg$ "Internal error. ~
                       Constant expression is not annotated: ~x0."
                      new-index))
            (index-nat?
             (value-to-integer
              (const-expr-info->value (const-expr->info new-index))))
            ((when (and index-nat? (not (natp index-nat?))))
             (retmsg$ "The first or only index of the designator ~x0 ~
                       is negative."))
            ((unless index-nat?)
             (retok (make-designor-sub :index new-index :range? new-range?)
                    (initer-subobjects-stack-unknown)
                    (set::union index-types range?-types)
                    vstate))
            ((erp range-nat?)
             (b* (((reterr) nil)
                  ((when (const-expr-option-case new-range? :none))
                   (retok nil))
                  (new-range (const-expr-option-some->val new-range?))
                  ((unless (const-expr-infop
                            (const-expr->info new-range)))
                   (retmsg$ "Internal error. ~
                             Constant expression is not annotated: ~x0."
                            new-range))
                  (range-nat?
                   (value-to-integer
                    (const-expr-info->value (const-expr->info new-range))))
                  ((when (and range-nat? (not (natp range-nat?))))
                   (retmsg$ "The second index of the designator ~x0 ~
                             is negative.")))
               (retok range-nat?)))
            (new-subobjects-stack
             (initer-subobjects-stack-case
              subobjects-stack
              :unknown (initer-subobjects-stack-fix subobjects-stack)
              :known (initer-subobjects-stack-known
                      (cons (make-initer-subobjects-array-index
                             :of element-type
                             :index index-nat?
                             :range? range-nat?)
                            subobjects-stack.list)))))
         (retok (make-designor-sub :index new-index :range? new-range?)
                new-subobjects-stack
                (set::union index-types range?-types)
                vstate))
       :dot
       (type-case
        target-type
        :struct (b* (((erp members)
                      (type-struni-tag/members->members
                       target-type.tag/members
                       target-type.uid
                       (vstate->completions vstate))
                      :iferr (msg$ "Designator cannot be applied to ~
                                     incomplete struct type ~x0."
                                   (type-fix target-type)))
                     ((erp subobjects-list)
                      (subobjects-from-members-lookup designor.name t members)
                      :iferr (msg$ "Struct type ~x0 does not have member ~x1."
                                   (type-fix target-type)
                                   (ident->unwrap designor.name)))
                     (new-subobjects-stack
                      (initer-subobjects-stack-case
                       subobjects-stack
                       :unknown (initer-subobjects-stack-fix subobjects-stack)
                       :known (initer-subobjects-stack-known
                               (append subobjects-list
                                       subobjects-stack.list)))))
                  (retok (designor-dot designor.name)
                         new-subobjects-stack
                         nil
                         (vstate-fix vstate)))
        :union (b* (((erp members)
                     (type-struni-tag/members->members
                      target-type.tag/members
                      target-type.uid
                      (vstate->completions vstate))
                     :iferr (msg$ "Designator cannot be applied to ~
                                    incomplete struct type ~x0."
                                  (type-fix target-type)))
                    ((erp subobjects-list)
                     (subobjects-from-members-lookup designor.name nil members)
                     :iferr (msg$ "Struct type ~x0 does not have member ~x1."
                                  (type-fix target-type)
                                  (ident->unwrap designor.name)))
                    (new-subobjects-stack
                     (initer-subobjects-stack-case
                      subobjects-stack
                      :unknown (initer-subobjects-stack-fix subobjects-stack)
                      :known (initer-subobjects-stack-known
                              (append subobjects-list
                                      subobjects-stack.list)))))
                 (retok (designor-fix designor)
                        new-subobjects-stack
                        nil
                        (vstate-fix vstate)))
        :unknown (retok (designor-fix designor)
                        (initer-subobjects-stack-unknown)
                        nil
                        (vstate-fix vstate))
        :otherwise (retmsg$ "Designator ~x0 cannot be applied to ~
                              non-member, non-union type ~x1."
                            (designor-fix designor)
                            (type-fix target-type)))))
    :measure (acl2::two-nats-measure (designor-count designor) 0)

    ///

    (defret subobjects-stack-end-p-of-valid-designor.new-subobjects-stack
      (implies (not erp)
               (not (subobjects-stack-end-p new-subobjects-stack)))
      :hints (("Goal"
               :in-theory (enable endp)
               :expand ((valid-designor
                         designor target-type subobjects-stack vstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor-list ((designors designor-listp)
                               (target-type typep)
                               (subobjects-stack initer-subobjects-stack-p)
                               (vstate vstatep))
    :guard (designor-list-unambp designors)
    :returns (mv (erp maybe-msgp)
                 (new-designors designor-listp)
                 (new-subobjects-stack initer-subobjects-stack-p)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the one that the designator must apply to.
       The returned subobjects stack is the new stack
       with the subobjects obtained by applying each designator
       pushed to the top, in order."))
    (b* (((reterr) nil (irr-initer-subobjects-stack) nil (irr-vstate))
         ((when (endp designors))
          (retok nil
                 (initer-subobjects-stack-fix subobjects-stack)
                 nil
                 (vstate-fix vstate)))
         ((erp new-designor subobjects-stack types vstate)
          (valid-designor
           (car designors) target-type subobjects-stack vstate))
         (new-target-type (subobjects-stack-peek-type subobjects-stack))
         ((erp new-designors subobjects-stack more-types vstate)
          (valid-designor-list
           (cdr designors) new-target-type subobjects-stack vstate)))
      (retok (cons new-designor new-designors)
             subobjects-stack
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (designor-list-count designors) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor ((declor declorp)
                        (fundef-params-p booleanp)
                        (type typep)
                        (vstate vstatep))
    :guard (declor-unambp declor)
    :returns (mv (erp maybe-msgp)
                 (new-declor declorp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function is called after validating
       a list of declaration specifiers,
       or a list of specifiers and qualifiers:
       if the validation of those lists is successful,
       they determine a type, which the declarator can further refine:
       we pass that type as input to this validation function,
       which returns the possibly refined type,
       along with the identifier being declared.
       This function is also called recursively,
       since declarators and direct declarators are mutually recursive.")
     (xdoc::p
      "The @('fundef-params-p') flag is @('t')
       when this function is called
       to validate the declarator of a function definition,
       and only when the parameters of the function have not been validated yet.
       The exact handling of this flag,
       and the exact treatment of the parameters of function declarations,
       are explained in @(tsee valid-dirdeclor).")
     (xdoc::p
      "In our currently approximate type system,
       we do not validate type qualifiers, or attributes.
       So the only role of the @('pointers') component of @(tsee declor)
       is to refine the type passed as input into the derived pointer type
       [C17:6.7.6.1/1].
       This resulting type is then passed to
       the function to validate the direct declarator that follows.")
     (xdoc::p
      "We also pass the @('fundef-params-p') flag to @(tsee valid-dirdeclor).
       The reason is that, after peeling off the pointers,
       which refine the return result of the function,
       the direct declarator is still expected to be for a function,
       and we have not validated the parameters yet."))
    (b* (((reterr) (irr-declor) (irr-type) (irr-ident) nil (irr-vstate))
         ((declor declor) declor)
         (type (make-pointers-to declor.pointers type))
         ((erp new-dirdeclor type ident types vstate)
          (valid-dirdeclor declor.direct fundef-params-p type vstate)))
      (retok (make-declor :pointers declor.pointers :direct new-dirdeclor)
             type
             ident
             types
             vstate))
    :measure (acl2::two-nats-measure (declor-count declor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor-option ((declor? declor-optionp)
                               (type typep)
                               (vstate vstatep))
    :guard (declor-option-unambp declor?)
    :returns (mv (erp maybe-msgp)
                 (new-declor? declor-optionp)
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no declarator,
       we return the type and validation table unchanged,
       and no identifier.
       Otherwise, we validate the declarator,
       using a separate validation function.")
     (xdoc::p
      "This function does not take or return a @('fundef-params-p') flag
       because optional declarators are not used in function parameters."))
    (b* (((reterr) nil (irr-type) nil nil (irr-vstate)))
      (declor-option-case
       declor?
       :none (retok nil (type-fix type) nil nil (vstate-fix vstate))
       :some (b* (((erp new-declor type ident types vstate)
                   (valid-declor declor?.val nil type vstate)))
               (retok new-declor type ident types vstate))))
    :measure (acl2::two-nats-measure (declor-option-count declor?) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirdeclor ((dirdeclor dirdeclorp)
                           (fundef-params-p booleanp)
                           (type typep)
                           (vstate vstatep))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-dirdeclor dirdeclorp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type passed as input is the one resulting from the validation of
       the list of declaration specifiers
       or the list of specifiers and qualifiers
       that precedes the declarator of which the direct declarator is part.
       This type is refined according to the direct declarator,
       and we return the refined type,
       along with the declared identifier.")
     (xdoc::p
      "The meaning of the @('fundef-params-p') flag passed as input is
       the same as in @(tsee valid-declor): see that function's documentation.")
     (xdoc::p
      "If the direct declarator is just an identifier,
       the type is not further refined by this direct declarator.")
     (xdoc::p
      "If the direct declarator is a parenthesized declarator,
       we recursively validate the declarator.")
     (xdoc::p
      "If the direct declarator is one of the array kinds,
       we refine the type to an array type [C17:6.7.6.2/3]
       derived from the input type,
       and we recursively validate the enclosed direct declarator.
       Then we validate the index expression (if present),
       ensuring that it has integer type.
       For now we do not check that, if these expressions are constant,
       their values are greater than 0 [C17:6.7.6.2/1].
       Currently we do not need to do anything
       with type qualifiers and attributes.
       The @('fundef-params-p') flag is threaded through.")
     (xdoc::p
      "If the direct declarator is one of the function kinds,
       we ensure that the input type, which is the function return type,
       is not a function or array type [C17:6.7.6.3/1].
       We refine the input type to a function type
       (which in our current type system means we override it),
       and we validate the declarator.
       Then things differ between the kinds of function declarators.")
     (xdoc::p
      "In a function declarator with a parameter type list,
       we push a new scope for the parameters.
       If @('fundef-params-p') is @('t'),
       we then check whether the parameters of the current direct declarator
       are in fact the ones of the function.
       If so, we validate the parameters
       with a @('fundef-params-p') value of @('t').
       Otherwise, we use a value of @('nil').
       Validating the parameters adds them to the new scope.
       We then pop the scope if the parameters
       are not those of our function definition.
       Finally, we validate the enclosed direct declarator,
       returning the refined type.")
     (xdoc::p
      "To check whether the parameter type list
       in the current direct declarator
       represents the parameters of the current function definition,
       we check if the enclosed direct declarator contains function parameters.
       If so, this enclosed direct declarator
       contains the definition parameters;
       the parameter type list of the outer direct declarator
       does not correspond to the definition.
       To make things clearer, consider a function definition")
     (xdoc::codeblock
      "void (*f(int x, int y))(int z) { ... }")
     (xdoc::p
      "which defines a function @('f') with parameters @('x') and @('y'),
       which returns a pointer to a function
       that has a parameter @('z') and returns @('void').
       When we validate the full declarator of this function definition,
       @('fundef-params-p') is @('t').
       When we encounter the outer function declarator,
       first we check whether the inner direct declarator
       (@('(*f(int x, int y))')) contains function parameters.
       Since it does, we determine that the outer parameter type list
       (@('(int z)')) does not correspond the function definition,
       and we recursively process the inner direct declarator
       with @('fundef-params-p') @('t').")
     (xdoc::p
      "In any case, when the current function declarator
       is the one whose parameters are for the function definition,
       after validating the parameters, which pushes a new scope with them,
       we return the validation table as such,
       so that when we later validate the function body,
       we already have the top-level scope for the body.
       If instead @('fundef-params-p') is @('nil'),
       the parameters form a function prototype scope [C17:6.2.1/4],
       which is therefore popped.")
     (xdoc::p
      "For the function declarator with a parameter type list,
       we handle the special case of a single @('void') [C17:6.7.6.3/10].")
     (xdoc::p
      "A function declarator with a non-empty name list can only occur
       as the parameters of a function being defined [C17:6.7.6.3/3]
       Thus, we raise an error when the list is nonempty
       and @('fundef-params-p') is @('nil')
       (i.e. we are not validating the parameters of a defined function).
       Otherwise, we ensure that the names have no duplicates,
       and we push a new scope for the parameters and the function body,
       but we do not add the parameters to the new scope,
       because their types are specified by the declarations
       that must occur between the end of the whole function declarator
       and the beginning of the defined function's body.
       Note, in the case that we have a nonempty list of names,
       we currently return an imprecise type for the function.
       Since the type of each parameter is unknowable
       until the later declarations,
       we currently approximate the function type
       by assigning the unknown type to each function parameter."))
    (b* (((reterr) (irr-dirdeclor) (irr-type) (irr-ident) nil (irr-vstate)))
      (dirdeclor-case
       dirdeclor
       :ident
       (retok (dirdeclor-ident dirdeclor.ident)
              (type-fix type)
              dirdeclor.ident
              nil
              (vstate-fix vstate))
       :paren
       (b* (((erp new-declor type ident types vstate)
             (valid-declor dirdeclor.inner fundef-params-p type vstate)))
         (retok (dirdeclor-paren new-declor)
                type
                ident
                types
                vstate))
       :array
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-dirdeclor type ident types vstate)
             (valid-dirdeclor dirdeclor.declor fundef-params-p type vstate))
            ((erp new-expr? index-type? more-types vstate)
             (valid-expr-option dirdeclor.size? vstate))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type?)))
         (retok (make-dirdeclor-array :declor new-dirdeclor
                                      :qualspecs dirdeclor.qualspecs
                                      :size? new-expr?)
                type
                ident
                (set::union types more-types)
                vstate))
       :array-static1
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-dirdeclor type ident types vstate)
             (valid-dirdeclor dirdeclor.declor fundef-params-p type vstate))
            ((erp new-expr index-type more-types vstate)
             (valid-expr dirdeclor.size vstate))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type)))
         (retok (make-dirdeclor-array-static1 :declor new-dirdeclor
                                              :qualspecs dirdeclor.qualspecs
                                              :size new-expr)
                type
                ident
                (set::union types more-types)
                vstate))
       :array-static2
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-dirdeclor type ident types vstate)
             (valid-dirdeclor dirdeclor.declor fundef-params-p type vstate))
            ((erp new-expr index-type more-types vstate)
             (valid-expr dirdeclor.size vstate))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type)))
         (retok (make-dirdeclor-array-static2 :declor new-dirdeclor
                                              :qualspecs dirdeclor.qualspecs
                                              :size new-expr)
                type
                ident
                (set::union types more-types)
                vstate))
       :array-star
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-dirdeclor type ident types vstate)
             (valid-dirdeclor
              dirdeclor.declor fundef-params-p type vstate)))
         (retok (make-dirdeclor-array-star :declor new-dirdeclor
                                           :qualspecs dirdeclor.qualspecs)
                type
                ident
                types
                vstate))
       :function-params
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct declarator ~x0 has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      (type-fix type)))
            (outermost-fundef-params-p
             (and fundef-params-p
                  (not (dirdeclor-has-params-p dirdeclor.declor))))
            (vstate (vstate-push-scope vstate))
            ((erp new-params type-params return-types0 vstate)
             (b* (((reterr) nil (irr-type-params) nil vstate)
                  ((when (and (not (endp dirdeclor.params))
                              (endp (rest dirdeclor.params))
                              (equal (param-declon->specs
                                       (first dirdeclor.params))
                                     (list (decl-spec-typespec
                                             (type-spec-void))))
                              (equal (param-declon->declor
                                       (first dirdeclor.params))
                                     (param-declor-none))
                              (not (param-declon->attribs
                                     (first dirdeclor.params)))))
                   (retok (list (change-param-declon (first dirdeclor.params)
                                                    :info (make-param-declon-info :type nil)))
                          (make-type-params-prototype
                           :params nil
                           :ellipsis nil)
                          nil
                          vstate))
                  ((erp new-params types return-types vstate)
                   (valid-param-declon-list
                    dirdeclor.params outermost-fundef-params-p vstate)))
               (retok new-params
                      (make-type-params-prototype
                       :params types
                       :ellipsis dirdeclor.ellipsis)
                      return-types
                      vstate)))
            (vstate (if outermost-fundef-params-p
                       vstate
                     (vstate-pop-scope vstate)))
            (type (make-type-function :ret type :params type-params))
            ((erp new-dirdeclor type ident return-types1 vstate)
             (valid-dirdeclor
              dirdeclor.declor fundef-params-p type vstate)))
         (retok (make-dirdeclor-function-params :declor new-dirdeclor
                                                :params new-params
                                                :ellipsis dirdeclor.ellipsis)
                type
                ident
                (set::union return-types0 return-types1)
                vstate))
       :function-names
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct declarator ~x0 has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      (type-fix type)))
            (outermost-fundef-params-p
             (and fundef-params-p
                  (not (dirdeclor-has-params-p dirdeclor))))
            ((erp type vstate)
             (b* (((reterr) (irr-type) (irr-vstate)))
               (if fundef-params-p
                   (if (no-duplicatesp-equal dirdeclor.names)
                       (retok (make-type-function
                               :ret type
                               :params (make-type-params-old-style
                                        :params (make-list
                                                 (len dirdeclor.names)
                                                 :initial-element
                                                 (type-unknown))))
                              (vstate-push-scope vstate))
                     (retmsg$ "The list of parameter names ~
                               in the function declarator ~x0 ~
                               has duplicates."
                              (dirdeclor-fix dirdeclor)))
                 (if (endp dirdeclor.names)
                     (retok (make-type-function
                             :ret type
                             :params (type-params-unspecified))
                            vstate)
                   (retmsg$ "A non-empty list of parameter names ~
                             occurs in a function declarator ~x0 ~
                             that is not part of a function definition."
                            (dirdeclor-fix dirdeclor))))))
            ((erp new-dirdeclor type ident types vstate)
             (valid-dirdeclor
              dirdeclor.declor outermost-fundef-params-p type vstate)))
         (retok (make-dirdeclor-function-names :declor new-dirdeclor
                                               :names dirdeclor.names)
                type
                ident
                types
                vstate))))
    :measure (acl2::two-nats-measure (dirdeclor-count dirdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor ((absdeclor absdeclorp)
                           (type typep)
                           (vstate vstatep))
    :guard (absdeclor-unambp absdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-absdeclor absdeclorp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-declor)
       (see that function's documentation),
       but since the declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a declarator,
       not an abstract declarator."))
    (b* (((reterr) (irr-absdeclor) (irr-type) nil (irr-vstate))
         ((absdeclor absdeclor) absdeclor)
         (type (make-pointers-to absdeclor.pointers type))
         ((erp new-direct? type types vstate)
          (valid-dirabsdeclor-option absdeclor.direct? type vstate)))
      (retok (make-absdeclor :pointers absdeclor.pointers :direct? new-direct?)
             type
             types
             vstate))
    :measure (acl2::two-nats-measure (absdeclor-count absdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor-option ((absdeclor? absdeclor-optionp)
                                  (type typep)
                                  (vstate vstatep))
    :guard (absdeclor-option-unambp absdeclor?)
    :returns (mv (erp maybe-msgp)
                 (new-absdeclor? absdeclor-optionp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the abstract declarator,
       using a separate validation function."))
    (b* (((reterr) nil (irr-type) nil (irr-vstate)))
      (absdeclor-option-case
       absdeclor?
       :none (retok nil (type-fix type) nil (vstate-fix vstate))
       :some (valid-absdeclor absdeclor?.val type vstate)))
    :measure (acl2::two-nats-measure (absdeclor-option-count absdeclor?) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                              (type typep)
                              (vstate vstatep))
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-dirabsdeclor dirabsdeclorp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-dirdeclor)
       (see that function's documentation),
       but since the direct declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a (direct) declarator,
       not an (direct) abstract declarator."))
    (b* (((reterr) (irr-dirabsdeclor) (irr-type) nil (irr-vstate)))
      (dirabsdeclor-case
       dirabsdeclor
       :paren
       (b* (((erp new-absdeclor type types vstate)
             (valid-absdeclor dirabsdeclor.inner type vstate)))
         (retok (dirabsdeclor-paren new-absdeclor)
                type
                types
                vstate))
       :array
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-declor? type types vstate)
             (valid-dirabsdeclor-option dirabsdeclor.declor? type vstate))
            ((erp new-size? index-type? more-types vstate)
             (valid-expr-option dirabsdeclor.size? vstate))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type?)))
         (retok (make-dirabsdeclor-array
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size? new-size?)
                type
                (set::union types more-types)
                vstate))
       :array-static1
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-declor? type types vstate)
             (valid-dirabsdeclor-option dirabsdeclor.declor? type vstate))
            ((erp new-size index-type more-types vstate)
             (valid-expr dirabsdeclor.size vstate))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type)))
         (retok (make-dirabsdeclor-array-static1
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size new-size)
                type
                (set::union types more-types)
                vstate))
       :array-static2
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-declor? type types vstate)
             (valid-dirabsdeclor-option dirabsdeclor.declor? type vstate))
            ((erp new-size index-type more-types vstate)
             (valid-expr dirabsdeclor.size vstate))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type)))
         (retok (make-dirabsdeclor-array-static2
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size new-size)
                type
                (set::union types more-types)
                vstate))
       :array-star
       (b* ((type (make-type-array :of type :size nil)) ; TODO: size
            ((erp new-declor? type types vstate)
             (valid-dirabsdeclor-option dirabsdeclor.declor? type vstate)))
         (retok (dirabsdeclor-array-star new-declor?)
                type
                types
                vstate))
       :function
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      (type-fix type)))
            (vstate (vstate-push-scope vstate))
            ((erp new-params type-params return-types0 vstate)
             (b* (((reterr) nil (irr-type-params) nil vstate)
                  ((when (and (not (endp dirabsdeclor.params))
                              (endp (rest dirabsdeclor.params))
                              (equal (param-declon->specs
                                       (first dirabsdeclor.params))
                                     (list (decl-spec-typespec
                                             (type-spec-void))))
                              (equal (param-declon->declor
                                       (first dirabsdeclor.params))
                                     (param-declor-none))
                              (not (param-declon->attribs
                                     (first dirabsdeclor.params)))))
                   (retok (list (change-param-declon (first dirabsdeclor.params)
                                                    :info (make-param-declon-info :type nil)))
                          (make-type-params-prototype
                           :params nil
                           :ellipsis nil)
                          nil
                          vstate))
                  ((erp new-params types return-types vstate)
                   (valid-param-declon-list
                    dirabsdeclor.params nil vstate)))
               (retok new-params
                      (make-type-params-prototype
                       :params types
                       :ellipsis dirabsdeclor.ellipsis)
                      return-types
                      vstate)))
            (vstate (vstate-pop-scope vstate))
            (type (make-type-function :ret type :params type-params))
            ((erp new-declor? type return-types1 vstate)
             (valid-dirabsdeclor-option dirabsdeclor.declor? type vstate)))
         (retok (make-dirabsdeclor-function :declor? new-declor?
                                            :params new-params
                                            :ellipsis dirabsdeclor.ellipsis)
                type
                (set::union return-types0 return-types1)
                vstate))
       :dummy-base
       (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (dirabsdeclor-count dirabsdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                     (type typep)
                                     (vstate vstatep))
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
    :returns (mv (erp maybe-msgp)
                 (new-dirabsdeclor? dirabsdeclor-optionp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no direct abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the direct abstract declarator,
       using a separate validation function."))
    (b* (((reterr) nil (irr-type) nil (irr-vstate)))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :none (retok nil (type-fix type) nil (vstate-fix vstate))
       :some (valid-dirabsdeclor dirabsdeclor?.val type vstate)))
    :measure (acl2::two-nats-measure (dirabsdeclor-option-count dirabsdeclor?)
                                     0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declon ((paramdecl param-declonp)
                              (fundef-params-p booleanp)
                              (vstate vstatep))
    :guard (param-declon-unambp paramdecl)
    :returns (mv (erp maybe-msgp)
                 (new-paramdecl param-declonp)
                 (type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('fundef-params-p') input is @('t') iff
       we are validating the parameter of a function definition.")
     (xdoc::p
      "We validate the declaration specifiers,
       which results in a type,
       a list of storage class specifiers,
       and a possibly updated table.
       We ensure that the list of storage class specifiers
       is either empty or the singleton @('register') [C17:6.7.6.3/2].")
     (xdoc::p
      "We validate the parameter declarator,
       ensuring that it has an identifier if @('fundef-params-p') is @('t')
       [C17:6.9.1/5].
       We adjust the type if necessary [C17:6.7.6.3/7] [C17:6.7.6.3/8].
       If the parameter declarator has an identifier,
       we extend the validation table with it,
       unless there is already an ordinary identifier
       with the same name in the same (i.e. current) scope;
       since parameters have no linkage [C17:6.2.2/6],
       they can be only declared once in the same scope [C17:6.7/3].
       Parameters of function declarations have no linkage [C17:6.2.2/6].
       Since storage is allocated for them when the function is called,
       they are considered defined [C17:6.7/5]."))
    (b* (((reterr) (irr-param-declon) (irr-type) nil (irr-vstate))
         ((param-declon paramdecl) paramdecl)
         ((erp new-specs type storspecs types vstate)
          (valid-decl-spec-list paramdecl.specs nil nil nil vstate))
         ((unless (or (endp storspecs)
                      (stor-spec-list-register-p storspecs)))
          (retmsg$ "The parameter declaration ~x0 ~
                    has storage class specifiers ~x1."
                   (param-declon-fix paramdecl)
                   (stor-spec-list-fix storspecs)))
         ((erp new-decl type ident? more-types uid? vstate)
          (valid-param-declor paramdecl.declor type vstate))
         ((when (and fundef-params-p
                     (not ident?)))
          (retmsg$ "The parameter declaration ~x0 ~
                    is for a function definition but has no identifier."
                   (param-declon-fix paramdecl)))
         (type (type-case
                type
                :array (make-type-pointer :to type.of)
                :function (make-type-pointer :to type)
                :otherwise type))
         (info (param-declon-info type))
         ((when (not ident?))
          (retok (make-param-declon :specs new-specs
                                    :declor new-decl
                                    :attribs paramdecl.attribs
                                    :info info)
                 type
                 (set::union types more-types)
                 vstate))
         (ord-info (make-valid-ord-info-objfun
                    :type type
                    :linkage (linkage-none)
                    :defstatus (valid-defstatus-defined)
                    :uid uid?))
         ((mv info? currentp) (vstate-lookup-ord ident? vstate))
         ((when (and info? currentp))
          (retmsg$ "The parameter declared in ~x0 ~
                    in already declared in the current scope ~
                    with associated information ~x1."
                   (param-declon-fix paramdecl) info?))
         (vstate (vstate-add-ord ident? ord-info vstate)))
      (retok (make-param-declon :specs new-specs
                                :declor new-decl
                                :attribs paramdecl.attribs
                                :info info)
             type
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (param-declon-count paramdecl) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declon-list ((paramdecls param-declon-listp)
                                   (fundef-params-p booleanp)
                                   (vstate vstatep))
    :guard (param-declon-list-unambp paramdecls)
    :returns (mv (erp maybe-msgp)
                 (new-paramdecls param-declon-listp)
                 (types type-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each parameter in turn,
       threading the validation table through,
       using a separate validation function."))
    (b* (((reterr) nil nil nil (irr-vstate))
         ((when (endp paramdecls)) (retok nil nil nil (vstate-fix vstate)))
         ((erp new-paramdecl type return-types0 vstate)
          (valid-param-declon (car paramdecls) fundef-params-p vstate))
         ((erp new-paramdecls types return-types1 vstate)
          (valid-param-declon-list (cdr paramdecls) fundef-params-p vstate)))
      (retok (cons new-paramdecl new-paramdecls)
             (cons type types)
             (set::union return-types0 return-types1)
             vstate))
    :measure (acl2::two-nats-measure (param-declon-list-count paramdecls) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declor ((paramdeclor param-declorp)
                              (type typep)
                              (vstate vstatep))
    :guard (param-declor-unambp paramdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-paramdeclor param-declorp)
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (uid? uid-optionp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The input type is the one resulting from
       the declaration specifiers of the parameter declaration
       of which the parameter declarator is part of.
       If validation is successful,
       we return a possibly refined type,
       and an optional identifier.")
     (xdoc::p
      "If the parameter declarator is a (non-abstract) declarator,
       we return the possibly refined type, the identifier, and the @(see UID).
       If the parameter declarator is an abstract declarator,
       we return the possibly refined type but no identifier nor @(see UID).
       If the parameter declarator is absent,
       we return the type unchanged and no identifier nor @(see UID)."))
    (b* (((reterr)
          (irr-param-declor) (irr-type) (irr-ident) nil nil (irr-vstate)))
      (param-declor-case
       paramdeclor
       :nonabstract
       (b* (((erp new-declor type ident types vstate)
             (valid-declor paramdeclor.declor nil type vstate))
            ((mv uid vstate) (vstate-get-fresh-uid ident (linkage-none) vstate))
            (info (make-param-declor-nonabstract-info :type type :uid uid)))
         (retok (make-param-declor-nonabstract :declor new-declor
                                               :info info)
                type
                ident
                types
                uid
                vstate))
       :abstract
       (b* (((erp new-absdeclor type types vstate)
             (valid-absdeclor paramdeclor.declor type vstate)))
         (retok (param-declor-abstract new-absdeclor)
                type
                nil
                types
                nil
                vstate))
       :none
       (retok (param-declor-none)
              (type-fix type)
              nil
              nil
              nil
              (vstate-fix vstate))
       :ambig
       (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (param-declor-count paramdeclor) 0)

    ///

    (defret valid-param-declor.uid?-under-iff
      (implies (not erp)
               (iff uid? ident?))
      :hints
      (("Goal"
        :expand (valid-param-declor paramdeclor type vstate)
        :in-theory (disable return-type-of-valid-declor.ident)
        :use ((:instance return-type-of-valid-declor.ident
                         (declor (param-declor-nonabstract->declor paramdeclor))
                         (fundef-params-p nil)))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-tyname ((tyname tynamep) (vstate vstatep))
    :guard (tyname-unambp tyname)
    :returns (mv (erp maybe-msgp)
                 (new-tyname tynamep)
                 (type typep)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A valid type name denotes a type,
       so we return a type if validation is successful.")
     (xdoc::p
      "First we validate the list of specifiers and qualifiers,
       which returns a type if successful.
       Then we validate the optional abstract declarator,
       which returns a possibly refined type.
       We return the latter type."))
    (b* (((reterr) (irr-tyname) (irr-type) nil (irr-vstate))
         ((tyname tyname) tyname)
         ((erp new-specquals type types vstate)
          (valid-spec/qual-list tyname.specquals nil nil vstate))
         ((erp new-decl? type more-types vstate)
          (valid-absdeclor-option tyname.declor? type vstate))
         (info (make-tyname-info :type type)))
      (retok (make-tyname :specquals new-specquals
                          :declor? new-decl?
                          :info info)
             type
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (tyname-count tyname) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struni-spec ((struni-spec struni-specp)
                             (vstate vstatep))
    :guard (struni-spec-unambp struni-spec)
    :returns (mv (erp maybe-msgp)
                 (new-struni-spec struni-specp)
                 (type-struni-members type-struni-member-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We recursively validate the members
       and return the @(tsee type-struni-member-list),
       which represents the name and types of the members.")
     (xdoc::p
      "We do not extend the validation table
       with struct or union type definitions.
       This is handled by @(tsee valid-type-spec)
       using information returned by this function.")
     (xdoc::p
      "We also check that there is a name or a list of members
       [C17:6.7.2.1/2]."))
    (b* (((reterr) (irr-struni-spec) nil nil (irr-vstate))
         ((struni-spec struni-spec) struni-spec)
         ((when (and (not struni-spec.name?)
                     (endp struni-spec.members)))
          (retmsg$ "The structure or union specifier ~x0 ~
                    has no name and no members."
                   (struni-spec-fix struni-spec)))
         ((erp new-members type-struni-members types vstate)
          (valid-struct-declon-list struni-spec.members nil vstate)))
      (retok (make-struni-spec :attribs struni-spec.attribs
                               :name? struni-spec.name?
                               :members new-members)
             type-struni-members
             types
             vstate))
    :measure (acl2::two-nats-measure (struni-spec-count struni-spec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struct-declon ((structdeclon struct-declonp)
                               (previous ident-listp)
                               (vstate vstatep))
    :guard (struct-declon-unambp structdeclon)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclon struct-declonp)
                 (new-previous ident-listp)
                 (type-struni-members type-struni-member-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede this structure declaration
       in the structure or union specifier being validated.
       The @('new-previous') output consists of
       the extension of @('previous') with
       the names of the members declared by this structure declaration.")
     (xdoc::p
      "The @('type-struni-members') output consists
       of the names and types for the members declared by
       the structure declaration.")
     (xdoc::p
      "If the structure declaration declares members,
       first we validate the list of specifiers and qualifiers,
       obtaining a type if the validation is successful.
       Then we use a separate validation function for the structure declarators,
       which also returns a possibly extended list of member names.
       If there are no structure declarators,
       the structure declaration must be
       an anonymous structure or anonymous union [C17:6.7.2.1/13].")
     (xdoc::p
      "If the structure declaration consists of a static assertion declaration,
       we validate it using a separate validation function.
       The list of member names is unchanged.")
     (xdoc::p
      "If the structure declaration is empty (i.e. a semicolon),
       which is a GCC extension,
       the list of member names and the validation table are unchanged."))
    (b* (((reterr) (irr-struct-declon) nil nil nil (irr-vstate)))
      (struct-declon-case
       structdeclon
       :member
       (b* (((erp new-specquals type types vstate)
             (valid-spec/qual-list structdeclon.specquals nil nil vstate))
            ((when (endp structdeclon.declors))
             (if (type-case
                  type
                  :struct (type-struni-tag/members-case
                           type.tag/members :untagged)
                  :union (type-struni-tag/members-case
                          type.tag/members :untagged)
                  :otherwise nil)
                 (retok (make-struct-declon-member
                         :extension structdeclon.extension
                         :specquals new-specquals
                         :declors nil
                         :attribs structdeclon.attribs)
                        (ident-list-fix previous)
                        (list (make-type-struni-member
                               :name? nil
                               :type type))
                        types
                        vstate)
               (retmsg$ "Struct member ~x0 with type ~x1 ~
                         must have a struct declarator list."
                        (struct-declon-fix structdeclon)
                        type)))
            ((erp new-declors previous type-struni-members more-types vstate)
             (valid-struct-declor-list
              structdeclon.declors previous type vstate)))
         (retok (make-struct-declon-member :extension structdeclon.extension
                                           :specquals new-specquals
                                           :declors new-declors
                                           :attribs structdeclon.attribs)
                previous
                type-struni-members
                (set::union types more-types)
                vstate))
       :statassert
       (b* (((erp new-statassert types vstate)
             (valid-statassert structdeclon.statassert vstate)))
         (retok (struct-declon-statassert new-statassert)
                (ident-list-fix previous)
                nil
                types
                vstate))
       :empty
       (retok (struct-declon-empty)
              (ident-list-fix previous)
              nil
              nil
              (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (struct-declon-count structdeclon) 0)

    ///

    (defret valid-struct-declon.type-struni-members-type-prescription
      (true-listp type-struni-members)
      :rule-classes :type-prescription
      :hints
      (("Goal"
        :in-theory
        (disable return-type-of-valid-struct-declon.type-struni-members)
        :use return-type-of-valid-struct-declon.type-struni-members))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struct-declon-list ((structdeclons struct-declon-listp)
                                    (previous ident-listp)
                                    (vstate vstatep))
    :guard (struct-declon-list-unambp structdeclons)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclons struct-declon-listp)
                 (type-struni-members type-struni-member-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede these structure declarations
       (which declare more members)
       in the structure or union specifier being validated.
       This list is used to ensure uniqueness of member names.")
     (xdoc::p
      "The @('type-struni-members') output consists
       of the names and types for the members declared by
       the structure declaration list."))
    (b* (((reterr) nil nil nil (irr-vstate))
         ((when (endp structdeclons))
          (retok nil nil nil (vstate-fix vstate)))
         ((erp new-structdeclon previous type-struni-members types vstate)
          (valid-struct-declon (car structdeclons) previous vstate))
         ((erp new-structdeclons more-type-struni-members more-types vstate)
          (valid-struct-declon-list (cdr structdeclons) previous vstate)))
      (retok (cons new-structdeclon new-structdeclons)
             (append type-struni-members more-type-struni-members)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (struct-declon-list-count structdeclons)
                                     0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struct-declor ((structdeclor struct-declorp)
                               (previous ident-listp)
                               (type typep)
                               (vstate vstatep))
    :guard (struct-declor-unambp structdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclor struct-declorp)
                 (new-previous ident-listp)
                 (type-struni-member type-struni-member-p)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input and @('new-previous') output
       have the same meaning as in @(tsee valid-struct-declon).")
     (xdoc::p
      "The @('type') input comes from the list of specifiers and qualifiers
       that precedes the list of structure declarators
       of which this structure declarator is an element.
       We ensure that there is either a declarator or a constant expression
       (this is actually a syntactic constraint,
       but it is currently not captured in the abstract syntax,
       so we check it here).
       If there is a declarator, we validate it,
       and we add the declared identifier to the list of member names,
       after ensuring that it is not already there.
       If there is a constant expression, we validate it,
       but for now we do not perform any checks related to its value
       [C17:6.7.2.1/4];
       we also do not constrain the types of bit fields [C17:6.7.2.1/5],
       but we ensure that the constant expression, if present, is integer.")
     (xdoc::p
      "The @('type-struni-member') output consist
       of the name and type for the member declared by
       the structure declarator."))
    (b* (((reterr) (irr-struct-declor)
          nil
          (irr-type-struni-member)
          nil
          (irr-vstate))
         ((struct-declor structdeclor) structdeclor)
         ((when (and (not structdeclor.declor?)
                     (not structdeclor.expr?)))
          (retmsg$ "The structure declarator ~x0 is empty."
                   (struct-declor-fix structdeclor)))
         ((erp new-declor? new-type ident? types vstate)
          (valid-declor-option structdeclor.declor? type vstate))
         (previous (ident-list-fix previous))
         ((when (and ident?
                     (member-equal ident? previous)))
          (retmsg$ "The structure declarator ~x0 ~
                    duplicates the member name."
                   (struct-declor-fix structdeclor)))
         (previous (if ident?
                       (rcons ident? previous)
                     previous))
         ((erp new-expr? width-type? more-types vstate)
          (valid-const-expr-option structdeclor.expr? vstate))
         ((when (and width-type?
                     (not (type-integerp width-type?))
                     (not (type-case width-type? :unknown))))
          (retmsg$ "The structure declarator ~x0 ~
                    has a width of type ~x1."
                   (struct-declor-fix structdeclor)
                   width-type?)))
      (retok (make-struct-declor :declor? new-declor? :expr? new-expr?)
             previous
             (make-type-struni-member
              :name? (and structdeclor.declor?
                          (declor->ident structdeclor.declor?))
              :type new-type)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (struct-declor-count structdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struct-declor-list ((structdeclors struct-declor-listp)
                                    (previous ident-listp)
                                    (type typep)
                                    (vstate vstatep))
    :guard (struct-declor-list-unambp structdeclors)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclors struct-declor-listp)
                 (new-previous ident-listp)
                 (type-struni-members type-struni-member-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each structure declarator in turn,
       threading the data through.
       Note that the same type
       (coming from the list of specifiers and qualifiers)
       is passed to the validation function for each structure declarator,
       since that type applied to all them
       (possibly refined, possibly differently, by the structure declarators.")
     (xdoc::p
      "The @('type-struni-members') output consist
       of the names and types for the members declared by
       the structure declarator."))
    (b* (((reterr) nil nil nil nil (irr-vstate))
         ((when (endp structdeclors))
          (retok nil (ident-list-fix previous) nil nil (vstate-fix vstate)))
         ((erp new-structdeclor previous type-struni-member types vstate)
          (valid-struct-declor (car structdeclors) previous type vstate))
         ((erp new-structdeclors previous type-struni-members more-types vstate)
          (valid-struct-declor-list
           (cdr structdeclors) previous type vstate)))
      (retok (cons new-structdeclor new-structdeclors)
             previous
             (cons type-struni-member type-struni-members)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (struct-declor-list-count structdeclors)
                                     0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enum-spec ((enumspec enum-specp)
                           (vstate vstatep))
    :guard (enum-spec-unambp enumspec)
    :returns (mv (erp maybe-msgp)
                 (new-enumspec enum-specp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that there is at least a name of a list of enumerators;
       although this is a syntactic constraint,
       it is currently not captured in our abstract syntax,
       so we double-check it here.")
     (xdoc::p
      "For now our validation tables include
       no information about enumeration tags,
       so we do not extend the validation table,
       if the enumeration specifier has a name.
       However, we validate the enumerators, if present."))
    (b* (((reterr) (irr-enum-spec) nil (irr-vstate))
         ((enum-spec enumspec) enumspec)
         ((when (and (not enumspec.name?)
                     (endp enumspec.enumers)))
          (retmsg$ "The enumeration specifier ~x0 ~
                    has no name and no enumerators."
                   (enum-spec-fix enumspec)))
         ((erp new-enumers types vstate)
          (valid-enumer-list enumspec.enumers vstate)))
      (retok (make-enum-spec :name? enumspec.name?
                             :enumers new-enumers
                             :final-comma enumspec.final-comma)
             types
             vstate))
    :measure (acl2::two-nats-measure (enum-spec-count enumspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer ((enumer enumerp) (vstate vstatep))
    :guard (enumer-unambp enumer)
    :returns (mv (erp maybe-msgp)
                 (new-enumer enumerp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumerator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The enumeration constant is added to the validation table [C17:6.2.1/7],
       unless there is already an ordinary identifier
       with the same name and in the same (i.e. current) scope;
       since enumeration constants have no linkage [C17:6.2.2/6],
       they can be only declared once in the same scope [C17:6.7/3].
       If there is a constant expression,
       we validate it and check that it has integer type,
       but for now we do not check that the value
       is representable as @('int') [C17:6.7.2.2/2]."))
    (b* (((reterr) (irr-enumer) nil (irr-vstate))
         ((enumer enumer) enumer)
         ((mv info? currentp) (vstate-lookup-ord enumer.name vstate))
         ((when (and info? currentp))
          (retmsg$ "The enumerator declared in ~x0 ~
                    in already declared in the current scope ~
                    with associated information ~x1."
                   (enumer-fix enumer) info?))
         (vstate (vstate-add-ord enumer.name (valid-ord-info-enumconst) vstate))
         ((erp new-value? type? types vstate)
          (valid-const-expr-option enumer.value? vstate))
         ((when (and type?
                     (not (type-integerp type?))
                     (not (type-case type? :unknown))))
          (retmsg$ "The value of the numerator ~x0 has type ~x1."
                   (enumer-fix enumer) type?)))
      (retok (make-enumer :name enumer.name :value? new-value?) types vstate))
    :measure (acl2::two-nats-measure (enumer-count enumer) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer-list ((enumers enumer-listp)
                             (vstate vstatep))
    :guard (enumer-list-unambp enumers)
    :returns (mv (erp maybe-msgp)
                 (new-enumers enumer-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through each enumerator in order,
       extending the validation table with each."))
    (b* (((reterr) nil nil (irr-vstate))
         ((when (endp enumers)) (retok nil nil (vstate-fix vstate)))
         ((erp new-enumer types vstate) (valid-enumer (car enumers) vstate))
         ((erp new-enumers more-types vstate)
          (valid-enumer-list (cdr enumers) vstate)))
      (retok (cons new-enumer new-enumers) (set::union types more-types) vstate))
    :measure (acl2::two-nats-measure (enumer-list-count enumers) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-statassert ((statassert statassertp)
                            (vstate vstatep))
    :guard (statassert-unambp statassert)
    :returns (mv (erp maybe-msgp)
                 (new-statassert statassertp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a static assertion declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate the constant expression,
       which must be integer [C17:6.7.10/3],
       and we validate the string literal(s)."))
    (b* (((reterr) (irr-statassert) nil (irr-vstate))
         (ienv (vstate->ienv vstate))
         ((statassert statassert) statassert)
         ((erp new-test type types vstate)
          (valid-const-expr statassert.test vstate))
         ((unless (or (type-integerp type)
                      (type-case type :unknown)))
          (retmsg$ "The expression in the static assertion declaration ~x0 ~
                    has type ~x1."
                   (statassert-fix statassert)
                   type))
         ((erp &) (valid-stringlit-list statassert.message ienv)))
      (retok (make-statassert :test new-test :message statassert.message)
             types
             vstate))
    :measure (acl2::two-nats-measure (statassert-count statassert) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-init-declor ((initdeclor init-declorp)
                             (type typep)
                             (storspecs stor-spec-listp)
                             (vstate vstatep))
    :guard (init-declor-unambp initdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-initdeclor init-declorp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializer declarators [C17:6.7/1]
       appear in declarations, after declaration specifiers.
       The latter determine a type, passed as input,
       which an initializer declarator may refine.
       We also pass as input the storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We validate the declarator,
       which returns the identifier and the possibly refined type.
       Here the @('fundef-params-p') flag is always @('nil'),
       because we are not in a function definition.")
     (xdoc::p
      "Then we validate the storage class specifiers,
       which together with the identifier and final type
       determine whether we are declaring a @('typedef'),
       and what the linkage and lifetime are.")
     (xdoc::p
      "If the @('typedef') flag is @('t'),
       there must be no initializer,
       because we are not declaring an object.
       In this case, we add the @('typedef') to the validation table.
       A @('typedef') may be redefined in the same scope
       assuming the two types are compatible and not variably modified
       [C17:6.7/3] (the latter of which is inexpressible in our current
       approximate type system
       so we conservatively permit redefinition of any compatible types).")
     (xdoc::p
      "If the @('typedef') flag is @('nil'),
       the identifier may denote a function or an object.
       The initializer may be present only if
       the type is not that of a function,
       because initializers only apply to objects,
       and the type is not void,
       because the type must be complete [C17:6.7.9/3].
       We validate the initializer if present;
       we pass the type of the identifier,
       so the initializer is checked against that.
       The initializer is validated after
       the declared identifier is added to the table [C17:6.2.1/7].")
     (xdoc::p
      "We calculate the definition status for the declaration.
       If we are declaring a function, the status is undefined,
       because we do not have a function body here.
       Otherwise, we are declaring an object.
       If we are in a block scope,
       the status is undefined if the object has external linkage
       (because it refers to some external entity from the block),
       while it is defined otherwise
       (because the declaration allocates storage for the object).
       If we are in a file scope, we follow [C17:6.9.2/1] and [C17:6.9.2/2]:
       an initializer makes the status defined;
       otherwise, the presence of @('extern') makes the status undefined
       and its absence makes the status defined.
       This is slightly different from what [C17:6.9.2/2] says,
       which mentions no storage class specifier or @('static'),
       but it seems clear that this neglects to consider @('_Thread_local');
       in fact, the wording in the newly released C23 standard is clearer.")
     (xdoc::p
      "If the declaration being validated has external linkage,
       we look up the identifier in the @('externals') map.
       If we find the identifier has already been declared elsewhere
       with external linkage,
       we check that the types are compatible [C17:6.2.2/2] [C17:6.2.7/2].
       We also check that the identifier has not been previously declared
       in this translation unit with internal linkage [C17:6.2.2/7].
       If the declaration being validated has internal linkage,
       we look up the identifier in the @('externals') map
       and check that no previous declaration of the identifier
       exists in this translation unit with external linkage [C17:6.2.2/7].")
     (xdoc::p
      "We look up the identifier in the validation table.
       If no information is found in the validation table,
       we add the identifier to the table.
       If the current declaration has no linkage,
       or if the information in the table has no linkage
       (which includes the case of the information in the table
       being for a @('typedef') or an enumeration constant),
       the two must denote different entities,
       and thus we ensure that the one in the table
       is not in the same (i.e. current) scope [C17:6.2.1/4] [C17:6.7/3];
       if the checks pass, we add the identifier to the table.
       If instead both have internal or external linkage,
       they must refer to the same entity,
       and so we ensure that the types are the same.
       We also need to check that the linkages are the same,
       in which case we still add the identifier to the table,
       to record that it is also declared in the current scope;
       in this case, it is not clear whether we should suitable combine
       the old and new definition statuses,
       but for now we just use the newest.
       It is an error if the current linkage is internal
       while the one in the table is external.
       The situation where the current one is external
       while the one in the table is internal cannot happen,
       because as defined in @(tsee valid-stor-spec-list),
       the current one would ``inherit''
       the internal linkage from the previous one.")
     (xdoc::p
      "For now we ignore the optional assembler name specifier,
       as well as any attribute specifiers."))
    (b* (((reterr) (irr-init-declor) nil (irr-vstate))
         (ienv (vstate->ienv vstate))
         ((init-declor initdeclor) initdeclor)
         ((erp new-declor type ident types vstate)
          (valid-declor initdeclor.declor nil type vstate))
         ((erp typedefp linkage lifetime?)
          (valid-stor-spec-list storspecs ident type nil vstate))
         ((when typedefp)
          (b* (((when initdeclor.initer?)
                (retmsg$ "The typedef name ~x0 ~
                          has an initializer ~x1."
                         ident initdeclor.initer?))
               ((mv info? currentp) (vstate-lookup-ord ident vstate))
               ((when (and info?
                           currentp
                           (or (not (valid-ord-info-case info? :typedef))
                               (not (type-compatible-p
                                     (valid-ord-info-typedef->def info?)
                                     type
                                     (vstate->completions vstate)
                                     ienv)))))
                (retmsg$ "The typedef name ~x0 ~
                          is already declared in the current scope ~
                          with associated information ~x1."
                         ident info?))
               (vstate (vstate-add-ord ident
                                       (valid-ord-info-typedef type)
                                       vstate))
               (anno-info (make-init-declor-info :type type
                                                 :typedefp t
                                                 :uid? nil)))
            (retok (make-init-declor :declor new-declor
                                     :asm? initdeclor.asm?
                                     :attribs initdeclor.attribs
                                     :initer? nil
                                     :info anno-info)
                   types
                   vstate)))
         ((when (and initdeclor.initer?
                     (or (type-case type :function)
                         (type-case type :void))))
          (retmsg$ "The identifier ~x0 has type ~x1, ~
                    which disallows the initializer, ~
                    but the initializer ~x2 is present."
                   ident type initdeclor.initer?))
         ((mv info? currentp) (vstate-lookup-ord ident vstate))
         (defstatus (if (type-case type :function)
                        (valid-defstatus-undefined)
                      (if (> (vstate-num-scopes vstate) 1)
                          (if (linkage-case linkage :external)
                              (valid-defstatus-undefined)
                            (valid-defstatus-defined))
                        (if initdeclor.initer?
                            (valid-defstatus-defined)
                          (if (member-equal (stor-spec-extern)
                                            (stor-spec-list-fix storspecs))
                              (valid-defstatus-undefined)
                            (valid-defstatus-tentative))))))
         ((mv uid vstate)
          (if (and info? currentp (valid-ord-info-case info? :objfun))
              (mv (valid-ord-info-objfun->uid info?) vstate)
            (vstate-get-fresh-uid ident linkage vstate)))
         (new-info (make-valid-ord-info-objfun
                    :type type
                    :linkage linkage
                    :defstatus defstatus
                    :uid uid))
         (vstate (vstate-add-ord ident new-info vstate))
         (anno-info (make-init-declor-info :type type
                                           :typedefp nil
                                           :uid? uid))
         ((erp new-initer? more-types vstate)
          (valid-initer-option initdeclor.initer? type lifetime? vstate))
         ((when (and (linkage-case linkage :external)
                     (let ((ext-info? (vstate-lookup-ext ident vstate)))
                       (and ext-info?
                            (not (type-compatible-p
                                  (valid-ext-info->type ext-info?)
                                  type
                                  (vstate->completions vstate)
                                  ienv))))))
          (retmsg$ "The identifier ~x0 with external linkage and type ~x1 ~
                    was previously declared with incompatible type ~x2."
                   ident
                   type
                   (valid-ext-info->type
                    (vstate-lookup-ext ident vstate))))
         ((when (and (linkage-case linkage :external)
                     (vstate-has-internalp ident vstate)))
          (retmsg$ "The identifier ~x0 with external linkage ~
                    was previously declared with internal linkage ~
                    in the same translation unit."
                   ident))
         ((when (and (linkage-case linkage :internal)
                     (let ((ext-info? (vstate-lookup-ext ident vstate)))
                       (and ext-info?
                            (in (vstate->filepath vstate)
                                (valid-ext-info->declared-in ext-info?))))))
          (retmsg$ "The identifier ~x0 with internal linkage ~
                    was previously declared with external linkage ~
                    in the same translation unit."
                   ident))
         ((when (not info?))
          (retok (make-init-declor :declor new-declor
                                   :asm? initdeclor.asm?
                                   :attribs initdeclor.attribs
                                   :initer? new-initer?
                                   :info anno-info)
                 (set::union types more-types)
                 vstate))
         ((when (or (valid-ord-info-case info? :typedef)
                    (valid-ord-info-case info? :enumconst)))
          (if currentp
              (retmsg$ "The identifier ~x0 ~
                        is already declared in the current scope ~
                        with associated information ~x1."
                       ident info?)
            (retok (make-init-declor :declor new-declor
                                     :asm? initdeclor.asm?
                                     :attribs initdeclor.attribs
                                     :initer? new-initer?
                                     :info anno-info)
                   (set::union types more-types)
                   vstate)))
         ((valid-ord-info-objfun info) info?)
         ((when (or (linkage-case linkage :none)
                    (linkage-case info.linkage :none)))
          (if currentp
              (retmsg$ "The identifier ~x0 ~
                        is already declared in the current scope ~
                        with associated information ~x1."
                       ident info?)
            (retok (make-init-declor :declor new-declor
                                     :asm? initdeclor.asm?
                                     :attribs initdeclor.attribs
                                     :initer? new-initer?
                                     :info anno-info)
                   (set::union types more-types)
                   vstate)))
         ((unless (or (equal type info.type)
                      (equal type (type-unknown))
                      (equal info.type (type-unknown))))
          (retmsg$ "The identifier ~x0 ~
                    is declared with type ~x1 ~
                    after being declared with type ~x2."
                   ident type info.type))
         ((when (and (linkage-case linkage :internal)
                     (linkage-case info.linkage :external)))
          (retmsg$ "The identifier ~x0 ~
                    is declared with internal linkage ~
                    after being declared with external linkage."
                   ident))
         ((when (and (linkage-case linkage :external)
                     (linkage-case info.linkage :internal)))
          (raise "Internal error: ~ the identifier ~x0 ~
                  is declared with external linkage ~
                  after being declared with internal linkage."
                 ident)
          (retmsg$ "")))
      (retok (make-init-declor :declor new-declor
                               :asm? initdeclor.asm?
                               :attribs initdeclor.attribs
                               :initer? new-initer?
                               :info anno-info)
             (set::union types more-types)
             vstate))
    :no-function nil
    :measure (acl2::two-nats-measure (init-declor-count initdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-init-declor-list ((initdeclors init-declor-listp)
                                  (type typep)
                                  (storspecs stor-spec-listp)
                                  (vstate vstatep))
    :guard (init-declor-list-unambp initdeclors)
    :returns (mv (erp maybe-msgp)
                 (new-initdeclors init-declor-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type and storage class specifiers come from
       the declaration specifiers that precede the initializer declarators.
       We validate each in turn."))
    (b* (((reterr) nil nil (irr-vstate))
         ((when (endp initdeclors)) (retok nil nil (vstate-fix vstate)))
         ((erp new-initdeclor types vstate)
          (valid-init-declor (car initdeclors) type storspecs vstate))
         ((erp new-initdeclors more-types vstate)
          (valid-init-declor-list (cdr initdeclors) type storspecs vstate)))
      (retok (cons new-initdeclor new-initdeclors)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (init-declor-list-count initdeclors) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declon ((declon declonp) (vstate vstatep))
    :guard (declon-unambp declon)
    :returns (mv (erp maybe-msgp)
                 (new-declon declonp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "If it is a static assertion declaration,
       we validate it using a separate validation function.
       Otherwise, we first validate the declaration specifiers
       and then the list of initializer declarators,
       passing information from the former to the latter.
       We ensure that the list of initializer declarators is not empty
       (i.e. there is at least a declarator),
       or the declaration specifiers declare a tag,
       as required in [C17:6.7/2].
       We ignore the GCC extension for now."))
    (b* (((reterr) (irr-declon) nil (irr-vstate)))
      (declon-case
       declon
       :declon
       (b* (((erp new-specs type storspecs types vstate)
             (valid-decl-spec-list declon.specs nil nil nil vstate))
            ((when (and (endp declon.declors)
                        (not (type-case type :struct))
                        (not (type-case type :union))
                        (not (type-case type :enum))))
             (retmsg$ "The declaration ~x0 declares ~
                       neither a declarator nor a tag."
                      (declon-fix declon)))
            ((erp new-declors more-types vstate)
             (valid-init-declor-list declon.declors type storspecs vstate)))
         (retok (make-declon-declon :extension declon.extension
                                    :specs new-specs
                                    :declors new-declors)
                (set::union types more-types)
                vstate))
       :statassert
       (b* (((erp new-statassert types vstate)
             (valid-statassert declon.statassert vstate)))
         (retok (declon-statassert new-statassert) types vstate))))
    :measure (acl2::two-nats-measure (declon-count declon) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declon-list ((declons declon-listp)
                             (vstate vstatep))
    :guard (declon-list-unambp declons)
    :returns (mv (erp maybe-msgp)
                 (new-declons declon-listp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each one in turn."))
    (b* (((reterr) nil nil (irr-vstate))
         ((when (endp declons)) (retok nil nil (vstate-fix vstate)))
         ((erp new-declon types vstate) (valid-declon (car declons) vstate))
         ((erp new-declons more-types vstate)
          (valid-declon-list (cdr declons) vstate)))
      (retok (cons new-declon new-declons)
             (set::union types more-types)
             vstate))
    :measure (acl2::two-nats-measure (declon-list-count declons) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-label ((label labelp) (vstate vstatep))
    :guard (label-unambp label)
    :returns (mv (erp maybe-msgp)
                 (new-label labelp)
                 (return-types type-setp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a label."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now this just amounts to validating the constant expression(s),
       for the case of a @('case') label,
       and ensuring it/they has/have integer type [C17:6.8.4.2/3];
       in the future, we should collect labels in the validation table
       so that we can check that referenced labels are in scope.
       Also, for now we do not check that @('case') and @('default') labels
       only appear in @('switch') statements [C17:6.8.1/2]."))
    (b* (((reterr) (irr-label) nil (irr-vstate)))
      (label-case
       label
       :name
       (retok (label-fix label) nil (vstate-fix vstate))
       :casexpr
       (b* (((erp new-expr type types vstate)
             (valid-const-expr label.expr vstate))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (retmsg$ "The first or only 'case' expression ~
                       in the label ~x0 has type ~x1."
                      (label-fix label) type))
            ((erp new-range? type? more-types vstate)
             (valid-const-expr-option label.range? vstate))
            ((when (and type?
                        (not (type-integerp type?))
                        (not (type-case type? :unknown))))
             (retmsg$ "The second 'case' expression~
                       in the label ~x0 has type ~x1."
                      (label-fix label) type?)))
         (retok (make-label-casexpr :expr new-expr :range? new-range?)
                (set::union types more-types)
                vstate))
       :default
       (retok (label-default) nil (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (label-count label) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-stmt ((stmt stmtp) (vstate vstatep))
    :guard (stmt-unambp stmt)
    :returns (mv (erp maybe-msgp)
                 (new-stmt stmtp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return,
       besides an updated validation table,
       also two pieces of type information.")
     (xdoc::p
      "The first piece is the set of types returned by the statement,
       via @('return') statements, with or without expressions.
       This is a set because a statement may contain
       multiple @('return') sub-statements.
       A @('return') statement with an expression
       contributes the type of the expression to the set;
       a @('return') statement without an expression
       contributes the type @('void') to the set.")
     (xdoc::p
      "The second piece of information is as follows.
       If the statement is either a (possibly labeled) expression statement,
       or is a (possibly labeled) compound one
       whose last block item is an expression statement,
       the second piece of information is the type of that expression.
       If the statement is not an expression or compound,
       or it is compound but does not end in an expression statement
       (including the case in which the compound statement has no block items),
       the second piece of information is @('nil').
       The reason for having this second piece of information
       is to support the validation of GCC statement expressions"
      (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html"
                   "[GCCM:6.12.1]")
      ".")
     (xdoc::p
      "To validate a labeled statement,
       we validate its label, and then the enclosed statement.
       We return the union of the return types,
       and the optional type from the statement.
       For now we do not check the requirements in
       [C17:6.8.1/2] and [C17:6.8.1/3].")
     (xdoc::p
      "To validate a compound statement,
       we push a new scope for the block,
       and we validate the list of block items.
       We pop the scope and we return the same results
       coming from the validation of the block items.")
     (xdoc::p
      "To validate an expression statement,
       we validate the expression if present,
       and return its type as the second result;
       this is @('nil') if there is no expression.
       The return types are the same as the ones of the expression.")
     (xdoc::p
      "A selection statement and its sub-statements are blocks [C17:6.8.4/3],
       so we push and pop scopes accordingly.
       We check that the test of @('if') has scalar type [C17:6.8.4.1/1]
       and that the target of @('switch') has integer type [C17:6.8.4.2/1].
       No type is returned as the @('last-expr-type?') result,
       because a selection statement is not an expression statement
       (see criterion above for that result of this validation function).")
     (xdoc::p
      "An iteration statement and its sub-statements are blocks [C17:6.8.5/5],
       so we push and pop scopes accordingly.
       We check that the test expression has scalar type.
       No type is returned as the @('last-expr-type?') result,
       because an iteraion statement is not an expression statement
       (see criterion above for that result of this validation function).
       For now we do not enforce that the declaration in a @('for')
       only uses the storage class specifiers @('auto') and @('register').")
     (xdoc::p
      "For now we do not check constraints on
       the label of a @('goto') [C17:6.8.6.1/1],
       the occurrence of @('continue') [C17:6.8.6.2/2],
       and the occurrence of @('break') [C17:6.8.6.3/1].")
     (xdoc::p
      "A @('return') statement explicitly adds a type to the return types,
       either the type of the expression,
       or @('void') is there is no expression.
       We check the constraints on occurrences [C17:6.8.6.4/1]
       in the validation function for function definitions.")
     (xdoc::p
      "For now we do not check any constraints on assembler statements."))
    (b* (((reterr) (irr-stmt) nil nil (irr-vstate)))
      (stmt-case
       stmt
       :labeled
       (b* (((erp new-label types vstate) (valid-label stmt.label vstate))
            ((erp new-stmt more-types type? vstate)
             (valid-stmt stmt.stmt vstate)))
         (retok (make-stmt-labeled :label new-label :stmt new-stmt)
                (set::union types more-types)
                type?
                vstate))
       :compound
       (b* (((erp new-cstmt types type? vstate)
             (valid-comp-stmt stmt.stmt nil vstate)))
         (retok (stmt-compound new-cstmt) types type? vstate))
       :expr
       (b* (((erp new-expr? type? types vstate)
             (valid-expr-option stmt.expr? vstate)))
         (retok (make-stmt-expr :expr? new-expr? :info nil)
                types
                type?
                vstate))
       :null-attrib
       (retok (stmt-null-attrib stmt.attrib) nil nil (vstate-fix vstate))
       :if
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-test test-type test-types vstate)
             (valid-expr stmt.test vstate))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (vstate (vstate-push-scope vstate))
            ((erp new-then then-types & vstate)
             (valid-stmt stmt.then vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-if :test new-test :then new-then)
                (set::union test-types then-types)
                nil
                vstate))
       :ifelse
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-test test-type test-types vstate)
             (valid-expr stmt.test vstate))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (vstate (vstate-push-scope vstate))
            ((erp new-then then-types & vstate)
             (valid-stmt stmt.then vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-push-scope vstate))
            ((erp new-else else-types & vstate)
             (valid-stmt stmt.else vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-ifelse :test new-test :then new-then :else new-else)
                (set::union test-types (set::union then-types else-types))
                nil
                vstate))
       :switch
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-target target-type target-types vstate)
             (valid-expr stmt.target vstate))
            ((unless (or (type-integerp target-type)
                         (type-case target-type :unknown)))
             (retmsg$ "The target of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) target-type))
            (vstate (vstate-push-scope vstate))
            ((erp new-body body-types & vstate)
             (valid-stmt stmt.body vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-switch :target new-target :body new-body)
                (set::union target-types body-types)
                nil
                vstate))
       :while
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-test test-type test-types vstate)
             (valid-expr stmt.test vstate))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (vstate (vstate-push-scope vstate))
            ((erp new-body  body-types & vstate)
             (valid-stmt stmt.body vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate))
            (types (set::union test-types body-types)))
         (retok (make-stmt-while :test new-test :body new-body)
                types
                nil
                vstate))
       :dowhile
       (b* ((vstate (vstate-push-scope vstate))
            (vstate (vstate-push-scope vstate))
            ((erp new-body body-types & vstate)
             (valid-stmt stmt.body vstate))
            (vstate (vstate-pop-scope vstate))
            ((erp new-test test-type test-types vstate)
             (valid-expr stmt.test vstate))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-dowhile :body new-body :test new-test)
                (set::union test-types body-types)
                nil
                vstate))
       :for-expr
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-init & init-types vstate)
             (valid-expr-option stmt.init vstate))
            ((erp new-test test-type? test-types vstate)
             (valid-expr-option stmt.test vstate))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type?))
            ((erp new-next & next-types vstate)
             (valid-expr-option stmt.next vstate))
            (vstate (vstate-push-scope vstate))
            ((erp new-body body-types & vstate) (valid-stmt stmt.body vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-for-expr :init new-init
                                    :test new-test
                                    :next new-next
                                    :body new-body)
                (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                vstate))
       :for-declon
       (b* ((vstate (vstate-push-scope vstate))
            ((erp new-init init-types vstate) (valid-declon stmt.init vstate))
            ((erp new-test test-type? test-types vstate)
             (valid-expr-option stmt.test vstate))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type?))
            ((erp new-next & next-types vstate)
             (valid-expr-option stmt.next vstate))
            (vstate (vstate-push-scope vstate))
            ((erp new-body body-types & vstate)
             (valid-stmt stmt.body vstate))
            (vstate (vstate-pop-scope vstate))
            (vstate (vstate-pop-scope vstate)))
         (retok (make-stmt-for-declon :init new-init
                                      :test new-test
                                      :next new-next
                                      :body new-body)
                (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                vstate))
       :for-ambig
       (prog2$ (impossible) (retmsg$ ""))
       :goto
       (retok (stmt-goto stmt.label) nil nil (vstate-fix vstate))
       :gotoe
       (b* (((erp new-label type types vstate)
             (valid-expr stmt.label vstate)))
         (retok (stmt-gotoe new-label)
                (set::insert type types)
                nil
                vstate))
       :continue
       (retok (stmt-continue) nil nil (vstate-fix vstate))
       :break
       (retok (stmt-break) nil nil (vstate-fix vstate))
       :return
       (b* (((erp new-expr? type? types vstate)
             (valid-expr-option stmt.expr? vstate))
            (return-type (or type? (type-void))))
         (retok (make-stmt-return :expr? new-expr? :info nil)
                (set::insert return-type types)
                nil
                vstate))
       :return-attrib
       (b* (((erp new-expr type types vstate)
             (valid-expr stmt.expr vstate)))
         (retok (make-stmt-return-attrib :attrib stmt.attrib
                                         :expr new-expr)
                (set::insert type types)
                nil
                vstate))
       :asm
       (retok (stmt-asm stmt.stmt) nil nil (vstate-fix vstate))))
    :measure (acl2::two-nats-measure (stmt-count stmt) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-comp-stmt ((cstmt comp-stmtp)
                           (fundefp booleanp)
                           (vstate vstatep))
    :guard (comp-stmt-unambp cstmt)
    :returns (mv (erp maybe-msgp)
                 (new-cstmt comp-stmtp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a compound statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the modification that
       the @('last-expr-type?') result is a type exactly when
       the list of block items is not empty
       and the validation of the last block item
       returns a type as that result.")
     (xdoc::p
      "The @('fundefp') flag says whether the compound statement
       is the body of a function definition.
       If that is the case, we do not push a new scope and then pop it,
       because that is already done in @(tsee valid-fundef):
       the body itself of the function does not start a new scope;
       it is the function definition itself that starts a new scope,
       involving the parameters."))
    (b* (((reterr) (irr-comp-stmt) nil nil (irr-vstate))
         ((comp-stmt cstmt) cstmt)
         (vstate (if fundefp vstate (vstate-push-scope vstate)))
         ((erp new-items types last-expr-type? vstate)
          (valid-block-item-list cstmt.items vstate))
         (vstate (if fundefp vstate (vstate-pop-scope vstate))))
      (retok (make-comp-stmt :labels cstmt.labels :items new-items)
             types
             last-expr-type?
             vstate))
    :measure (acl2::two-nats-measure (comp-stmt-count cstmt) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item ((item block-itemp)
                            (vstate vstatep))
    :guard (block-item-unambp item)
    :returns (mv (erp maybe-msgp)
                 (new-item block-itemp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the slight modification that
       the @('last-expr-type?') result is a type exactly when
       the block item is a compound statement
       whose last block item is an expression statement,
       in which case the @('last-expr-type?') result is
       the type of that expression.")
     (xdoc::p
      "If the block item is a declaration,
       the @('last-expr-type?') result is @('nil'),
       because the block item is not a statement of the kind
       described in @(tsee valid-stmt)."))
    (b* (((reterr) (irr-block-item) nil nil (irr-vstate)))
      (block-item-case
       item
       :declon (b* (((erp new-declon types vstate)
                     (valid-declon item.declon vstate)))
                 (retok (make-block-item-declon :declon new-declon :info nil)
                        types
                        nil
                        vstate))
       :stmt (b* (((erp new-stmt types last-expr-type? vstate)
                   (valid-stmt item.stmt vstate)))
               (retok (make-block-item-stmt :stmt new-stmt :info nil)
                      types
                      last-expr-type?
                      vstate))
       :ambig (prog2$ (impossible) (retmsg$ ""))))
    :measure (acl2::two-nats-measure (block-item-count item) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item-list ((items block-item-listp)
                                 (vstate vstatep))
    :guard (block-item-list-unambp items)
    :returns (mv (erp maybe-msgp)
                 (new-items block-item-listp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-vstate vstatep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the modification that
       the @('last-expr-type?') result is a type exactly when
       the list of block items is not empty
       and the validation of the last block item
       returns a type as that result."))
    (b* (((reterr) nil nil nil (irr-vstate))
         ((when (endp items)) (retok nil nil nil (vstate-fix vstate)))
         ((erp new-item types last-expr-type? vstate)
          (valid-block-item (car items) vstate))
         ((when (endp (cdr items)))
          (retok (list new-item) types last-expr-type? vstate))
         ((erp new-items more-types last-expr-type? vstate)
          (valid-block-item-list (cdr items) vstate)))
      (retok (cons new-item new-items)
             (set::union types more-types)
             last-expr-type?
             vstate))
    :measure (acl2::two-nats-measure (block-item-list-count items) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :ruler-extenders :all

  :verify-guards nil ; done below

  :prepwork
  ((local (in-theory (enable acons)))

   ;; The following theorems are (for some reason)
   ;; necessary for the termination proof.

   (defrulel expr-count-min-when-complit-linear
     (implies (expr-case expr :complit)
              (<= 4 (expr-count expr)))
     :rule-classes :linear
     :expand (expr-count expr))

   (defrulel dirdeclor-count-when-function-linear
     (implies (equal (dirdeclor-kind dirdeclor) :function-params)
              (<= 4 (dirdeclor-count dirdeclor)))
     :rule-classes :linear
     :expand (dirdeclor-count dirdeclor))

   (defrulel dirabsdeclor-count-when-function-linear
     (implies (equal (dirabsdeclor-kind dirabsdeclor) :function)
              (<= 4 (dirabsdeclor-count dirabsdeclor)))
     :rule-classes :linear
     :expand (dirabsdeclor-count dirabsdeclor)))

  ///

  (verify-guards valid-expr)

  (fty::deffixequiv-mutual valid-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual valid-exprs/decls/stmts
    (defret expr-unambp-of-valid-expr
      (implies (not erp)
               (expr-unambp new-expr))
      :hyp (expr-unambp expr)
      :fn valid-expr)
    (defret expr-list-unambp-of-valid-expr-list
      (implies (not erp)
               (expr-list-unambp new-exprs))
      :hyp (expr-list-unambp exprs)
      :fn valid-expr-list)
    (defret expr-option-unambp-of-valid-expr-option
      (implies (not erp)
               (expr-option-unambp new-expr?))
      :hyp (expr-option-unambp expr?)
      :fn valid-expr-option)
    (defret const-expr-unambp-of-valid-const-expr
      (implies (not erp)
               (const-expr-unambp new-cexpr))
      :hyp (const-expr-unambp cexpr)
      :fn valid-const-expr)
    (defret const-expr-option-unambp-of-valid-const-expr-option
      (implies (not erp)
               (const-expr-option-unambp new-cexpr?))
      :hyp (const-expr-option-unambp cexpr?)
      :fn valid-const-expr-option)
    (defret genassoc-unambp-of-valid-genassoc
      (implies (not erp)
               (genassoc-unambp new-genassoc))
      :hyp (genassoc-unambp genassoc)
      :fn valid-genassoc)
    (defret genassoc-list-unambp-of-valid-genassoc-list
      (implies (not erp)
               (genassoc-list-unambp new-genassocs))
      :hyp (genassoc-list-unambp genassocs)
      :fn valid-genassoc-list)
    (defret member-designor-unambp-of-valid-member-designor
      (implies (not erp)
               (member-designor-unambp new-memdesign))
      :hyp (member-designor-unambp memdesign)
      :fn valid-member-designor)
    (defret type-spec-unambp-of-valid-type-spec
      (implies (not erp)
               (and (type-spec-unambp new-tyspec)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-list-unambp tyspecs))
      :fn valid-type-spec)
    (defret spec/qual-unambp-of-valid-spec/qual
      (implies (not erp)
               (and (spec/qual-unambp new-specqual)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (spec/qual-unambp specqual)
                (type-spec-list-unambp tyspecs))
      :fn valid-spec/qual)
    (defret spec/qual-list-unambp-of-valid-spec/qual-list
      (implies (not erp)
               (spec/qual-list-unambp new-specquals))
      :hyp (and (spec/qual-list-unambp specquals)
                (type-spec-list-unambp tyspecs))
      :fn valid-spec/qual-list)
    (defret align-spec-unambp-of-valid-align-spec
      (implies (not erp)
               (align-spec-unambp new-align))
      :hyp (align-spec-unambp align)
      :fn valid-align-spec)
    (defret decl-spec-unambp-of-valid-decl-spec
      (implies (not erp)
               (and (decl-spec-unambp new-declspec)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (decl-spec-unambp declspec)
                (type-spec-list-unambp tyspecs))
      :fn valid-decl-spec)
    (defret decl-spec-list-unambp-of-valid-decl-spec-list
      (implies (not erp)
               (decl-spec-list-unambp new-declspecs))
      :hyp (and (decl-spec-list-unambp declspecs)
                (type-spec-list-unambp tyspecs))
      :fn valid-decl-spec-list)
    (defret initer-unambp-of-valid-initer
      (implies (not erp)
               (initer-unambp new-initer))
      :hyp (initer-unambp initer)
      :fn valid-initer)
    (defret initer-option-unambp-of-valid-initer-option
      (implies (not erp)
               (initer-option-unambp new-initer?))
      :hyp (initer-option-unambp initer?)
      :fn valid-initer-option)
    (defret desiniter-unambp-of-valid-desiniter
      (implies (not erp)
               (desiniter-unambp new-desiniter))
      :hyp (desiniter-unambp desiniter)
      :fn valid-desiniter)
    (defret desiniter-list-unambp-of-valid-desiniter-list
      (implies (not erp)
               (desiniter-list-unambp new-desiniters))
      :hyp (desiniter-list-unambp desiniters)
      :fn valid-desiniter-list)
    (defret designor-unambp-of-valid-designor
      (implies (not erp)
               (designor-unambp new-designor))
      :hyp (designor-unambp designor)
      :fn valid-designor)
    (defret designor-list-unambp-of-valid-designor-list
      (implies (not erp)
               (designor-list-unambp new-designors))
      :hyp (designor-list-unambp designors)
      :fn valid-designor-list)
    (defret declor-unambp-of-valid-declor
      (implies (not erp)
               (declor-unambp new-declor))
      :hyp (declor-unambp declor)
      :fn valid-declor)
    (defret declor-option-unambp-of-valid-declor-option
      (implies (not erp)
               (declor-option-unambp new-declor?))
      :hyp (declor-option-unambp declor?)
      :fn valid-declor-option)
    (defret dirdeclor-unambp-of-valid-dirdeclor
      (implies (not erp)
               (dirdeclor-unambp new-dirdeclor))
      :hyp (dirdeclor-unambp dirdeclor)
      :fn valid-dirdeclor)
    (defret absdeclor-unambp-of-valid-absdeclor
      (implies (not erp)
               (absdeclor-unambp new-absdeclor))
      :hyp (absdeclor-unambp absdeclor)
      :fn valid-absdeclor)
    (defret absdeclor-option-unambp-of-valid-absdeclor-option
      (implies (not erp)
               (absdeclor-option-unambp new-absdeclor?))
      :hyp (absdeclor-option-unambp absdeclor?)
      :fn valid-absdeclor-option)
    (defret dirabsdeclor-unambp-of-valid-dirabsdeclor
      (implies (not erp)
               (dirabsdeclor-unambp new-dirabsdeclor))
      :hyp (dirabsdeclor-unambp dirabsdeclor)
      :fn valid-dirabsdeclor)
    (defret dirabsdeclor-option-unambp-of-valid-dirabsdeclor-option
      (implies (not erp)
               (dirabsdeclor-option-unambp new-dirabsdeclor?))
      :hyp (dirabsdeclor-option-unambp dirabsdeclor?)
      :fn valid-dirabsdeclor-option)
    (defret param-declon-unambp-of-valid-param-declon
      (implies (not erp)
               (param-declon-unambp new-paramdecl))
      :hyp (param-declon-unambp paramdecl)
      :fn valid-param-declon)
    (defret param-declon-list-unambp-of-valid-param-declon-list
      (implies (not erp)
               (param-declon-list-unambp new-paramdecls))
      :hyp (param-declon-list-unambp paramdecls)
      :fn valid-param-declon-list)
    (defret param-declor-unambp-of-valid-param-declor
      (implies (not erp)
               (param-declor-unambp new-paramdeclor))
      :hyp (param-declor-unambp paramdeclor)
      :fn valid-param-declor)
    (defret tyname-unambp-of-valid-tyname
      (implies (not erp)
               (tyname-unambp new-tyname))
      :hyp (tyname-unambp tyname)
      :fn valid-tyname)
    (defret struni-spec-unambp-of-valid-struni-spec
      (implies (not erp)
               (struni-spec-unambp new-struni-spec))
      :hyp (struni-spec-unambp struni-spec)
      :fn valid-struni-spec)
    (defret struct-declon-unambp-of-valid-struct-declon
      (implies (not erp)
               (struct-declon-unambp new-structdeclon))
      :hyp (struct-declon-unambp structdeclon)
      :fn valid-struct-declon)
    (defret struct-declon-list-unambp-of-valid-struct-declon-list
      (implies (not erp)
               (struct-declon-list-unambp new-structdeclons))
      :hyp (struct-declon-list-unambp structdeclons)
      :fn valid-struct-declon-list)
    (defret struct-declor-unambp-of-valid-struct-declor
      (implies (not erp)
               (struct-declor-unambp new-structdeclor))
      :hyp (struct-declor-unambp structdeclor)
      :fn valid-struct-declor)
    (defret struct-declor-list-unambp-of-valid-struct-declor-list
      (implies (not erp)
               (struct-declor-list-unambp new-structdeclors))
      :hyp (struct-declor-list-unambp structdeclors)
      :fn valid-struct-declor-list)
    (defret enum-spec-unambp-of-valid-enum-spec
      (implies (not erp)
               (enum-spec-unambp new-enumspec))
      :hyp (enum-spec-unambp enumspec)
      :fn valid-enum-spec)
    (defret enumer-unambp-of-valid-enumer
      (implies (not erp)
               (enumer-unambp new-enumer))
      :hyp (enumer-unambp enumer)
      :fn valid-enumer)
    (defret enumer-list-unambp-of-valid-enumer-list
      (implies (not erp)
               (enumer-list-unambp new-enumers))
      :hyp (enumer-list-unambp enumers)
      :fn valid-enumer-list)
    (defret statassert-unambp-of-valid-statassert
      (implies (not erp)
               (statassert-unambp new-statassert))
      :hyp (statassert-unambp statassert)
      :fn valid-statassert)
    (defret init-declor-unambp-of-valid-init-declor
      (implies (not erp)
               (init-declor-unambp new-initdeclor))
      :hyp (init-declor-unambp initdeclor)
      :fn valid-init-declor
      :hints
      ('(:expand ((valid-init-declor initdeclor type storspecs vstate)))))
    (defret init-declor-list-unambp-of-valid-init-declor-list
      (implies (not erp)
               (init-declor-list-unambp new-initdeclors))
      :hyp (init-declor-list-unambp initdeclors)
      :fn valid-init-declor-list)
    (defret declon-unambp-of-valid-declon
      (implies (not erp)
               (declon-unambp new-declon))
      :hyp (declon-unambp declon)
      :fn valid-declon)
    (defret declon-list-unambp-of-valid-declon-list
      (implies (not erp)
               (declon-list-unambp new-declons))
      :hyp (declon-list-unambp declons)
      :fn valid-declon-list)
    (defret label-unambp-of-valid-label
      (implies (not erp)
               (label-unambp new-label))
      :hyp (label-unambp label)
      :fn valid-label)
    (defret stmt-unambp-of-valid-stmt
      (implies (not erp)
               (stmt-unambp new-stmt))
      :hyp (stmt-unambp stmt)
      :fn valid-stmt)
    (defret comp-stmt-unambp-of-valid-comp-stmt
      (implies (not erp)
               (comp-stmt-unambp new-cstmt))
      :hyp (comp-stmt-unambp cstmt)
      :fn valid-comp-stmt)
    (defret block-item-unambp-of-valid-block-item
      (implies (not erp)
               (block-item-unambp new-item))
      :hyp (block-item-unambp item)
      :fn valid-block-item)
    (defret block-item-list-unambp-of-valid-block-item-list
      (implies (not erp)
               (block-item-list-unambp new-items))
      :hyp (block-item-list-unambp items)
      :fn valid-block-item-list)
    ;; These hints only enable VALID-DECL-SPEC-LIST
    ;; in the cases involving that function.
    ;; Without this, the proof seems to hang, or at least take a very long time.
    :hints
    (("Goal" :in-theory (disable valid-decl-spec-list))
     (cond ((acl2::occur-lst '(acl2::flag-is 'valid-decl-spec-list) clause)
            '(:in-theory (enable valid-decl-spec-list)))
           ((acl2::occur-lst '(acl2::flag-is 'valid-initer) clause)
            '(:expand ((valid-initer initer ctx lifetime vstate steps))))
           ((acl2::occur-lst '(acl2::flag-is 'valid-dirdeclor) clause)
            '(:expand ((valid-dirdeclor dirdeclor fundef-params-p type vstate)
                       (valid-dirdeclor dirdeclor nil type vstate)
                       (valid-dirdeclor dirdeclor t type vstate))))
           ((acl2::occur-lst '(acl2::flag-is 'valid-dirabsdeclor) clause)
            '(:expand ((valid-dirabsdeclor dirabsdeclor type vstate))))
           (t nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fundef ((fundef fundefp) (vstate vstatep))
  :guard (fundef-unambp fundef)
  :returns (mv (erp maybe-msgp)
               (new-fundef fundefp)
               (new-vstate vstatep))
  :short "Validate a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we ignore all the GCC extensions.
     We validate the declaration specifiers, then the declarator.
     It is an error if the validation of the declarator
     returns a non-empty set of types,
     because it means that there are statement expressions
     with return statements in them,
     which can only happen inside a function's body.
     We validate the storage class specifiers.
     It is an error if the declaration is for a @('typedef').
     We also ensure that the type is the function type [C17:6.9.1/2].")
   (xdoc::p
    "As with declarations, the scope of the function name
     starts just after its declarator;
     it must be added to the file scope of the validation table.
     However, recall that the validation of the declarator
     pushes a new scope for the outermost block of the function definition.
     Thus, instead of using @(tsee vstate-add-ord) to add the function,
     we use @(tsee vstate-add-ord-file-scope).
     But before adding it, we need to look it up,
     and again in the file scope, not the block scope
     (it is in fact legal for a function parameter
     to have the same name as the function:
     its scope is the block, and it hides the function name there);
     so we use @(tsee vstate-lookup-ord-file-scope)
     instead of the usual @(tsee vstate-lookup-ord).")
   (xdoc::p
    "If the name of the function is not found in the file scope,
     we add it to the file scope, with the appropriate information.
     Note that the definition status is defined,
     since we are validating a function definition.
     If the name is found already, and does not denote a function,
     it is an error;
     it is also an error if the linkages do not match.
     And it is an error if the function is alread defined.
     If all the checks pass, we add the function to the table,
     which overwrites the previous entry,
     but the only information actually overwritten
     is the definition status, from undefined to defined,
     which is appropriate.")
   (xdoc::p
    "The declarations between declarator and body should be present
     if and only if the function declarator has a list of identifiers,
     and there should be exactly one declaration per identifier
     [C17:6.9.1/5] [C17:6.9.1/6].
     For now we do not check those constraints,
     but we validate any declarations
     (ensuring they return no types),
     which will add entries to the block scope in the validation table.")
   (xdoc::p
    "We extend the validation table with the identifier @('__func__')
     [C17:6.4.2.2].
     In our currently approximate type system, this has @('char') array type
     (the @('const') type qualifier is ignored).
     If the GCC/Clang flag is enabled (i.e. GCC/Clang extensions are allowed),
     we further extend the table with the identifiers @('__FUNCTION__') and
     @('__PRETTY_FUNCTION__') "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Function-Names.html"
                 "[GCCM:6.12.24]")
    ".")
   (xdoc::p
    "We ensure that the body is a compound statement,
     and we validate directly the block items;
     this way, we do not push an extra scope,
     because the outer scope must include the parameters.
     In our approximate type system,
     the function type alone does not give us enough information
     to check the types returned by the body
     against the return type of the function,
     to enforce the constraints in [C17:6.8.6.4/1];
     so for now we discard the set of return types
     obtained by validating the body.")
   (xdoc::p
    "Finally we pop the scope of the function body.
     Recall that the function itself stays in the validation table,
     because we have added it to the file scope."))
  (b* (((reterr) (irr-fundef) (irr-vstate))
       ((fundef fundef) fundef)
       (ienv (vstate->ienv vstate))
       ((erp new-specs type storspecs types vstate)
        (valid-decl-spec-list fundef.specs nil nil nil vstate))
       ((erp new-declor type ident more-types vstate)
        (valid-declor fundef.declor t type vstate))
       ((unless (and (set::emptyp types)
                     (set::emptyp more-types)))
        (retmsg$ "The declarator of the function definition ~x0 ~
                  contains return statements."
                 (fundef-fix fundef)))
       ((erp typedefp linkage &)
        (valid-stor-spec-list storspecs ident type t vstate))
       ((when typedefp)
        (retmsg$ "The function definition ~x0 ~
                  declares a 'typedef' name instead of a function."
                 (fundef-fix fundef)))
       ((unless (type-case type :function))
        (retmsg$ "The function definition ~x0 has type ~x1."
                 (fundef-fix fundef) type))
       ((when (and (linkage-case linkage :external)
                   (let ((ext-info? (vstate-lookup-ext ident vstate)))
                     (and ext-info?
                          (not (type-compatible-p
                                (valid-ext-info->type ext-info?)
                                type
                                (vstate->completions vstate)
                                ienv))))))
        (retmsg$ "The function definition ~x0 ~
                  with external linkage and type ~x1 ~
                  was previously declared with incompatible type ~x2."
                 ident
                 type
                 (valid-ext-info->type
                  (vstate-lookup-ext ident vstate))))
       ((when (and (linkage-case linkage :external)
                   (vstate-has-internalp ident vstate)))
        (retmsg$ "The function definition ~x0 with external linkage ~
                  was previously declared with internal linkage ~
                  in the same translation unit."
                 ident))
       ((when (and (linkage-case linkage :internal)
                   (let ((ext-info? (vstate-lookup-ext ident vstate)))
                     (and ext-info?
                          (in (vstate->filepath vstate)
                              (valid-ext-info->declared-in ext-info?))))))
        (retmsg$ "The function definition ~x0 with internal linkage ~
                  was previously declared with external linkage ~
                  in the same translation unit."
                 ident))
       (info? (vstate-lookup-ord-file-scope ident vstate))
       ((erp fundef-uid vstate)
        (b* (((reterr) (irr-uid) (irr-vstate))
             ((when (not info?))
              (b* (((mv uid vstate) (vstate-get-fresh-uid ident linkage vstate))
                   (info (make-valid-ord-info-objfun
                          :type type
                          :linkage linkage
                          :defstatus (valid-defstatus-defined)
                          :uid uid)))
                (retok uid (vstate-add-ord-file-scope ident info vstate))))
             (info info?)
             ((unless (valid-ord-info-case info :objfun))
              (retmsg$ "The name of the function definition ~x0 ~
                        is already in the file scope, ~
                        but is not a function; ~
                        its associated information is ~x1."
                       (fundef-fix fundef) info))
             ((valid-ord-info-objfun info) info)
             ((unless (type-compatible-p info.type
                                         type
                                         (vstate->completions vstate)
                                         ienv))
              (retmsg$ "The name of the function definition ~x0 ~
                        is already in the file scope, ~
                        but it has type ~x1."
                       (fundef-fix fundef) info.type))
             ((unless (equal linkage info.linkage))
              (retmsg$ "The function definition ~x0 has linkage ~s1, ~
                        which is inconsistent with the linkage ~s2 ~
                        already present in the validation table."
                       (fundef-fix fundef)
                       (if (linkage-case linkage :external)
                           "external"
                         "internal")
                       (if (linkage-case info.linkage :external)
                           "external"
                         "internal")))
             ((when (valid-defstatus-case info.defstatus :defined))
              (retmsg$ "The function definition ~x0 ~
                        is a redefinition of the function."
                       (fundef-fix fundef)))
             ((mv uid vstate)
              (if (and info? (valid-ord-info-case info? :objfun))
                  (mv (valid-ord-info-objfun->uid info?) vstate)
                (vstate-get-fresh-uid ident linkage vstate)))
             (info (make-valid-ord-info-objfun
                    :type type
                    :linkage linkage
                    :defstatus (valid-defstatus-defined)
                    :uid uid)))
          (retok uid (vstate-add-ord-file-scope ident info vstate))))
       ((erp new-declons types vstate)
        (valid-declon-list fundef.declons vstate))
       ((unless (set::emptyp types))
        (retmsg$ "The declarations of the function definition ~x0 ~
                  contain return statements."
                 (fundef-fix fundef)))
       ((mv uid vstate) (vstate-get-fresh-uid ident (linkage-none) vstate))
       (vstate (vstate-add-ord (ident "__func__")
                              (make-valid-ord-info-objfun
                               :type (make-type-array :of (type-char)
                                                      :size nil) ; TODO: size
                               :linkage (linkage-none)
                               :defstatus (valid-defstatus-defined)
                               :uid uid)
                              vstate))
       ((mv uid vstate) (vstate-get-fresh-uid ident (linkage-none) vstate))
       (vstate (if (ienv->gcc/clang ienv)
                  (vstate-add-ord (ident "__FUNCTION__")
                                  (make-valid-ord-info-objfun
                                   :type (make-type-array :of (type-char)
                                                          :size nil) ; TODO: size
                                   :linkage (linkage-none)
                                   :defstatus (valid-defstatus-defined)
                                   :uid uid)
                                  vstate)
                vstate))
       ((mv uid vstate) (vstate-get-fresh-uid ident (linkage-none) vstate))
       (vstate (if (ienv->gcc/clang ienv)
                  (vstate-add-ord (ident "__PRETTY_FUNCTION__")
                                  (make-valid-ord-info-objfun
                                   :type (make-type-array :of (type-char)
                                                          :size nil) ; TODO: size
                                   :linkage (linkage-none)
                                   :defstatus (valid-defstatus-defined)
                                   :uid uid)
                                  vstate)
                vstate))
       ((erp new-body & & vstate) (valid-comp-stmt fundef.body t vstate))
       (vstate (vstate-pop-scope vstate))
       (info (make-fundef-info :type type
                               :uid fundef-uid)))
    (retok (make-fundef :extension fundef.extension
                        :specs new-specs
                        :declor new-declor
                        :asm? fundef.asm?
                        :attribs fundef.attribs
                        :declons new-declons
                        :body new-body
                        :info info)
           vstate))

  ///

  (defret fundef-unambp-of-valid-fundef
    (implies (not erp)
             (fundef-unambp new-fundef))
    :hyp (fundef-unambp fundef)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-ext-declon ((edecl ext-declonp) (vstate vstatep))
  :guard (ext-declon-unambp edecl)
  :returns (mv (erp maybe-msgp)
               (new-edecl ext-declonp)
               (new-vstate vstatep))
  :short "Validate an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not do anything with assembler statements.
     The empty external declaration is always valid.
     We check that declarations contain no return statements."))
  (b* (((reterr) (irr-ext-declon) (irr-vstate)))
    (ext-declon-case
     edecl
     :fundef (b* (((erp new-fundef vstate)
                   (valid-fundef edecl.fundef vstate)))
               (retok (ext-declon-fundef new-fundef) vstate))
     :declon (b* (((erp new-decl types vstate)
                   (valid-declon edecl.declon vstate))
                  ((unless (set::emptyp types))
                   (retmsg$ "The top-level declaration ~x0 ~
                           contains return statements."
                            edecl.declon)))
               (retok (ext-declon-declon new-decl) vstate))
     :empty (retok (ext-declon-empty) (vstate-fix vstate))
     :asm (retok (ext-declon-fix edecl) (vstate-fix vstate))))

  ///

  (defret ext-declon-unambp-of-valid-ext-declon
    (implies (not erp)
             (ext-declon-unambp new-edecl))
    :hyp (ext-declon-unambp edecl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-trans-item ((item trans-itemp) (vstate vstatep))
  :guard (trans-item-unambp item)
  :returns (mv (erp maybe-msgp)
               (new-items trans-item-listp)
               (new-vstate vstatep))
  :short "Validate a translation item."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function returns a list of translation items,
     to accommodate the case in which a @('#include') translation item
     must be expanded in place, which results in a list.
     In all other cases, the resulting list is a singleton,
     i.e. the translation item is disambiguated to a translation item.")
   (xdoc::p
    "For external declarations, we use a separate function.")
   (xdoc::p
    "@('#include') directives are not supported yet.")
   (xdoc::p
    "A @('#define') or @('#undef') directive
     is considered valid and undergoes no transformation,
     but it adds an entry (definition or undefinition) to the macro table.
     Recall that, as a translation item,
     a @('#define') directive is implicitly always
     an object-like macro whose replacement list is just the macro name.")
   (xdoc::p
    "Conditional directives are not supported yet.")
   (xdoc::p
    "Comments are always considered valid,
     and undergo no transformation."))
  (b* (((reterr) nil (irr-vstate)))
    (trans-item-case
     item
     :declon (b* (((erp new-declon vstate)
                   (valid-ext-declon item.declon vstate)))
               (retok (list (trans-item-declon new-declon)) vstate))
     :include (reterr
               (msg "Validator does not support #include directives yet."))
     :define (b* ((name (ident->unwrap item.macro))
                  ((unless (stringp name))
                   (raise "Internal error: macro name ~x0." name)
                   (reterr "irrelevant"))
                  (info (macro-info-object
                         (list (make-plexeme-ident :ident name
                                                   :provenance nil))))
                  (table (vstate->table vstate))
                  ((mv erp new-macros)
                   (macro-define name info (valid-table->macros table)))
                  ((unless (maybe-msgp erp))
                   (raise "Internal error: malformed error ~x0." erp)
                   (reterr "irrelevant"))
                  ((when erp) (mv erp nil (irr-vstate)))
                  (vstate (change-vstate
                            vstate
                            :table (change-valid-table
                                     table
                                     :macros new-macros))))
               (retok (list (trans-item-fix item)) vstate))
     :undef (b* ((name (ident->unwrap item.macro))
                 ((unless (stringp name))
                  (raise "Internal error: macro name ~x0." name)
                  (reterr "irrelevant"))
                 (table (vstate->table vstate))
                 ((mv erp new-macros)
                  (macro-undefine name (valid-table->macros table)))
                 ((unless (maybe-msgp erp))
                  (raise "Internal error: malformed error ~x0." erp)
                  (reterr "irrelevant"))
                 ((when erp) (mv erp nil (irr-vstate)))
                 (vstate (change-vstate
                           vstate
                           :table
                           (change-valid-table
                             table
                             :macros new-macros))))
              (retok (list (trans-item-fix item)) vstate))
     :cond (reterr
            (msg "Validator does not support conditional directives yet."))
     :line-comment (retok (list (trans-item-fix item)) (vstate-fix vstate))))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable plexeme-token/space-p
                                           plexeme-tokenp)))
  :hooks (:fix)

  ///

  (more-returns
   (new-items true-listp :rule-classes (:rewrite :type-prescription)))

  (defret trans-item-list-unambp-of-valid-trans-item
    (implies (not erp)
             (trans-item-list-unambp new-items))
    :hyp (trans-item-unambp item)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-trans-item-list ((items trans-item-listp)
                               (vstate vstatep))
  :guard (trans-item-list-unambp items)
  :returns (mv (erp maybe-msgp)
               (new-items trans-item-listp)
               (new-vstate vstatep))
  :short "Validate a list of translation items."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate them in order, threading the validation table through."))
  (b* (((reterr) nil (irr-vstate))
       ((when (endp items)) (retok nil (vstate-fix vstate)))
       ((erp car-new-items vstate) (valid-trans-item (car items) vstate))
       ((erp cdr-new-items vstate) (valid-trans-item-list (cdr items) vstate)))
    (retok (append car-new-items cdr-new-items) vstate))

  ///

  (defret ext-declon-list-unambp-of-valid-ext-declon-list
    (implies (not erp)
             (trans-item-list-unambp new-items))
    :hyp (trans-item-list-unambp items)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-trans-unit ((filepath filepathp)
                          (tunit trans-unitp)
                          (vstate vstatep))
  :guard (trans-unit-unambp tunit)
  :returns (mv (erp maybe-msgp) (new-tunit trans-unitp) (new-vstate vstatep))
  :short "Validate a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the C dialect does not have any extensions,
     the initial validation table is the one
     returned by @(tsee init-valid-table).
     Otherwise, we add a number of objects and functions
     that we have encountered in practical code;
     we should eventually have a comprehensive list here.")
   (xdoc::p
    "Starting with the validation table as just described,
     we validate all the external declarations in the translation unit.
     Since these are translation units after preprocesing,
     all the referenced names must be declared in the translation unit,
     so it is appropriate to start with the initial validation table.")
   (xdoc::p
    "If validation is successful,
     we add the final validation table to
     the information slot of the translation unit,
     i.e. we annotate the translation unit with its final validation table.")
   (xdoc::p
    "For each built-in function, the associated information consists of
     an unknown function type, external linkage, and defined status.
     The latter two seem reasonable, given that these identifiers
     are visible and have the same meaning in every translation unit,
     and have their own (built-in) definitions.
     For each built-in object, the associated information consists of
     the unknown type, external linkage, and defined status;
     the rationale for the latter two is the same as for functions."))
  (b* (((reterr) (irr-trans-unit) (irr-vstate))
       ((vstate vstate) vstate)
       (dialect (ienv->dialect vstate.ienv))
       (vstate (change-vstate vstate :table (init-valid-table filepath dialect)))
       (vstate (vstate-add-ord-objfuns-file-scope
               (built-in-functions-for dialect)
               (make-type-function :ret (type-unknown)
                                   :params (type-params-unspecified))
               (linkage-external)
               (valid-defstatus-defined)
               vstate))
       (vstate (vstate-add-ord-objfuns-file-scope
               (built-in-vars-for dialect)
               (type-unknown)
               (linkage-external)
               (valid-defstatus-defined)
               vstate))
       ((erp new-items vstate)
        (valid-trans-item-list (trans-unit->items tunit) vstate))
       (info (make-trans-unit-info :table-end (vstate->table vstate))))
    (retok (make-trans-unit :items new-items
                            :info info)
           vstate))

  ///

  (defret trans-unit-unambp-of-valid-trans-unit
    (implies (not erp)
             (trans-unit-unambp new-tunit))
    :hyp (trans-unit-unambp tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-filepath-trans-unit-map ((tumap filepath-trans-unit-mapp)
                                       (keep-going booleanp)
                                       (vstate vstatep))
  :guard (filepath-trans-unit-map-unambp tumap)
  :returns (mv (erp maybe-msgp)
               (new-tumap filepath-trans-unit-mapp)
               (final-vstate vstatep))
  :short "Validate a map from file paths to translation units."
  (valid-filepath-trans-unit-map-loop (omap::keys
                                       (filepath-trans-unit-map-fix tumap))
                                      tumap
                                      keep-going
                                      vstate)

  :prepwork
  ((define valid-filepath-trans-unit-map-loop ((paths filepath-setp)
                                               (tumap filepath-trans-unit-mapp)
                                               (keep-going booleanp)
                                               (vstate vstatep))
     :guard (and (set::subset paths (omap::keys tumap))
                 (filepath-trans-unit-map-unambp tumap))
     :returns (mv (erp maybe-msgp)
                  (new-tumap filepath-trans-unit-mapp)
                  (final-vstate vstatep))
     :parents nil
     (b* (((reterr) nil (irr-vstate))
          ((when (set::emptyp (filepath-set-fix paths)))
           (retok nil (vstate-fix vstate)))
          (tumap (filepath-trans-unit-map-fix tumap))
          (path (set::head paths))
          (tunit (omap::lookup path tumap))
          ((mv erp new-tunit vstate)
           (valid-trans-unit path tunit vstate))
          ((when erp)
           (if keep-going
               (prog2$ (cw "Error in translation unit ~x0: ~@1~%"
                           (filepath->string path)
                           erp)
                       (valid-filepath-trans-unit-map-loop (set::tail paths)
                                                           tumap
                                                           keep-going
                                                           vstate))
             (retmsg$ "Error in translation unit ~x0: ~@1"
                      (filepath->string path)
                      erp)))
          ((erp new-tumap -) (valid-filepath-trans-unit-map-loop (set::tail paths)
                                                                 tumap
                                                                 keep-going
                                                                 vstate)))
       (retok (omap::update path new-tunit new-tumap)
              vstate))
     :no-function nil
     :prepwork ((local (in-theory (enable emptyp-of-filepath-set-fix))))
     :verify-guards :after-returns
     :guard-hints (("Goal" :in-theory (enable* omap::assoc-to-in-of-keys
                                               set::expensive-rules)))

     ///

     (defret
       filepath-trans-unit-map-unambp-of-valid-filepath-trans-unit-map-loop
       (implies (not erp)
                (filepath-trans-unit-map-unambp new-tumap))
       :hyp (and (filepath-trans-unit-mapp tumap)
                 (filepath-trans-unit-map-unambp tumap)
                 (set::subset (filepath-set-fix paths) (omap::keys tumap)))
       :hints (("Goal"
                :induct t
                :in-theory (enable* set::expensive-rules))))))

  ///

  (defret filepath-trans-unit-map-unambp-of-valid-filepath-trans-unit-map
    (implies (not erp)
             (filepath-trans-unit-map-unambp new-tumap))
    :hyp (and (filepath-trans-unit-mapp tumap)
              (filepath-trans-unit-map-unambp tumap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-trans-ensemble ((tuens trans-ensemblep)
                              (ienv ienvp)
                              (keep-going booleanp))
  :guard (trans-ensemble-unambp tuens)
  :returns (mv (erp maybe-msgp) (new-tuens trans-ensemblep))
  :short "Validate a translation ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate each translation unit,
     annotating each one with its final validation table.
     Information that accumulates across translation units
     (external linkage identifiers, type completions, and the UID counter)
     is threaded through the validation of each unit
     and collected into the @(tsee trans-ensemble-info) annotation
     on the resulting ensemble."))
  (b* (((reterr) (irr-trans-ensemble))
       (tumap (trans-ensemble->units tuens))
       (vstate (init-vstate ienv (irr-filepath)))
       ((erp new-tumap vstate)
        (valid-filepath-trans-unit-map tumap keep-going vstate))
       (- (if keep-going
              (b* ((len-tumap (omap::size tumap))
                   (len-new-tumap (omap::size new-tumap))
                   (diff (- len-tumap len-new-tumap)))
                (if (= (the integer diff) 0)
                    nil
                  (cw "Validated ~x0/~x1 translation units.~%"
                      len-new-tumap len-tumap)))
            nil))
       (info (make-trans-ensemble-info
               :externals (vstate->externals vstate)
               :completions (vstate->completions vstate)
               :next-uid (vstate->next-uid vstate))))
    (retok (make-trans-ensemble
            :units new-tumap
            :resolved-includes nil
            :info info)))

  ///

  (defret trans-ensemble-unambp-of-valid-trans-ensemble
    (implies (not erp)
             (trans-ensemble-unambp new-tuens))
    :hyp (trans-ensemble-unambp tuens)))
