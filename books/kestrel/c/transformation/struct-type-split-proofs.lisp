; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "struct-type-split")

(include-book "variables-in-computation-states")

(include-book "kestrel/c/language/dynamic-semantics" :dir :system)
(include-book "kestrel/c/syntax/abstract-syntax-formal-mapping-direct" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

(include-book "std/basic/symbol-lfix" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* c$::abstract-syntax-unambp-rules
                           c$::abstract-syntax-annop-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption ext-declon-option
  ext-declon
  :short "Fixtype of optional external declarators."
  :pred ext-declon-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cdr-of-trans-item-list-fix
  (equal (cdr (trans-item-list-fix items))
         (trans-item-list-fix (cdr items)))
  :enable trans-item-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon-declon ((edeclon ext-declonp))
  :returns (declon? declon-optionp)
  :short "Check if an external declaration is a declaration,
          return the declaration if successful."
  (if (ext-declon-case edeclon :declon)
      (ext-declon-declon->declon edeclon)
    nil)

  ///

  (defret declon-unambp-of-check-ext-declon-declon
    (implies declon?
             (declon-unambp declon?))
    :hyp (ext-declon-unambp edeclon))

  (defret declon-annop-of-check-ext-declon-declon
    (implies declon?
             (declon-annop declon?))
    :hyp (ext-declon-annop edeclon)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon-fundef ((edeclon ext-declonp))
  :returns (fundef? fundef-optionp)
  :short "Check if an external declaration is a function definition,
          return the function definition if successful."
  (if (ext-declon-case edeclon :fundef)
      (ext-declon-fundef->fundef edeclon)
    nil)

  ///

  (defret fundef-unambp-of-check-ext-declon-fundef
    (implies fundef?
             (fundef-unambp fundef?))
    :hyp (ext-declon-unambp edeclon))

  (defret fundef-annop-of-check-ext-declon-fundef
    (implies fundef?
             (fundef-annop fundef?))
    :hyp (ext-declon-annop edeclon)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-trans-item-ext-declon ((item trans-itemp))
  :returns (edeclon? ext-declon-optionp)
  :short "Check if a translation item is an external declaration,
          returning the external declaration if successful."
  (if (trans-item-case item :declon)
      (trans-item-declon->declon item)
    nil)

  ///

  (defret ext-declon-unambp-of-check-trans-item-ext-declon
    (implies edeclon?
             (ext-declon-unambp edeclon?))
    :hyp (trans-item-unambp item))

  (defret ext-declon-annop-of-check-trans-item-ext-declon
    (implies edeclon?
             (ext-declon-annop edeclon?))
    :hyp (trans-item-annop item)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-trans-item-declon ((item trans-itemp))
  :returns (declon? declon-optionp)
  :short "Check if a translation item is a declaration,
          returning the declaration if successful."
  (b* ((edeclon (check-trans-item-ext-declon item)))
    (if edeclon
        (check-ext-declon-declon edeclon)
      nil))

  ///

  (defret declon-unambp-of-check-trans-item-declon
    (implies declon?
             (declon-unambp declon?))
    :hyp (trans-item-unambp item))

  (defret declon-annop-of-check-trans-item-declon
    (implies declon?
             (declon-annop declon?))
    :hyp (trans-item-annop item)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-trans-item-fundef ((item trans-itemp))
  :returns (fundef? fundef-optionp)
  :short "Check if a translation item is a function definition,
          returning the function definition if successful."
  (b* ((edeclon (check-trans-item-ext-declon item)))
    (if edeclon
        (check-ext-declon-fundef edeclon)
      nil))

  ///

  (defret fundef-unambp-of-check-trans-item-fundef
    (implies fundef?
             (fundef-unambp fundef?))
    :hyp (trans-item-unambp item))

  (defret fundef-annop-of-check-trans-item-fundef
    (implies fundef?
             (fundef-annop fundef?))
    :hyp (trans-item-annop item)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist ident-list-formalp (x)
  :guard (ident-listp x)
  :short "Lift @(tsee ident-formalp) to lists."
  (ident-formalp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-ident-list ((idents ident-listp))
  :returns (mv erp (idents1 c::ident-listp))
  :short "Map a list of identifiers
          to a list of identifiers in the language definition."
  (b* (((reterr) nil)
       ((when (endp idents)) (retok nil))
       ((erp ident1) (ldm-ident (car idents)))
       ((erp idents1) (ldm-ident-list (cdr idents))))
    (retok (cons ident1 idents1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-type-split-proofs
  :parents (struct-type-split)
  :short "Proof generation for the struct type split (STS) transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an event macro @('struct-type-split-proofs'),
     which can be used after @(tsee struct-type-split),
     to generate, under certain conditions,
     ACL2 theorems saying that the transformation operated correctly.
     The conditions are quite restrictive initially,
     but they will be relaxed incrementally.")
   (xdoc::p
    "The macro has the form")
   (xdoc::codeblock
    "(struct-type-split-proofs const-old"
    "                          const-new"
    "                          :struct-tag    ... ; required, no default"
    "                          :new-tag       ... ; required, no default"
    "                          :right-members ... ; required, no default"
    "  )")
   (xdoc::p
    "where the inputs are the same as in @(tsee struct-type-split),
     but @('const-new') must be the constant generated by that event.")
   (xdoc::p
    "If proofs cannot be generated, this macro fails with an error.
     Otherwise, it generates theorems, submitting them to ACL2.")
   (xdoc::p
    "We plan to integrate this proof generation capability
     into the @(tsee struct-type-split) transformation.")
   (xdoc::p
    "This is work in progress;
     only some of the events are currently generated."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-process-const-old/new (const (name symbolp) (wrld plist-worldp))
  :returns (mv (erp maybe-msgp)
               (code code-ensemblep))
  :short "Process the @('const-old') or @('const-new') input."
  (b* (((reterr) (irr-code-ensemble))
       ((unless (symbolp const))
        (retmsg$ "The ~x0 input must be a symbol, but it is ~x1 instead."
                 (symbol-lfix name) const))
       ((unless (constant-symbolp const wrld))
        (retmsg$ "The ~x0 input must be a constant symbol, but ~x1 is not."
                 (symbol-lfix name) const))
       (code (constant-value const wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "The value of the constant ~x0 ~
                  must be a code ensemble, ~
                  but it is ~x1 instead."
                 const code))
       ((unless (code-ensemble-unambp code))
        (retmsg$ "The code ensemble ~x0 ~
                  that is the value of the constant ~x1 ~
                  must be unambiguous, ~
                  but it is not."
                 code const))
       ((unless (code-ensemble-annop code))
        (retmsg$ "The code ensemble ~x0 ~
                  that is the value of the constant ~x1 ~
                  must contains validation information, ~
                  but it does not."
                 code const)))
    (retok code))

  ///

  (defret code-ensemble-unambp-of-stsp-process-const-old/new
    (implies (not erp)
             (code-ensemble-unambp code)))

  (defret code-ensemble-annop-of-stsp-process-const-old/new
    (implies (not erp)
             (code-ensemble-annop code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-process-inputs (const-old
                             const-new
                             struct-tag
                             new-tag
                             right-members
                             (wrld plist-worldp))
  :returns (mv (erp maybe-msgp)
               (old-code code-ensemblep)
               (new-code code-ensemblep)
               (tag identp)
               (tag2 identp)
               (rmems ident-listp))
  :short "Process all the inputs."
  (b* (((reterr)
        (irr-code-ensemble) (irr-code-ensemble) (irr-ident) (irr-ident) nil)
       ((erp old-code) (stsp-process-const-old/new const-old 'const-old wrld))
       ((erp new-code) (stsp-process-const-old/new const-new 'const-new wrld))
       ((unless (stringp struct-tag))
        (retmsg$ "The :STRUCT-TAG input must be a string, ~
                  but it is ~x0 instead."
                 struct-tag))
       ((unless (stringp new-tag))
        (retmsg$ "The :NEW-TAG input must be a string, ~
                  but it is ~x0 instead."
                 new-tag))
       ((unless (and (string-listp right-members)
                     (no-duplicatesp-equal right-members)))
        (retmsg$ "The ;RIGHT-MEMBERS input must be ~
                  a list of strings without repetitions, ~
                  but it is ~x0 instead."
                 right-members)))
    (retok old-code
           new-code
           (ident struct-tag)
           (ident new-tag)
           (ident-list-of right-members)))

  ///

  (defret code-ensemble-unambp-of-stsp-process-inputs.old-code
    (implies (not erp)
             (code-ensemble-unambp old-code)))

  (defret code-ensemble-unambp-of-stsp-process-inputs.new-code
    (implies (not erp)
             (code-ensemble-unambp new-code)))

  (defret code-ensemble-annop-of-stsp-process-inputs.old-code
    (implies (not erp)
             (code-ensemble-annop old-code)))

  (defret code-ensemble-annop-of-stsp-process-inputs.new-code
    (implies (not erp)
             (code-ensemble-annop new-code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum stsp-stage
  :short "Fixtypes of code scanning stages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently proof generation is supported only for
     code ensembles with single translation units.
     The old and new translation units are scanned in parallel,
     to check whether they meet
     the conditions under which proof generation is supported,
     and to generate proofs if those conditions are met.")
   (xdoc::p
    "This fixtype captures the possible stages of that scan.
     Starting with @(':init'),
     we switch to @(':types') when we have found the struct types,
     then to @(':objects') when we have found the struct objects.
     See the scanning code for details."))
  (:init ())
  (:types ())
  (:objects ())
  :pred stsp-stagep)

;;;;;;;;;;

(defirrelevant irr-stsp-stage
  :short "An irrelevant scanning stage."
  :type stsp-stagep
  :body (stsp-stage-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-check-struct-type-declon ((declon declonp))
  :guard (and (declon-unambp declon)
              (declon-annop declon))
  :returns (mv (erp maybe-msgp)
               (tag identp)
               (mems ident-listp))
  :short "Check if a declaration is that of a struct type
          that we currently support for proof generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must consists of a single struct type specifier
     with a tag and with members each of which consists of
     an identifier with type specifiers for an integer type.
     If that is the case, we return the tag and the names of the members."))
  (b* (((reterr) (irr-ident) nil)
       ((unless (and (declon-case declon :declon)
                     (not (declon-declon->extension declon))
                     (endp (declon-declon->declors declon))))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (specs (declon-declon->specs declon))
       ((unless (and (consp specs)
                     (endp (cdr specs))))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (spec (car specs))
       ((unless (decl-spec-case spec :typespec))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (tyspec (decl-spec-typespec->spec spec))
       ((unless (type-spec-case tyspec :struct))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       ((struni-spec suspec) (type-spec-struct->spec tyspec))
       ((unless (and (endp suspec.attribs)
                     suspec.name?
                     (consp suspec.members)))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (tag suspec.name?)
       ((erp mems) (stsp-check-struct-type-declon-loop suspec.members)))
    (retok tag mems))

  :prepwork
  ((define stsp-check-struct-type-declon-loop ((members struct-declon-listp))
     :guard (and (struct-declon-list-unambp members)
                 (struct-declon-list-annop members))
     :returns (mv (erp maybe-msgp)
                  (mems ident-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp members)) (retok nil))
          (sdeclon (struct-declon-fix (car members)))
          ((unless (struct-declon-case sdeclon :member))
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          ((struct-declon-member sdeclon) sdeclon)
          ((unless (and (not sdeclon.extension)
                        (consp sdeclon.declors)
                        (endp (cdr sdeclon.declors))
                        (endp sdeclon.attribs)))
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          ((mv okp tyspecs)
           (check-spec/qual-list-all-typespec sdeclon.specquals))
          ((unless okp)
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          ((unless (type-spec-list-integer-formalp tyspecs))
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          ((struct-declor sdeclor) (car sdeclon.declors))
          ((unless (and sdeclor.declor?
                        (not sdeclor.expr?)))
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          ((unless (type-integerp (type-vinfo->type sdeclor.info)))
           (retmsg$ "Unsupported proof generation for ~x0." sdeclon))
          (mem (declor->ident sdeclor.declor?))
          ((erp mems) (stsp-check-struct-type-declon-loop (cdr members))))
       (retok (cons mem mems))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-check-struct-object-declon ((declon declonp))
  :guard (and (declon-unambp declon)
              (declon-annop declon))
  :returns (mv (erp maybe-msgp)
               (tag identp)
               (name identp))
  :short "Check if a declaration is that of a struct object
          that we currently support for proof generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must consists of
     a single struct type specifier with a tag and without members
     followed by a single identifier declarator.
     If that is the case, we return the tag and name."))
  (b* (((reterr) (irr-ident) (irr-ident))
       ((unless (and (declon-case declon :declon)
                     (not (declon-declon->extension declon))))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (specs (declon-declon->specs declon))
       ((unless (and (consp specs)
                     (endp (cdr specs))))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (spec (car specs))
       ((unless (decl-spec-case spec :typespec))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (tyspec (decl-spec-typespec->spec spec))
       ((unless (type-spec-case tyspec :struct))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       ((struni-spec suspec) (type-spec-struct->spec tyspec))
       ((unless (and (endp suspec.attribs)
                     suspec.name?
                     (endp suspec.members)))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (tag suspec.name?)
       (ideclors (declon-declon->declors declon))
       ((unless (and (consp ideclors)
                     (endp (cdr ideclors))))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       ((init-declor ideclor) (car ideclors))
       ((unless (and (not ideclor.asm?)
                     (endp ideclor.attribs)
                     (not ideclor.initer?)))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       ((declor declor) ideclor.declor)
       ((unless (and (endp declor.pointers)
                     (dirdeclor-case declor.direct :ident)))
        (retmsg$ "Unsupported proof generation for ~x0." (declon-fix declon)))
       (name (dirdeclor-ident->ident declor.direct)))
    (retok tag name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-struct-value-pred ((onlr (member-eq onlr '(old newl newr)))
                                (tag identp)
                                (mems ident-listp))
  :returns (mv (erp maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate a predicate characterizing a struct value
          with the given tag and members."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for the old, left new, and right new struct types:
     one predicate for each, named @('struct-value-<onlr>p'),
     where @('<onlr>') is passed as input to this function."))
  (b* (((reterr) '(_))
       (struct-value-onlrp (packn-pos (list 'struct-value- onlr 'p)
                                      'struct-value-))
       (value-kind-when-struct-value-onlrp
        (packn-pos (list 'value-kind-when- struct-value-onlrp)
                   struct-value-onlrp))
       ((erp ctag) (ldm-ident tag) :iferr "")
       ((erp b*-bindings) (stsp-struct-value-pred-loop mems 0)))
    (retok
     `(define ,struct-value-onlrp ((sval c::valuep))
        :returns (yes/no booleanp)
        (b* (((unless (c::value-case sval :struct)) nil)
             ((unless (equal (c::value-struct->tag sval) ',ctag)) nil)
             (memvals (c::value-struct->members sval))
             ((unless (equal (len memvals) ',(len mems))) nil)
             ,@b*-bindings
             ((unless (not (c::value-struct->flexiblep sval))) nil))
          t)
        ///
        (defruled ,value-kind-when-struct-value-onlrp
          (implies (,struct-value-onlrp sval)
                   (equal (c::value-kind sval) :struct))))))

  :prepwork
  ((define stsp-struct-value-pred-loop ((mems ident-listp) (index natp))
     :returns (mv (erp maybe-msgp)
                  (b*-binders true-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp mems)) (retok nil))
          (memval `(nth ,(lnfix index) memvals))
          ((erp cmem) (ldm-ident (car mems)) :iferr "")
          (b*-binder
           `((unless (equal (c::member-value->name ,memval) ',cmem)) nil))
          ((erp b*-binders)
           (stsp-struct-value-pred-loop (cdr mems) (1+ (lnfix index)))))
       (retok (cons b*-binder b*-binders))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-struct-value-accs ((onlr (member-eq onlr '(old newl newr)))
                                (mems ident-listp))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Generate the accessor functions for the values of
          the members of the struct values characterized by
          the predicates generated by @(tsee stsp-struct-value-pred)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are accessors @('struct-value-<onlr>-><mem>'),
     where @('<onlr>') is passed as input and refers to the struct,
     and @('<mem>') is the name of a member."))
  (b* (((reterr) nil)
       ((when (endp mems)) (retok nil))
       ((erp cmem) (ldm-ident (car mems)) :iferr "")
       (struct-value-onlr-mem
        (packn-pos (list 'struct-value- onlr '- (c::ident->name cmem))
                   'struct-value-))
       (struct-value-onlrp (packn-pos (list 'struct-value- onlr 'p)
                                      'struct-value-))
       (value-struct-read-mem-when-struct-value-onlrp
        (packn-pos (list 'value-struct-read-
                         (c::ident->name cmem)
                         '-when-
                         struct-value-onlrp)
                   'struct-value-))
       (event
        `(define ,struct-value-onlr-mem ((sval c::valuep))
           :guard (,struct-value-onlrp sval)
           :returns (mval c::valuep)
           (c::value-fix (c::struct-value-read ',cmem sval))
           :prepwork ((local (in-theory (enable ,struct-value-onlrp
                                                c::value-struct-read
                                                c::value-struct-read-aux))))
           ///
           (defruled ,value-struct-read-mem-when-struct-value-onlrp
             (implies (,struct-value-onlrp sval)
                      (equal (c::value-struct-read ',cmem sval)
                             (,struct-value-onlr-mem sval))))))
       ((erp events) (stsp-struct-value-accs onlr (cdr mems))))
    (retok (cons event events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-struct-value-equiv ((mems ident-listp)
                                 (lmems ident-listp)
                                 (rmems ident-listp))
  :returns (mv (erp maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate the equivalence predicate on
          old, left new, and right new struct values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the three values satisfy
     the predicates that characterize them,
     and that the accessor of each old member returns the same value as
     the corresponding accessor of each new member."))
  (b* (((reterr) '(_))
       ((erp conjuncts) (stsp-struct-value-equiv-loop mems lmems rmems))
       (event
        `(define struct-value-equivp ((old-val c::valuep)
                                      (newl-val c::valuep)
                                      (newr-val c::valuep))
           :returns (yes/no booleanp)
           (and (struct-value-oldp old-val)
                (struct-value-newlp newl-val)
                (struct-value-newrp newr-val)
                ,@conjuncts))))
    (retok event))

  :prepwork
  ((define stsp-struct-value-equiv-loop ((mems ident-listp)
                                         (lmems ident-listp)
                                         (rmems ident-listp))
     :returns (mv (erp maybe-msgp)
                  (conjuncts true-listp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp mems)) (retok nil))
          (mem (car mems))
          ((erp cmem) (ldm-ident mem) :iferr "")
          (old-acc (packn-pos (list 'struct-value-old- (c::ident->name cmem))
                              'struct-value-))
          ((erp (cons new-acc new-val))
           (cond ((member-equal (ident-fix mem) (ident-list-fix lmems))
                  (retok
                   (cons
                    (packn-pos (list 'struct-value-newl- (c::ident->name cmem))
                               'struct-value-)
                    'newl-val)))
                 ((member-equal (ident-fix mem) (ident-list-fix rmems))
                  (retok
                   (cons
                    (packn-pos (list 'struct-value-nerl- (c::ident->name cmem))
                               'struct-value-)
                    'newr-val)))
                 (t (retmsg$ "Member ~x0 is neither in ~x1 nor in ~x2."
                             (ident-fix mem)
                             (ident-list-fix lmems)
                             (ident-list-fix rmems)))))
          (conjunct `(equal (,old-acc old-val)
                            (,new-acc ,new-val)))
          ((erp conjuncts)
           (stsp-struct-value-equiv-loop (cdr mems) lmems rmems)))
       (retok (cons conjunct conjuncts))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-static-equiv ((old-name identp)
                           (newl-name identp)
                           (newr-name identp))
  :returns (mv (erp maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate the equivalence predicate on old and new static store."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the two stores are the same, except that
     if the old one has the old struct object,
     then the new one has, instead, the new left and right struct objects,
     and the values of those three objects are related by
     the equivalence predicate on struct values."))
  (b* (((reterr) '(_))
       ((erp old-cname) (ldm-ident old-name) :iferr "")
       ((erp newl-cname) (ldm-ident newl-name) :iferr "")
       ((erp newr-cname) (ldm-ident newr-name) :iferr "")
       (event
        `(define static-equivp ((old-static c::scopep)
                                (new-static c::scopep))
           :returns (yes/no booleanp)
           (b* (((when (omap::emptyp (c::scope-fix old-static)))
                 (omap::emptyp (c::scope-fix new-static)))
                ((mv var old-val) (omap::head old-static)))
             (if (equal var ',old-cname
                        (b* ((newl-var ',newl-cname)
                             (newr-var ',newr-cname)
                             (newl-var+val
                              (omap::assoc newl-var (c::scope-fix new-static)))
                             (newr-var+val
                              (omap::assoc newr-var (c::scope-fix new-static)))
                             ((unless (and newl-var+val newr-var+val)) nil)
                             (newl-val (cdr newl-var+val))
                             (newr-val (cdr newr-var+val))
                             ((unless (struct-value-equivp old-val
                                                           newl-val
                                                           newr-val))
                              nil)
                             (old-static (omap::tail old-static))
                             (new-static
                              (omap::delete newl-var (c::scope-fix new-static)))
                             (new-static
                              (omap::delete newr-val (c::scope-fix new-static))))
                          (static-equivp old-static new-static))
                        (b* ((new-var+val
                              (omap::assoc var (c::scope-fix new-static)))
                             ((unless new-var+val) nil)
                             (new-val (cdr new-var+val))
                             ((unless (equal old-val new-val)) nil)
                             (old-static (omap::tail old-static))
                             (new-static
                              (omap::delete var (c::scope-fix new-static))))
                          (static-equivp old-static new-static)))))
           ///
           (defruled struct-value-equivp-when-static-equivp
             (b* ((old-var+val (omap::assoc ',old-cname old-static))
                  (newl-var+val (omap::assoc ',newl-cname new-static))
                  (newr-var+val (omap::assoc ',newr-cname new-static)))
               (implies (and (static-equivp old-static new-static)
                             (c::scopep old-static)
                             (c::scopep new-static)
                             old-var+val)
                        (and newl-var+val
                             newr-var+val
                             (struct-value-equivp (cdr old-var+val)
                                                  (cdr newl-var+val)
                                                  (cdr newr-var+val)))))
             :induct (static-equivp old-static new-static)))))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-compustate-equiv ((old-name identp)
                               (newl-name identp)
                               (newr-name identp)
                               (old-tag identp)
                               (newl-tag identp)
                               (newr-tag identp))
  :returns (mv (erp maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate the equivalence predicate on old and new computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that
     the static stores are equivalent,
     the frame stacks are the same,
     the heaps are the same,
     the old computation state has the old struct object in static store,
     and the new computation state has
     the new left and right struct objects in static store."))
  (b* (((reterr) '(_))
       ((erp old-cname) (ldm-ident old-name) :iferr "")
       ((erp newl-cname) (ldm-ident newl-name) :iferr "")
       ((erp newr-cname) (ldm-ident newr-name) :iferr "")
       ((erp old-ctag) (ldm-ident old-tag) :iferr "")
       ((erp newl-ctag) (ldm-ident newl-tag) :iferr "")
       ((erp newr-ctag) (ldm-ident newr-tag) :iferr "")
       (event
        `(define compustate-equivp ((old-compst c::compustatep)
                                    (new-compst c::compustatep))
           :returns (yes/no booleanp)
           (and (static-equivp (c::compustate->static old-compst)
                               (c::compustate->static new-compst))
                (equal (c::compustate->frames old-compst)
                       (c::compustate->frames new-compst))
                (equal (c::compustate->heap old-compst)
                       (c::compustate->heap new-compst))
                (c::compustate-has-static-var-with-type-p
                 ',old-cname ',old-ctag old-compst)
                (c::compustate-has-static-var-with-type-p
                 ',newl-cname ',newl-ctag new-compst)
                (c::compustate-has-static-var-with-type-p
                 ',newr-cname ',newr-ctag new-compst))
           ///
           (defruled struct-value-equivp-when-compustate-equivp
             (b* ((old-val
                   (c::read-object (c::objdesign-of-var ',old-cname old-compst)
                                   old-compst))
                  (newl-val
                   (c::read-object (c::objdesign-of-var ',newl-cname new-compst)
                                   new-compst))
                  (newr-val
                   (c::read-object (c::objdesign-of-var ',newr-cname new-compst)
                                   new-compst)))
               (implies (compustate-equivp old-compst new-compst)
                        (struct-value-equivp old-val newl-val newr-val)))
             :use ((:instance
                    c::read-object-when-compustate-has-static-var-with-type-p
                    (var ',old-cname)
                    (type (c::type-struct ',old-ctag))
                    (compst old-compst))
                   (:instance
                    c::read-object-when-compustate-has-static-var-with-type-p
                    (var ',newl-cname)
                    (type (c::type-struct ',newl-ctag))
                    (compst new-compst))
                   (:instance
                    c::read-object-when-compustate-has-static-var-with-type-p
                    (var ',newr-cname)
                    (type (c::type-struct ',newr-ctag))
                    (compst new-compst))
                   (:instance
                    struct-value-equivp-when-static-equivp
                    (old-static (c::compustate->static old-compst))
                    (new-static (c::compustate->static new-compst))))
             :enable
             c::assoc-static-when-compustate-has-static-var-with-type-p))))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-struct-type-declon ((old-declon declonp)
                                 (new-declon declonp)
                                 (new-declon2 declonp)
                                 (tag identp)
                                 (tag2 identp)
                                 (rmems ident-listp))
  :guard (and (declon-unambp old-declon)
              (declon-unambp new-declon)
              (declon-unambp new-declon2)
              (declon-annop old-declon)
              (declon-annop new-declon)
              (declon-annop new-declon2))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Check, and generate events for,
          the declarations of the old and new left and right struct types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is given the declarations of
     the old struct type and the new left and right struct types.
     We need to check that they have the correct form, based on
     the tag of the old structure type and new left structure type,
     the tag of the new right structure type,
     and the members moved to the right structure type.
     We only check the names of the members,
     but we should also check their types.")
   (xdoc::p
    "If everything checks out, we generate
     the three predicates that characterize the struct values,
     the accessors of the member values in the old and new structs,
     and the equivalence predicates over struct values."))
  (b* (((reterr) nil)
       ((erp old-tag old-mems) (stsp-check-struct-type-declon old-declon))
       ((erp newl-tag newl-mems) (stsp-check-struct-type-declon new-declon))
       ((erp newr-tag newr-mems) (stsp-check-struct-type-declon new-declon2))
       ((unless (equal old-tag (ident-fix tag)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix old-declon)))
       ((unless (equal newl-tag (ident-fix tag)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix new-declon)))
       ((unless (equal newr-tag (ident-fix tag2)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix new-declon2)))
       ((unless (and (consp old-mems)
                     (consp newl-mems)
                     (consp newr-mems)
                     (not (intersectp-equal newl-mems newr-mems))
                     (set-equiv old-mems (append newl-mems newr-mems))
                     (set-equiv (ident-list-fix rmems) newr-mems)))
        (retmsg$ "Unsupported proof generation for ~&0."
                 (list (declon-fix old-declon)
                       (declon-fix new-declon)
                       (declon-fix new-declon2))))
       ((erp old-pred) (stsp-struct-value-pred 'old old-tag old-mems))
       ((erp newl-pred) (stsp-struct-value-pred 'newl newl-tag newl-mems))
       ((erp newr-pred) (stsp-struct-value-pred 'newr newr-tag newr-mems))
       ((erp old-accs) (stsp-struct-value-accs 'old old-mems))
       ((erp newl-accs) (stsp-struct-value-accs 'newl newl-mems))
       ((erp newr-accs) (stsp-struct-value-accs 'newr newr-mems))
       ((erp equiv-pred)
        (stsp-struct-value-equiv old-mems newl-mems newr-mems)))
    (retok (append (list old-pred)
                   (list newl-pred)
                   (list newr-pred)
                   old-accs
                   newl-accs
                   newr-accs
                   (list equiv-pred))))
  :guard-hints
  (("Goal"
    :in-theory (enable c$::true-listp-when-ident-listp
                       acl2::true-listp-when-pseudo-event-form-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-struct-object-declon ((old-declon declonp)
                                   (new-declon declonp)
                                   (new-declon2 declonp)
                                   (tag identp)
                                   (tag2 identp))
  :guard (and (declon-unambp old-declon)
              (declon-unambp new-declon)
              (declon-unambp new-declon2)
              (declon-annop old-declon)
              (declon-annop new-declon)
              (declon-annop new-declon2))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Check, and generate events for,
          the declarations of the old and new left and right struct objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is given the declarations of
     the old struct object and the new left and right struct objects.
     We need to check that they have the correct form, based on
     the tag of the old structure type and new left structure type,
     and the tag of the new right structure type.")
   (xdoc::p
    "If everything checks out, we generate
     the equivalence predicate on old and new static stores
     and the equivalence predicate on the old and new computation states."))
  (b* (((reterr) nil)
       ((erp old-tag old-name) (stsp-check-struct-object-declon old-declon))
       ((erp newl-tag newl-name) (stsp-check-struct-object-declon new-declon))
       ((erp newr-tag newr-name) (stsp-check-struct-object-declon new-declon2))
       ((unless (equal old-tag (ident-fix tag)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix old-declon)))
       ((unless (equal newl-tag (ident-fix tag)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix new-declon)))
       ((unless (equal newr-tag (ident-fix tag2)))
        (retmsg$ "Unsupported proof generation for ~x0."
                 (declon-fix new-declon2)))
       ((erp static-equiv-pred)
        (stsp-static-equiv old-name newl-name newr-name))
       ((erp compustate-equiv-pred)
        (stsp-compustate-equiv old-name newl-name newr-name
                               old-tag newl-tag newr-tag)))
    (retok (list static-equiv-pred
                 compustate-equiv-pred))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-declon ((old-declon declonp)
                     (new-items trans-item-listp)
                     (tag identp)
                     (tag2 identp)
                     (rmems ident-listp)
                     (stage stsp-stagep))
  :guard (and (declon-unambp old-declon)
              (declon-annop old-declon)
              (trans-item-list-unambp new-items)
              (trans-item-list-annop new-items)
              (consp new-items))
  :returns (mv (erp maybe-msgp)
               (new-stage stsp-stagep)
               (rest-new-items trans-item-listp)
               (events pseudo-event-form-listp))
  :short "Generate events for a (top-level) declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we are very restrictive:
     the only (top-level) declarations we support for proof generation
     are the ones of the struct type and struct object,
     in that order.
     This is guided by the stage we are in.")
   (xdoc::p
    "If we are in the @(':init') stage,
     the declaration in the old code must be that of the struct type.
     We must find, in the new code, two declarations,
     for the two struct types into which the original one is split.
     We use a separate function to handle those three declarations.
     Then we advance the stage.")
   (xdoc::p
    "If we are in the @(':types') stage,
     the declaration in the fold code must be that of the struct object.
     We must find, in the new code, two declarations,
     for the two struct objects into which the original one is split.
     We use a separate function to handle those three declarations.
     Then we advance the stage.")
   (xdoc::p
    "If we are in the @(':objects') stage,
     we do not support proof generation yet."))
  (b* (((reterr) (irr-stsp-stage) nil nil))
    (stsp-stage-case
     stage
     :init
     (b* ((new-item (car new-items))
          (new-declon (check-trans-item-declon new-item))
          ((unless new-declon)
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into non-declaration ~x1."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)))
          (new-items (cdr new-items))
          ((unless (consp new-items))
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into declaration ~x1 ~
                     without a following declaration."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)))
          (new-item2 (car new-items))
          (new-declon2 (check-trans-item-declon new-item2))
          ((unless new-declon2)
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into declaration ~x1 ~
                     followed by non-declaration ~x2."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)
                    (trans-item-fix new-item2)))
          ((erp events) (stsp-struct-type-declon old-declon
                                                 new-declon
                                                 new-declon2
                                                 tag
                                                 tag2
                                                 rmems)))
       (retok (stsp-stage-types)
              (trans-item-list-fix (cdr new-items))
              events))
     :types
     (b* ((new-item (car new-items))
          (new-declon (check-trans-item-declon new-item))
          ((unless new-declon)
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into non-declaration ~x1."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)))
          (new-items (cdr new-items))
          ((unless (consp new-items))
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into declaration ~x1 ~
                     without a following declaration."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)))
          (new-item2 (car new-items))
          (new-declon2 (check-trans-item-declon new-item2))
          ((unless new-declon2)
           (retmsg$ "Unsupported proof generation for ~
                     declaration ~x0 transformed into declaration ~x1 ~
                     followed by non-declaration ~x2."
                    (trans-item-declon (ext-declon-declon old-declon))
                    (trans-item-fix new-item)
                    (trans-item-fix new-item2)))
          ((erp events) (stsp-struct-object-declon old-declon
                                                   new-declon
                                                   new-declon2
                                                   tag
                                                   tag2)))
       (retok (stsp-stage-objects)
              (trans-item-list-fix (cdr new-items))
              events))
     :objects (retmsg$ "Unsupported proof generation for ~
                        declaration after the ones of ~
                        the struct type and struct object.")))
  :hooks
  ((:fix :hints (("Goal" :in-theory (enable cdr-of-trans-item-list-fix)))))

  ///

  (defret trans-item-list-unambp-of-stsp-declon
    (trans-item-list-unambp rest-new-items)
    :hyp (trans-item-list-unambp new-items))

  (defret trans-item-list-annop-of-stsp-declon
    (trans-item-list-annop rest-new-items)
    :hyp (trans-item-list-annop new-items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-fundef ((old-fundef fundefp)
                     (new-fundef fundefp)
                     (tag identp)
                     (tag2 identp)
                     (rmems ident-listp))
  :guard (and (fundef-unambp old-fundef)
              (fundef-unambp new-fundef)
              (fundef-annop old-fundef)
              (fundef-annop new-fundef))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Generate events for a function definition."
  (declare (ignore old-fundef new-fundef tag tag2 rmems))
  (retok
   `((acl2::cw-event "TODO: theorems for ~x0~%" (fundef-fix old-fundef)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-ext-declon ((old-edeclon ext-declonp)
                         (new-items trans-item-listp)
                         (tag identp)
                         (tag2 identp)
                         (rmems ident-listp)
                         (stage stsp-stagep))
  :guard (and (ext-declon-unambp old-edeclon)
              (ext-declon-annop old-edeclon)
              (trans-item-list-unambp new-items)
              (trans-item-list-annop new-items)
              (consp new-items))
  :returns (mv (erp maybe-msgp)
               (new-stage stsp-stagep)
               (rest-new-items trans-item-listp)
               (events pseudo-event-form-listp))
  :short "Generate events for an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the external declaration is assembler,
     we do not support proof generation yet.")
   (xdoc::p
    "If it is an empty external declaration,
     we expect to find the same in the new code,
     but we generate no theorems and we keep the stage as is.")
   (xdoc::p
    "If it is a function definition,
     we expect to find one in the new code.
     We must be in the stage where
     we have already encountered the struct types and struct objects,
     otherwise proof generation is not supported.
     We use a separate function to handle the old and new function definitions,
     and there is no stage change.")
   (xdoc::p
    "If it is a declaration, we use a separate function to handle it."))
  (b* (((reterr) (irr-stsp-stage) nil nil))
    (ext-declon-case
     old-edeclon
     :fundef
     (b* ((new-item (car new-items))
          (new-fundef (check-trans-item-fundef new-item))
          ((unless new-fundef)
           (raise "Internal error: ~x0 transformed into ~x1."
                  (trans-item-declon old-edeclon)
                  (trans-item-fix new-item))
           (retmsg$ ""))
          ((unless (stsp-stage-case stage :objects))
           (retmsg$ "Unsupported proof generation for ~
                     function definition before struct type or object."))
          ((erp events)
           (stsp-fundef old-edeclon.fundef new-fundef tag tag2 rmems)))
       (retok (stsp-stage-fix stage)
              (trans-item-list-fix (cdr new-items))
              events))
     :declon
     (stsp-declon old-edeclon.declon new-items tag tag2 rmems stage)
     :empty
     (b* ((new-item (car new-items))
          ((unless (trans-item-equiv new-item
                                     (trans-item-declon (ext-declon-empty))))
           (raise "Internal error: ~x0 transformed into ~x1."
                  (trans-item-declon old-edeclon)
                  (trans-item-fix new-item))
           (retmsg$ "")))
       (retok (stsp-stage-fix stage)
              (trans-item-list-fix (cdr new-items))
              nil))
     :asm (retmsg$ "Unsupported proof generation for assembler.")))
  :no-function nil

  ///

  (defret trans-item-list-unambp-of-stsp-ext-declon
    (trans-item-list-unambp rest-new-items)
    :hyp (trans-item-list-unambp new-items))

  (defret trans-item-list-annop-of-stsp-ext-declon
    (trans-item-list-annop rest-new-items)
    :hyp (trans-item-list-annop new-items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-trans-item ((old-item trans-itemp)
                         (new-items trans-item-listp)
                         (tag identp)
                         (tag2 identp)
                         (rmems ident-listp)
                         (stage stsp-stagep))
  :guard (and (trans-item-unambp old-item)
              (trans-item-annop old-item)
              (trans-item-list-unambp new-items)
              (trans-item-list-annop new-items)
              (consp new-items))
  :returns (mv (erp maybe-msgp)
               (new-stage stsp-stagep)
               (rest-new-items trans-item-listp)
               (events pseudo-event-form-listp))
  :short "Generate events for a translation item."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the translation item is a preprocessing construct,
     we do not support proof generation yet.")
   (xdoc::p
    "For a line comment,
     the new translation item should be always identical.
     There is no change to the scanning stage.")
   (xdoc::p
    "For an external declaration, we use a separate function."))
  (b* (((reterr) (irr-stsp-stage) nil nil))
    (trans-item-case
     old-item
     :declon (stsp-ext-declon old-item.declon new-items tag tag2 rmems stage)
     :include (retmsg$ "Unsupported proof generation for #include.")
     :define (retmsg$ "Unsupported proof generation for #define.")
     :undef (retmsg$ "Unsupported proof generation for #undef.")
     :cond (retmsg$ "Unsupported proof generation for #if/#ifdef/#ifndef.")
     :line-comment
     (b* ((new-item (car new-items))
          ((unless (trans-item-equiv new-item old-item))
           (raise "Internal error: ~x0 transformed into ~x1."
                  (trans-item-fix old-item)
                  (trans-item-fix new-item))
           (retmsg$ "")))
       (retok (stsp-stage-fix stage)
              (trans-item-list-fix (cdr new-items))
              nil))))
  :no-function nil

  ///

  (defret trans-item-list-unambp-of-stsp-trans-item
    (trans-item-list-unambp rest-new-items)
    :hyp (trans-item-list-unambp new-items))

  (defret trans-item-list-annop-of-stsp-trans-item
    (trans-item-list-annop rest-new-items)
    :hyp (trans-item-list-annop new-items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-trans-item-list ((old-items trans-item-listp)
                              (new-items trans-item-listp)
                              (tag identp)
                              (tag2 identp)
                              (rmems ident-listp)
                              (stage stsp-stagep))
  :guard (and (trans-item-list-unambp old-items)
              (trans-item-list-unambp new-items)
              (trans-item-list-annop old-items)
              (trans-item-list-annop new-items))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Generate events for a list of translation items."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the old list is empty,
     it means that we have reached the end of the translation unit,
     and it should always be the case that the new list must be empty too.
     Unless we have encountered both the struct types and the struct objects,
     proof generation fails.")
   (xdoc::p
    "If the old list is not empty,
     it should always be the case that the new list is not empty either.
     We use a separate function to handle the first translation item,
     along with one or two translation items from the new list
     (see the separate function for details).
     Then we continue with the rest of the translation items."))
  (b* (((reterr) nil)
       ((when (endp old-items))
        (b* (((unless (endp new-items))
              (raise "Internal error: extra new translation items ~x0."
                     (trans-item-list-fix new-items))
              (retmsg$ "")))
          (stsp-stage-case
           stage
           :init (retmsg$ "Unsupported proof generation for ~
                           missing struct type and object.")
           :types (retmsg$ "Unsupported proof generation for ~
                            struct object.")
           :objects (retok nil))))
       ((when (endp new-items))
        (raise "Internal error: extra old translation items ~x0."
               (trans-item-list-fix old-items))
        (retmsg$ ""))
       ((erp stage rest-new-items events) (stsp-trans-item (car old-items)
                                                           new-items
                                                           tag
                                                           tag2
                                                           rmems
                                                           stage))
       ((erp more-events)
        (stsp-trans-item-list (cdr old-items)
                              rest-new-items
                              tag
                              tag2
                              rmems
                              stage)))
    (retok (append events more-events)))
  :no-function nil
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::true-listp-when-pseudo-event-form-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-trans-unit ((old-tunit trans-unitp)
                         (new-tunit trans-unitp)
                         (tag identp)
                         (tag2 identp)
                         (rmems ident-listp))
  :guard (and (trans-unit-unambp old-tunit)
              (trans-unit-unambp new-tunit)
              (trans-unit-annop old-tunit)
              (trans-unit-annop new-tunit))
  :returns (mv (erp maybe-msgp)
               (events pseudo-event-form-listp))
  :short "Generate events for a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We initialize the scanning stage
     and we go through the translation items."))
  (stsp-trans-item-list (trans-unit->items old-tunit)
                        (trans-unit->items new-tunit)
                        tag
                        tag2
                        rmems
                        (stsp-stage-init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-gen-everything ((old-code code-ensemblep)
                             (new-code code-ensemblep)
                             (tag identp)
                             (tag2 identp)
                             (rmems ident-listp))
  :guard (and (code-ensemble-unambp old-code)
              (code-ensemble-unambp new-code)
              (code-ensemble-annop old-code)
              (code-ensemble-annop new-code))
  :returns (mv (erp maybe-msgp)
               (event
                pseudo-event-formp
                :hints
                (("Goal"
                  :in-theory
                  (enable
                   acl2::true-listp-when-pseudo-event-form-listp-rewrite)))))
  :short "Generate all the proofs."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support single translation units."))
  (b* (((reterr) '(_))
       (old-tens (code-ensemble->trans-units old-code))
       (new-tens (code-ensemble->trans-units new-code))
       (old-tunits (trans-ensemble->units old-tens))
       (new-tunits (trans-ensemble->units new-tens))
       ((unless (and (equal (omap::size old-tunits) 1)
                     (equal (omap::size new-tunits) 1)))
        (retmsg$ "Unsupported proof generation ~
                  for multiple translation units."))
       (old-tunit (omap::head-val old-tunits))
       (new-tunit (omap::head-val new-tunits))
       ((erp events) (stsp-trans-unit old-tunit new-tunit tag tag2 rmems)))
    (retok `(encapsulate () ,@events)))
  :guard-hints (("Goal"
                 :expand
                 ((:free (tens) (omap::size (trans-ensemble->units tens)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stsp-process-inputs-and-gen-everything (const-old
                                                const-new
                                                struct-tag
                                                new-tag
                                                right-members
                                                state)
  :returns (mv (erp maybe-msgp)
               (event pseudo-event-formp))
  :parents (simpadd0-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp old-code
             new-code
             tag
             tag2
             rmems)
        (stsp-process-inputs const-old
                             const-new
                             struct-tag
                             new-tag
                             right-members
                             (w state))))
    (stsp-gen-everything old-code new-code tag tag2 rmems)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-type-split-proofs-fn (const-old
                                     const-new
                                     struct-tag
                                     new-tag
                                     right-members
                                     (ctx ctxp)
                                     state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee struct-type-split-proofs)."
  (b* (((mv erp event)
        (stsp-process-inputs-and-gen-everything const-old
                                                const-new
                                                struct-tag
                                                new-tag
                                                right-members
                                                state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro struct-type-split-proofs (const-old
                                    const-new
                                    &key
                                    struct-tag
                                    new-tag
                                    right-members)
  `(make-event (struct-type-split-proofs-fn ',const-old
                                            ',const-new
                                            ',struct-tag
                                            ',new-tag
                                            ',right-members
                                            'struct-type-split-proofs
                                            state)))
