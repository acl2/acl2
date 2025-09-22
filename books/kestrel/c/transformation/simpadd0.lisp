; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "proof-generation")
(include-book "proof-generation-theorems")

(include-book "../syntax/unambiguity")
(include-book "../syntax/ascii-identifiers")
(include-book "../syntax/purity")
(include-book "../syntax/langdef-mapping")
(include-book "../representation/shallow-deep-relation")

(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (in-theory (enable* c$::abstract-syntax-aidentp-rules)))
(local (in-theory (enable* c$::abstract-syntax-unambp-rules)))
(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 simpadd0

 :items

 ((xdoc::evmac-topic-implementation-item-input "const-old")

  (xdoc::evmac-topic-implementation-item-input "const-new"))

 :additional

 ("This transformation is implemented as a collection of ACL2 functions
   that operate on the abstract syntax,
   following the recursive structure of the abstract syntax.
   This is a typical pattern for C-to-C transformations,
   which we may want to partially automate,
   via things like generalized `folds' over the abstract syntax."

  "These functions also return correctness theorems in a bottom-up fashion,
   for a growing subset of constructs currently supported.
   This is one of a few different or slightly different approaches
   to proof generation, which we are exploring."

  "The generated theorems have names obtained by
   combining @('const-new') with an increasing numeric index,
   which is threaded through the transformation functions.
   The generated theorem events are accumulated into a list
   that is threaded through the transformation functions;
   the list is accumulated in reverse order,
   so that each new generated event is @(tsee cons)ed,
   but the list is reversed to the right order
   in the top-level generated event that is submitted to ACL2."

  "For a growing number of constructs,
   we have ACL2 functions that perform
   the core of the transformation of the construct,
   including theorem generation when applicable,
   and these ACL2 function are outside the large mutual recursion.
   The recursive functions recursively transform the sub-constructs,
   and then call the separate non-recursive functions
   with the results from transforming the sub-constructs.
   A simple example is @(tsee simpadd0-expr-paren),
   which is called by @(tsee simpadd0-expr):
   the caller recursively transforms the inner expression,
   and passes the possibly transformed expression to the callee,
   along with some of the @(tsee simpadd0-gout) components
   resulting from that transformation;
   it also passes a @(tsee simpadd0-gin)
   whose components have been updated
   from the aforementioned @(tsee simpadd0-gout)."

  "The above paragraph also illustrates
   a naming convention used for the transformation functions.
   The functions in the mutual recursion are called @('simpadd0-<construct>'),
   where @('<construct>') is the fixtype of the construct,
   e.g. @('expr') in the example above.
   The functions not in the mutual recursion have more specific names,
   such as @('simpadd0-<construct>-<kind>'),
   where @('<kind>') is the appropriate kind of the @('<construct>') fixtype,
   such as @(':paren') (without the colon) in the example above.
   For fixtypes that are not tagged sums,
   we add @('core') to the name of the function outside the mutual recursion.
   For non-sum non-product fixtypes, e.g. lists,
   we add designations for empty and @(tsee cons) lists to the names."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs (const-old
                                 const-old-present
                                 const-new
                                 const-new-present
                                 (wrld plist-worldp))
  :returns (mv erp
               (code-old code-ensemblep)
               (const-new$ symbolp))
  :short "Process all the inputs."
  (b* (((reterr) (irr-code-ensemble) nil)
       ((unless const-old-present)
        (reterr (msg "The :CONST-OLD input must be supplied.")))
       ((unless (symbolp const-old))
        (reterr (msg "The :CONST-OLD must be a symbol, ~
                      but it is ~x0 instead."
                     const-old)))
       ((unless const-new-present)
        (reterr (msg "The :CONST-NEW input must be supplied.")))
       ((unless (symbolp const-new))
        (reterr (msg "The :CONST-NEW must be a symbol, ~
                      but it is ~x0 instead."
                     const-new)))
       ((unless (constant-symbolp const-old wrld))
        (reterr (msg "The :CONST-OLD input, ~x0, must be a named constant, ~
                      but it is not."
                     const-old)))
       (code-old (constant-value const-old wrld))
       ((unless (code-ensemblep code-old))
        (reterr (msg "The value of the constant ~x0 ~
                      must be a code ensemble, ~
                      but it is ~x1 instead."
                     const-old code-old)))
       ((unless (code-ensemble-unambp code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must be unambiguous, ~
                      but it is not."
                     code-old const-old)))
       ((unless (code-ensemble-annop code-old))
        (reterr (msg "The code ensemble ~x0 ~
                      that is the value of the constant ~x1 ~
                      must contains validation information, ~
                      but it does not."
                     code-old const-old))))
    (retok code-old const-new))

  ///

  (defret code-ensemble-unambp-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-unambp code-old)))

  (defret code-ensemble-annop-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-annop code-old))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod simpadd0-gin
  :short "General inputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions take as input the construct to transform,
     which has a different type for each transformation function.
     But each function also takes certain common inputs,
     which we put into this data structure
     for modularity and to facilitate extension."))
  ((ienv ienv
         "The implementation environment from the code ensemble.")
   (const-new symbol
              "The @(':const-new') input of the transformation.")
   (vartys c::ident-type-map
           "Some variables in scope at the beginning of the construct.
            The generated theorem (if any)
            includes hypotheses about their presence in the computation state
            before the execution of the C construct.
            Currently this could be actually a subset of the variables in scope,
            but it is adequate to the current proof generation,
            and we are working on extending this.")
   (events pseudo-event-form-list
           "Theorems generated so far, in reverse order;
            see @(see simpadd0-implementation).")
   (thm-index pos
              "Index used to generate unique theorem names;
               see @(see simpadd0-implementation)."))
  :pred simpadd0-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod simpadd0-gout
  :short "General outputs for transformation functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The transformation functions return as output the transformed construct,
     which has a different type for each transformation function.
     But each function also returns certain common outputs,
     which we put into this data structure
     for modularity and to facilitate extension."))
  ((events pseudo-event-form-list
           "Theorems generated so far, in reverse order;
            see @(see simpadd0-implementation).")
   (thm-index pos
              "Index used to generate unique theorem names;
               see @(see simpadd0-implementation).")
   (thm-name symbol
             "Name of the theorem generated by the transformation function.
              The theorem concerns the transformation of the C construct
              that the transformation function operates on.
              This is @('nil') if no theorem is generated.")
   (vartys c::ident-type-map
           "Some variables in scope at the end of the construct.
            The generated theorem (if any)
            includes conclusions about their presence in the computation state
            after the execution of the construct.
            This does not necessarily include all the variables in scope,
            because for certain constructs (e.g. lists of block items)
            we only consider variables that are also in scope
            at the beginning of the construct, i.e. that occur in
            the @('vartys') component of @(tsee simpadd0-gin)."))
  :pred simpadd0-goutp)

;;;;;;;;;;

(defirrelevant irr-simpadd0-gout
  :short "Irrelevant general outputs for transformation functions."
  :type simpadd0-goutp
  :body (make-simpadd0-gout :events nil
                            :thm-index 1
                            :thm-name nil
                            :vartys nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gin-update ((gin simpadd0-ginp) (gout simpadd0-goutp))
  :returns (new-gin simpadd0-ginp)
  :short "Update a @(tsee simpadd0-gin) with a @(tsee simpadd0-gout)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of theorems generated so far
     and the index for unique theorem names
     are threaded through the transformation functions;
     both are common components of
     @(tsee simpadd0-gin) and @(tsee simpadd0-gout).
     This function updates an input
     (to the next call of a transformation function)
     with an output
     (from the previous call of a transformation function),
     by updating those common components.")
   (xdoc::p
    "Although both @(tsee simpadd0-gin) and @(tsee simpadd0-gout)
     have a @('vartys') component, that one is not threaded through;
     it is handled differently (see the transformation functions).
     Thus, this function does not involve that component."))
  (b* (((simpadd0-gout gout) gout))
    (change-simpadd0-gin gin
                         :events gout.events
                         :thm-index gout.thm-index))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gout-no-thm ((gin simpadd0-ginp))
  :returns (gout simpadd0-goutp)
  :short "Build a @(tsee simpadd0-gout) without a theorem name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for constructs for which we do not generate proofs yet.
     The events, theorem index, and variable-type map
     are taken from a @(tsee simpadd0-gin),
     as they result from previous transformations."))
  (b* (((simpadd0-gin gin) gin))
    (make-simpadd0-gout :events gin.events
                        :thm-index gin.thm-index
                        :thm-name nil
                        :vartys gin.vartys))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-from-params ((params c::param-declon-listp)
                                  (gin simpadd0-ginp))
  :returns (mv (okp booleanp)
               (args symbol-listp)
               (parargs "A term.")
               (arg-types true-listp)
               (arg-types-compst true-listp)
               (vartys c::ident-type-mapp))
  :short "Generate certain pieces of information
          from the formal parameters of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The results of this function are used to generate
     theorems about function calls.")
   (xdoc::p
    "We generate the following:")
   (xdoc::ul
    (xdoc::li
     "A list @('args') of symbols used as ACL2 variables
      that denote the C values passed as arguments to the function.")
    (xdoc::li
     "A term @('parargs') that is a nest of @(tsee omap::update) calls
      that denotes the initial scope of the function.
      Each @(tsee omap::update) call adds
      the name of the parameter as key
      and the variable for the corresponding argument as value.")
    (xdoc::li
     "A list @('arg-types') of terms that assert that
      each variable in @('args') is a value of the appropriate type.")
    (xdoc::li
     "A list @('arg-types-compst') of terms that assert that
      each parameter in @('params') can be read from a computation state
      and its reading yields a value of the appropriate type.")
    (xdoc::li
     "A variable-type map corresponding to the parameters in the obvious way."))
   (xdoc::p
    "These results are generated only if
     all the parameters have certain types
     (see @(tsee simpadd0-tyspecseq-to-type)),
     which we check as we go through the parameters.
     The @('okp') result says whether this is the case;
     if it is @('nil'), the other results are @('nil') too."))
  (b* (((when (endp params)) (mv t nil nil nil nil nil))
       ((c::param-declon param) (car params))
       ((mv okp type) (simpadd0-tyspecseq-to-type param.tyspec))
       ((unless okp) (mv nil nil nil nil nil nil))
       ((unless (c::obj-declor-case param.declor :ident))
        (mv nil nil nil nil nil nil))
       (ident (c::obj-declor-ident->get param.declor))
       (par (c::ident->name ident))
       (arg (intern-in-package-of-symbol par (simpadd0-gin->const-new gin)))
       (arg-type `(and (c::valuep ,arg)
                       (equal (c::type-of-value ,arg) ',type)))
       (arg-type-compst
        `(c::compustate-has-var-with-type-p ',ident ',type compst))
       ((mv okp
            more-args
            parargs
            more-arg-types
            more-arg-types-compst
            more-vartys)
        (simpadd0-gen-from-params (cdr params) gin))
       ((unless okp) (mv nil nil nil nil nil nil))
       (parargs `(omap::update (c::ident ,par) ,arg ,parargs))
       (vartys (omap::update ident type more-vartys)))
    (mv t
        (cons arg more-args)
        parargs
        (cons arg-type more-arg-types)
        (cons arg-type-compst more-arg-types-compst)
        vartys))
  :verify-guards :after-returns

  ///

  (defret len-of-simpadd0-gen-from-params.arg-types
    (equal (len arg-types)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defret len-of-simpadd0-gen-from-params.arg-types-compst
    (equal (len arg-types-compst)
           (len args))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-init-scope-thm ((params c::param-declon-listp)
                                     (args symbol-listp)
                                     (parargs "A term.")
                                     (arg-types true-listp)
                                     (const-new symbolp)
                                     (thm-index posp))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (updated-thm-index posp
                                  :rule-classes (:rewrite :type-prescription)))
  :short "Generate a theorem about the initial scope of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args'), @('parargs'), and @('arg-types') inputs
     are the corresponding outputs of @(tsee simpadd0-gen-from-params).")
   (xdoc::p
    "The theorem says that, given values of certain types for the arguments,
     @(tsee c::init-scope) applied to the list of parameter declarations
     and to the list of parameter values
     yields an omap (which we express as an @(tsee omap::update) nest)
     that associates parameter name and argument value."))
  (b* ((formula `(implies (and ,@arg-types)
                          (equal (c::init-scope ',params (list ,@args))
                                 ,parargs)))
       (hints
        '(("Goal" :in-theory '(omap::assoc-when-emptyp
                               (:e omap::emptyp)
                               omap::assoc-of-update
                               c::init-scope
                               c::not-flexible-array-member-p-when-ucharp
                               c::not-flexible-array-member-p-when-scharp
                               c::not-flexible-array-member-p-when-ushortp
                               c::not-flexible-array-member-p-when-sshortp
                               c::not-flexible-array-member-p-when-uintp
                               c::not-flexible-array-member-p-when-sintp
                               c::not-flexible-array-member-p-when-ulongp
                               c::not-flexible-array-member-p-when-slongp
                               c::not-flexible-array-member-p-when-ullongp
                               c::not-flexible-array-member-p-when-sllongp
                               c::remove-flexible-array-member-when-absent
                               c::ucharp-alt-def
                               c::scharp-alt-def
                               c::ushortp-alt-def
                               c::sshortp-alt-def
                               c::uintp-alt-def
                               c::sintp-alt-def
                               c::ulongp-alt-def
                               c::slongp-alt-def
                               c::ullongp-alt-def
                               c::sllongp-alt-def
                               c::type-of-value-when-ucharp
                               c::type-of-value-when-scharp
                               c::type-of-value-when-ushortp
                               c::type-of-value-when-sshortp
                               c::type-of-value-when-uintp
                               c::type-of-value-when-sintp
                               c::type-of-value-when-ulongp
                               c::type-of-value-when-slongp
                               c::type-of-value-when-ullongp
                               c::type-of-value-when-sllongp
                               c::value-fix-when-valuep
                               c::value-list-fix-of-cons
                               c::type-of-value
                               c::type-array
                               c::type-pointer
                               c::type-struct
                               (:e c::adjust-type)
                               (:e c::apconvert-type)
                               (:e c::ident)
                               (:e c::param-declon-list-fix$inline)
                               (:e c::param-declon-to-ident+tyname)
                               (:e c::tyname-to-type)
                               (:e c::type-uchar)
                               (:e c::type-schar)
                               (:e c::type-ushort)
                               (:e c::type-sshort)
                               (:e c::type-uint)
                               (:e c::type-sint)
                               (:e c::type-ulong)
                               (:e c::type-slong)
                               (:e c::type-ullong)
                               (:e c::type-sllong)
                               (:e c::value-list-fix$inline)
                               mv-nth
                               car-cons
                               cdr-cons
                               (:e <<)
                               lemma1
                               lemma2))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints
                     :prep-lemmas
                     ((defruled lemma1
                        (not (c::errorp nil)))
                      (defruled lemma2
                        (not (c::errorp (omap::update key val map)))
                        :enable (c::errorp omap::update))))))
    (mv thm-event thm-name thm-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-param-thms ((arg-types-compst true-listp)
                                 (all-arg-types true-listp)
                                 (all-params c::param-declon-listp)
                                 (all-args symbol-listp)
                                 (init-scope-thm symbolp)
                                 (const-new symbolp)
                                 (thm-index posp))
  :returns (mv (thm-events pseudo-event-form-listp)
               (thm-names symbol-listp)
               (updated-thm-index posp
                                  :rule-classes (:rewrite :type-prescription)))
  :short "Generate theorems about the parameters of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('args') and @('arg-types-compst') inputs are
     the corresponding outputs of @(tsee simpadd0-gen-from-params);
     these are @(tsee cdr)ed in the recursion.
     The @('all-arg-types') input is
     the @('arg-types') output of @(tsee simpadd0-gen-from-params);
     it stays the same during the recursion.")
   (xdoc::p
    "We return the theorem events, along with the theorem names.")
   (xdoc::p
    "The theorem names are used locally in an enclosing theorem,
     so they do not need to be particularly unique.
     But we should check and disambiguate them more thoroughly.")
   (xdoc::p
    "For each parameter of the function,
     we generate a theorem saying that,
     in the computation state resulting from
     pushing the initial scope to the frame stack,
     if the value corresponding to the parameter has a certain type,
     then reading the parameter from the computation state
     succeeds and yields a value of that type."))
  (b* (((when (endp arg-types-compst)) (mv nil nil (pos-fix thm-index)))
       (formula
        `(b* ((compst
               (c::push-frame
                (c::frame fun
                          (list
                           (c::init-scope ',all-params (list ,@all-args))))
                compst0)))
           (implies (and ,@all-arg-types)
                    ,(car arg-types-compst))))
       (hints
        `(("Goal" :in-theory '(,init-scope-thm
                               (:e ident)
                               c::push-frame
                               c::compustate-has-var-with-type-p
                               c::objdesign-of-var
                               c::objdesign-of-var-aux
                               c::compustate-frames-number
                               c::top-frame
                               c::read-object
                               c::scopep-of-update
                               (:e c::scopep)
                               c::compustate->frames-of-compustate
                               c::frame->scopes-of-frame
                               c::frame-fix-when-framep
                               c::frame-list-fix-of-cons
                               c::mapp-when-scopep
                               c::framep-of-frame
                               c::objdesign-auto->frame-of-objdesign-auto
                               c::objdesign-auto->name-of-objdesign-auto
                               c::objdesign-auto->scope-of-objdesign-auto
                               c::return-type-of-objdesign-auto
                               c::scope-fix-when-scopep
                               c::scope-fix
                               c::scope-list-fix-of-cons
                               (:e c::ident)
                               (:e c::ident-fix$inline)
                               (:e c::identp)
                               (:t c::objdesign-auto)
                               omap::assoc-of-update
                               simpadd0-param-thm-list-lemma
                               nfix
                               fix
                               len
                               car-cons
                               cdr-cons
                               commutativity-of-+
                               acl2::fold-consts-in-+
                               acl2::len-of-append
                               acl2::len-of-rev
                               acl2::rev-of-cons
                               (:e acl2::fast-<<)
                               unicity-of-0
                               (:e rev)
                               (:t len)
                               (:e c::type-fix)))))
       ((mv thm-name thm-index) (gen-thm-name const-new thm-index))
       (thm-event `(defruled ,thm-name
                     ,formula
                     :hints ,hints))
       ((mv more-thm-events more-thm-names thm-index)
        (simpadd0-gen-param-thms (cdr arg-types-compst)
                                 all-arg-types
                                 all-params
                                 all-args
                                 init-scope-thm
                                 const-new
                                 thm-index)))
    (mv (cons thm-event more-thm-events)
        (cons thm-name more-thm-names)
        thm-index))
  :guard-hints (("Goal" :in-theory (enable len)))

  ///

  (defret len-of-simpadd-gen-param-thms.thm-names
    (equal (len thm-names)
           (len thm-events))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled simpadd0-param-thm-list-lemma
    (equal (nth (len l) (append (rev l) (list x)))
           x)
    :use (:instance lemma (l (rev l)))
    :prep-lemmas
    ((defruled lemma
       (equal (nth (len l) (append l (list x)))
              x)
       :induct t
       :enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-ident ((ident identp)
                             (info var-infop)
                             (gin simpadd0-ginp))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform an identifier expression (i.e. a variable)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This undergoes no actual transformation,
     but we introduce it for uniformity,
     also because we may eventually evolve the @(tsee simpadd0) implementation
     into a much more general transformation.
     Thus, the output expression consists of
     the identifier and validation information passed as inputs.")
   (xdoc::p
    "We generate a theorem
     of the variable has a type supported in our C formalization
     (which we check in the validation information),
     and if the variable is in the variable-type map."))
  (b* ((ident (ident-fix ident))
       ((var-info info) (var-info-fix info))
       ((simpadd0-gin gin) gin)
       (expr (make-expr-ident :ident ident :info info))
       (gout-no-thm (simpadd0-gout-no-thm gin))
       ((unless (and (ident-formalp ident)
                     (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr gout-no-thm))
       ((mv & cvar) (ldm-ident ident)) ; ERP is NIL because FORMALP
       ((mv & ctype) (ldm-type info.type)) ; ERP is NIL because FORMALP
       ((unless (omap::assoc cvar gin.vartys))
        (mv expr gout-no-thm))
       (hints `(("Goal"
                 :in-theory '((:e c::expr-ident)
                              (:e c::type-fix))
                 :use (:instance expr-ident-compustate-vars
                                 (var ',cvar)
                                 (type ',ctype)))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))
  :hooks (:fix)

  ///

  (defret expr-unambp-of-simpadd0-expr-ident
    (expr-unambp expr))

  (defret expr-annop-of-simpadd0-expr-ident
    (expr-annop expr))

  (defret expr-aidentp-of-simpadd0-expr-ident
    (expr-aidentp expr gcc)
    :hyp (ident-aidentp ident gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-const ((const constp) (gin simpadd0-ginp))
  :guard (const-annop const)
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This undergoes no actual transformation,
     but we introduce it for uniformity,
     also because we may eventually evolve the @(tsee simpadd0) implementation
     into a much more general transformation.
     Thus, the output expression consists of the constant passed as input.")
   (xdoc::p
    "We generate a theorem
     if the constant is an integer one,
     and under the following additional conditions:")
   (xdoc::ul
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('int'),
      it fits in 32 bits.")
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('long'),
      it fits in 64 bits.")
    (xdoc::li
     "If the constant has type (@('signed') or @('unsigned')) @('long long'),
      it fits in 64 bits."))
   (xdoc::p
    "The reason for these additional conditions is that
     our current dynamic semantics assumes that
     those types have those sizes,
     while our validator is more general
     (@(tsee c$::valid-iconst) takes an implementation environment as input,
     which specifies the size of those types).
     Until we extend our dynamic semantics to be more general,
     we need this additional condition for proof generation."))
  (b* (((simpadd0-gin gin) gin)
       (expr (expr-const const))
       (no-thm-gout (simpadd0-gout-no-thm gin))
       ((unless (const-case const :int)) (mv expr no-thm-gout))
       ((iconst iconst) (const-int->unwrap const))
       ((iconst-info info) iconst.info)
       ((unless (or (and (type-case info.type :sint)
                         (<= info.value (c::sint-max)))
                    (and (type-case info.type :uint)
                         (<= info.value (c::uint-max)))
                    (and (type-case info.type :slong)
                         (<= info.value (c::slong-max)))
                    (and (type-case info.type :ulong)
                         (<= info.value (c::ulong-max)))
                    (and (type-case info.type :sllong)
                         (<= info.value (c::sllong-max)))
                    (and (type-case info.type :ullong)
                         (<= info.value (c::ullong-max)))))
        (mv expr no-thm-gout))
       (hints `(("Goal" :in-theory '(c::exec-expr-pure
                                     (:e c::expr-const)
                                     (:e c::expr-fix)
                                     (:e c::expr-kind)
                                     (:e c::expr-const->get)
                                     (:e c::exec-const)
                                     (:e c::expr-value->value)
                                     (:e c::type-of-value)))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system)))) ; for speed
  :hooks (:fix)

  ///

  (defret expr-unambp-of-simpadd0-expr-const
    (expr-unambp expr))

  (defret expr-annop-of-simpadd0-expr-const
    (expr-annop expr)
    :hyp (const-annop const))

  (defret expr-aidentp-of-simpadd0-expr-const
    (expr-aidentp expr gcc)
    :hyp (const-aidentp const gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-paren ((inner exprp)
                             (inner-new exprp)
                             (inner-thm-name symbolp)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp inner)
              (expr-annop inner)
              (expr-unambp inner-new)
              (expr-annop inner-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a parenthesized pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     parenthesizing the possibly transformed inner expression.
     We generate a theorem iff
     a theorem was generated for the inner expression,
     and the inner expression is pure.
     The function @(tsee ldm-expr) maps
     a parenthesized expression to the same as the inner expression.
     Thus, the theorem for the parenthesized expression
     follows directly from the one for the inner expression."))
  (b* ((expr (expr-paren inner))
       (expr-new (expr-paren inner-new))
       ((simpadd0-gin gin) gin)
       ((unless (and inner-thm-name
                     (expr-purep inner)))
        (mv expr-new (simpadd0-gout-no-thm gin)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr))
                 :use ,inner-thm-name)))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-paren
    (expr-unambp expr)
    :hyp (expr-unambp inner-new))

  (defret expr-annop-of-simpadd0-expr-paren
    (expr-annop expr)
    :hyp (expr-annop inner-new))

  (defret expr-aidentp-of-simpadd0-expr-paren
    (expr-aidentp expr gcc)
    :hyp (expr-aidentp inner-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-unary ((op unopp)
                             (arg exprp)
                             (arg-new exprp)
                             (arg-thm-name symbolp)
                             (info expr-unary-infop)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp arg)
              (expr-annop arg)
              (expr-unambp arg-new)
              (expr-annop arg-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the unary operator with
     the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expression,
     the argument expression is pure,
     and the unary operator is among @('+'), @('-'), @('~') and @('!').
     The theorem is proved via two general ones that we prove below."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-unary :op op :arg arg :info info))
       (expr-new (make-expr-unary :op op :arg arg-new :info info))
       ((unless (and arg-thm-name
                     (expr-purep arg)
                     (member-eq (unop-kind op)
                                '(:plus :minus :bitnot :lognot))))
        (mv expr-new (simpadd0-gout-no-thm gin)))
       ((mv & old-arg) (ldm-expr arg)) ; ERP must be NIL
       ((mv & new-arg) (ldm-expr arg-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::unop-nonpointerp)
                              (:e c::unop-kind)
                              (:e c::expr-unary)
                              (:e c::type-kind)
                              (:e c::promote-type)
                              (:e c::type-nonchar-integerp)
                              (:e c::type-sint)
                              (:e member-equal))
                 :use (,arg-thm-name
                       (:instance
                        expr-unary-congruence
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (old-arg ',old-arg)
                        (new-arg ',new-arg))
                       (:instance
                        expr-unary-errors
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (arg ',old-arg))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-unary
    (expr-unambp expr)
    :hyp (expr-unambp arg-new))

  (defret expr-annop-of-simpadd0-expr-unary
    (expr-annop expr)
    :hyp (and (expr-annop arg-new)
              (expr-unary-infop info)))

  (defret expr-aidentp-of-simpadd0-expr-unary
    (expr-aidentp expr gcc)
    :hyp (expr-aidentp arg-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-cast ((type tynamep)
                            (type-new tynamep)
                            (type-thm-name symbolp)
                            (arg exprp)
                            (arg-new exprp)
                            (arg-thm-name symbolp)
                            (info tyname-infop)
                            (gin simpadd0-ginp))
  :guard (and (tyname-unambp type)
              (tyname-annop type)
              (tyname-unambp type-new)
              (tyname-annop type-new)
              (expr-unambp arg)
              (expr-annop arg)
              (expr-unambp arg-new)
              (expr-annop arg-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed type name with
     the possibly transformed argument expression.")
   (xdoc::p
    "For now, we generate no theorem for the transformation of the type name,
     but we double-check that here.
     We generate a theorem only if we generated one for the argument expression,
     the argument expression is pure,
     and the old and new type names are the same (i.e. no transformation)."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-cast :type type :arg arg))
       (expr-new (make-expr-cast :type type-new :arg arg-new))
       ((when type-thm-name)
        (raise "Internal error: ~
                unexpected type name transformation theorem ~x0."
               type-thm-name)
        (mv expr-new (irr-simpadd0-gout)))
       ((tyname-info info) info)
       ((unless (and arg-thm-name
                     (expr-purep arg)
                     (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))))
        (mv expr-new (simpadd0-gout-no-thm gin)))
       ((unless (equal type type-new))
        (raise "Internal error: ~
                type names ~x0 and ~x1 differ."
               type type-new)
        (mv expr-new (irr-simpadd0-gout)))
       ((mv & ctyname) (ldm-tyname type)) ; ERP must be NIL
       ((mv & old-arg) (ldm-expr arg)) ; ERP must be NIL
       ((mv & new-arg) (ldm-expr arg-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::expr-cast)
                              (:e c::tyname-to-type)
                              (:e c::type-nonchar-integerp))
                 :use (,arg-thm-name
                       (:instance
                        expr-cast-congruence
                        (tyname ',ctyname)
                        (old-arg ',old-arg)
                        (new-arg ',new-arg))
                       (:instance
                        expr-cast-errors
                        (tyname ',ctyname)
                        (arg ',old-arg))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-cast
    (expr-unambp expr)
    :hyp (and (tyname-unambp type-new)
              (expr-unambp arg-new)))

  (defret expr-annop-of-simpadd0-expr-cast
    (expr-annop expr)
    :hyp (and (tyname-annop type-new)
              (expr-annop arg-new)))

  (defret expr-aidentp-of-simpadd0-expr-cast
    (expr-aidentp expr gcc)
    :hyp (and (tyname-aidentp type-new gcc)
              (expr-aidentp arg-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-binary ((op binopp)
                              (arg1 exprp)
                              (arg1-new exprp)
                              (arg1-thm-name symbolp)
                              (arg2 exprp)
                              (arg2-new exprp)
                              (arg2-thm-name symbolp)
                              (info expr-binary-infop)
                              (gin simpadd0-ginp))
  :guard (and (expr-unambp arg1)
              (expr-annop arg1)
              (expr-unambp arg1-new)
              (expr-annop arg1-new)
              (expr-unambp arg2)
              (expr-annop arg2)
              (expr-unambp arg2-new)
              (expr-annop arg2-new))
  :returns (mv (expr exprp) (gout simpadd0-goutp))
  :short "Transform a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the binary operator with
     the possibly transformed argument expressions,
     unless the binary operator is @('+')
     and the possibly transformed left argument is an @('int') expression
     and the possibly transformed right argument is
     an @('int') octal 0 without leading zeros,
     in which case the resulting expression is just that expression.
     This is the core of this simple transformation.")
   (xdoc::p
    "We generate a theorem only if
     theorems were generated for both argument expressions,
     and the argument expressions are pure
     (the latter check excludes cases in which an assignment expression,
     for which we may have generated a theorem,
     is combined into a larger expression,
     which our dynamic semantics does not handle currently).
     We generate a theorem for pure strict and non-strict operators.
     We generate a theorem for simple assignment expressions
     whose left side is a variable of integer type
     and whose right side is a pure expression of the same integer type."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-binary :op op :arg1 arg1 :arg2 arg2 :info info))
       (simpp (and (binop-case op :add)
                   (type-case (expr-type arg1-new) :sint)
                   (expr-zerop arg2-new)))
       (expr-new (if simpp
                     (expr-fix arg1-new)
                   (make-expr-binary
                    :op op :arg1 arg1-new :arg2 arg2-new :info info)))
       (gout-no-thm (simpadd0-gout-no-thm gin))
       ((unless (and arg1-thm-name
                     arg2-thm-name
                     (expr-purep arg1)
                     (expr-purep arg2)))
        (mv expr-new gout-no-thm))
       (cop (ldm-binop op)) ; ERP must be NIL
       ((mv & old-arg1) (ldm-expr arg1)) ; ERP must be NIL
       ((mv & old-arg2) (ldm-expr arg2)) ; ERP must be NIL
       ((mv & new-arg1) (ldm-expr arg1-new)) ; ERP must be NIL
       ((mv & new-arg2) (ldm-expr arg2-new))) ; ERP must be NIL
    (cond
     ((member-eq (binop-kind op)
                 '(:mul :div :rem :add :sub :shl :shr
                   :lt :gt :le :ge :eq :ne
                   :bitand :bitxor :bitior))
      (b* ((hints `(("Goal"
                     :in-theory '((:e c::iconst-length-none)
                                  (:e c::iconst-base-oct)
                                  (:e c::iconst)
                                  (:e c::const-int)
                                  (:e c::expr-const)
                                  (:e c::binop-kind)
                                  (:e c::binop-add)
                                  (:e c::binop-purep)
                                  (:e c::binop-strictp)
                                  (:e c::expr-binary)
                                  (:e c::type-nonchar-integerp)
                                  (:e c::promote-type)
                                  (:e c::uaconvert-types)
                                  (:e c::type-sint)
                                  (:e member-equal))
                     :use (,arg1-thm-name
                           ,arg2-thm-name
                           (:instance
                            expr-binary-pure-strict-congruence
                            (op ',cop)
                            (old-arg1 ',old-arg1)
                            (old-arg2 ',old-arg2)
                            (new-arg1 ',new-arg1)
                            (new-arg2 ',new-arg2))
                           (:instance
                            expr-binary-pure-strict-errors
                            (op ',cop)
                            (arg1 ',old-arg1)
                            (arg2 ',old-arg2))
                           ,@(and simpp
                                  `((:instance
                                     simpadd0-expr-binary-simp-congruence
                                     (expr ',new-arg1))))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-pure-thm expr
                               expr-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
        (mv expr-new
            (make-simpadd0-gout :events (cons thm-event gin.events)
                                :thm-index thm-index
                                :thm-name thm-name
                                :vartys gin.vartys))))
     ((member-eq (binop-kind op) '(:logand :logor))
      (b* ((hints
            `(("Goal"
               :in-theory '((:e c::expr-binary)
                            (:e c::binop-logand)
                            (:e c::binop-logor)
                            (:e c::type-sint)
                            (:e c::type-nonchar-integerp))
               :use
               (,arg1-thm-name
                ,arg2-thm-name
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-first-congruence)
                    (:logor 'expr-binary-logor-first-congruence))
                 (old-arg1 ',old-arg1)
                 (old-arg2 ',old-arg2)
                 (new-arg1 ',new-arg1)
                 (new-arg2 ',new-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-second-congruence)
                    (:logor 'expr-binary-logor-second-congruence))
                 (old-arg1 ',old-arg1)
                 (old-arg2 ',old-arg2)
                 (new-arg1 ',new-arg1)
                 (new-arg2 ',new-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-first-errors)
                    (:logor 'expr-binary-logor-first-errors))
                 (arg1 ',old-arg1)
                 (arg2 ',old-arg2))
                (:instance
                 ,(case (binop-kind op)
                    (:logand 'expr-binary-logand-second-errors)
                    (:logor 'expr-binary-logor-second-errors))
                 (arg1 ',old-arg1)
                 (arg2 ',old-arg2))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-pure-thm expr
                               expr-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
        (mv expr-new
            (make-simpadd0-gout :events (cons thm-event gin.events)
                                :thm-index thm-index
                                :thm-name thm-name
                                :vartys gin.vartys))))
     ((eq (binop-kind op) :asg)
      (b* (((unless (and (expr-case arg1 :ident)
                         (equal (expr-type arg1)
                                (expr-type arg2))
                         (type-integerp (expr-type arg1))))
            (mv expr-new gout-no-thm))
           ((mv & cvar) (ldm-ident (expr-ident->ident arg1))) ; ERP must be NIL
           (hints
            `(("Goal"
               :in-theory
               '((:e c::expr-kind)
                 (:e c::expr-ident)
                 (:e c::expr-ident->get)
                 (:e c::expr-binary->op)
                 (:e c::expr-binary->arg1)
                 (:e c::expr-binary->arg2)
                 (:e c::expr-binary)
                 (:e c::binop-asg)
                 (:e c::ident)
                 (:e c::type-nonchar-integerp)
                 (:e c::type-fix)
                 c::not-errorp-when-compustate-has-var-with-type-p
                 c::type-of-value-when-compustate-has-var-with-type-p
                 c::valuep-of-read-object-of-objdesign-of-var
                 c::not-errorp-when-valuep
                 expr-binary-asg-compustate-vars)
               :use (,arg1-thm-name
                     ,arg2-thm-name
                     (:instance
                      expr-binary-asg-congruence
                      (old-arg ',old-arg2)
                      (new-arg ',new-arg2)
                      (var ',cvar))
                     (:instance
                      expr-binary-asg-errors
                      (var ',cvar)
                      (expr ',old-arg2)
                      (fenv old-fenv))))))
           ((mv thm-event thm-name thm-index)
            (gen-expr-asg-thm expr
                              expr-new
                              gin.vartys
                              gin.const-new
                              gin.thm-index
                              hints)))
        (mv expr-new
            (make-simpadd0-gout :events (cons thm-event gin.events)
                                :thm-index thm-index
                                :thm-name thm-name
                                :vartys gin.vartys))))
     (t (mv expr-new gout-no-thm))))

  ///

  (defret expr-unambp-of-simpadd0-expr-binary
    (expr-unambp expr)
    :hyp (and (expr-unambp arg1-new)
              (expr-unambp arg2-new)))

  (defret expr-annop-of-simpadd0-expr-binary
    (expr-annop expr)
    :hyp (and (expr-annop arg1-new)
              (expr-annop arg2-new)
              (expr-binary-infop info)))

  (defret expr-aidentp-of-simpadd0-expr-binary
    (expr-aidentp expr gcc)
    :hyp (and (expr-aidentp arg1-new gcc)
              (expr-aidentp arg2-new gcc)))

  (defruledl c::add-values-of-sint-and-sint0
    (implies (and (c::valuep val)
                  (c::value-case val :sint)
                  (equal sint0 (c::value-sint 0)))
             (equal (c::add-values val sint0)
                    val))
    :enable (c::add-values
             c::add-arithmetic-values
             c::add-integer-values
             c::value-arithmeticp-when-sintp
             c::value-integerp-when-sintp
             c::uaconvert-values-when-sintp-and-sintp
             c::sintp-alt-def
             c::type-of-value-when-sintp
             c::result-integer-value
             c::integer-type-rangep
             fix
             ifix))

  (defruled simpadd0-expr-binary-simp-congruence
    (b* ((zero (c::expr-const
                (c::const-int
                 (c::make-iconst
                  :value 0
                  :base (c::iconst-base-oct)
                  :unsignedp nil
                  :length (c::iconst-length-none)))))
         (expr+zero (c::expr-binary (c::binop-add) expr zero))
         (expr-result (c::exec-expr-pure expr compst))
         (expr-value (c::expr-value->value expr-result))
         (expr+zero-result (c::exec-expr-pure expr+zero compst))
         (expr+zero-value (c::expr-value->value expr+zero-result)))
      (implies (and (not (c::errorp expr-result))
                    (equal (c::type-of-value expr-value) (c::type-sint)))
               (equal expr+zero-value expr-value)))
    :enable (c::exec-expr-pure
             c::exec-binary-strict-pure
             c::eval-binary-strict-pure
             c::apconvert-expr-value-when-not-array
             c::add-values-of-sint-and-sint0
             c::type-of-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-cond ((test exprp)
                            (test-new exprp)
                            (test-thm-name symbolp)
                            (then expr-optionp)
                            (then-new expr-optionp)
                            (then-thm-name symbolp)
                            (else exprp)
                            (else-new exprp)
                            (else-thm-name symbolp)
                            (gin simpadd0-ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (expr-option-unambp then)
              (expr-option-annop then)
              (expr-option-unambp then-new)
              (expr-option-annop then-new)
              (expr-unambp else)
              (expr-annop else)
              (expr-unambp else-new)
              (expr-annop else-new))
  :returns (mv (expr exprp) (gou simpadd0-goutp))
  :short "Transform a conditional expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting expression is obtained by
     combining the possibly transformed argument expression.")
   (xdoc::p
    "We generate a theorem iff
     a theorem was generated for the argument expressions,
     and the argument expressions are pure.
     The theorem is proved via a few general ones that we prove below.
     These are a bit more complicated than for strict expressions,
     because conditional expressions are non-strict:
     the branch not taken could return an error
     while the conditional expression does not."))
  (b* (((simpadd0-gin gin) gin)
       (expr (make-expr-cond :test test :then then :else else))
       (expr-new (make-expr-cond :test test-new :then then-new :else else-new))
       ((unless (and test-thm-name
                     then-thm-name
                     else-thm-name
                     (expr-purep test)
                     (expr-option-purep then)
                     (expr-purep else)))
        (mv expr-new (simpadd0-gout-no-thm gin)))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & old-then) (ldm-expr-option then)) ; ERP must be NIL
       ((mv & old-else) (ldm-expr else)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & new-then) (ldm-expr-option then-new)) ; ERP must be NIL
       ((mv & new-else) (ldm-expr else-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory '((:e c::expr-cond)
                              (:e c::type-nonchar-integerp))
                 :use (,test-thm-name
                       ,then-thm-name
                       ,else-thm-name
                       (:instance
                        expr-cond-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else))
                       (:instance
                        expr-cond-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else))
                       (:instance
                        expr-cond-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))
                       (:instance
                        expr-cond-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))
                       (:instance
                        expr-cond-else-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-pure-thm expr
                           expr-new
                           gin.vartys
                           gin.const-new
                           gin.thm-index
                           hints)))
    (mv expr-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-cond
    (expr-unambp expr)
    :hyp (and (expr-unambp test-new)
              (expr-option-unambp then-new)
              (expr-unambp else-new)))

  (defret expr-annop-of-simpadd0-expr-cond
    (expr-annop expr)
    :hyp (and (expr-annop test-new)
              (expr-option-annop then-new)
              (expr-annop else-new)))

  (defret expr-aidentp-of-simpadd0-expr-cond
    (expr-aidentp expr gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (expr-option-aidentp then-new gcc)
              (expr-aidentp else-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-initer-single ((expr exprp)
                                (expr-new exprp)
                                (expr-thm-name symbolp)
                                (gin simpadd0-ginp))
  :guard (and (expr-unambp expr)
              (expr-annop expr)
              (expr-unambp expr-new)
              (expr-annop expr-new))
  :returns (mv (initer initerp) (gout simpadd0-goutp))
  :short "Transform an initializer consisting of a single expression."
  (b* (((simpadd0-gin gin) gin)
       (initer (initer-single expr))
       (initer-new (initer-single expr-new))
       ((unless (and expr-thm-name
                     (expr-purep expr)))
        (mv initer-new (simpadd0-gout-no-thm gin)))
       ((mv & old-expr) (ldm-expr expr)) ; ERP must be NIL
       ((mv & new-expr) (ldm-expr expr-new)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::initer-kind)
                        (:e c::initer-single)
                        (:e c::initer-single->get)
                        (:e c::expr-kind)
                        (:e c::type-nonchar-integerp)
                        initer-single-pure-compustate-vars)
           :use ((:instance ,expr-thm-name)
                 (:instance initer-single-pure-congruence
                            (old-expr ',old-expr)
                            (new-expr ',new-expr))
                 (:instance initer-single-pure-errors
                            (expr ',old-expr)
                            (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-initer-single-thm initer
                               initer-new
                               gin.vartys
                               gin.const-new
                               gin.thm-index
                               hints)))
    (mv initer-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret initer-unambp-of-simpadd0-initer-single
    (initer-unambp initer)
    :hyp (expr-unambp expr-new))

  (defret initer-annop-of-simpadd0-initer-single
    (initer-annop initer)
    :hyp (expr-annop expr-new))

  (defret initer-aidentp-of-simpadd0-initer-single
    (initer-aidentp initer gcc)
    :hyp (expr-aidentp expr-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-expr ((expr? expr-optionp)
                            (expr?-new expr-optionp)
                            (expr?-thm-name symbolp)
                            info
                            (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-annop expr?)
              (expr-option-unambp expr?-new)
              (expr-option-annop expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform an expression statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the optional expression into an expression statement.")
   (xdoc::p
    "We generate a theorem
     if there is no expression (i.e. the null statement),
     or if there is an assignment expression
     (which we recognize by checking that it is not pure)
     for which a theorem was generated.
     An expression statement does not change the variables in scope,
     so we use the variable-type map from the validation table in the AST
     for both before and after the statement, in the generated theorem."))
  (b* (((simpadd0-gin gin) gin)
       (stmt (make-stmt-expr :expr? expr? :info info))
       (stmt-new (make-stmt-expr :expr? expr?-new :info info))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv stmt-new (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    (and expr?-thm-name
                         (not (expr-purep expr?)))))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       ((mv & old-expr?) (ldm-expr-option expr?)) ; ERP must be NIL
       ((mv & new-expr?) (ldm-expr-option expr?-new)) ; ERP must be NIL
       (hints
        (if expr?
            `(("Goal"
               :in-theory '((:e c::stmt-kind)
                            (:e c::stmt-expr->get)
                            (:e c::stmt-expr)
                            (:e c::expr-kind)
                            (:e set::insert)
                            stmt-expr-asg-compustate-vars)
               :use ((:instance
                      ,expr?-thm-name
                      (limit (- limit 2)))
                     (:instance
                      stmt-expr-asg-congruence
                      (old-expr ',old-expr?)
                      (new-expr ',new-expr?))
                     (:instance
                      stmt-expr-asg-errors
                      (expr ',old-expr?)
                      (fenv old-fenv)))))
          `(("Goal"
             :in-theory '((:e c::stmt-kind)
                          (:e c::stmt-null)
                          c::type-option-of-stmt-value
                          (:e set::in)
                          (:e set::insert)
                          stmt-null-compustate-vars)
             :use (stmt-null-congruence)))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))
  :guard-hints (("Goal" :in-theory (enable ldm-expr-option)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-expr
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new))

  (defret stmt-annop-of-simpadd0-stmt-expr
    (stmt-annop stmt)
    :hyp (expr-option-annop expr?-new))

  (defret stmt-aidentp-of-simpadd0-stmt-expr
    (stmt-aidentp stmt gcc)
    :hyp (expr-option-aidentp expr?-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-return ((expr? expr-optionp)
                              (expr?-new expr-optionp)
                              (expr?-thm-name symbolp)
                              info
                              (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-annop expr?)
              (expr-option-unambp expr?-new)
              (expr-option-annop expr?-new)
              (iff expr? expr?-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform a return statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new optional expression into a return statement.")
   (xdoc::p
    "We generate a theorem iff
     the expression is absent
     or a theorem was generated for the expression.
     Note that the expression is present in the old statement
     iff it is present in the new statement;
     also note that, if there is no expression,
     old and new statements cannot differ.
     If the expression is present,
     the theorem is proved via two general ones proved below;
     if the expression is absent,
     the theorem is proved via another general one proved below."))
  (b* (((simpadd0-gin gin) gin)
       (stmt (make-stmt-return :expr? expr? :info info))
       (stmt-new (make-stmt-return :expr? expr?-new :info info))
       ((unless (iff expr? expr?-new))
        (raise "Internal error: ~
                return statement with optional expression ~x0 ~
                is transformed into ~
                return statement with optional expression ~x1."
               expr? expr?-new)
        (mv stmt-new (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    (and expr?-thm-name
                         (expr-purep expr?))))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       ((mv & old-expr?) (ldm-expr-option expr?)) ; ERP must be NIL
       ((mv & new-expr?) (ldm-expr-option expr?-new)) ; ERP must be NIL
       (hints
        (if expr?
            `(("Goal"
               :in-theory '((:e set::insert)
                            (:e c::stmt-kind)
                            (:e c::stmt-return)
                            (:e c::stmt-return->value)
                            (:e c::expr-kind)
                            (:e c::type-nonchar-integerp)
                            stmt-return-compustate-vars)
               :use (,expr?-thm-name
                     (:instance
                      stmt-return-value-congruence
                      (old-expr ',old-expr?)
                      (new-expr ',new-expr?))
                     (:instance
                      stmt-return-errors
                      (expr ',old-expr?)
                      (fenv old-fenv)))))
          `(("Goal"
             :in-theory '((:e c::stmt-return)
                          (:e c::type-void)
                          (:e set::insert)
                          stmt-return-compustate-vars)
             :use (stmt-return-novalue-congruence)))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-return
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new))

  (defret stmt-annop-of-simpadd0-stmt-return
    (stmt-annop stmt)
    :hyp (expr-option-annop expr?-new))

  (defret stmt-aidentp-of-simpadd0-stmt-return
    (stmt-aidentp stmt gcc)
    :hyp (expr-option-aidentp expr?-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-if ((test exprp)
                          (test-new exprp)
                          (test-thm-name symbolp)
                          (then stmtp)
                          (then-new stmtp)
                          (then-thm-name symbolp)
                          (gin simpadd0-ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp then)
              (stmt-annop then)
              (stmt-unambp then-new)
              (stmt-annop then-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform an @('if') statement (without @('else'))."
  (b* (((simpadd0-gin gin) gin)
       (stmt (make-stmt-if :test test :then then))
       (stmt-new (make-stmt-if :test test-new :then then-new))
       ((unless (and test-thm-name
                     then-thm-name
                     (expr-purep test)))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (then-types (stmt-types then))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-then) (ldm-stmt then)) ; ERP must be NIL
       ((mv & new-then) (ldm-stmt then-new)) ; ERP must be NIL
       ((mv & then-ctypes) (ldm-type-option-set then-types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::stmt-kind)
                   (:e c::stmt-if->test)
                   (:e c::stmt-if->then)
                   (:e c::stmt-if)
                   (:e c::type-nonchar-integerp)
                   (:e set::insert)
                   (:e set::subset)
                   set::subset-in
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   stmt-if-compustate-vars)
                 :use (,test-thm-name
                       (:instance ,then-thm-name (limit (1- limit)))
                       (:instance
                        stmt-if-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (types ',then-ctypes))
                       (:instance
                        stmt-if-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (new-test ',new-test)
                        (new-then ',new-then))
                       (:instance
                        stmt-if-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (fenv old-fenv))
                       (:instance
                        stmt-if-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-if
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp then-new)))

  (defret stmt-annop-of-simpadd0-stmt-if
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop then-new)))

  (defret stmt-aidentp-of-simpadd0-stmt-if
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp then-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-ifelse ((test exprp)
                              (test-new exprp)
                              (test-thm-name symbolp)
                              (then stmtp)
                              (then-new stmtp)
                              (then-thm-name symbolp)
                              (else stmtp)
                              (else-new stmtp)
                              (else-thm-name symbolp)
                              (gin simpadd0-ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp then)
              (stmt-annop then)
              (stmt-unambp then-new)
              (stmt-annop then-new)
              (stmt-unambp else)
              (stmt-annop else)
              (stmt-unambp else-new)
              (stmt-annop else-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform an @('if')-@('else') statement."
  (b* (((simpadd0-gin gin) gin)
       (stmt (make-stmt-ifelse :test test :then then :else else))
       (stmt-new
        (make-stmt-ifelse :test test-new :then then-new :else else-new))
       ((unless (and test-thm-name
                     then-thm-name
                     else-thm-name
                     (expr-purep test)))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (then-types (stmt-types then))
       (else-types (stmt-types else))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-then) (ldm-stmt then)) ; ERP must be NIL
       ((mv & new-then) (ldm-stmt then-new)) ; ERP must be NIL
       ((mv & old-else) (ldm-stmt else)) ; ERP must be NIL
       ((mv & new-else) (ldm-stmt else-new)) ; ERP must be NIL
       ((mv & then-ctypes) (ldm-type-option-set then-types)) ; ERP must be NIL
       ((mv & else-ctypes) (ldm-type-option-set else-types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::stmt-kind)
                   (:e c::stmt-ifelse->test)
                   (:e c::stmt-ifelse->then)
                   (:e c::stmt-ifelse->else)
                   (:e c::stmt-ifelse)
                   (:e c::type-nonchar-integerp)
                   (:e set::insert)
                   (:e set::subset)
                   set::subset-in
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   stmt-ifelse-compustate-vars)
                 :use (,test-thm-name
                       (:instance ,then-thm-name (limit (1- limit)))
                       (:instance ,else-thm-name (limit (1- limit)))
                       (:instance
                        stmt-ifelse-true-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else)
                        (types ',then-ctypes))
                       (:instance
                        stmt-ifelse-false-congruence
                        (old-test ',old-test)
                        (old-then ',old-then)
                        (old-else ',old-else)
                        (new-test ',new-test)
                        (new-then ',new-then)
                        (new-else ',new-else)
                        (types ',else-ctypes))
                       (:instance
                        stmt-ifelse-test-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))
                       (:instance
                        stmt-ifelse-then-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))
                       (:instance
                        stmt-ifelse-else-errors
                        (test ',old-test)
                        (then ',old-then)
                        (else ',old-else)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-ifelse
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp then-new)
              (stmt-unambp else-new)))

  (defret stmt-annop-of-simpadd0-stmt-ifelse
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop then-new)
              (stmt-annop else-new)))

  (defret stmt-aidentp-of-simpadd0-stmt-ifelse
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp then-new gcc)
              (stmt-aidentp else-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-compound ((items block-item-listp)
                                (items-new block-item-listp)
                                (items-thm-name symbolp)
                                (gin simpadd0-ginp))
  :guard (and (block-item-list-unambp items)
              (block-item-list-annop items)
              (block-item-list-unambp items-new)
              (block-item-list-annop items-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform a compound statement."
  (b* (((simpadd0-gin gin) gin)
       (stmt (stmt-compound items))
       (stmt-new (stmt-compound items-new))
       ((unless items-thm-name)
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (types (block-item-list-types items))
       ((mv & old-items) (ldm-block-item-list items)) ; ERP must be NIL
       ((mv & new-items) (ldm-block-item-list items-new)) ; ERP must be NIL
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::stmt-compound)
                        (:e c::stmt-kind)
                        c::compustate-frames-number-of-enter-scope
                        c::compustate-has-var-with-type-p-of-enter-scope
                        stmt-compound-compustate-vars)
           :use ((:instance ,items-thm-name
                            (compst (c::enter-scope compst))
                            (limit (1- limit)))
                 (:instance stmt-compound-congruence
                            (old-items ',old-items)
                            (new-items ',new-items)
                            (types ',ctypes))
                 (:instance stmt-compound-errors
                            (items ',old-items)
                            (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-compound
    (stmt-unambp stmt)
    :hyp (block-item-list-unambp items-new))

  (defret stmt-annop-of-simpadd0-stmt-compound
    (stmt-annop stmt)
    :hyp (block-item-list-annop items-new))

  (defret stmt-aidentp-of-simpadd0-stmt-compound
    (stmt-aidentp stmt gcc)
    :hyp (block-item-list-aidentp items-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-while ((test exprp)
                             (test-new exprp)
                             (test-thm-name symbolp)
                             (body stmtp)
                             (body-new stmtp)
                             (body-thm-name symbolp)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp test)
              (expr-annop test)
              (expr-unambp test-new)
              (expr-annop test-new)
              (stmt-unambp body)
              (stmt-annop body)
              (stmt-unambp body-new)
              (stmt-annop body-new))
  :returns (mv (stmt stmtp) (gout simpadd0-goutp))
  :short "Transform a @('while') loop."
  (b* (((simpadd0-gin gin) gin)
       (stmt (make-stmt-while :test test
                              :body body))
       (stmt-new (make-stmt-while :test test-new
                                  :body body-new))
       ((unless (and test-thm-name
                     body-thm-name))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (types (stmt-types body))
       ((mv & old-test) (ldm-expr test)) ; ERP must be NIL
       ((mv & new-test) (ldm-expr test-new)) ; ERP must be NIL
       ((mv & old-body) (ldm-stmt body)) ; ERP must be NIL
       ((mv & new-body) (ldm-stmt body-new)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory '((:e c::stmt-while)
                        (:e c::ident-type-map-fix)
                        (:e omap::emptyp)
                        (:e omap::head)
                        (:e omap::tail)
                        (:e set::insert)
                        (:e c::type-nonchar-integerp)
                        while-hyp
                        c::compustate-has-vars-with-types-p)
           :use ((:instance
                  ,test-thm-name
                  (compst (mv-nth 0 (while-hyp-witness ',old-test
                                                       ',new-test
                                                       ',old-body
                                                       ',new-body
                                                       old-fenv
                                                       new-fenv
                                                       ',types
                                                       ',gin.vartys))))
                 (:instance
                  ,body-thm-name
                  (compst (mv-nth 0 (while-hyp-witness ',old-test
                                                       ',new-test
                                                       ',old-body
                                                       ',new-body
                                                       old-fenv
                                                       new-fenv
                                                       ',types
                                                       ',gin.vartys)))
                  (limit (mv-nth 1 (while-hyp-witness ',old-test
                                                      ',new-test
                                                      ',old-body
                                                      ',new-body
                                                      old-fenv
                                                      new-fenv
                                                      ',types
                                                      ',gin.vartys))))
                 (:instance
                  stmt-while-theorem
                  (old-test ',old-test)
                  (new-test ',new-test)
                  (old-body ',old-body)
                  (new-body ',new-body)
                  (types ',types)
                  (vartys ',gin.vartys))))))
       ((mv thm-event thm-name thm-index)
        (gen-stmt-thm stmt
                      stmt-new
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv stmt-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-while
    (stmt-unambp stmt)
    :hyp (and (expr-unambp test-new)
              (stmt-unambp body-new)))

  (defret stmt-annop-of-simpadd0-stmt-while
    (stmt-annop stmt)
    :hyp (and (expr-annop test-new)
              (stmt-annop body-new)))

  (defret stmt-aidentp-of-simpadd0-stmt-while
    (stmt-aidentp stmt gcc)
    :hyp (and (expr-aidentp test-new gcc)
              (stmt-aidentp body-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-decl-decl ((extension booleanp)
                            (specs decl-spec-listp)
                            (specs-new decl-spec-listp)
                            (specs-thm-name symbolp)
                            (init initdeclor-listp)
                            (init-new initdeclor-listp)
                            (init-thm-name symbolp)
                            (vartys-post c::ident-type-mapp)
                            (gin simpadd0-ginp))
  :guard (and (decl-spec-list-unambp specs)
              (decl-spec-list-annop specs)
              (decl-spec-list-unambp specs-new)
              (decl-spec-list-annop specs-new)
              (initdeclor-list-unambp init)
              (initdeclor-list-annop init)
              (initdeclor-list-unambp init-new)
              (initdeclor-list-annop init-new))
  :returns (mv (decl declp) (gout simpadd0-goutp))
  :short "Transform a non-static-assert declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We combine the (untransformed) extension flag
     with the possibly transformed
     declaration specifiers and initializer declarators.")
   (xdoc::p
    "Currently we do not generate theorems for lists of declaration specifiers.
     We double-check that here."))
  (b* (((simpadd0-gin gin) gin)
       (decl (make-decl-decl :extension extension
                             :specs specs
                             :init init))
       (decl-new (make-decl-decl :extension extension
                                 :specs specs-new
                                 :init init-new))
       (gout-no-thm (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                          :vartys vartys-post))
       ((when specs-thm-name)
        (raise "Internal error: ~
                new list of initializer declarators ~x0 ~
                is not in the formalized subset."
               init)
        (mv decl-new (irr-simpadd0-gout)))
       ((unless (and init-thm-name
                     (decl-block-formalp decl)))
        (mv decl-new gout-no-thm))
       ((unless (decl-block-formalp decl-new))
        (raise "Internal error: ~
                new declaration ~x0 is not in the formalized subset ~
                while old declaration ~x1 is."
               decl-new decl)
        (mv decl-new (irr-simpadd0-gout)))
       (initdeclor (car init))
       (var (dirdeclor-ident->ident
             (declor->direct
              (initdeclor->declor initdeclor))))
       (initer (initdeclor->init? initdeclor))
       (initdeclor-new (car init-new))
       ((unless (equal var (dirdeclor-ident->ident
                            (declor->direct
                             (initdeclor->declor initdeclor-new)))))
        (raise "Internal error: ~
                new variable ~x0 differs from old variable ~x1."
               (dirdeclor-ident->ident
                (declor->direct
                 (initdeclor->declor initdeclor-new)))
               var)
        (mv decl-new (irr-simpadd0-gout)))
       (initer-new (initdeclor->init? initdeclor-new))
       ((unless (equal specs specs-new))
        (raise "Internal error: ~
                new declaration specifiers ~x0 differ from ~
                old declaration specifiers ~x1."
               specs-new specs)
        (mv decl-new (irr-simpadd0-gout)))
       ((mv & tyspecs) (check-decl-spec-list-all-typespec specs))
       ((mv & ctyspecs) (ldm-type-spec-list tyspecs))
       (ctype (c::tyspecseq-to-type ctyspecs))
       ((unless (c::type-nonchar-integerp ctype))
        (mv decl-new gout-no-thm))
       ((mv & cvar) (ldm-ident var))
       ((mv & old-initer) (ldm-initer initer))
       ((mv & new-initer) (ldm-initer initer-new))
       (vartys-post (omap::update cvar ctype gin.vartys))
       (hints `(("Goal"
                 :in-theory
                 '((:e c::obj-declon->scspec)
                   (:e c::obj-declon->tyspec)
                   (:e c::obj-declon->declor)
                   (:e c::obj-declon->init?)
                   (:e c::obj-declon)
                   (:e c::obj-declor-kind)
                   (:e c::obj-declor-ident->get)
                   (:e c::obj-declor-ident)
                   (:e c::scspecseq-none)
                   (:e c::tyspecseq-to-type)
                   (:e c::identp)
                   c::compustate-frames-number-of-exec-initer
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   decl-decl-compustate-vars-old
                   decl-decl-compustate-vars-new)
                 :use ((:instance ,init-thm-name (limit (1- limit)))
                       (:instance
                        decl-decl-congruence
                        (var ',cvar)
                        (tyspecs ',ctyspecs)
                        (old-initer ',old-initer)
                        (new-initer ',new-initer))
                       (:instance
                        decl-decl-errors
                        (var ',cvar)
                        (tyspecs ',ctyspecs)
                        (initer ',old-initer)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-decl-thm decl
                      decl-new
                      gin.vartys
                      vartys-post
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv decl-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys vartys-post)))
  :guard-hints (("Goal" :in-theory (enable decl-block-formalp
                                           initdeclor-block-formalp
                                           declor-block-formalp
                                           dirdeclor-block-formalp)))

  ///

  (defret decl-unambp-of-simpadd0-decl-decl
    (decl-unambp decl)
    :hyp (and (decl-spec-list-unambp specs-new)
              (initdeclor-list-unambp init-new)))

  (defret decl-annop-of-simpadd0-decl-decl
    (decl-annop decl)
    :hyp (and (decl-spec-list-annop specs-new)
              (initdeclor-list-annop init-new)))

  (defret decl-aidentp-of-simpadd0-decl-decl
    (decl-aidentp decl gcc)
    :hyp (and (decl-spec-list-aidentp specs-new gcc)
              (initdeclor-list-aidentp init-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-stmt ((stmt stmtp)
                                  (stmt-new stmtp)
                                  (stmt-thm-name symbolp)
                                  info
                                  (gin simpadd0-ginp))
  :guard (and (stmt-unambp stmt)
              (stmt-annop stmt)
              (stmt-unambp stmt-new)
              (stmt-annop stmt-new))
  :returns (mv (item block-itemp) (gout simpadd0-goutp))
  :short "Transform a block item that consists of a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new statement into a block item."))
  (b* (((simpadd0-gin gin) gin)
       (item (make-block-item-stmt :stmt stmt :info info))
       (item-new (make-block-item-stmt :stmt stmt-new :info info))
       ((unless stmt-thm-name)
        (mv item-new (simpadd0-gout-no-thm gin)))
       (types (stmt-types stmt))
       ((mv & old-stmt) (ldm-stmt stmt)) ; ERP must be NIL
       ((mv & new-stmt) (ldm-stmt stmt-new)) ; ERP must be NIL
       ((mv & ctypes) (ldm-type-option-set types)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::block-item-stmt)
                   (:e c::block-item-kind)
                   (:e c::block-item-stmt->get)
                   c::compustate-frames-number-of-exec-stmt
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   block-item-stmt-compustate-vars)
                 :use ((:instance ,stmt-thm-name (limit (1- limit)))
                       (:instance
                        block-item-stmt-congruence
                        (old-stmt ',old-stmt)
                        (new-stmt ',new-stmt)
                        (types ',ctypes))
                       (:instance
                        block-item-stmt-errors
                        (stmt ',old-stmt)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-thm item
                            item-new
                            gin.vartys
                            gin.vartys
                            gin.const-new
                            gin.thm-index
                            hints)))
    (mv item-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (defret block-item-unambp-of-simpadd0-block-item-stmt
    (block-item-unambp item)
    :hyp (stmt-unambp stmt-new))

  (defret block-item-annop-of-simpadd0-block-item-stmt
    (block-item-annop item)
    :hyp (stmt-annop stmt-new))

  (defret block-item-aidentp-of-simpadd0-block-item-stmt
    (block-item-aidentp item gcc)
    :hyp (stmt-aidentp stmt-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-decl ((decl declp)
                                  (decl-new declp)
                                  (decl-thm-name symbolp)
                                  info
                                  (vartys-post c::ident-type-mapp)
                                  (gin simpadd0-ginp))
  :guard (and (decl-unambp decl)
              (decl-annop decl)
              (decl-unambp decl-new)
              (decl-annop decl-new))
  :returns (mv (item block-itemp) (gout simpadd0-goutp))
  :short "Transform a block item that consists of a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put the new declaration into a block item."))
  (b* (((simpadd0-gin gin) gin)
       (item (make-block-item-decl :decl decl :info info))
       (item-new (make-block-item-decl :decl decl-new :info info))
       (gout-no-thm (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                          :vartys vartys-post))
       ((unless decl-thm-name) (mv item-new gout-no-thm))
       ((mv & old-declon) (ldm-decl-obj decl)) ; ERP must be NIL
       ((mv & new-declon) (ldm-decl-obj decl-new)) ; ERP must be NIL
       (hints `(("Goal"
                 :in-theory
                 '((:e c::block-item-declon)
                   (:e c::block-item-kind)
                   (:e c::block-item-declon->get)
                   (:e set::insert)
                   c::compustate-frames-number-of-exec-obj-declon
                   c::compustatep-when-compustate-resultp-and-not-errorp
                   block-item-decl-compustate-vars)
                 :use ((:instance ,decl-thm-name (limit (1- limit)))
                       (:instance
                        block-item-decl-congruence
                        (old-declon ',old-declon)
                        (new-declon ',new-declon))
                       (:instance
                        block-item-decl-errors
                        (declon ',old-declon)
                        (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-thm item
                            item-new
                            gin.vartys
                            vartys-post
                            gin.const-new
                            gin.thm-index
                            hints)))
    (mv item-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys vartys-post)))
  :guard-hints (("Goal" :in-theory (enable decl-block-formalp
                                           initdeclor-block-formalp
                                           declor-block-formalp
                                           dirdeclor-block-formalp)))

  ///

  (defret block-item-unambp-of-simpadd0-block-item-decl
    (block-item-unambp item)
    :hyp (decl-unambp decl-new))

  (defret block-item-annop-of-simpadd0-block-item-decl
    (block-item-annop item)
    :hyp (decl-annop decl-new))

  (defret block-item-aidentp-of-simpadd0-block-item-decl
    (block-item-aidentp item gcc)
    :hyp (decl-aidentp decl-new gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-empty ((gin simpadd0-ginp))
  :returns (gout simpadd0-goutp)
  :short "Transform an empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is introduced mainly for uniformity.
     It actually takes and returns no block item list,
     because there is only one empty block item list."))
  (b* (((simpadd0-gin gin) gin)
       (items nil)
       (hints `(("Goal"
                 :in-theory '((:e set::insert)
                              block-item-list-empty-compustate-vars)
                 :use (block-item-list-empty-congruence))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm items
                                 items
                                 gin.vartys
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (make-simpadd0-gout :events (cons thm-event gin.events)
                        :thm-index thm-index
                        :thm-name thm-name
                        :vartys gin.vartys))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-cons ((item block-itemp)
                                       (item-new block-itemp)
                                       (item-thm-name symbolp)
                                       (items block-item-listp)
                                       (items-new block-item-listp)
                                       (items-thm-name symbolp)
                                       (gin simpadd0-ginp))
  :guard (and (block-item-unambp item)
              (block-item-annop item)
              (block-item-unambp item-new)
              (block-item-annop item-new)
              (block-item-list-unambp items)
              (block-item-list-annop items)
              (block-item-list-unambp items-new)
              (block-item-list-annop items-new))
  :returns (mv (item+items block-item-listp) (gout simpadd0-goutp))
  :short "Transform a non-empty list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting list of block items is obtained by
     @(tsee cons)ing the possibly transformed first item
     and the possibly transformed rest of the items.")
   (xdoc::p
    "We generate a theorem iff theorems were generated for
     both the first item and (the list of) the rest of the items."))
  (b* (((simpadd0-gin gin) gin)
       (item (block-item-fix item))
       (items (block-item-list-fix items))
       (item-new (block-item-fix item-new))
       (items-new (block-item-list-fix items-new))
       (item+items (cons item items))
       (item+items-new (cons item-new items-new))
       (gout-no-thm (simpadd0-gout-no-thm gin))
       ((unless (and item-thm-name
                     items-thm-name))
        (mv item+items-new gout-no-thm))
       (first-types (block-item-types item))
       (rest-types (block-item-list-types items))
       ((mv & old-item) (ldm-block-item item)) ; ERP must be NIL
       ((mv & new-item) (ldm-block-item item-new)) ; ERP must be NIL
       ((mv & old-items) (ldm-block-item-list items)) ; ERP must be NIL
       ((mv & new-items) (ldm-block-item-list items-new)) ; ERP must be NIL
       ((mv & first-ctypes) (ldm-type-option-set first-types)) ; ERP must be NIL
       ((mv & rest-ctypes) (ldm-type-option-set rest-types)) ; ERP must be NIL
       (hints
        `(("Goal"
           :in-theory
           '(c::stmt-value-kind-possibilities
             (:e set::delete)
             (:e set::union)
             c::compustate-frames-number-of-exec-block-item
             c::compustatep-when-compustate-resultp-and-not-errorp
             block-item-list-cons-compustate-vars)
           :use ((:instance
                  ,item-thm-name
                  (limit (1- limit)))
                 (:instance
                  ,items-thm-name
                  (compst
                   (mv-nth 1 (c::exec-block-item
                              ',old-item compst old-fenv (1- limit))))
                  (limit (1- limit)))
                 (:instance
                  block-item-list-cons-first-congruence
                  (old-item ',old-item)
                  (old-items ',old-items)
                  (new-item ',new-item)
                  (new-items ',new-items)
                  (first-types ',first-ctypes)
                  (rest-types ',rest-ctypes))
                 (:instance
                  block-item-list-cons-rest-congruence
                  (old-item ',old-item)
                  (old-items ',old-items)
                  (new-item ',new-item)
                  (new-items ',new-items)
                  (first-types ',first-ctypes)
                  (rest-types ',rest-ctypes))
                 (:instance
                  block-item-list-cons-first-errors
                  (item ',old-item)
                  (items ',old-items)
                  (fenv old-fenv))
                 (:instance
                  block-item-list-cons-rest-errors
                  (item ',old-item)
                  (items ',old-items)
                  (fenv old-fenv))))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm item+items
                                 item+items-new
                                 gin.vartys
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (mv item+items-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys gin.vartys)))

  ///

  (fty::deffixequiv simpadd0-block-item-list-cons
    :args ((item block-itemp)
           (item-new block-itemp)
           (items block-item-listp)
           (items-new block-item-listp)))

  (defret block-item-list-unambp-of-simpadd0-block-item-list-cons
    (block-item-list-unambp item+items)
    :hyp (and (block-item-unambp item-new)
              (block-item-list-unambp items-new)))

  (defret block-item-list-annop-of-simpadd0-block-item-list-cons
    (block-item-list-annop item+items)
    :hyp (and (block-item-annop item-new)
              (block-item-list-annop items-new)))

  (defret block-item-list-aidentp-of-simpadd0-block-item-list-cons
    (block-item-list-aidentp item+items gcc)
    :hyp (and (block-item-aidentp item-new gcc)
              (block-item-list-aidentp items-new gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines simpadd0-exprs/decls/stmts
  :short "Transform expressions, declarations, statements,
          and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate theorems for certain kinds of expressions.
     We are in the process of extending the implementation to generate theorems
     for additional kinds of expressions and for other constructs."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr ((expr exprp) (gin simpadd0-ginp))
    :guard (and (expr-unambp expr)
                (expr-annop expr))
    :returns (mv (new-expr exprp) (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an expression."
    (b* (((simpadd0-gin gin) gin))
      (expr-case
       expr
       :ident (simpadd0-expr-ident expr.ident expr.info gin)
       :const (simpadd0-expr-const expr.const gin)
       :string (mv (expr-fix expr) (simpadd0-gout-no-thm gin))
       :paren
       (b* (((mv new-inner (simpadd0-gout gout-inner))
             (simpadd0-expr expr.inner gin))
            (gin (simpadd0-gin-update gin gout-inner)))
         (simpadd0-expr-paren expr.inner
                              new-inner
                              gout-inner.thm-name
                              gin))
       :gensel
       (b* (((mv new-control (simpadd0-gout gout-control))
             (simpadd0-expr expr.control gin))
            (gin (simpadd0-gin-update gin gout-control))
            ((mv new-assocs (simpadd0-gout gout-assocs))
             (simpadd0-genassoc-list expr.assocs gin))
            (gin (simpadd0-gin-update gin gout-assocs)))
         (mv (make-expr-gensel :control new-control
                               :assocs new-assocs)
             (simpadd0-gout-no-thm gin)))
       :arrsub
       (b* (((mv new-arg1 (simpadd0-gout gout-arg1))
             (simpadd0-expr expr.arg1 gin))
            (gin (simpadd0-gin-update gin gout-arg1))
            ((mv new-arg2 (simpadd0-gout gout-arg2))
             (simpadd0-expr expr.arg2 gin))
            (gin (simpadd0-gin-update gin gout-arg2)))
         (mv (make-expr-arrsub :arg1 new-arg1
                               :arg2 new-arg2)
             (simpadd0-gout-no-thm gin)))
       :funcall
       (b* (((mv new-fun (simpadd0-gout gout-fun))
             (simpadd0-expr expr.fun gin))
            (gin (simpadd0-gin-update gin gout-fun))
            ((mv new-args (simpadd0-gout gout-args))
             (simpadd0-expr-list expr.args gin))
            (gin (simpadd0-gin-update gin gout-args)))
         (mv (make-expr-funcall :fun new-fun
                                :args new-args)
             (simpadd0-gout-no-thm gin)))
       :member
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (simpadd0-gin-update gin gout-arg)))
         (mv (make-expr-member :arg new-arg
                               :name expr.name)
             (simpadd0-gout-no-thm gin)))
       :memberp
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (simpadd0-gin-update gin gout-arg)))
         (mv (make-expr-memberp :arg new-arg
                                :name expr.name)
             (simpadd0-gout-no-thm gin)))
       :complit
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-elems (simpadd0-gout gout-elems))
             (simpadd0-desiniter-list expr.elems gin))
            (gin (simpadd0-gin-update gin gout-elems)))
         (mv (make-expr-complit :type new-type
                                :elems new-elems
                                :final-comma expr.final-comma)
             (simpadd0-gout-no-thm gin)))
       :unary
       (b* (((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (simpadd0-gin-update gin gout-arg)))
         (simpadd0-expr-unary expr.op
                              expr.arg
                              new-arg
                              gout-arg.thm-name
                              expr.info
                              gin))
       :sizeof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type)))
         (mv (expr-sizeof new-type)
             (simpadd0-gout-no-thm gin)))
       :alignof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type)))
         (mv (make-expr-alignof :type new-type
                                :uscores expr.uscores)
             (simpadd0-gout-no-thm gin)))
       :cast
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-arg (simpadd0-gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (simpadd0-gin-update gin gout-arg)))
         (simpadd0-expr-cast expr.type
                             new-type
                             gout-type.thm-name
                             expr.arg
                             new-arg
                             gout-arg.thm-name
                             (tyname->info expr.type)
                             gin))
       :binary
       (b* (((mv new-arg1 (simpadd0-gout gout-arg1))
             (simpadd0-expr expr.arg1 gin))
            (gin (simpadd0-gin-update gin gout-arg1))
            ((mv new-arg2 (simpadd0-gout gout-arg2))
             (simpadd0-expr expr.arg2 gin))
            (gin (simpadd0-gin-update gin gout-arg2)))
         (simpadd0-expr-binary expr.op
                               expr.arg1
                               new-arg1
                               gout-arg1.thm-name
                               expr.arg2
                               new-arg2
                               gout-arg2.thm-name
                               expr.info
                               gin))
       :cond
       (b* (((mv new-test (simpadd0-gout gout-test))
             (simpadd0-expr expr.test gin))
            (gin (simpadd0-gin-update gin gout-test))
            ((mv new-then (simpadd0-gout gout-then))
             (simpadd0-expr-option expr.then gin))
            (gin (simpadd0-gin-update gin gout-then))
            ((mv new-else (simpadd0-gout gout-else))
             (simpadd0-expr expr.else gin))
            (gin (simpadd0-gin-update gin gout-else)))
         (simpadd0-expr-cond expr.test
                             new-test
                             gout-test.thm-name
                             expr.then
                             new-then
                             gout-then.thm-name
                             expr.else
                             new-else
                             gout-else.thm-name
                             gin))
       :comma
       (b* (((mv new-first (simpadd0-gout gout-first))
             (simpadd0-expr expr.first gin))
            (gin (simpadd0-gin-update gin gout-first))
            ((mv new-next (simpadd0-gout gout-next))
             (simpadd0-expr expr.next gin))
            (gin (simpadd0-gin-update gin gout-next)))
         (mv (make-expr-comma :first new-first
                              :next new-next)
             (simpadd0-gout-no-thm gin)))
       :stmt
       (b* (((mv new-items (simpadd0-gout gout-items))
             (simpadd0-block-item-list expr.items gin))
            (gin (simpadd0-gin-update gin gout-items)))
         (mv (expr-stmt new-items)
             (simpadd0-gout-no-thm gin)))
       :tycompat
       (b* (((mv new-type1 (simpadd0-gout gout-type1))
             (simpadd0-tyname expr.type1 gin))
            (gin (simpadd0-gin-update gin gout-type1))
            ((mv new-type2 (simpadd0-gout gout-type2))
             (simpadd0-tyname expr.type2 gin))
            (gin (simpadd0-gin-update gin gout-type2)))
         (mv (make-expr-tycompat :type1 new-type1
                                 :type2 new-type2)
             (simpadd0-gout-no-thm gin)))
       :offsetof
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor expr.member gin))
            (gin (simpadd0-gin-update gin gout-member)))
         (mv (make-expr-offsetof :type new-type
                                 :member new-member)
             (simpadd0-gout-no-thm gin)))
       :va-arg
       (b* (((mv new-list (simpadd0-gout gout-list))
             (simpadd0-expr expr.list gin))
            (gin (simpadd0-gin-update gin gout-list))
            ((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (simpadd0-gin-update gin gout-type)))
         (mv (make-expr-va-arg :list new-list
                               :type new-type)
             (simpadd0-gout-no-thm gin)))
       :extension
       (b* (((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr expr.expr gin))
            (gin (simpadd0-gin-update gin gout-expr)))
         (mv (expr-extension new-expr)
             (simpadd0-gout-no-thm gin)))
       :otherwise (prog2$ (impossible) (mv (irr-expr) (irr-simpadd0-gout)))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-list ((exprs expr-listp) (gin simpadd0-ginp))
    :guard (and (expr-list-unambp exprs)
                (expr-list-annop exprs))
    :returns (mv (new-exprs expr-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of expressions."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp exprs))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-expr (simpadd0-gout gout-expr))
          (simpadd0-expr (car exprs) gin))
         (gin (simpadd0-gin-update gin gout-expr))
         ((mv new-exprs (simpadd0-gout gout-exprs))
          (simpadd0-expr-list (cdr exprs) gin))
         (gin (simpadd0-gin-update gin gout-exprs)))
      (mv (cons new-expr new-exprs)
          (simpadd0-gout-no-thm gin)))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-option ((expr? expr-optionp) (gin simpadd0-ginp))
    :guard (and (expr-option-unambp expr?)
                (expr-option-annop expr?))
    :returns (mv (new-expr? expr-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional expression."
    (b* (((simpadd0-gin gin) gin))
      (expr-option-case
       expr?
       :some (simpadd0-expr expr?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (expr-option-count expr?)

    ///

    (defret simpadd0-expr-option-iff-expr-option
      (iff new-expr? expr?)
      :hints (("Goal" :expand (simpadd0-expr-option expr? gin)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr ((cexpr const-exprp) (gin simpadd0-ginp))
    :guard (and (const-expr-unambp cexpr)
                (const-expr-annop cexpr))
    :returns (mv (new-cexpr const-exprp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a constant expression."
    (b* (((simpadd0-gin gin) gin)
         ((mv new-expr (simpadd0-gout gout-expr))
          (simpadd0-expr (const-expr->expr cexpr) gin))
         (gin (simpadd0-gin-update gin gout-expr)))
      (mv (const-expr new-expr)
          (simpadd0-gout-no-thm gin)))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr-option ((cexpr? const-expr-optionp)
                                      (gin simpadd0-ginp))
    :guard (and (const-expr-option-unambp cexpr?)
                (const-expr-option-annop cexpr?))
    :returns (mv (new-cexpr? const-expr-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional constant expression."
    (b* (((simpadd0-gin gin) gin))
      (const-expr-option-case
       cexpr?
       :some (simpadd0-const-expr cexpr?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc ((genassoc genassocp) (gin simpadd0-ginp))
    :guard (and (genassoc-unambp genassoc)
                (genassoc-annop genassoc))
    :returns (mv (new-genassoc genassocp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a generic association."
    (b* (((simpadd0-gin gin) gin))
      (genassoc-case
       genassoc
       :type
       (b* (((mv new-type (simpadd0-gout gout-type))
             (simpadd0-tyname genassoc.type gin))
            (gin (simpadd0-gin-update gin gout-type))
            ((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr genassoc.expr gin))
            (gin (simpadd0-gin-update gin gout-expr)))
         (mv (make-genassoc-type :type new-type
                                 :expr new-expr)
             (simpadd0-gout-no-thm gin)))
       :default
       (b* (((mv new-expr (simpadd0-gout gout-expr))
             (simpadd0-expr genassoc.expr gin))
            (gin (simpadd0-gin-update gin gout-expr)))
         (mv (genassoc-default new-expr)
             (simpadd0-gout-no-thm gin)))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc-list ((genassocs genassoc-listp)
                                  (gin simpadd0-ginp))
    :guard (and (genassoc-list-unambp genassocs)
                (genassoc-list-annop genassocs))
    :returns (mv (new-genassocs genassoc-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of generic associations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp genassocs))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-assoc (simpadd0-gout gout-assoc))
          (simpadd0-genassoc (car genassocs) gin))
         (gin (simpadd0-gin-update gin gout-assoc))
         ((mv new-assocs (simpadd0-gout gout-assocs))
          (simpadd0-genassoc-list (cdr genassocs) gin))
         (gin (simpadd0-gin-update gin gout-assocs)))
      (mv (cons new-assoc new-assocs)
          (simpadd0-gout-no-thm gin)))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-member-designor ((memdes member-designorp)
                                    (gin simpadd0-ginp))
    :guard (and (member-designor-unambp memdes)
                (member-designor-annop memdes))
    :returns (mv (new-memdes member-designorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a member designator."
    (b* (((simpadd0-gin gin) gin))
      (member-designor-case
       memdes
       :ident (mv (member-designor-fix memdes) (simpadd0-gout-no-thm gin))
       :dot
       (b* (((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor memdes.member gin))
            (gin (simpadd0-gin-update gin gout-member)))
         (mv (make-member-designor-dot :member new-member
                                       :name memdes.name)
             (simpadd0-gout-no-thm gin)))
       :sub
       (b* (((mv new-member (simpadd0-gout gout-member))
             (simpadd0-member-designor memdes.member gin))
            (gin (simpadd0-gin-update gin gout-member))
            ((mv new-index (simpadd0-gout gout-index))
             (simpadd0-expr memdes.index gin))
            (gin (simpadd0-gin-update gin gout-member)))
         (mv (make-member-designor-sub :member new-member
                                       :index new-index)
             (simpadd0-gout-no-thm gin)))))
    :measure (member-designor-count memdes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-type-spec ((tyspec type-specp) (gin simpadd0-ginp))
    :guard (and (type-spec-unambp tyspec)
                (type-spec-annop tyspec))
    :returns (mv (new-tyspec type-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier."
    (b* (((simpadd0-gin gin) gin)
         (gout0 (simpadd0-gout-no-thm gin)))
      (type-spec-case
       tyspec
       :void (mv (type-spec-fix tyspec) gout0)
       :char (mv (type-spec-fix tyspec) gout0)
       :short (mv (type-spec-fix tyspec) gout0)
       :int (mv (type-spec-fix tyspec) gout0)
       :long (mv (type-spec-fix tyspec) gout0)
       :float (mv (type-spec-fix tyspec) gout0)
       :double (mv (type-spec-fix tyspec) gout0)
       :signed (mv (type-spec-fix tyspec) gout0)
       :unsigned (mv (type-spec-fix tyspec) gout0)
       :bool (mv (type-spec-fix tyspec) gout0)
       :complex (mv (type-spec-fix tyspec) gout0)
       :atomic (b* (((mv new-type (simpadd0-gout gout-type))
                     (simpadd0-tyname tyspec.type gin))
                    (gin (simpadd0-gin-update gin gout-type)))
                 (mv (type-spec-atomic new-type)
                     (simpadd0-gout-no-thm gin)))
       :struct (b* (((mv new-spec (simpadd0-gout gout-spec))
                     (simpadd0-struni-spec tyspec.spec gin))
                    (gin (simpadd0-gin-update gin gout-spec)))
                 (mv (type-spec-struct new-spec)
                     (simpadd0-gout-no-thm gin)))
       :union (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-struni-spec tyspec.spec gin))
                   (gin (simpadd0-gin-update gin gout-spec)))
                (mv (type-spec-union new-spec)
                    (simpadd0-gout-no-thm gin)))
       :enum (b* (((mv new-spec (simpadd0-gout gout-spec))
                   (simpadd0-enum-spec tyspec.spec gin))
                  (gin (simpadd0-gin-update gin gout-spec)))
               (mv (type-spec-enum new-spec)
                   (simpadd0-gout-no-thm gin)))
       :typedef (mv (type-spec-fix tyspec) gout0)
       :int128 (mv (type-spec-fix tyspec) gout0)
       :float32 (mv (type-spec-fix tyspec) gout0)
       :float32x (mv (type-spec-fix tyspec) gout0)
       :float64 (mv (type-spec-fix tyspec) gout0)
       :float64x (mv (type-spec-fix tyspec) gout0)
       :float128 (mv (type-spec-fix tyspec) gout0)
       :float128x (mv (type-spec-fix tyspec) gout0)
       :builtin-va-list (mv (type-spec-fix tyspec) gout0)
       :struct-empty (mv (type-spec-fix tyspec) gout0)
       :typeof-expr (b* (((mv new-expr (simpadd0-gout gout-expr))
                          (simpadd0-expr tyspec.expr gin))
                         (gin (simpadd0-gin-update gin gout-expr)))
                      (mv (make-type-spec-typeof-expr :expr new-expr
                                                      :uscores tyspec.uscores)
                          (simpadd0-gout-no-thm gin)))
       :typeof-type (b* (((mv new-type (simpadd0-gout gout-type))
                          (simpadd0-tyname tyspec.type gin))
                         (gin (simpadd0-gin-update gin gout-type)))
                      (mv (make-type-spec-typeof-type :type new-type
                                                      :uscores tyspec.uscores)
                          (simpadd0-gout-no-thm gin)))
       :typeof-ambig (prog2$ (impossible)
                             (mv (irr-type-spec) (irr-simpadd0-gout)))
       :auto-type (mv (type-spec-fix tyspec) gout0)))
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual ((specqual spec/qual-p)
                              (gin simpadd0-ginp))
    :guard (and (spec/qual-unambp specqual)
                (spec/qual-annop specqual))
    :returns (mv (new-specqual spec/qual-p)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier or qualifier."
    (b* (((simpadd0-gin gin) gin))
      (spec/qual-case
       specqual
       :typespec (b* (((mv new-spec (simpadd0-gout gout-spec))
                       (simpadd0-type-spec specqual.spec gin))
                      (gin (simpadd0-gin-update gin gout-spec)))
                   (mv (spec/qual-typespec new-spec)
                       (simpadd0-gout-no-thm gin)))
       :typequal (mv (spec/qual-fix specqual) (simpadd0-gout-no-thm gin))
       :align (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-align-spec specqual.spec gin))
                   (gin (simpadd0-gin-update gin gout-spec)))
                (mv (spec/qual-align new-spec)
                    (simpadd0-gout-no-thm gin)))
       :attrib (mv (spec/qual-fix specqual) (simpadd0-gout-no-thm gin))))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual-list ((specquals spec/qual-listp)
                                   (gin simpadd0-ginp))
    :guard (and (spec/qual-list-unambp specquals)
                (spec/qual-list-annop specquals))
    :returns (mv (new-specquals spec/qual-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of type specifiers and qualifiers."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp specquals))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-specqual (simpadd0-gout gout-specqual))
          (simpadd0-spec/qual (car specquals) gin))
         (gin (simpadd0-gin-update gin gout-specqual))
         ((mv new-specquals (simpadd0-gout gout-specquals))
          (simpadd0-spec/qual-list (cdr specquals) gin))
         (gin (simpadd0-gin-update gin gout-specquals)))
      (mv (cons new-specqual new-specquals)
          (simpadd0-gout-no-thm gin)))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-align-spec ((alignspec align-specp)
                               (gin simpadd0-ginp))
    :guard (and (align-spec-unambp alignspec)
                (align-spec-annop alignspec))
    :returns (mv (new-alignspec align-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an alignment specifier."
    (b* (((simpadd0-gin gin) gin))
      (align-spec-case
       alignspec
       :alignas-type (b* (((mv new-type (simpadd0-gout gout-type))
                           (simpadd0-tyname alignspec.type gin))
                          (gin (simpadd0-gin-update gin gout-type)))
                       (mv (align-spec-alignas-type new-type)
                           (simpadd0-gout-no-thm gin)))
       :alignas-expr (b* (((mv new-expr (simpadd0-gout gout-expr))
                           (simpadd0-const-expr alignspec.expr gin))
                          (gin (simpadd0-gin-update gin gout-expr)))
                       (mv (align-spec-alignas-expr new-expr)
                           (simpadd0-gout-no-thm gin)))
       :alignas-ambig (prog2$ (impossible)
                              (mv (irr-align-spec) (irr-simpadd0-gout)))))
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec ((declspec decl-specp) (gin simpadd0-ginp))
    :guard (and (decl-spec-unambp declspec)
                (decl-spec-annop declspec))
    :returns (mv (new-declspec decl-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration specifier."
    (b* (((simpadd0-gin gin) gin))
      (decl-spec-case
       declspec
       :stoclass (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))
       :typespec (b* (((mv new-spec (simpadd0-gout gout-spec))
                       (simpadd0-type-spec declspec.spec gin))
                      (gin (simpadd0-gin-update gin gout-spec)))
                   (mv (decl-spec-typespec new-spec)
                       (simpadd0-gout-no-thm gin)))
       :typequal (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))
       :function (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))
       :align (b* (((mv new-spec (simpadd0-gout gout-spec))
                    (simpadd0-align-spec declspec.spec gin))
                   (gin (simpadd0-gin-update gin gout-spec)))
                (mv (decl-spec-align new-spec)
                    (simpadd0-gout-no-thm gin)))
       :attrib (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))
       :stdcall (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))
       :declspec (mv (decl-spec-fix declspec) (simpadd0-gout-no-thm gin))))
    :measure (decl-spec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec-list ((declspecs decl-spec-listp)
                                   (gin simpadd0-ginp))
    :guard (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-annop declspecs))
    :returns (mv (new-declspecs decl-spec-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declaration specifiers."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp declspecs))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-declspec (simpadd0-gout gout-declspec))
          (simpadd0-decl-spec (car declspecs) gin))
         (gin (simpadd0-gin-update gin gout-declspec))
         ((mv new-declspecs (simpadd0-gout gout-declspecs))
          (simpadd0-decl-spec-list (cdr declspecs) gin))
         (gin (simpadd0-gin-update gin gout-declspecs)))
      (mv (cons new-declspec new-declspecs)
          (simpadd0-gout-no-thm gin)))
    :measure (decl-spec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer ((initer initerp) (gin simpadd0-ginp))
    :guard (and (initer-unambp initer)
                (initer-annop initer))
    :returns (mv (new-initer initerp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer."
    (b* (((simpadd0-gin gin) gin))
      (initer-case
       initer
       :single (b* (((mv new-expr (simpadd0-gout gout-expr))
                     (simpadd0-expr initer.expr gin))
                    (gin (simpadd0-gin-update gin gout-expr)))
                 (simpadd0-initer-single initer.expr
                                         new-expr
                                         gout-expr.thm-name
                                         gin))
       :list (b* (((mv new-elems (simpadd0-gout gout-elems))
                   (simpadd0-desiniter-list initer.elems gin))
                  (gin (simpadd0-gin-update gin gout-elems)))
               (mv (make-initer-list :elems new-elems
                                     :final-comma initer.final-comma)
                   (simpadd0-gout-no-thm gin)))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer-option ((initer? initer-optionp)
                                  (gin simpadd0-ginp))
    :guard (and (initer-option-unambp initer?)
                (initer-option-annop initer?))
    :returns (mv (new-initer? initer-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional initializer."
    (b* (((simpadd0-gin gin) gin))
      (initer-option-case
       initer?
       :some (simpadd0-initer initer?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter ((desiniter desiniterp)
                              (gin simpadd0-ginp))
    :guard (and (desiniter-unambp desiniter)
                (desiniter-annop desiniter))
    :returns (mv (new-desiniter desiniterp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter)
         ((mv new-designors (simpadd0-gout gout-designors))
          (simpadd0-designor-list desiniter.designors gin))
         ((mv new-initer (simpadd0-gout gout-initer))
          (simpadd0-initer desiniter.initer gin))
         (gin (simpadd0-gin-update gin gout-initer)))
      (mv (make-desiniter :designors new-designors
                          :initer new-initer)
          (simpadd0-gout-no-thm gin)))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter-list ((desiniters desiniter-listp)
                                   (gin simpadd0-ginp))
    :guard (and (desiniter-list-unambp desiniters)
                (desiniter-list-annop desiniters))
    :returns (mv (new-desiniters desiniter-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializers with optional designations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp desiniters))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-desiniter (simpadd0-gout gout-desiniter))
          (simpadd0-desiniter (car desiniters) gin))
         (gin (simpadd0-gin-update gin gout-desiniter))
         ((mv new-desiniters (simpadd0-gout gout-desiniters))
          (simpadd0-desiniter-list (cdr desiniters) gin))
         (gin (simpadd0-gin-update gin gout-desiniters)))
      (mv (cons new-desiniter new-desiniters)
          (simpadd0-gout-no-thm gin)))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor ((designor designorp) (gin simpadd0-ginp))
    :guard (and (designor-unambp designor)
                (designor-annop designor))
    :returns (mv (new-designor designorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a designator."
    (b* (((simpadd0-gin gin) gin))
      (designor-case
       designor
       :sub (b* (((mv new-index (simpadd0-gout gout-index))
                  (simpadd0-const-expr designor.index gin))
                 (gin (simpadd0-gin-update gin gout-index))
                 ((mv new-range? (simpadd0-gout gout-range?))
                  (simpadd0-const-expr-option designor.range? gin))
                 (gin (simpadd0-gin-update gin gout-range?)))
              (mv (make-designor-sub :index new-index :range? new-range?)
                  (simpadd0-gout-no-thm gin)))
       :dot (mv (designor-fix designor) (simpadd0-gout-no-thm gin))))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor-list ((designors designor-listp)
                                  (gin simpadd0-ginp))
    :guard (and (designor-list-unambp designors)
                (designor-list-annop designors))
    :returns (mv (new-designors designor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of designators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp designors))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-designor (simpadd0-gout gout-designor))
          (simpadd0-designor (car designors) gin))
         (gin (simpadd0-gin-update gin gout-designor))
         ((mv new-designors (simpadd0-gout gout-designors))
          (simpadd0-designor-list (cdr designors) gin))
         (gin (simpadd0-gin-update gin gout-designors)))
      (mv (cons new-designor new-designors)
          (simpadd0-gout-no-thm gin)))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor ((declor declorp) (gin simpadd0-ginp))
    :guard (and (declor-unambp declor)
                (declor-annop declor))
    :returns (mv (new-declor declorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declarator."
    (b* (((simpadd0-gin gin) gin)
         ((declor declor) declor)
         ((mv new-direct (simpadd0-gout gout-direct))
          (simpadd0-dirdeclor declor.direct gin))
         (gin (simpadd0-gin-update gin gout-direct)))
      (mv (make-declor :pointers declor.pointers
                       :direct new-direct)
          (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                :vartys gout-direct.vartys)))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor-option ((declor? declor-optionp)
                                  (gin simpadd0-ginp))
    :guard (and (declor-option-unambp declor?)
                (declor-option-annop declor?))
    :returns (mv (new-declor? declor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional declarator."
    (b* (((simpadd0-gin gin) gin))
      (declor-option-case
       declor?
       :some (simpadd0-declor declor?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirdeclor ((dirdeclor dirdeclorp) (gin simpadd0-ginp))
    :guard (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-annop dirdeclor))
    :returns (mv (new-dirdeclor dirdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirdeclor-case
       dirdeclor
       :ident (mv (dirdeclor-fix dirdeclor) (simpadd0-gout-no-thm gin))
       :paren (b* (((mv new-declor (simpadd0-gout gout-declor))
                    (simpadd0-declor dirdeclor.inner gin))
                   (gin (simpadd0-gin-update gin gout-declor)))
                (mv (dirdeclor-paren new-declor)
                    (simpadd0-gout-no-thm gin)))
       :array (b* (((mv new-decl (simpadd0-gout gout-decl))
                    (simpadd0-dirdeclor dirdeclor.declor gin))
                   (gin (simpadd0-gin-update gin gout-decl))
                   ((mv new-expr? (simpadd0-gout gout-expr?))
                    (simpadd0-expr-option dirdeclor.size? gin))
                   (gin (simpadd0-gin-update gin gout-expr?)))
                (mv (make-dirdeclor-array :declor new-decl
                                          :qualspecs dirdeclor.qualspecs
                                          :size? new-expr?)
                    (simpadd0-gout-no-thm gin)))
       :array-static1 (b* (((mv new-decl (simpadd0-gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor gin))
                           (gin (simpadd0-gin-update gin gout-decl))
                           ((mv new-expr (simpadd0-gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin))
                           (gin (simpadd0-gin-update gin gout-expr)))
                        (mv (make-dirdeclor-array-static1
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            (simpadd0-gout-no-thm gin)))
       :array-static2 (b* (((mv new-decl (simpadd0-gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor gin))
                           (gin (simpadd0-gin-update gin gout-decl))
                           ((mv new-expr (simpadd0-gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin))
                           (gin (simpadd0-gin-update gin gout-expr)))
                        (mv (make-dirdeclor-array-static2
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            (simpadd0-gout-no-thm gin)))
       :array-star (b* (((mv new-decl (simpadd0-gout gout-decl))
                         (simpadd0-dirdeclor dirdeclor.declor gin))
                        (gin (simpadd0-gin-update gin gout-decl)))
                     (mv (make-dirdeclor-array-star
                          :declor new-decl
                          :qualspecs dirdeclor.qualspecs)
                         (simpadd0-gout-no-thm gin)))
       :function-params (b* (((mv new-decl (simpadd0-gout gout-decl))
                              (simpadd0-dirdeclor dirdeclor.declor gin))
                             (gin (simpadd0-gin-update gin gout-decl))
                             ((mv new-params (simpadd0-gout gout-params))
                              (simpadd0-param-declon-list dirdeclor.params
                                                          gin))
                             (gin (simpadd0-gin-update gin gout-params)))
                          (mv (make-dirdeclor-function-params
                               :declor new-decl
                               :params new-params
                               :ellipsis dirdeclor.ellipsis)
                              (simpadd0-gout-no-thm gin)))
       :function-names (b* (((mv new-decl (simpadd0-gout gout-decl))
                             (simpadd0-dirdeclor dirdeclor.declor gin))
                            (gin (simpadd0-gin-update gin gout-decl)))
                         (mv (make-dirdeclor-function-names
                              :declor new-decl
                              :names dirdeclor.names)
                             (simpadd0-gout-no-thm gin)))))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor ((absdeclor absdeclorp) (gin simpadd0-ginp))
    :guard (and (absdeclor-unambp absdeclor)
                (absdeclor-annop absdeclor))
    :returns (mv (new-absdeclor absdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an abstract declarator."
    (b* (((simpadd0-gin gin) gin)
         ((absdeclor absdeclor) absdeclor)
         ((mv new-direct? (simpadd0-gout gout-direct?))
          (simpadd0-dirabsdeclor-option absdeclor.direct? gin))
         (gin (simpadd0-gin-update gin gout-direct?)))
      (mv (make-absdeclor :pointers absdeclor.pointers
                          :direct? new-direct?)
          (simpadd0-gout-no-thm gin)))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor-option ((absdeclor? absdeclor-optionp)
                                     (gin simpadd0-ginp))
    :guard (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-annop absdeclor?))
    :returns (mv (new-absdeclor? absdeclor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (absdeclor-option-case
       absdeclor?
       :some (simpadd0-absdeclor absdeclor?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                                 (gin simpadd0-ginp))
    :guard (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-annop dirabsdeclor))
    :returns (mv (new-dirabsdeclor dirabsdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirabsdeclor-case
       dirabsdeclor
       :dummy-base (prog2$
                    (raise "Misusage error: ~x0."
                           (dirabsdeclor-fix dirabsdeclor))
                    (mv (irr-dirabsdeclor) (irr-simpadd0-gout)))
       :paren (b* (((mv new-inner (simpadd0-gout gout-inner))
                    (simpadd0-absdeclor dirabsdeclor.inner gin))
                   (gin (simpadd0-gin-update gin gout-inner)))
                (mv (dirabsdeclor-paren new-inner)
                    (simpadd0-gout-no-thm gin)))
       :array (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                    (simpadd0-dirabsdeclor-option
                     dirabsdeclor.declor? gin))
                   (gin (simpadd0-gin-update gin gout-declor?))
                   ((mv new-size? (simpadd0-gout gout-expr?))
                    (simpadd0-expr-option dirabsdeclor.size? gin))
                   (gin (simpadd0-gin-update gin gout-expr?)))
                (mv (make-dirabsdeclor-array
                     :declor? new-declor?
                     :qualspecs dirabsdeclor.qualspecs
                     :size? new-size?)
                    (simpadd0-gout-no-thm gin)))
       :array-static1 (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin))
                           (gin (simpadd0-gin-update gin gout-declor?))
                           ((mv new-size (simpadd0-gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin))
                           (gin (simpadd0-gin-update gin gout-expr)))
                        (mv (make-dirabsdeclor-array-static1
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (simpadd0-gout-no-thm gin)))
       :array-static2 (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin))
                           (gin (simpadd0-gin-update gin gout-declor?))
                           ((mv new-size (simpadd0-gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin))
                           (gin (simpadd0-gin-update gin gout-expr)))
                        (mv (make-dirabsdeclor-array-static2
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (simpadd0-gout-no-thm gin)))
       :array-star (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                         (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                       gin))
                        (gin (simpadd0-gin-update gin gout-declor?)))
                     (mv (dirabsdeclor-array-star new-declor?)
                         (simpadd0-gout-no-thm gin)))
       :function (b* (((mv new-declor? (simpadd0-gout gout-declor?))
                       (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                     gin))
                      (gin (simpadd0-gin-update gin gout-declor?))
                      ((mv new-params (simpadd0-gout gout-params))
                       (simpadd0-param-declon-list dirabsdeclor.params gin))
                      (gin (simpadd0-gin-update gin gout-params)))
                   (mv (make-dirabsdeclor-function
                        :declor? new-declor?
                        :params new-params
                        :ellipsis dirabsdeclor.ellipsis)
                       (simpadd0-gout-no-thm gin)))))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                        (gin simpadd0-ginp))
    :guard (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-annop dirabsdeclor?))
    :returns (mv (new-dirabsdeclor? dirabsdeclor-optionp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional direct abstract declarator."
    (b* (((simpadd0-gin gin) gin))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :some (simpadd0-dirabsdeclor dirabsdeclor?.val gin)
       :none (mv nil (simpadd0-gout-no-thm gin))))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon ((paramdecl param-declonp) (gin simpadd0-ginp))
    :guard (and (param-declon-unambp paramdecl)
                (param-declon-annop paramdecl))
    :returns (mv (new-paramdecl param-declonp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declaration."
    (b* (((simpadd0-gin gin) gin)
         ((param-declon paramdecl) paramdecl)
         ((mv new-specs (simpadd0-gout gout-specs))
          (simpadd0-decl-spec-list paramdecl.specs gin))
         (gin (simpadd0-gin-update gin gout-specs))
         ((mv new-declor (simpadd0-gout gout-declor))
          (simpadd0-param-declor paramdecl.declor gin))
         (gin (simpadd0-gin-update gin gout-declor)))
      (mv (make-param-declon :specs new-specs
                             :declor new-declor
                             :attribs paramdecl.attribs)
          (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                :vartys gout-declor.vartys)))
    :measure (param-declon-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon-list ((paramdecls param-declon-listp)
                                      (gin simpadd0-ginp))
    :guard (and (param-declon-list-unambp paramdecls)
                (param-declon-list-annop paramdecls))
    :returns (mv (new-paramdecls param-declon-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of parameter declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp paramdecls))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-paramdecl (simpadd0-gout gout-paramdecl))
          (simpadd0-param-declon (car paramdecls) gin))
         (gin (simpadd0-gin-update gin gout-paramdecl))
         ((mv new-paramdecls (simpadd0-gout gout-paramdecls))
          (simpadd0-param-declon-list (cdr paramdecls)
                                      (change-simpadd0-gin
                                       gin :vartys gout-paramdecl.vartys)))
         (gin (simpadd0-gin-update gin gout-paramdecls)))
      (mv (cons new-paramdecl new-paramdecls)
          (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                :vartys gout-paramdecls.vartys)))
    :measure (param-declon-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declor ((paramdeclor param-declorp)
                                 (gin simpadd0-ginp))
    :guard (and (param-declor-unambp paramdeclor)
                (param-declor-annop paramdeclor))
    :returns (mv (new-paramdeclor param-declorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declarator."
    (b* (((simpadd0-gin gin) gin))
      (param-declor-case
       paramdeclor
       :nonabstract
       (b* (((mv new-declor (simpadd0-gout gout-declor))
             (simpadd0-declor paramdeclor.declor gin))
            (gin (simpadd0-gin-update gin gout-declor))
            (type (param-declor-nonabstract-info->type paramdeclor.info))
            (ident (declor->ident paramdeclor.declor))
            (post-vartys
             (if (and (ident-formalp ident)
                      (type-formalp type))
                 (b* (((mv & cvar) (ldm-ident ident))
                      ((mv & ctype) (ldm-type type)))
                   (omap::update cvar ctype gin.vartys))
               gin.vartys)))
         (mv (make-param-declor-nonabstract
              :declor new-declor
              :info paramdeclor.info)
             (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                   :vartys post-vartys)))
       :abstract (b* (((mv new-absdeclor (simpadd0-gout gout-absdeclor))
                       (simpadd0-absdeclor paramdeclor.declor gin))
                      (gin (simpadd0-gin-update gin gout-absdeclor)))
                   (mv (param-declor-abstract new-absdeclor)
                       (simpadd0-gout-no-thm gin)))
       :none (mv (param-declor-none) (simpadd0-gout-no-thm gin))
       :ambig (prog2$ (impossible) (mv (irr-param-declor) (irr-simpadd0-gout)))))
    :measure (param-declor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-tyname ((tyname tynamep) (gin simpadd0-ginp))
    :guard (and (tyname-unambp tyname)
                (tyname-annop tyname))
    :returns (mv (new-tyname tynamep)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type name."
    (b* (((simpadd0-gin gin) gin)
         ((tyname tyname) tyname)
         ((mv new-specquals (simpadd0-gout gout-specqual))
          (simpadd0-spec/qual-list tyname.specquals gin))
         (gin (simpadd0-gin-update gin gout-specqual))
         ((mv new-declor? (simpadd0-gout gout-declor?))
          (simpadd0-absdeclor-option tyname.declor? gin))
         (gin (simpadd0-gin-update gin gout-declor?)))
      (mv (make-tyname :specquals new-specquals
                       :declor? new-declor?
                       :info tyname.info)
          (simpadd0-gout-no-thm gin)))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struni-spec ((struni-spec struni-specp)
                                (gin simpadd0-ginp))
    :guard (and (struni-spec-unambp struni-spec)
                (struni-spec-annop struni-spec))
    :returns (mv (new-struni-spec struni-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure or union specifier."
    (b* (((simpadd0-gin gin) gin)
         ((struni-spec struni-spec) struni-spec)
         ((mv new-members (simpadd0-gout gout-members))
          (simpadd0-struct-declon-list struni-spec.members gin))
         (gin (simpadd0-gin-update gin gout-members)))
      (mv (make-struni-spec :name? struni-spec.name?
                            :members new-members)
          (simpadd0-gout-no-thm gin)))
    :measure (struni-spec-count struni-spec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declon ((structdeclon struct-declonp)
                                  (gin simpadd0-ginp))
    :guard (and (struct-declon-unambp structdeclon)
                (struct-declon-annop structdeclon))
    :returns (mv (new-structdeclon struct-declonp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declaration."
    (b* (((simpadd0-gin gin) gin))
      (struct-declon-case
       structdeclon
       :member (b* (((mv new-specqual (simpadd0-gout gout-specqual))
                     (simpadd0-spec/qual-list structdeclon.specqual gin))
                    (gin (simpadd0-gin-update gin gout-specqual))
                    ((mv new-declor (simpadd0-gout gout-declor))
                     (simpadd0-struct-declor-list structdeclon.declor gin))
                    (gin (simpadd0-gin-update gin gout-declor)))
                 (mv (make-struct-declon-member
                      :extension structdeclon.extension
                      :specqual new-specqual
                      :declor new-declor
                      :attrib structdeclon.attrib)
                     (simpadd0-gout-no-thm gin)))
       :statassert (b* (((mv new-structdeclon (simpadd0-gout gout-structdeclon))
                         (simpadd0-statassert structdeclon.unwrap gin))
                        (gin (simpadd0-gin-update gin gout-structdeclon)))
                     (mv (struct-declon-statassert new-structdeclon)
                         (simpadd0-gout-no-thm gin)))
       :empty (mv (struct-declon-empty) (simpadd0-gout-no-thm gin))))
    :measure (struct-declon-count structdeclon))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declon-list ((structdeclons struct-declon-listp)
                                       (gin simpadd0-ginp))
    :guard (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-annop structdeclons))
    :returns (mv (new-structdeclons struct-declon-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdeclons))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-structdeclon (simpadd0-gout gout-structdeclon))
          (simpadd0-struct-declon (car structdeclons) gin))
         (gin (simpadd0-gin-update gin gout-structdeclon))
         ((mv new-structdeclons (simpadd0-gout gout-structdeclons))
          (simpadd0-struct-declon-list (cdr structdeclons) gin))
         (gin (simpadd0-gin-update gin gout-structdeclons)))
      (mv (cons new-structdeclon new-structdeclons)
          (simpadd0-gout-no-thm gin)))
    :measure (struct-declon-list-count structdeclons))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declor ((structdeclor struct-declorp)
                                  (gin simpadd0-ginp))
    :guard (and (struct-declor-unambp structdeclor)
                (struct-declor-annop structdeclor))
    :returns (mv (new-structdeclor struct-declorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declarator."
    (b* (((simpadd0-gin gin) gin)
         ((struct-declor structdeclor) structdeclor)
         ((mv new-declor? (simpadd0-gout gout-declor?))
          (simpadd0-declor-option structdeclor.declor? gin))
         (gin (simpadd0-gin-update gin gout-declor?))
         ((mv new-expr? (simpadd0-gout gout-expr?))
          (simpadd0-const-expr-option structdeclor.expr? gin))
         (gin (simpadd0-gin-update gin gout-expr?)))
      (mv (make-struct-declor :declor? new-declor?
                              :expr? new-expr?)
          (simpadd0-gout-no-thm gin)))
    :measure (struct-declor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declor-list ((structdeclors struct-declor-listp)
                                       (gin simpadd0-ginp))
    :guard (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-annop structdeclors))
    :returns (mv (new-structdeclors struct-declor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdeclors))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-structdeclor (simpadd0-gout gout-structdeclor))
          (simpadd0-struct-declor (car structdeclors) gin))
         (gin (simpadd0-gin-update gin gout-structdeclor))
         ((mv new-structdeclors (simpadd0-gout gout-structdeclors))
          (simpadd0-struct-declor-list (cdr structdeclors) gin))
         (gin (simpadd0-gin-update gin gout-structdeclors)))
      (mv (cons new-structdeclor new-structdeclors)
          (simpadd0-gout-no-thm gin)))
    :measure (struct-declor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enum-spec ((enumspec enum-specp) (gin simpadd0-ginp))
    :guard (and (enum-spec-unambp enumspec)
                (enum-spec-annop enumspec))
    :returns (mv (new-enumspec enum-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumeration specifier."
    (b* (((simpadd0-gin gin) gin)
         ((enum-spec enumspec) enumspec)
         ((mv new-list (simpadd0-gout gout-list))
          (simpadd0-enumer-list enumspec.list gin))
         (gin (simpadd0-gin-update gin gout-list)))
      (mv (make-enum-spec :name enumspec.name
                          :list new-list
                          :final-comma enumspec.final-comma)
          (simpadd0-gout-no-thm gin)))
    :measure (enum-spec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp) (gin simpadd0-ginp))
    :guard (and (enumer-unambp enumer)
                (enumer-annop enumer))
    :returns (mv (new-enumer enumerp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumerator."
    (b* (((simpadd0-gin gin) gin)
         ((enumer enumer) enumer)
         ((mv new-value (simpadd0-gout gout-value))
          (simpadd0-const-expr-option enumer.value gin))
         (gin (simpadd0-gin-update gin gout-value)))
      (mv (make-enumer :name enumer.name
                       :value new-value)
          (simpadd0-gout-no-thm gin)))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer-list ((enumers enumer-listp)
                                (gin simpadd0-ginp))
    :guard (and (enumer-list-unambp enumers)
                (enumer-list-annop enumers))
    :returns (mv (new-enumers enumer-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of enumerators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp enumers))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-enumer (simpadd0-gout gout-enumer))
          (simpadd0-enumer (car enumers) gin))
         (gin (simpadd0-gin-update gin gout-enumer))
         ((mv new-enumers (simpadd0-gout gout-enumers))
          (simpadd0-enumer-list (cdr enumers) gin))
         (gin (simpadd0-gin-update gin gout-enumers)))
      (mv (cons new-enumer new-enumers)
          (simpadd0-gout-no-thm gin)))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-statassert ((statassert statassertp)
                               (gin simpadd0-ginp))
    :guard (and (statassert-unambp statassert)
                (statassert-annop statassert))
    :returns (mv (new-statassert statassertp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an static assertion declaration."
    (b* (((simpadd0-gin gin) gin)
         ((statassert statassert) statassert)
         ((mv new-test (simpadd0-gout gout-test))
          (simpadd0-const-expr statassert.test gin))
         (gin (simpadd0-gin-update gin gout-test)))
      (mv (make-statassert :test new-test
                           :message statassert.message)
          (simpadd0-gout-no-thm gin)))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor ((initdeclor initdeclorp)
                               (gin simpadd0-ginp))
    :guard (and (initdeclor-unambp initdeclor)
                (initdeclor-annop initdeclor))
    :returns (mv (new-initdeclor initdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If a theorem was generated for the initializer,
       it is regarded as the theorem for the initializer declarator.
       This is so that the theorem can surface up to block item declarations.")
     (xdoc::p
      "If the type of the declared identifier is supported for proof generation,
       we update the variable-type map."))
    (b* (((initdeclor initdeclor) initdeclor)
         ((mv new-declor (simpadd0-gout gout-declor))
          (simpadd0-declor initdeclor.declor gin))
         (gin (simpadd0-gin-update gin gout-declor))
         ((mv new-init? (simpadd0-gout gout-init?))
          (simpadd0-initer-option initdeclor.init?
                                  (change-simpadd0-gin
                                   gin :vartys gout-declor.vartys)))
         ((simpadd0-gin gin) (simpadd0-gin-update gin gout-init?))
         (type (initdeclor-info->type initdeclor.info))
         (ident (declor->ident initdeclor.declor))
         (post-vartys
          (if (and (not (initdeclor-info->typedefp initdeclor.info))
                   (ident-formalp ident)
                   (type-formalp type)
                   (not (type-case type :void))
                   (not (type-case type :char)))
              (b* (((mv & cvar) (ldm-ident ident))
                   ((mv & ctype) (ldm-type type)))
                (omap::update cvar ctype gout-init?.vartys))
            gout-init?.vartys)))
      (mv (make-initdeclor :declor new-declor
                           :asm? initdeclor.asm?
                           :attribs initdeclor.attribs
                           :init? new-init?
                           :info initdeclor.info)
          (if gout-init?.thm-name
              (make-simpadd0-gout :events gin.events
                                  :thm-index gin.thm-index
                                  :thm-name gout-init?.thm-name
                                  :vartys post-vartys)
            (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                  :vartys post-vartys))))
    :measure (initdeclor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initdeclor-list ((initdeclors initdeclor-listp)
                                    (gin simpadd0-ginp))
    :guard (and (initdeclor-list-unambp initdeclors)
                (initdeclor-list-annop initdeclors))
    :returns (mv (new-initdeclors initdeclor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the list is a singleton
       and a theorem was generated for that one element,
       it is regarded as the theorem for the list of initializer declarators.
       This is so that the theorem can surface up to block item declarations."))
    (b* (((when (endp initdeclors))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-initdeclor (simpadd0-gout gout-initdeclor))
          (simpadd0-initdeclor (car initdeclors) gin))
         (gin (simpadd0-gin-update gin gout-initdeclor))
         ((mv new-initdeclors (simpadd0-gout gout-initdeclors))
          (simpadd0-initdeclor-list (cdr initdeclors)
                                    (change-simpadd0-gin
                                     gin :vartys gout-initdeclor.vartys)))
         ((simpadd0-gin gin) (simpadd0-gin-update gin gout-initdeclors)))
      (mv (cons new-initdeclor new-initdeclors)
          (if (and (not (consp new-initdeclors))
                   gout-initdeclor.thm-name)
              (make-simpadd0-gout :events gin.events
                                  :thm-index gin.thm-index
                                  :thm-name gout-initdeclor.thm-name
                                  :vartys gout-initdeclor.vartys)
            (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                  :vartys gout-initdeclors.vartys))))
    :measure (initdeclor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl ((decl declp) (gin simpadd0-ginp))
    :guard (and (decl-unambp decl)
                (decl-annop decl))
    :returns (mv (new-decl declp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "In the case of a non-static-assert declaration,
       if a theorem was generated for the list of initializer declarators,
       it is regarded as the theorem for the declaration.
       This is so that the theorem can surface up to block item declarations."))
    (decl-case
     decl
     :decl (b* (((mv new-specs (simpadd0-gout gout-specs))
                 (simpadd0-decl-spec-list decl.specs gin))
                (gin (simpadd0-gin-update gin gout-specs))
                ((mv new-init (simpadd0-gout gout-init))
                 (simpadd0-initdeclor-list decl.init gin))
                ((simpadd0-gin gin) (simpadd0-gin-update gin gout-init)))
             (simpadd0-decl-decl decl.extension
                                 decl.specs
                                 new-specs
                                 gout-specs.thm-name
                                 decl.init
                                 new-init
                                 gout-init.thm-name
                                 gout-init.vartys
                                 gin))
     :statassert (b* (((mv new-decl (simpadd0-gout gout-decl))
                       (simpadd0-statassert decl.unwrap gin))
                      (gin (simpadd0-gin-update gin gout-decl)))
                   (mv (decl-statassert new-decl)
                       (simpadd0-gout-no-thm gin))))
    :measure (decl-count decl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-list ((decls decl-listp) (gin simpadd0-ginp))
    :guard (and (decl-list-unambp decls)
                (decl-list-annop decls))
    :returns (mv (new-decls decl-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp decls))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-decl (simpadd0-gout gout-decl))
          (simpadd0-decl (car decls) gin))
         (gin (simpadd0-gin-update gin gout-decl))
         ((mv new-decls (simpadd0-gout gout-decls))
          (simpadd0-decl-list (cdr decls)
                              (change-simpadd0-gin
                               gin :vartys gout-decl.vartys)))
         (gin (simpadd0-gin-update gin gout-decls)))
      (mv (cons new-decl new-decls)
          (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                :vartys gout-decls.vartys)))
    :measure (decl-list-count decls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-label ((label labelp) (gin simpadd0-ginp))
    :guard (and (label-unambp label)
                (label-annop label))
    :returns (mv (new-label labelp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a label."
    (b* (((simpadd0-gin gin) gin))
      (label-case
       label
       :name (mv (label-fix label) (simpadd0-gout-no-thm gin))
       :casexpr (b* (((mv new-expr (simpadd0-gout gout-expr))
                      (simpadd0-const-expr label.expr gin))
                     (gin (simpadd0-gin-update gin gout-expr))
                     ((mv new-range? (simpadd0-gout gout-range?))
                      (simpadd0-const-expr-option label.range? gin))
                     (gin (simpadd0-gin-update gin gout-range?)))
                  (mv (make-label-casexpr :expr new-expr
                                          :range? new-range?)
                      (simpadd0-gout-no-thm gin)))
       :default (mv (label-fix label) (simpadd0-gout-no-thm gin))))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-stmt ((stmt stmtp) (gin simpadd0-ginp))
    :guard (and (stmt-unambp stmt)
                (stmt-annop stmt))
    :returns (mv (new-stmt stmtp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a statement."
    (b* (((simpadd0-gin gin) gin))
      (stmt-case
       stmt
       :labeled (b* (((mv new-label (simpadd0-gout gout-label))
                      (simpadd0-label stmt.label gin))
                     (gin (simpadd0-gin-update gin gout-label))
                     ((mv new-stmt (simpadd0-gout gout-stmt))
                      (simpadd0-stmt stmt.stmt gin))
                     (gin (simpadd0-gin-update gin gout-stmt)))
                  (mv (make-stmt-labeled :label new-label
                                         :stmt new-stmt)
                      (simpadd0-gout-no-thm gin)))
       :compound (b* (((mv new-items (simpadd0-gout gout-items))
                       (simpadd0-block-item-list stmt.items gin))
                      (gin (simpadd0-gin-update gin gout-items)))
                   (simpadd0-stmt-compound stmt.items
                                           new-items
                                           gout-items.thm-name
                                           gin))
       :expr (b* (((mv new-expr? (simpadd0-gout gout-expr?))
                   (simpadd0-expr-option stmt.expr? gin))
                  (gin (simpadd0-gin-update gin gout-expr?)))
               (simpadd0-stmt-expr stmt.expr?
                                   new-expr?
                                   gout-expr?.thm-name
                                   stmt.info
                                   gin))
       :if (b* (((mv new-test (simpadd0-gout gout-test))
                 (simpadd0-expr stmt.test gin))
                (gin (simpadd0-gin-update gin gout-test))
                ((mv new-then (simpadd0-gout gout-then))
                 (simpadd0-stmt stmt.then gin))
                (gin (simpadd0-gin-update gin gout-then)))
             (simpadd0-stmt-if stmt.test
                               new-test
                               gout-test.thm-name
                               stmt.then
                               new-then
                               gout-then.thm-name
                               gin))
       :ifelse (b* (((mv new-test (simpadd0-gout gout-test))
                     (simpadd0-expr stmt.test gin))
                    (gin (simpadd0-gin-update gin gout-test))
                    ((mv new-then (simpadd0-gout gout-then))
                     (simpadd0-stmt stmt.then gin))
                    (gin (simpadd0-gin-update gin gout-then))
                    ((mv new-else (simpadd0-gout gout-else))
                     (simpadd0-stmt stmt.else gin))
                    (gin (simpadd0-gin-update gin gout-else)))
                 (simpadd0-stmt-ifelse stmt.test
                                       new-test
                                       gout-test.thm-name
                                       stmt.then
                                       new-then
                                       gout-then.thm-name
                                       stmt.else
                                       new-else
                                       gout-else.thm-name
                                       gin))
       :switch (b* (((mv new-target (simpadd0-gout gout-target))
                     (simpadd0-expr stmt.target gin))
                    (gin (simpadd0-gin-update gin gout-target))
                    ((mv new-body (simpadd0-gout gout-body))
                     (simpadd0-stmt stmt.body gin))
                    (gin (simpadd0-gin-update gin gout-body)))
                 (mv (make-stmt-switch :target new-target
                                       :body new-body)
                     (simpadd0-gout-no-thm gin)))
       :while (b* (((mv new-test (simpadd0-gout gout-test))
                    (simpadd0-expr stmt.test gin))
                   (gin (simpadd0-gin-update gin gout-test))
                   ((mv new-body (simpadd0-gout gout-body))
                    (simpadd0-stmt stmt.body gin))
                   (gin (simpadd0-gin-update gin gout-body)))
                (simpadd0-stmt-while stmt.test
                                     new-test
                                     gout-test.thm-name
                                     stmt.body
                                     new-body
                                     gout-body.thm-name
                                     gin))
       :dowhile (b* (((mv new-body (simpadd0-gout gout-body))
                      (simpadd0-stmt stmt.body gin))
                     (gin (simpadd0-gin-update gin gout-body))
                     ((mv new-test (simpadd0-gout gout-test))
                      (simpadd0-expr stmt.test gin))
                     (gin (simpadd0-gin-update gin gout-test)))
                  (mv (make-stmt-dowhile :body new-body
                                         :test new-test)
                      (simpadd0-gout-no-thm gin)))
       :for-expr (b* (((mv new-init (simpadd0-gout gout-init))
                       (simpadd0-expr-option stmt.init gin))
                      (gin (simpadd0-gin-update gin gout-init))
                      ((mv new-test (simpadd0-gout gout-test))
                       (simpadd0-expr-option stmt.test gin))
                      (gin (simpadd0-gin-update gin gout-test))
                      ((mv new-next (simpadd0-gout gout-next))
                       (simpadd0-expr-option stmt.next gin))
                      (gin (simpadd0-gin-update gin gout-next))
                      ((mv new-body (simpadd0-gout gout-body))
                       (simpadd0-stmt stmt.body gin))
                      (gin (simpadd0-gin-update gin gout-body)))
                   (mv (make-stmt-for-expr :init new-init
                                           :test new-test
                                           :next new-next
                                           :body new-body)
                       (simpadd0-gout-no-thm gin)))
       :for-decl (b* (((mv new-init (simpadd0-gout gout-init))
                       (simpadd0-decl stmt.init gin))
                      (gin (simpadd0-gin-update gin gout-init))
                      (gin1 (change-simpadd0-gin gin :vartys gout-init.vartys))
                      ((mv new-test (simpadd0-gout gout-test))
                       (simpadd0-expr-option stmt.test gin1))
                      (gin (simpadd0-gin-update gin gout-test))
                      ((mv new-next (simpadd0-gout gout-next))
                       (simpadd0-expr-option stmt.next gin1))
                      (gin (simpadd0-gin-update gin gout-next))
                      ((mv new-body (simpadd0-gout gout-body))
                       (simpadd0-stmt stmt.body gin1))
                      (gin (simpadd0-gin-update gin gout-body)))
                   (mv (make-stmt-for-decl :init new-init
                                           :test new-test
                                           :next new-next
                                           :body new-body)
                       (simpadd0-gout-no-thm gin)))
       :for-ambig (prog2$ (impossible) (mv (irr-stmt) (irr-simpadd0-gout)))
       :goto (mv (stmt-fix stmt) (simpadd0-gout-no-thm gin))
       :continue (mv (stmt-fix stmt) (simpadd0-gout-no-thm gin))
       :break (mv (stmt-fix stmt) (simpadd0-gout-no-thm gin))
       :return (b* (((mv new-expr? (simpadd0-gout gout-expr?))
                     (simpadd0-expr-option stmt.expr? gin))
                    (gin (simpadd0-gin-update gin gout-expr?)))
                 (simpadd0-stmt-return stmt.expr?
                                       new-expr?
                                       gout-expr?.thm-name
                                       stmt.info
                                       gin))
       :asm (mv (stmt-fix stmt) (simpadd0-gout-no-thm gin))))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item ((item block-itemp) (gin simpadd0-ginp))
    :guard (and (block-item-unambp item)
                (block-item-annop item))
    :returns (mv (new-item block-itemp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a block item."
    (b* (((simpadd0-gin gin) gin))
      (block-item-case
       item
       :decl (b* (((mv new-decl (simpadd0-gout gout-decl))
                   (simpadd0-decl item.decl gin))
                  (gin (simpadd0-gin-update gin gout-decl)))
               (simpadd0-block-item-decl item.decl
                                         new-decl
                                         gout-decl.thm-name
                                         item.info
                                         gout-decl.vartys
                                         gin))
       :stmt (b* (((mv new-stmt (simpadd0-gout gout-stmt))
                   (simpadd0-stmt item.stmt gin))
                  (gin (simpadd0-gin-update gin gout-stmt)))
               (simpadd0-block-item-stmt item.stmt
                                         new-stmt
                                         gout-stmt.thm-name
                                         item.info
                                         gin))
       :ambig (prog2$ (impossible) (mv (irr-block-item) (irr-simpadd0-gout)))))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item-list ((items block-item-listp)
                                    (gin simpadd0-ginp))
    :guard (and (block-item-list-unambp items)
                (block-item-list-annop items))
    :returns (mv (new-items block-item-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of block items."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp items))
          (mv nil (simpadd0-block-item-list-empty gin)))
         (item (car items))
         ((mv new-item (simpadd0-gout gout-item))
          (simpadd0-block-item item gin))
         (gin (simpadd0-gin-update gin gout-item))
         ((mv new-items (simpadd0-gout gout-items))
          (simpadd0-block-item-list (cdr items)
                                    (change-simpadd0-gin
                                     gin :vartys gout-item.vartys)))
         (gin (simpadd0-gin-update gin gout-items)))
      (simpadd0-block-item-list-cons (car items)
                                     new-item
                                     gout-item.thm-name
                                     (cdr items)
                                     new-items
                                     gout-items.thm-name
                                     gin))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done after the unambiguity proofs

  ///

  (local (in-theory (enable irr-absdeclor
                            irr-dirabsdeclor)))

  (fty::deffixequiv-mutual simpadd0-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-unambp-of-simpadd0-exprs/decls
    (defret expr-unambp-of-simpadd0-expr
      (expr-unambp new-expr)
      :fn simpadd0-expr)
    (defret expr-list-unambp-of-simpadd0-expr-list
      (expr-list-unambp new-exprs)
      :fn simpadd0-expr-list)
    (defret expr-option-unambp-of-simpadd0-expr-option
      (expr-option-unambp new-expr?)
      :fn simpadd0-expr-option)
    (defret const-expr-unambp-of-simpadd0-const-expr
      (const-expr-unambp new-cexpr)
      :fn simpadd0-const-expr)
    (defret const-expr-option-unambp-of-simpadd0-const-expr-option
      (const-expr-option-unambp new-cexpr?)
      :fn simpadd0-const-expr-option)
    (defret genassoc-unambp-of-simpadd0-genassoc
      (genassoc-unambp new-genassoc)
      :fn simpadd0-genassoc)
    (defret genassoc-list-unambp-of-simpadd0-genassoc-list
      (genassoc-list-unambp new-genassocs)
      :fn simpadd0-genassoc-list)
    (defret member-designor-unambp-of-simpadd0-member-designor
      (member-designor-unambp new-memdes)
      :fn simpadd0-member-designor)
    (defret type-spec-unambp-of-simpadd0-type-spec
      (type-spec-unambp new-tyspec)
      :fn simpadd0-type-spec)
    (defret spec/qual-unambp-of-simpadd0-spec/qual
      (spec/qual-unambp new-specqual)
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-unambp-of-simpadd0-spec/qual-list
      (spec/qual-list-unambp new-specquals)
      :fn simpadd0-spec/qual-list)
    (defret align-spec-unambp-of-simpadd0-align-spec
      (align-spec-unambp new-alignspec)
      :fn simpadd0-align-spec)
    (defret decl-spec-unambp-of-simpadd0-decl-spec
      (decl-spec-unambp new-declspec)
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-unambp-of-simpadd0-decl-spec-list
      (decl-spec-list-unambp new-declspecs)
      :fn simpadd0-decl-spec-list)
    (defret initer-unambp-of-simpadd0-initer
      (initer-unambp new-initer)
      :fn simpadd0-initer)
    (defret initer-option-unambp-of-simpadd0-initer-option
      (initer-option-unambp new-initer?)
      :fn simpadd0-initer-option)
    (defret desiniter-unambp-of-simpadd0-desiniter
      (desiniter-unambp new-desiniter)
      :fn simpadd0-desiniter)
    (defret desiniter-list-unambp-of-simpadd0-desiniter-list
      (desiniter-list-unambp new-desiniters)
      :fn simpadd0-desiniter-list)
    (defret designor-unambp-of-simpadd0-designor
      (designor-unambp new-designor)
      :fn simpadd0-designor)
    (defret designor-list-unambp-of-simpadd0-designor-list
      (designor-list-unambp new-designors)
      :fn simpadd0-designor-list)
    (defret declor-unambp-of-simpadd0-declor
      (declor-unambp new-declor)
      :fn simpadd0-declor)
    (defret declor-option-unambp-of-simpadd0-declor-option
      (declor-option-unambp new-declor?)
      :fn simpadd0-declor-option)
    (defret dirdeclor-unambp-of-simpadd0-dirdeclor
      (dirdeclor-unambp new-dirdeclor)
      :fn simpadd0-dirdeclor)
    (defret absdeclor-unambp-of-simpadd0-absdeclor
      (absdeclor-unambp new-absdeclor)
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-unambp-of-simpadd0-absdeclor-option
      (absdeclor-option-unambp new-absdeclor?)
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-unambp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-unambp new-dirabsdeclor)
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-unambp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-unambp new-dirabsdeclor?)
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-unambp-of-simpadd0-param-declon
      (param-declon-unambp new-paramdecl)
      :fn simpadd0-param-declon)
    (defret param-declon-list-unambp-of-simpadd0-param-declon-list
      (param-declon-list-unambp new-paramdecls)
      :fn simpadd0-param-declon-list)
    (defret param-declor-unambp-of-simpadd0-param-declor
      (param-declor-unambp new-paramdeclor)
      :fn simpadd0-param-declor)
    (defret tyname-unambp-of-simpadd0-tyname
      (tyname-unambp new-tyname)
      :fn simpadd0-tyname)
    (defret struni-spec-unambp-of-simpadd0-struni-spec
      (struni-spec-unambp new-struni-spec)
      :fn simpadd0-struni-spec)
    (defret struct-declon-unambp-of-simpadd0-struct-declon
      (struct-declon-unambp new-structdeclon)
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-unambp-of-simpadd0-struct-declon-list
      (struct-declon-list-unambp new-structdeclons)
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-unambp-of-simpadd0-struct-declor
      (struct-declor-unambp new-structdeclor)
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-unambp-of-simpadd0-struct-declor-list
      (struct-declor-list-unambp new-structdeclors)
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-unambp-of-simpadd0-enum-spec
      (enum-spec-unambp new-enumspec)
      :fn simpadd0-enum-spec)
    (defret enumer-unambp-of-simpadd0-enumer
      (enumer-unambp new-enumer)
      :fn simpadd0-enumer)
    (defret enumer-list-unambp-of-simpadd0-enumer-list
      (enumer-list-unambp new-enumers)
      :fn simpadd0-enumer-list)
    (defret statassert-unambp-of-simpadd0-statassert
      (statassert-unambp new-statassert)
      :fn simpadd0-statassert)
    (defret initdeclor-unambp-of-simpadd0-initdeclor
      (initdeclor-unambp new-initdeclor)
      :fn simpadd0-initdeclor)
    (defret initdeclor-list-unambp-of-simpadd0-initdeclor-list
      (initdeclor-list-unambp new-initdeclors)
      :fn simpadd0-initdeclor-list)
    (defret decl-unambp-of-simpadd0-decl
      (decl-unambp new-decl)
      :fn simpadd0-decl)
    (defret decl-list-unambp-of-simpadd0-decl-list
      (decl-list-unambp new-decls)
      :fn simpadd0-decl-list)
    (defret label-unambp-of-simpadd0-label
      (label-unambp new-label)
      :fn simpadd0-label)
    (defret stmt-unambp-of-simpadd0-stmt
      (stmt-unambp new-stmt)
      :fn simpadd0-stmt)
    (defret block-item-unambp-of-simpadd0-block-item
      (block-item-unambp new-item)
      :fn simpadd0-block-item)
    (defret block-item-list-unambp-of-simpadd0-block-item-list
      (block-item-list-unambp new-items)
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-initdeclor
                                       simpadd0-initdeclor-list
                                       simpadd0-decl
                                       simpadd0-decl-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list
                                       irr-expr
                                       irr-const-expr
                                       irr-align-spec
                                       irr-dirabsdeclor
                                       irr-param-declor
                                       irr-type-spec
                                       irr-stmt
                                       irr-block-item))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-annop-of-simpadd0-exprs/decls
    (defret expr-annop-of-simpadd0-expr
      (expr-annop new-expr)
      :hyp (and (expr-unambp expr)
                (expr-annop expr))
      :fn simpadd0-expr)
    (defret expr-list-annop-of-simpadd0-expr-list
      (expr-list-annop new-exprs)
      :hyp (and (expr-list-unambp exprs)
                (expr-list-annop exprs))
      :fn simpadd0-expr-list)
    (defret expr-option-annop-of-simpadd0-expr-option
      (expr-option-annop new-expr?)
      :hyp (and (expr-option-unambp expr?)
                (expr-option-annop expr?))
      :fn simpadd0-expr-option)
    (defret const-expr-annop-of-simpadd0-const-expr
      (const-expr-annop new-cexpr)
      :hyp (and (const-expr-unambp cexpr)
                (const-expr-annop cexpr))
      :fn simpadd0-const-expr)
    (defret const-expr-option-annop-of-simpadd0-const-expr-option
      (const-expr-option-annop new-cexpr?)
      :hyp (and (const-expr-option-unambp cexpr?)
                (const-expr-option-annop cexpr?))
      :fn simpadd0-const-expr-option)
    (defret genassoc-annop-of-simpadd0-genassoc
      (genassoc-annop new-genassoc)
      :hyp (and (genassoc-unambp genassoc)
                (genassoc-annop genassoc))
      :fn simpadd0-genassoc)
    (defret genassoc-list-annop-of-simpadd0-genassoc-list
      (genassoc-list-annop new-genassocs)
      :hyp (and (genassoc-list-unambp genassocs)
                (genassoc-list-annop genassocs))
      :fn simpadd0-genassoc-list)
    (defret member-designor-annop-of-simpadd0-member-designor
      (member-designor-annop new-memdes)
      :hyp (and (member-designor-unambp memdes)
                (member-designor-annop memdes))
      :fn simpadd0-member-designor)
    (defret type-spec-annop-of-simpadd0-type-spec
      (type-spec-annop new-tyspec)
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-annop tyspec))
      :fn simpadd0-type-spec)
    (defret spec/qual-annop-of-simpadd0-spec/qual
      (spec/qual-annop new-specqual)
      :hyp (and (spec/qual-unambp specqual)
                (spec/qual-annop specqual))
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-annop-of-simpadd0-spec/qual-list
      (spec/qual-list-annop new-specquals)
      :hyp (and (spec/qual-list-unambp specquals)
                (spec/qual-list-annop specquals))
      :fn simpadd0-spec/qual-list)
    (defret align-spec-annop-of-simpadd0-align-spec
      (align-spec-annop new-alignspec)
      :hyp (and (align-spec-unambp alignspec)
                (align-spec-annop alignspec))
      :fn simpadd0-align-spec)
    (defret decl-spec-annop-of-simpadd0-decl-spec
      (decl-spec-annop new-declspec)
      :hyp (and (decl-spec-unambp declspec)
                (decl-spec-annop declspec))
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-annop-of-simpadd0-decl-spec-list
      (decl-spec-list-annop new-declspecs)
      :hyp (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-annop declspecs))
      :fn simpadd0-decl-spec-list)
    (defret initer-annop-of-simpadd0-initer
      (initer-annop new-initer)
      :hyp (and (initer-unambp initer)
                (initer-annop initer))
      :fn simpadd0-initer)
    (defret initer-option-annop-of-simpadd0-initer-option
      (initer-option-annop new-initer?)
      :hyp (and (initer-option-unambp initer?)
                (initer-option-annop initer?))
      :fn simpadd0-initer-option)
    (defret desiniter-annop-of-simpadd0-desiniter
      (desiniter-annop new-desiniter)
      :hyp (and (desiniter-unambp desiniter)
                (desiniter-annop desiniter))
      :fn simpadd0-desiniter)
    (defret desiniter-list-annop-of-simpadd0-desiniter-list
      (desiniter-list-annop new-desiniters)
      :hyp (and (desiniter-list-unambp desiniters)
                (desiniter-list-annop desiniters))
      :fn simpadd0-desiniter-list)
    (defret designor-annop-of-simpadd0-designor
      (designor-annop new-designor)
      :hyp (and (designor-unambp designor)
                (designor-annop designor))
      :fn simpadd0-designor)
    (defret designor-list-annop-of-simpadd0-designor-list
      (designor-list-annop new-designors)
      :hyp (and (designor-list-unambp designors)
                (designor-list-annop designors))
      :fn simpadd0-designor-list)
    (defret declor-annop-of-simpadd0-declor
      (declor-annop new-declor)
      :hyp (and (declor-unambp declor)
                (declor-annop declor))
      :fn simpadd0-declor)
    (defret declor-option-annop-of-simpadd0-declor-option
      (declor-option-annop new-declor?)
      :hyp (and (declor-option-unambp declor?)
                (declor-option-annop declor?))
      :fn simpadd0-declor-option)
    (defret dirdeclor-annop-of-simpadd0-dirdeclor
      (dirdeclor-annop new-dirdeclor)
      :hyp (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-annop dirdeclor))
      :fn simpadd0-dirdeclor)
    (defret absdeclor-annop-of-simpadd0-absdeclor
      (absdeclor-annop new-absdeclor)
      :hyp (and (absdeclor-unambp absdeclor)
                (absdeclor-annop absdeclor))
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-annop-of-simpadd0-absdeclor-option
      (absdeclor-option-annop new-absdeclor?)
      :hyp (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-annop absdeclor?))
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-annop-of-simpadd0-dirabsdeclor
      (dirabsdeclor-annop new-dirabsdeclor)
      :hyp (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-annop dirabsdeclor))
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-annop-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-annop new-dirabsdeclor?)
      :hyp (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-annop dirabsdeclor?))
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-annop-of-simpadd0-param-declon
      (param-declon-annop new-paramdecl)
      :hyp (and (param-declon-unambp paramdecl)
                (param-declon-annop paramdecl))
      :fn simpadd0-param-declon)
    (defret param-declon-list-annop-of-simpadd0-param-declon-list
      (param-declon-list-annop new-paramdecls)
      :hyp (and (param-declon-list-unambp paramdecls)
                (param-declon-list-annop paramdecls))
      :fn simpadd0-param-declon-list)
    (defret param-declor-annop-of-simpadd0-param-declor
      (param-declor-annop new-paramdeclor)
      :hyp (and (param-declor-unambp paramdeclor)
                (param-declor-annop paramdeclor))
      :fn simpadd0-param-declor)
    (defret tyname-annop-of-simpadd0-tyname
      (tyname-annop new-tyname)
      :hyp (and (tyname-unambp tyname)
                (tyname-annop tyname))
      :fn simpadd0-tyname)
    (defret struni-spec-annop-of-simpadd0-struni-spec
      (struni-spec-annop new-struni-spec)
      :hyp (and (struni-spec-unambp struni-spec)
                (struni-spec-annop struni-spec))
      :fn simpadd0-struni-spec)
    (defret struct-declon-annop-of-simpadd0-struct-declon
      (struct-declon-annop new-structdeclon)
      :hyp (and (struct-declon-unambp structdeclon)
                (struct-declon-annop structdeclon))
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-annop-of-simpadd0-struct-declon-list
      (struct-declon-list-annop new-structdeclons)
      :hyp (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-annop structdeclons))
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-annop-of-simpadd0-struct-declor
      (struct-declor-annop new-structdeclor)
      :hyp (and (struct-declor-unambp structdeclor)
                (struct-declor-annop structdeclor))
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-annop-of-simpadd0-struct-declor-list
      (struct-declor-list-annop new-structdeclors)
      :hyp (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-annop structdeclors))
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-annop-of-simpadd0-enum-spec
      (enum-spec-annop new-enumspec)
      :hyp (and (enum-spec-unambp enumspec)
                (enum-spec-annop enumspec))
      :fn simpadd0-enum-spec)
    (defret enumer-annop-of-simpadd0-enumer
      (enumer-annop new-enumer)
      :hyp (and (enumer-unambp enumer)
                (enumer-annop enumer))
      :fn simpadd0-enumer)
    (defret enumer-list-annop-of-simpadd0-enumer-list
      (enumer-list-annop new-enumers)
      :hyp (and (enumer-list-unambp enumers)
                (enumer-list-annop enumers))
      :fn simpadd0-enumer-list)
    (defret statassert-annop-of-simpadd0-statassert
      (statassert-annop new-statassert)
      :hyp (and (statassert-unambp statassert)
                (statassert-annop statassert))
      :fn simpadd0-statassert)
    (defret initdeclor-annop-of-simpadd0-initdeclor
      (initdeclor-annop new-initdeclor)
      :hyp (and (initdeclor-unambp initdeclor)
                (initdeclor-annop initdeclor))
      :fn simpadd0-initdeclor)
    (defret initdeclor-list-annop-of-simpadd0-initdeclor-list
      (initdeclor-list-annop new-initdeclors)
      :hyp (and (initdeclor-list-unambp initdeclors)
                (initdeclor-list-annop initdeclors))
      :fn simpadd0-initdeclor-list)
    (defret decl-annop-of-simpadd0-decl
      (decl-annop new-decl)
      :hyp (and (decl-unambp decl)
                (decl-annop decl))
      :fn simpadd0-decl)
    (defret decl-list-annop-of-simpadd0-decl-list
      (decl-list-annop new-decls)
      :hyp (and (decl-list-unambp decls)
                (decl-list-annop decls))
      :fn simpadd0-decl-list)
    (defret label-annop-of-simpadd0-label
      (label-annop new-label)
      :hyp (and (label-unambp label)
                (label-annop label))
      :fn simpadd0-label)
    (defret stmt-annop-of-simpadd0-stmt
      (stmt-annop new-stmt)
      :hyp (and (stmt-unambp stmt)
                (stmt-annop stmt))
      :fn simpadd0-stmt)
    (defret block-item-annop-of-simpadd0-block-item
      (block-item-annop new-item)
      :hyp (and (block-item-unambp item)
                (block-item-annop item))
      :fn simpadd0-block-item)
    (defret block-item-list-annop-of-simpadd0-block-item-list
      (block-item-list-annop new-items)
      :hyp (and (block-item-list-unambp items)
                (block-item-list-annop items))
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-initdeclor
                                       simpadd0-initdeclor-list
                                       simpadd0-decl
                                       simpadd0-decl-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-aidentp-of-simpadd0-exprs/decls
    (defret expr-aidentp-of-simpadd0-expr
      (expr-aidentp new-expr gcc)
      :hyp (and (expr-unambp expr)
                (expr-aidentp expr gcc))
      :fn simpadd0-expr)
    (defret expr-list-aidentp-of-simpadd0-expr-list
      (expr-list-aidentp new-exprs gcc)
      :hyp (and (expr-list-unambp exprs)
                (expr-list-aidentp exprs gcc))
      :fn simpadd0-expr-list)
    (defret expr-option-aidentp-of-simpadd0-expr-option
      (expr-option-aidentp new-expr? gcc)
      :hyp (and (expr-option-unambp expr?)
                (expr-option-aidentp expr? gcc))
      :fn simpadd0-expr-option)
    (defret const-expr-aidentp-of-simpadd0-const-expr
      (const-expr-aidentp new-cexpr gcc)
      :hyp (and (const-expr-unambp cexpr)
                (const-expr-aidentp cexpr gcc))
      :fn simpadd0-const-expr)
    (defret const-expr-option-aidentp-of-simpadd0-const-expr-option
      (const-expr-option-aidentp new-cexpr? gcc)
      :hyp (and (const-expr-option-unambp cexpr?)
                (const-expr-option-aidentp cexpr? gcc))
      :fn simpadd0-const-expr-option)
    (defret genassoc-aidentp-of-simpadd0-genassoc
      (genassoc-aidentp new-genassoc gcc)
      :hyp (and (genassoc-unambp genassoc)
                (genassoc-aidentp genassoc gcc))
      :fn simpadd0-genassoc)
    (defret genassoc-list-aidentp-of-simpadd0-genassoc-list
      (genassoc-list-aidentp new-genassocs gcc)
      :hyp (and (genassoc-list-unambp genassocs)
                (genassoc-list-aidentp genassocs gcc))
      :fn simpadd0-genassoc-list)
    (defret member-designor-aidentp-of-simpadd0-member-designor
      (member-designor-aidentp new-memdes gcc)
      :hyp (and (member-designor-unambp memdes)
                (member-designor-aidentp memdes gcc))
      :fn simpadd0-member-designor)
    (defret type-spec-aidentp-of-simpadd0-type-spec
      (type-spec-aidentp new-tyspec gcc)
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-aidentp tyspec gcc))
      :fn simpadd0-type-spec)
    (defret spec/qual-aidentp-of-simpadd0-spec/qual
      (spec/qual-aidentp new-specqual gcc)
      :hyp (and (spec/qual-unambp specqual)
                (spec/qual-aidentp specqual gcc))
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-aidentp-of-simpadd0-spec/qual-list
      (spec/qual-list-aidentp new-specquals gcc)
      :hyp (and (spec/qual-list-unambp specquals)
                (spec/qual-list-aidentp specquals gcc))
      :fn simpadd0-spec/qual-list)
    (defret align-spec-aidentp-of-simpadd0-align-spec
      (align-spec-aidentp new-alignspec gcc)
      :hyp (and (align-spec-unambp alignspec)
                (align-spec-aidentp alignspec gcc))
      :fn simpadd0-align-spec)
    (defret decl-spec-aidentp-of-simpadd0-decl-spec
      (decl-spec-aidentp new-declspec gcc)
      :hyp (and (decl-spec-unambp declspec)
                (decl-spec-aidentp declspec gcc))
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-aidentp-of-simpadd0-decl-spec-list
      (decl-spec-list-aidentp new-declspecs gcc)
      :hyp (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-aidentp declspecs gcc))
      :fn simpadd0-decl-spec-list)
    (defret initer-aidentp-of-simpadd0-initer
      (initer-aidentp new-initer gcc)
      :hyp (and (initer-unambp initer)
                (initer-aidentp initer gcc))
      :fn simpadd0-initer)
    (defret initer-option-aidentp-of-simpadd0-initer-option
      (initer-option-aidentp new-initer? gcc)
      :hyp (and (initer-option-unambp initer?)
                (initer-option-aidentp initer? gcc))
      :fn simpadd0-initer-option)
    (defret desiniter-aidentp-of-simpadd0-desiniter
      (desiniter-aidentp new-desiniter gcc)
      :hyp (and (desiniter-unambp desiniter)
                (desiniter-aidentp desiniter gcc))
      :fn simpadd0-desiniter)
    (defret desiniter-list-aidentp-of-simpadd0-desiniter-list
      (desiniter-list-aidentp new-desiniters gcc)
      :hyp (and (desiniter-list-unambp desiniters)
                (desiniter-list-aidentp desiniters gcc))
      :fn simpadd0-desiniter-list)
    (defret designor-aidentp-of-simpadd0-designor
      (designor-aidentp new-designor gcc)
      :hyp (and (designor-unambp designor)
                (designor-aidentp designor gcc))
      :fn simpadd0-designor)
    (defret designor-list-aidentp-of-simpadd0-designor-list
      (designor-list-aidentp new-designors gcc)
      :hyp (and (designor-list-unambp designors)
                (designor-list-aidentp designors gcc))
      :fn simpadd0-designor-list)
    (defret declor-aidentp-of-simpadd0-declor
      (declor-aidentp new-declor gcc)
      :hyp (and (declor-unambp declor)
                (declor-aidentp declor gcc))
      :fn simpadd0-declor)
    (defret declor-option-aidentp-of-simpadd0-declor-option
      (declor-option-aidentp new-declor? gcc)
      :hyp (and (declor-option-unambp declor?)
                (declor-option-aidentp declor? gcc))
      :fn simpadd0-declor-option)
    (defret dirdeclor-aidentp-of-simpadd0-dirdeclor
      (dirdeclor-aidentp new-dirdeclor gcc)
      :hyp (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-aidentp dirdeclor gcc))
      :fn simpadd0-dirdeclor)
    (defret absdeclor-aidentp-of-simpadd0-absdeclor
      (absdeclor-aidentp new-absdeclor gcc)
      :hyp (and (absdeclor-unambp absdeclor)
                (absdeclor-aidentp absdeclor gcc))
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-aidentp-of-simpadd0-absdeclor-option
      (absdeclor-option-aidentp new-absdeclor? gcc)
      :hyp (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-aidentp absdeclor? gcc))
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-aidentp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-aidentp new-dirabsdeclor gcc)
      :hyp (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-aidentp dirabsdeclor gcc))
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-aidentp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-aidentp new-dirabsdeclor? gcc)
      :hyp (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-aidentp dirabsdeclor? gcc))
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-aidentp-of-simpadd0-param-declon
      (param-declon-aidentp new-paramdecl gcc)
      :hyp (and (param-declon-unambp paramdecl)
                (param-declon-aidentp paramdecl gcc))
      :fn simpadd0-param-declon)
    (defret param-declon-list-aidentp-of-simpadd0-param-declon-list
      (param-declon-list-aidentp new-paramdecls gcc)
      :hyp (and (param-declon-list-unambp paramdecls)
                (param-declon-list-aidentp paramdecls gcc))
      :fn simpadd0-param-declon-list)
    (defret param-declor-aidentp-of-simpadd0-param-declor
      (param-declor-aidentp new-paramdeclor gcc)
      :hyp (and (param-declor-unambp paramdeclor)
                (param-declor-aidentp paramdeclor gcc))
      :fn simpadd0-param-declor)
    (defret tyname-aidentp-of-simpadd0-tyname
      (tyname-aidentp new-tyname gcc)
      :hyp (and (tyname-unambp tyname)
                (tyname-aidentp tyname gcc))
      :fn simpadd0-tyname)
    (defret struni-spec-aidentp-of-simpadd0-struni-spec
      (struni-spec-aidentp new-struni-spec gcc)
      :hyp (and (struni-spec-unambp struni-spec)
                (struni-spec-aidentp struni-spec gcc))
      :fn simpadd0-struni-spec)
    (defret struct-declon-aidentp-of-simpadd0-struct-declon
      (struct-declon-aidentp new-structdeclon gcc)
      :hyp (and (struct-declon-unambp structdeclon)
                (struct-declon-aidentp structdeclon gcc))
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-aidentp-of-simpadd0-struct-declon-list
      (struct-declon-list-aidentp new-structdeclons gcc)
      :hyp (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-aidentp structdeclons gcc))
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-aidentp-of-simpadd0-struct-declor
      (struct-declor-aidentp new-structdeclor gcc)
      :hyp (and (struct-declor-unambp structdeclor)
                (struct-declor-aidentp structdeclor gcc))
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-aidentp-of-simpadd0-struct-declor-list
      (struct-declor-list-aidentp new-structdeclors gcc)
      :hyp (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-aidentp structdeclors gcc))
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-aidentp-of-simpadd0-enum-spec
      (enum-spec-aidentp new-enumspec gcc)
      :hyp (and (enum-spec-unambp enumspec)
                (enum-spec-aidentp enumspec gcc))
      :fn simpadd0-enum-spec)
    (defret enumer-aidentp-of-simpadd0-enumer
      (enumer-aidentp new-enumer gcc)
      :hyp (and (enumer-unambp enumer)
                (enumer-aidentp enumer gcc))
      :fn simpadd0-enumer)
    (defret enumer-list-aidentp-of-simpadd0-enumer-list
      (enumer-list-aidentp new-enumers gcc)
      :hyp (and (enumer-list-unambp enumers)
                (enumer-list-aidentp enumers gcc))
      :fn simpadd0-enumer-list)
    (defret statassert-aidentp-of-simpadd0-statassert
      (statassert-aidentp new-statassert gcc)
      :hyp (and (statassert-unambp statassert)
                (statassert-aidentp statassert gcc))
      :fn simpadd0-statassert)
    (defret initdeclor-aidentp-of-simpadd0-initdeclor
      (initdeclor-aidentp new-initdeclor gcc)
      :hyp (and (initdeclor-unambp initdeclor)
                (initdeclor-aidentp initdeclor gcc))
      :fn simpadd0-initdeclor)
    (defret initdeclor-list-aidentp-of-simpadd0-initdeclor-list
      (initdeclor-list-aidentp new-initdeclors gcc)
      :hyp (and (initdeclor-list-unambp initdeclors)
                (initdeclor-list-aidentp initdeclors gcc))
      :fn simpadd0-initdeclor-list)
    (defret decl-aidentp-of-simpadd0-decl
      (decl-aidentp new-decl gcc)
      :hyp (and (decl-unambp decl)
                (decl-aidentp decl gcc))
      :fn simpadd0-decl)
    (defret decl-list-aidentp-of-simpadd0-decl-list
      (decl-list-aidentp new-decls gcc)
      :hyp (and (decl-list-unambp decls)
                (decl-list-aidentp decls gcc))
      :fn simpadd0-decl-list)
    (defret label-aidentp-of-simpadd0-label
      (label-aidentp new-label gcc)
      :hyp (and (label-unambp label)
                (label-aidentp label gcc))
      :fn simpadd0-label)
    (defret stmt-aidentp-of-simpadd0-stmt
      (stmt-aidentp new-stmt gcc)
      :hyp (and (stmt-unambp stmt)
                (stmt-aidentp stmt gcc))
      :fn simpadd0-stmt)
    (defret block-item-aidentp-of-simpadd0-block-item
      (block-item-aidentp new-item gcc)
      :hyp (and (block-item-unambp item)
                (block-item-aidentp item gcc))
      :fn simpadd0-block-item)
    (defret block-item-list-aidentp-of-simpadd0-block-item-list
      (block-item-list-aidentp new-items gcc)
      :hyp (and (block-item-list-unambp items)
                (block-item-list-aidentp items gcc))
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-member-designor
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-initdeclor
                                       simpadd0-initdeclor-list
                                       simpadd0-decl
                                       simpadd0-decl-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards simpadd0-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp) (gin simpadd0-ginp))
  :guard (and (fundef-unambp fundef)
              (fundef-annop fundef))
  :returns (mv (new-fundef fundefp)
               (gout simpadd0-goutp))
  :short "Transform a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem for the function
     only under certain conditions,
     including the fact that a theorem for the body gets generated.")
   (xdoc::p
    "For the body of the function,
     currently we obtain the variable-type map from
     the validation table that annotates the function definition
     (the validation table at the start of the body,
     not at the start of the function definition;
     we plan to avoid this, and use instead the variable-type map
     coming from the transformation of the constructs preceding the body,
     since now we may have sufficient propagation of variable-type maps,
     which was not the case some time ago
     (which motivated the use of
     the validation table at the start of the body).
     The validation table at the start of the body
     is put into the @(tsee simpadd0-gin)
     and passed to @(tsee simpadd0-block-item-list).")
   (xdoc::p
    "We generate the folllowing theorems:")
   (xdoc::ul
    (xdoc::li
     "A theorem about the initial scope of the function body.
      See @(tsee simpadd0-gen-init-scope-thm).")
    (xdoc::li
     "For each function parameter, a theorem saying that,
      after pushing a frame with the initial scope above,
      the computation state has a variable for the parameter
      with the associated type.")
    (xdoc::li
     "The main theorem for the function definition,
      saying that, if the execution of the old function does not yield an error,
      neither does the execition of the new function,
      and they return the same results and computation states."))
   (xdoc::p
    "We use @(tsee simpadd0-gen-from-params) to obtain
     certain information from the parameters,
     which is used to generate the theorems.
     This information includes the variable-type map
     corresponding to the function parameters:
     we ensure that it is the same as
     the variable-type map from the validation table
     that annotates the start of the function body.
     In general the former is a sub-map of the latter,
     because the validation table could include global variables;
     but for now proof generation does not handle global variables,
     so we generate proofs for the body only if
     the theorems about the initial scope and the parameters
     suffice to establish the variable-type hypotheses of the body."))
  (b* (((fundef fundef) fundef)
       ((mv new-spec (simpadd0-gout gout-spec))
        (simpadd0-decl-spec-list fundef.spec gin))
       (gin (simpadd0-gin-update gin gout-spec))
       ((mv new-declor (simpadd0-gout gout-declor))
        (simpadd0-declor fundef.declor gin))
       (gin (simpadd0-gin-update gin gout-declor))
       (type (fundef-info->type fundef.info))
       (ident (declor->ident fundef.declor))
       (vartys-with-fun (if (and (ident-formalp ident)
                                 (type-formalp type)
                                 (not (type-case type :void))
                                 (not (type-case type :char)))
                            (b* (((mv & cvar) (ldm-ident ident))
                                 ((mv & ctype) (ldm-type type)))
                              (omap::update cvar ctype gout-declor.vartys))
                          gout-declor.vartys))
       ((mv new-decls (simpadd0-gout gout-decls))
        (simpadd0-decl-list fundef.decls (change-simpadd0-gin
                                          gin :vartys vartys-with-fun)))
       (gin (simpadd0-gin-update gin gout-decls))
       (vartys (vartys-from-valid-table
                (fundef-info->table-body-start fundef.info)))
       ((mv new-body (simpadd0-gout gout-body))
        (simpadd0-block-item-list fundef.body
                                  (change-simpadd0-gin gin :vartys vartys)))
       ((simpadd0-gin gin) (simpadd0-gin-update gin gout-body))
       (new-fundef (make-fundef :extension fundef.extension
                                :spec new-spec
                                :declor new-declor
                                :asm? fundef.asm?
                                :attribs fundef.attribs
                                :decls new-decls
                                :body new-body
                                :info fundef.info))
       (gout-no-thm (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                          :vartys vartys-with-fun))
       ((unless gout-body.thm-name) (mv new-fundef gout-no-thm))
       ((unless (fundef-formalp fundef)) (mv new-fundef gout-no-thm))
       ((declor declor) fundef.declor)
       ((when (consp declor.pointers)) (mv new-fundef gout-no-thm))
       ((mv okp params dirdeclor)
        (dirdeclor-case
         declor.direct
         :function-params (mv t declor.direct.params declor.direct.declor)
         :function-names (mv (endp declor.direct.names)
                             nil
                             declor.direct.declor)
         :otherwise (mv nil nil (irr-dirdeclor))))
       ((unless okp) (mv new-fundef gout-no-thm))
       ((unless (dirdeclor-case dirdeclor :ident))
        (raise "Internal error: ~x0 is not just the function name."
               dirdeclor)
        (mv new-fundef (irr-simpadd0-gout)))
       (fun (ident->unwrap (dirdeclor-ident->ident dirdeclor)))
       ((unless (stringp fun))
        (raise "Internal error: non-string identifier ~x0." fun)
        (mv new-fundef (irr-simpadd0-gout)))
       ((mv erp ldm-params) (ldm-param-declon-list params))
       ((when erp) (mv new-fundef gout-no-thm))
       (types (fundef-types fundef))
       ((mv okp args parargs arg-types arg-types-compst param-vartys)
        (simpadd0-gen-from-params ldm-params gin))
       ((unless okp) (mv new-fundef gout-no-thm))
       ((unless (equal param-vartys vartys)) (mv new-fundef gout-no-thm))
       ((mv init-scope-thm-event init-scope-thm-name thm-index)
        (simpadd0-gen-init-scope-thm ldm-params
                                     args
                                     parargs
                                     arg-types
                                     gin.const-new
                                     gin.thm-index))
       (events (cons init-scope-thm-event gout-body.events))
       ((mv param-thm-events param-thm-names thm-index)
        (simpadd0-gen-param-thms arg-types-compst
                                 arg-types
                                 ldm-params
                                 args
                                 init-scope-thm-name
                                 gin.const-new
                                 thm-index))
       (events (append (rev param-thm-events) events))
       ((mv thm-name thm-index) (gen-thm-name gin.const-new thm-index))
       (formula
        `(b* ((old ',(fundef-fix fundef))
              (new ',new-fundef)
              (fun (mv-nth 1 (ldm-ident (ident ,fun))))
              ((mv old-result old-compst)
               (c::exec-fun fun (list ,@args) compst old-fenv limit))
              ((mv new-result new-compst)
               (c::exec-fun fun (list ,@args) compst new-fenv limit)))
           (implies (and ,@arg-types
                         (equal (c::fun-env-lookup fun old-fenv)
                                (c::fun-info-from-fundef
                                 (mv-nth 1 (ldm-fundef old))))
                         (equal (c::fun-env-lookup fun new-fenv)
                                (c::fun-info-from-fundef
                                 (mv-nth 1 (ldm-fundef new))))
                         (not (c::errorp old-result)))
                    (and (not (c::errorp new-result))
                         (equal old-result new-result)
                         (equal old-compst new-compst)
                         (set::in (c::type-of-value-option old-result)
                                  (mv-nth 1 (ldm-type-set ',types)))))))
       (hints
        `(("Goal"
           :expand ((c::exec-fun
                     ',(c::ident fun) (list ,@args) compst old-fenv limit)
                    (c::exec-fun
                     ',(c::ident fun) (list ,@args) compst new-fenv limit))
           :use (,init-scope-thm-name
                 ,@(simpadd0-fundef-loop param-thm-names fun)
                 (:instance ,gout-body.thm-name
                            (compst
                             (c::push-frame
                              (c::frame (mv-nth 1 (ldm-ident
                                                   (ident ,fun)))
                                        (list
                                         (c::init-scope
                                          ',ldm-params
                                          (list ,@args))))
                              compst))
                            (limit (1- limit))))
           :in-theory '((:e c::fun-info->body$inline)
                        (:e c::fun-info->params$inline)
                        (:e c::fun-info->result$inline)
                        (:e c::fun-info-from-fundef)
                        (:e ident)
                        (:e ldm-block-item-list)
                        (:e ldm-fundef)
                        (:e ldm-ident)
                        (:e ldm-type)
                        (:e ldm-type-set)
                        (:e ldm-block-item-list)
                        (:e c::tyname-to-type)
                        (:e c::block-item-list-nocallsp)
                        (:e set::in)
                        c::errorp-of-error
                        c::compustate-frames-number-of-push-frame
                        (:t c::compustate-frames-number)))))
       (thm-event `(defrule ,thm-name
                     ,formula
                     :rule-classes nil
                     :hints ,hints)))
    (mv new-fundef
        (make-simpadd0-gout :events (cons thm-event events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys vartys-with-fun)))
  :hooks (:fix)

  :prepwork
  ((local (in-theory (disable (:e tau-system)))) ; for speed
   (define simpadd0-fundef-loop ((thms symbol-listp) (fun stringp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (endp thms)) nil)
          (thm (car thms))
          (lemma-instance
           `(:instance ,thm
                       (fun (mv-nth 1 (ldm-ident (ident ,fun))))
                       (compst0 compst)))
          (more-lemma-instances
           (simpadd0-fundef-loop (cdr thms) fun)))
       (cons lemma-instance more-lemma-instances))))

  ///

  (defret fundef-unambp-of-simpadd0-fundef
    (fundef-unambp new-fundef))

  (defret fundef-annop-of-simpadd0-fundef
    (fundef-annop new-fundef)
    :hyp (and (fundef-unambp fundef)
              (fundef-annop fundef)))

  (defret fundef-aidentp-of-simpadd0-fundef
    (fundef-aidentp new-fundef gcc)
    :hyp (and (fundef-unambp fundef)
              (fundef-aidentp fundef gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp) (gin simpadd0-ginp))
  :guard (and (extdecl-unambp extdecl)
              (extdecl-annop extdecl))
  :returns (mv (new-extdecl extdeclp)
               (gout simpadd0-goutp))
  :short "Transform an external declaration."
  (b* (((simpadd0-gin gin) gin))
    (extdecl-case
     extdecl
     :fundef (b* (((mv new-fundef (simpadd0-gout gout-fundef))
                   (simpadd0-fundef extdecl.unwrap gin))
                  (gin (simpadd0-gin-update gin gout-fundef)))
               (mv (extdecl-fundef new-fundef)
                   (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                         :vartys gout-fundef.vartys)))
     :decl (b* (((mv new-decl (simpadd0-gout gout-decl))
                 (simpadd0-decl extdecl.unwrap gin))
                (gin (simpadd0-gin-update gin gout-decl)))
             (mv (extdecl-decl new-decl)
                 (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                       :vartys gout-decl.vartys)))
     :empty (mv (extdecl-empty) (simpadd0-gout-no-thm gin))
     :asm (mv (extdecl-fix extdecl) (simpadd0-gout-no-thm gin))))
  :hooks (:fix)

  ///

  (defret extdecl-unambp-of-simpadd0-extdecl
    (extdecl-unambp new-extdecl))

  (defret extdecl-annop-of-simpadd0-extdecl
    (extdecl-annop new-extdecl)
    :hyp (and (extdecl-unambp extdecl)
              (extdecl-annop extdecl)))

  (defret extdecl-aidentp-of-simpadd0-extdecl
    (extdecl-aidentp new-extdecl gcc)
    :hyp (and (extdecl-unambp extdecl)
              (extdecl-aidentp extdecl gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp)
                               (gin simpadd0-ginp))
  :guard (and (extdecl-list-unambp extdecls)
              (extdecl-list-annop extdecls))
  :returns (mv (new-extdecls extdecl-listp)
               (gout simpadd0-goutp))
  :short "Transform a list of external declarations."
  (b* (((simpadd0-gin gin) gin)
       ((when (endp extdecls))
        (mv nil (simpadd0-gout-no-thm gin)))
       ((mv new-edecl (simpadd0-gout gout-edecl))
        (simpadd0-extdecl (car extdecls) gin))
       (gin (simpadd0-gin-update gin gout-edecl))
       ((mv new-edecls (simpadd0-gout gout-edecls))
        (simpadd0-extdecl-list (cdr extdecls)
                               (change-simpadd0-gin
                                gin :vartys gout-edecl.vartys)))
       (gin (simpadd0-gin-update gin gout-edecls)))
    (mv (cons new-edecl new-edecls)
        (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                              :vartys gout-edecls.vartys)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret extdecl-list-unambp-of-simpadd0-extdecl-list
    (extdecl-list-unambp new-extdecls)
    :hints (("Goal" :induct t)))

  (defret extdecl-list-annop-of-simpadd0-extdecl-list
    (extdecl-list-annop new-extdecls)
    :hyp (and (extdecl-list-unambp extdecls)
              (extdecl-list-annop extdecls))
    :hints (("Goal" :induct t)))

  (defret extdecl-list-aidentp-of-simpadd0-extdecl-list
    (extdecl-list-aidentp new-extdecls gcc)
    :hyp (and (extdecl-list-unambp extdecls)
              (extdecl-list-aidentp extdecls gcc))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp) (gin simpadd0-ginp))
  :guard (and (transunit-unambp tunit)
              (transunit-annop tunit))
  :returns (mv (new-tunit transunitp)
               (gout simpadd0-goutp))
  :short "Transform a translation unit."
  (b* (((simpadd0-gin gin) gin)
       ((transunit tunit) tunit)
       ((mv new-decls (simpadd0-gout gout-decls))
        (simpadd0-extdecl-list tunit.decls gin))
       (gin (simpadd0-gin-update gin gout-decls)))
    (mv  (make-transunit :decls new-decls
                         :info tunit.info)
         (simpadd0-gout-no-thm gin)))
  :hooks (:fix)

  ///

  (defret transunit-unambp-of-simpadd0-transunit
    (transunit-unambp new-tunit))

  (defret transunit-annop-of-simpadd0-transunit
    (transunit-annop new-tunit)
    :hyp (and (transunit-unambp tunit)
              (transunit-annop tunit)))

  (defret transunit-aidentp-of-simpadd0-transunit
    (transunit-aidentp new-tunit gcc)
    :hyp (and (transunit-unambp tunit)
              (transunit-aidentp tunit gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath-transunit-map ((map filepath-transunit-mapp)
                                         (gin simpadd0-ginp))
  :guard (and (filepath-transunit-map-unambp map)
              (filepath-transunit-map-annop map))
  :returns (mv (new-map filepath-transunit-mapp
                        :hyp (filepath-transunit-mapp map))
               (gout simpadd0-goutp))
  :short "Transform a map from file paths to translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform both the file paths and the translation units."))
  (b* (((simpadd0-gin gin) gin)
       ((when (omap::emptyp map))
        (mv nil (simpadd0-gout-no-thm gin)))
       ((mv path tunit) (omap::head map))
       ((mv new-tunit (simpadd0-gout gout-tunit))
        (simpadd0-transunit tunit gin))
       (gin (simpadd0-gin-update gin gout-tunit))
       ((mv new-map (simpadd0-gout gout-map))
        (simpadd0-filepath-transunit-map (omap::tail map) gin))
       (gin (simpadd0-gin-update gin gout-map)))
    (mv (omap::update path new-tunit new-map)
        (simpadd0-gout-no-thm gin)))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv simpadd0-filepath-transunit-map
    :args ((gin simpadd0-ginp)))

  (defret filepath-transunit-map-unambp-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-unambp new-map)
    :hyp (filepath-transunit-mapp map)
    :hints (("Goal" :induct t)))

  (defret filepath-transunit-map-annop-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-annop new-map)
    :hyp (and (filepath-transunit-mapp map)
              (filepath-transunit-map-unambp map)
              (filepath-transunit-map-annop map))
    :hints (("Goal" :induct t)))

  (defret filepath-transunit-map-aidentp-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-aidentp new-map gcc)
    :hyp (and (filepath-transunit-mapp map)
              (filepath-transunit-map-unambp map)
              (filepath-transunit-map-aidentp map gcc))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep)
                                     (gin simpadd0-ginp))
  :guard (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-annop tunits))
  :returns (mv (new-tunits transunit-ensemblep)
               (gout simpadd0-goutp))
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits)
       ((mv new-map (simpadd0-gout gout-map))
        (simpadd0-filepath-transunit-map tunits.unwrap gin))
       (gin (simpadd0-gin-update gin gout-map)))
    (mv (transunit-ensemble new-map)
        (simpadd0-gout-no-thm gin)))
  :hooks (:fix)

  ///

  (defret transunit-ensemble-unambp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-unambp new-tunits))

  (defret transunit-ensemble-annop-of-simpadd0-transunit-ensemble
    (transunit-ensemble-annop new-tunits)
    :hyp (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-annop tunits)))

  (defret transunit-ensemble-aidentp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-aidentp new-tunits gcc)
    :hyp (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-aidentp tunits gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-code-ensemble ((code code-ensemblep)
                                (gin simpadd0-ginp))
  :guard (and (code-ensemble-unambp code)
              (code-ensemble-annop code))
  :returns (mv (new-code code-ensemblep)
               (gout simpadd0-goutp))
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code)
       ((mv tunits-new (simpadd0-gout gout))
        (simpadd0-transunit-ensemble code.transunits gin)))
    (mv (change-code-ensemble code :transunits tunits-new) gout))
  :hooks (:fix)

  ///

  (defret code-ensemble-unambp-of-simpadd0-code-ensemble
    (code-ensemble-unambp new-code))

  (defret code-ensemble-annop-of-simpadd0-code-ensemble
    (code-ensemble-annop new-code)
    :hyp (and (code-ensemble-unambp code)
              (code-ensemble-annop code)))

  (defret code-ensemble-aidentp-of-simpadd0-code-ensemble
    (code-ensemble-aidentp new-code)
    :hyp (and (code-ensemble-unambp code)
              (code-ensemble-aidentp code))
    :hints (("Goal" :in-theory (enable code-ensemble-aidentp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-everything ((code-old code-ensemblep)
                                 (const-new symbolp))
  :guard (and (code-ensemble-unambp code-old)
              (code-ensemble-annop code-old))
  :returns (mv erp (event pseudo-event-formp))
  :short "Event expansion of the transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('vartys') component of @(tsee simpadd0-gin)
     is just initialized to @('nil') here;
     its actual initialization for theorem generation is done elsewhere."))
  (b* (((reterr) '(_))
       (gin (make-simpadd0-gin :ienv (code-ensemble->ienv code-old)
                               :const-new const-new
                               :vartys nil
                               :events nil
                               :thm-index 1))
       ((mv code-new (simpadd0-gout gout))
        (simpadd0-code-ensemble code-old gin))
       (const-event `(defconst ,const-new ',code-new)))
    (retok `(encapsulate () ,const-event ,@(rev gout.events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs-and-gen-everything (const-old
                                                    const-old-present
                                                    const-new
                                                    const-new-present
                                                    state)
  :returns (mv erp (event pseudo-event-formp))
  :parents (simpadd0-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code-old const-new)
        (simpadd0-process-inputs const-old
                                 const-old-present
                                 const-new
                                 const-new-present
                                 (w state))))
    (simpadd0-gen-everything code-old const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fn (const-old
                     const-old-present
                     const-new
                     const-new-present
                     (ctx ctxp)
                     state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (simpadd0-implementation)
  :short "Event expansion of @(tsee simpadd0)."
  (b* (((mv erp event)
        (simpadd0-process-inputs-and-gen-everything const-old
                                                    const-old-present
                                                    const-new
                                                    const-new-present
                                                    state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection simpadd0-macro-definition
  :parents (simpadd0-implementation)
  :short "Definition of the @(tsee simpadd0) macro."
  (defmacro simpadd0 (&key (const-old 'irrelevant const-old-present)
                           (const-new 'irrelevant const-new-present))
    `(make-event
      (simpadd0-fn ',const-old
                   ',const-old-present
                   ',const-new
                   ',const-new-present
                   'simpadd0
                   state))))
