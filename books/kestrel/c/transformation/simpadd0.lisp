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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled simpadd0-set-lemma
  (implies (equal (set::cardinality set) 1)
           (equal (set::in x set)
                  (equal x (set::head set))))
  :do-not-induct t
  :expand (set::in x set)
  :enable (set::cardinality
           set::in
           set::emptyp
           set::head
           set::tail
           set::setp))

(defruled simpadd0-type-of-value-not-void-lemma
  (not (equal (c::type-of-value val) '(:void)))
  :enable c::type-of-value)

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

(define simpadd0-process-inputs (const-old const-new (wrld plist-worldp))
  :returns (mv erp
               (code-old code-ensemblep)
               (const-new$ symbolp))
  :short "Process all the inputs."
  (b* (((reterr) (irr-code-ensemble) nil)
       ((unless (symbolp const-old))
        (reterr (msg "The first input must be a symbol, ~
                      but it is ~x0 instead."
                     const-old)))
       ((unless (symbolp const-new))
        (reterr (msg "The second input must be a symbol, ~
                      but it is ~x0 instead."
                     const-new)))
       ((unless (constant-symbolp const-old wrld))
        (reterr (msg "The first input, ~x0, must be a named constant, ~
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
  ((ienv c$::ienvp
         "The implementation environment from the code ensemble.")
   (const-new symbolp
              "The @(':const-new') input of the transformation.")
   (vartys ident-type-mapp
           "Variables in scope at the beginning of the construct.
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
   (vartys ident-type-map
           "Variables in scope at the end of the construct.
            The generated theorem (if any)
            includes conclusions about their presence in the computation state
            after the execution of the construct.
            Currently this could be actually a subset of the variables in scope,
            but it is adequate to the current proof generation,
            and we are working on extending this."))
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
               (vartys ident-type-mapp))
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
        `(b* ((var (mv-nth 1 (ldm-ident (ident ,par)))))
           (c::compustate-has-var-with-type-p var ',type compst)))
       ((mv okp
            more-args
            parargs
            more-arg-types
            more-arg-types-compst
            more-vartys)
        (simpadd0-gen-from-params (cdr params) gin))
       ((unless okp) (mv nil nil nil nil nil nil))
       (parargs `(omap::update (c::ident ,par) ,arg ,parargs))
       (vartys (omap::update (ident par) (ildm-type type) more-vartys)))
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
                               (:e ldm-ident)
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
                               (:t len)))))
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
       ((unless (and (type-formalp info.type)
                     (not (type-case info.type :void))
                     (not (type-case info.type :char))
                     (omap::assoc ident gin.vartys)))
        (mv expr (simpadd0-gout-no-thm gin)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-ident)
                              (:e ldm-expr)
                              (:e c::expr-ident))
                 :use (:instance simpadd0-expr-ident-support-lemma
                                 (var (mv-nth 1 (ldm-ident ',ident)))
                                 (type (mv-nth 1 (ldm-type ',info.type)))))))
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

  (defret expr-aidentp-of-simpadd0-expr-ident
    (c$::expr-aidentp expr gcc)
    :hyp (c$::ident-aidentp ident gcc))

  (defruled simpadd0-expr-ident-support-lemma
    (b* ((expr (c::expr-ident var))
         (result (c::exec-expr-pure expr compst))
         (value (c::expr-value->value result)))
      (implies (c::compustate-has-var-with-type-p var type compst)
               (equal (c::type-of-value value) type)))
    :enable (c::exec-expr-pure
             c::exec-ident
             c::compustate-has-var-with-type-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-const ((const constp) (gin simpadd0-ginp))
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
       ((iconst-info info) (coerce-iconst-info iconst.info))
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
                                     (:e ldm-expr)
                                     (:e ldm-type)
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
  :hooks (:fix)

  ///

  (defret expr-unambp-of-simpadd0-expr-const
    (expr-unambp expr))

  (defret expr-aidentp-of-simpadd0-expr-const
    (c$::expr-aidentp expr gcc)
    :hyp (c$::const-aidentp const gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-paren ((inner exprp)
                             (inner-new exprp)
                             (inner-thm-name symbolp)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp inner)
              (expr-unambp inner-new))
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
    :hyp (expr-unambp inner-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-unary ((op unopp)
                             (arg exprp)
                             (arg-new exprp)
                             (arg-thm-name symbolp)
                             (info expr-unary-infop)
                             (gin simpadd0-ginp))
  :guard (and (expr-unambp arg)
              (expr-unambp arg-new))
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
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e ldm-type)
                              (:e c::unop-nonpointerp)
                              (:e c::unop-kind)
                              (:e c::expr-unary)
                              (:e c::type-kind)
                              (:e c::promote-type)
                              (:e c::type-nonchar-integerp)
                              (:e c::type-sint)
                              (:e member-equal))
                 :use (,arg-thm-name
                       (:instance
                        simpadd0-expr-unary-support-lemma
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (old-arg (mv-nth 1 (ldm-expr ',arg)))
                        (new-arg (mv-nth 1 (ldm-expr ',arg-new))))
                       (:instance
                        simpadd0-expr-unary-error-support-lemma
                        (op ',(unop-case
                               op
                               :plus (c::unop-plus)
                               :minus (c::unop-minus)
                               :bitnot (c::unop-bitnot)
                               :lognot (c::unop-lognot)
                               :otherwise (impossible)))
                        (arg (mv-nth 1 (ldm-expr ',arg))))))))
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

  (defruledl c::lognot-value-lemma
    (implies (and (c::valuep val)
                  (member-equal (c::value-kind val)
                                '(:uchar :schar
                                  :ushort :sshort
                                  :uint :sint
                                  :ulong :slong
                                  :ullong :sllong)))
             (equal (c::value-kind (c::lognot-value val)) :sint))
    :enable (c::lognot-value
             c::lognot-scalar-value
             c::lognot-integer-value
             c::value-scalarp
             c::value-arithmeticp
             c::value-realp
             c::value-integerp
             c::value-signed-integerp
             c::value-unsigned-integerp))

  (defruled simpadd0-expr-unary-support-lemma
    (b* ((old (c::expr-unary op old-arg))
         (new (c::expr-unary op new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type (c::type-of-value old-arg-value)))
      (implies (and (c::unop-nonpointerp op)
                    (not (c::errorp old-result))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           (if (equal (c::unop-kind op) :lognot)
                               (c::type-sint)
                             (c::promote-type type))))))
    :expand ((c::exec-expr-pure (c::expr-unary op old-arg) compst)
             (c::exec-expr-pure (c::expr-unary op new-arg) compst))
    :disable ((:e c::type-sint))
    :enable (c::unop-nonpointerp
             c::exec-unary
             c::eval-unary
             c::apconvert-expr-value-when-not-array
             c::value-arithmeticp
             c::value-realp
             c::value-integerp
             c::value-signed-integerp
             c::value-unsigned-integerp
             c::lognot-value-lemma
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-unary-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg compst))
             (c::errorp (c::exec-expr-pure (c::expr-unary op arg) compst)))
    :expand (c::exec-expr-pure (c::expr-unary op arg) compst)))

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
              (tyname-unambp type-new)
              (expr-unambp arg)
              (expr-unambp arg-new))
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
        (mv (irr-expr) (irr-simpadd0-gout)))
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
        (mv (irr-expr) (irr-simpadd0-gout)))
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e ldm-tyname)
                              (:e ldm-type)
                              (:e c::expr-cast)
                              (:e c::tyname-to-type)
                              (:e c::type-nonchar-integerp))
                 :use (,arg-thm-name
                       (:instance
                        simpadd0-expr-cast-support-lemma
                        (tyname (mv-nth 1 (ldm-tyname ',type)))
                        (old-arg (mv-nth 1 (ldm-expr ',arg)))
                        (new-arg (mv-nth 1 (ldm-expr ',arg-new))))
                       (:instance
                        simpadd0-expr-cast-error-support-lemma
                        (tyname (mv-nth 1 (ldm-tyname ',type)))
                        (arg (mv-nth 1 (ldm-expr ',arg))))))))
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
              (expr-unambp arg-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-cast-support-lemma
    (b* ((old (c::expr-cast tyname old-arg))
         (new (c::expr-cast tyname new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type (c::type-of-value old-arg-value))
         (type1 (c::tyname-to-type tyname)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (c::type-nonchar-integerp type)
                    (c::type-nonchar-integerp type1))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           type1))))
    :expand ((c::exec-expr-pure (c::expr-cast tyname old-arg) compst)
             (c::exec-expr-pure (c::expr-cast tyname new-arg) compst))
    :enable (c::exec-cast
             c::eval-cast
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cast-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg compst))
             (c::errorp (c::exec-expr-pure (c::expr-cast tyname arg) compst)))
    :expand ((c::exec-expr-pure (c::expr-cast tyname arg) compst))))

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
              (expr-unambp arg1-new)
              (expr-unambp arg2)
              (expr-unambp arg2-new))
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
        (mv expr-new gout-no-thm)))
    (cond
     ((member-eq (binop-kind op)
                 '(:mul :div :rem :add :sub :shl :shr
                   :lt :gt :le :ge :eq :ne
                   :bitand :bitxor :bitior))
      (b* ((hints `(("Goal"
                     :in-theory '((:e ldm-expr)
                                  (:e ldm-type)
                                  (:e c::iconst-length-none)
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
                            simpadd0-expr-binary-pure-strict-support-lemma
                            (op ',(ldm-binop op))
                            (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                            (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                            (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                            (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                           (:instance
                            simpadd0-expr-binary-pure-strict-error-support-lemma
                            (op ',(ldm-binop op))
                            (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                            (arg2 (mv-nth 1 (ldm-expr ',arg2))))
                           ,@(and simpp
                                  `((:instance
                                     simpadd0-expr-binary-simp-support-lemma
                                     (expr (mv-nth 1 (ldm-expr
                                                      ',arg1-new))))))))))
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
               :in-theory '((:e ldm-expr)
                            (:e ldm-ident)
                            (:e ldm-type)
                            (:e c::expr-binary)
                            (:e c::binop-logand)
                            (:e c::binop-logor)
                            (:e c::type-sint)
                            (:e c::type-nonchar-integerp))
               :use
               (,arg1-thm-name
                ,arg2-thm-name
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-first-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-first-support-lemma))
                 (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                 (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                 (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-second-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-second-support-lemma))
                 (old-arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (old-arg2 (mv-nth 1 (ldm-expr ',arg2)))
                 (new-arg1 (mv-nth 1 (ldm-expr ',arg1-new)))
                 (new-arg2 (mv-nth 1 (ldm-expr ',arg2-new))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-first-error-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-first-error-support-lemma))
                 (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (arg2 (mv-nth 1 (ldm-expr ',arg2))))
                (:instance
                 ,(case (binop-kind op)
                    (:logand
                     'simpadd0-expr-binary-logand-second-error-support-lemma)
                    (:logor
                     'simpadd0-expr-binary-logor-second-error-support-lemma))
                 (arg1 (mv-nth 1 (ldm-expr ',arg1)))
                 (arg2 (mv-nth 1 (ldm-expr ',arg2))))))))
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
           (vartys-lemma-instances
            (simpadd0-expr-asg-lemma-instances gin.vartys
                                               (expr-ident->ident arg1)
                                               arg2))
           (hints
            `(("Goal"
               :in-theory
               '((:e ldm-expr)
                 (:e ldm-ident)
                 (:e ldm-type)
                 (:e c::expr-kind)
                 (:e c::expr-ident)
                 (:e c::expr-binary)
                 (:e c::binop-asg)
                 (:e c::ident)
                 (:e c::type-nonchar-integerp)
                 c::not-errorp-when-compustate-has-var-with-type-p
                 c::type-of-value-when-compustate-has-var-with-type-p
                 c::valuep-of-read-object-of-objdesign-of-var
                 c::not-errorp-when-valuep)
               :use (,arg1-thm-name
                     ,arg2-thm-name
                     (:instance
                      simpadd0-expr-binary-asg-support-lemma
                      (old-arg (mv-nth 1 (ldm-expr ',arg2)))
                      (new-arg (mv-nth 1 (ldm-expr ',arg2-new)))
                      (var (mv-nth 1 (ldm-ident
                                      ',(expr-ident->ident arg1)))))
                     (:instance
                      simpadd0-expr-binary-asg-error-support-lemma
                      (var (mv-nth 1 (ldm-ident
                                      ',(expr-ident->ident arg1))))
                      (expr (mv-nth 1 (ldm-expr ',arg2)))
                      (fenv old-fenv))
                     ,@vartys-lemma-instances))))
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

  :prepwork
  ((define simpadd0-expr-asg-lemma-instances ((vartys ident-type-mapp)
                                              (asg-var identp)
                                              (asg-expr exprp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-expr-binary-asg-vartys-support-lemma
                       (var (mv-nth 1 (ldm-ident ',asg-var)))
                       (expr (mv-nth 1 (ldm-expr ',asg-expr)))
                       (fenv old-fenv)
                       (var1 (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-expr-asg-lemma-instances (omap::tail vartys)
                                              asg-var
                                              asg-expr)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret expr-unamp-of-simpadd0-expr-binary
    (expr-unambp expr)
    :hyp (and (expr-unambp arg1-new)
              (expr-unambp arg2-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-binary-pure-strict-support-lemma
    (b* ((old (c::expr-binary op old-arg1 old-arg2))
         (new (c::expr-binary op new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (c::binop-purep op)
                    (c::binop-strictp op)
                    (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value)
                           (cond ((member-equal (c::binop-kind op)
                                                '(:mul :div :rem :add :sub
                                                  :bitand :bitxor :bitior))
                                  (c::uaconvert-types type1 type2))
                                 ((member-equal (c::binop-kind op)
                                                '(:shl :shr))
                                  (c::promote-type type1))
                                 (t (c::type-sint)))))))
    :expand ((c::exec-expr-pure (c::expr-binary op old-arg1 old-arg2) compst)
             (c::exec-expr-pure (c::expr-binary op new-arg1 new-arg2) compst))
    :disable ((:e c::type-sint))
    :enable (c::binop-purep
             c::binop-strictp
             c::exec-binary-strict-pure
             c::eval-binary-strict-pure
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-pure-strict-error-support-lemma
    (implies (and (c::binop-strictp op)
                  (or (c::errorp (c::exec-expr-pure arg1 compst))
                      (c::errorp (c::exec-expr-pure arg2 compst))))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary op arg1 arg2) compst)))
    :expand (c::exec-expr-pure (c::expr-binary op arg1 arg2) compst)
    :enable c::binop-strictp)

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

  (defruled simpadd0-expr-binary-simp-support-lemma
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
             c::type-of-value))

  (defruled simpadd0-expr-binary-logand-first-support-lemma
    (b* ((old (c::expr-binary (c::binop-logand) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logand) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (equal old-arg1-value new-arg1-value)
                    (c::type-nonchar-integerp type1)
                    (not (c::test-value old-arg1-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logand) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logand) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logand-second-support-lemma
    (b* ((old (c::expr-binary (c::binop-logand) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logand) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2)
                    (c::test-value old-arg1-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logand) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logand) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logand-first-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg1 compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logand) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logand) arg1 arg2) compst))

  (defruled simpadd0-expr-binary-logand-second-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure arg1 compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (c::test-value
                   (c::expr-value->value (c::exec-expr-pure arg1 compst)))
                  (c::errorp (c::exec-expr-pure arg2 compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logand) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logand) arg1 arg2) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-first-support-lemma
    (b* ((old (c::expr-binary (c::binop-logor) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logor) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (equal old-arg1-value new-arg1-value)
                    (c::type-nonchar-integerp type1)
                    (c::test-value old-arg1-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logor) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logor) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-second-support-lemma
    (b* ((old (c::expr-binary (c::binop-logor) old-arg1 old-arg2))
         (new (c::expr-binary (c::binop-logor) new-arg1 new-arg2))
         (old-arg1-result (c::exec-expr-pure old-arg1 compst))
         (old-arg2-result (c::exec-expr-pure old-arg2 compst))
         (new-arg1-result (c::exec-expr-pure new-arg1 compst))
         (new-arg2-result (c::exec-expr-pure new-arg2 compst))
         (old-arg1-value (c::expr-value->value old-arg1-result))
         (old-arg2-value (c::expr-value->value old-arg2-result))
         (new-arg1-value (c::expr-value->value new-arg1-result))
         (new-arg2-value (c::expr-value->value new-arg2-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type1 (c::type-of-value old-arg1-value))
         (type2 (c::type-of-value old-arg2-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-arg1-result))
                    (not (c::errorp new-arg2-result))
                    (equal old-arg1-value new-arg1-value)
                    (equal old-arg2-value new-arg2-value)
                    (c::type-nonchar-integerp type1)
                    (c::type-nonchar-integerp type2)
                    (not (c::test-value old-arg1-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) (c::type-sint)))))
    :expand ((c::exec-expr-pure (c::expr-binary '(:logor) old-arg1 old-arg2)
                                compst)
             (c::exec-expr-pure (c::expr-binary '(:logor) new-arg1 new-arg2)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-logor-first-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure arg1 compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logor) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logor) arg1 arg2) compst))

  (defruled simpadd0-expr-binary-logor-second-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure arg1 compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (not (c::test-value
                        (c::expr-value->value (c::exec-expr-pure arg1 compst))))
                  (c::errorp (c::exec-expr-pure arg2 compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-binary (c::binop-logor) arg1 arg2)
                                 compst)))
    :expand (c::exec-expr-pure (c::expr-binary '(:logor) arg1 arg2) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-binary-asg-support-lemma
    (b* ((old (c::expr-binary (c::binop-asg) (c::expr-ident var) old-arg))
         (new (c::expr-binary (c::binop-asg) (c::expr-ident var) new-arg))
         (old-arg-result (c::exec-expr-pure old-arg compst))
         (new-arg-result (c::exec-expr-pure new-arg compst))
         (old-arg-value (c::expr-value->value old-arg-result))
         (new-arg-value (c::expr-value->value new-arg-result))
         (old-compst (c::exec-expr-asg old compst old-fenv limit))
         (new-compst (c::exec-expr-asg new compst new-fenv limit))
         (val (c::read-object (c::objdesign-of-var var compst) compst))
         (type (c::type-of-value val)))
      (implies (and (not (equal (c::expr-kind old-arg) :call))
                    (not (equal (c::expr-kind new-arg) :call))
                    (not (c::errorp val))
                    (c::type-nonchar-integerp type)
                    (not (c::errorp old-compst))
                    (not (c::errorp new-arg-result))
                    (equal old-arg-value new-arg-value)
                    (equal (c::type-of-value old-arg-value) type))
               (and (not (c::errorp new-compst))
                    (equal old-compst new-compst))))
    :expand ((c::exec-expr-asg
              (c::expr-binary '(:asg) (c::expr-ident var) old-arg)
              compst old-fenv limit)
             (c::exec-expr-asg
              (c::expr-binary '(:asg) (c::expr-ident var) new-arg)
              compst new-fenv limit))
    :enable (c::exec-expr-call-or-pure
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)
    :use (:instance
          lemma
          (val1 (c::read-object (c::objdesign-of-var var compst) compst))
          (val2 (c::expr-value->value (c::exec-expr-pure old-arg compst))))
    :prep-lemmas
    ((defruled lemma
       (implies (equal (c::type-of-value val1)
                       (c::type-of-value val2))
                (equal (c::value-integerp val1)
                       (c::value-integerp val2)))
       :enable (c::type-of-value
                c::value-integerp
                c::value-unsigned-integerp
                c::value-signed-integerp))))

  (defruled simpadd0-expr-binary-asg-error-support-lemma
    (implies (and (not (equal (c::expr-kind expr) :call))
                  (or (c::errorp (c::exec-expr-pure (c::expr-ident var) compst))
                      (c::errorp (c::exec-expr-pure expr compst))))
             (c::errorp
              (c::exec-expr-asg (c::expr-binary (c::binop-asg)
                                                (c::expr-ident var)
                                                expr)
                                compst fenv limit)))
    :expand (c::exec-expr-asg (c::expr-binary '(:asg) (c::expr-ident var) expr)
                              compst fenv limit)
    :enable c::exec-expr-call-or-pure)

  (defruled simpadd0-expr-binary-asg-vartys-support-lemma
    (implies (not (equal (c::expr-kind expr) :call))
             (b* ((asg (c::expr-binary (c::binop-asg) (c::expr-ident var) expr))
                  (compst1 (c::exec-expr-asg asg compst fenv limit)))
               (implies (and (not (c::errorp compst1))
                             (equal (c::type-of-value
                                     (c::read-object
                                      (c::objdesign-of-var var compst)
                                      compst))
                                    (c::type-of-value
                                     (c::expr-value->value
                                      (c::exec-expr-pure expr compst))))
                             (c::type-nonchar-integerp
                              (c::type-of-value
                               (c::expr-value->value
                                (c::exec-expr-pure expr compst))))
                             (c::compustate-has-var-with-type-p var1 type compst))
                        (c::compustate-has-var-with-type-p var1 type compst1))))
    :expand (c::exec-expr-asg (c::expr-binary '(:asg) (c::expr-ident var) expr)
                              compst fenv limit)
    :enable (c::compustate-has-var-with-type-p
             c::exec-expr-call-or-pure
             c::exec-expr-pure
             c::exec-ident
             c::objdesign-of-var-of-write-object
             c::read-object-of-write-object-when-auto-or-static
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)))

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
              (expr-unambp test-new)
              (expr-option-unambp then)
              (expr-option-unambp then-new)
              (expr-unambp else)
              (expr-unambp else-new))
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
       (hints `(("Goal"
                 :in-theory '((:e ldm-expr)
                              (:e ldm-ident)
                              (:e ldm-type)
                              (:e c::expr-cond)
                              (:e c::type-nonchar-integerp))
                 :use (,test-thm-name
                       ,then-thm-name
                       ,else-thm-name
                       (:instance
                        simpadd0-expr-cond-true-support-lemma
                        (old-test (mv-nth 1 (ldm-expr ',test)))
                        (old-then (mv-nth 1 (ldm-expr ',then)))
                        (old-else (mv-nth 1 (ldm-expr ',else)))
                        (new-test (mv-nth 1 (ldm-expr ',test-new)))
                        (new-then (mv-nth 1 (ldm-expr ',then-new)))
                        (new-else (mv-nth 1 (ldm-expr ',else-new))))
                       (:instance
                        simpadd0-expr-cond-false-support-lemma
                        (old-test (mv-nth 1 (ldm-expr ',test)))
                        (old-then (mv-nth 1 (ldm-expr ',then)))
                        (old-else (mv-nth 1 (ldm-expr ',else)))
                        (new-test (mv-nth 1 (ldm-expr ',test-new)))
                        (new-then (mv-nth 1 (ldm-expr ',then-new)))
                        (new-else (mv-nth 1 (ldm-expr ',else-new))))
                       (:instance
                        simpadd0-expr-cond-test-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))
                       (:instance
                        simpadd0-expr-cond-then-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))
                       (:instance
                        simpadd0-expr-cond-else-error-support-lemma
                        (test (mv-nth 1 (ldm-expr ',test)))
                        (then (mv-nth 1 (ldm-expr ',then)))
                        (else (mv-nth 1 (ldm-expr ',else))))))))
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
              (expr-unambp else-new))
    :hints (("Goal" :in-theory (enable irr-expr))))

  (defruled simpadd0-expr-cond-true-support-lemma
    (b* ((old (c::expr-cond old-test old-then old-else))
         (new (c::expr-cond new-test new-then new-else))
         (old-test-result (c::exec-expr-pure old-test compst))
         (old-then-result (c::exec-expr-pure old-then compst))
         (new-test-result (c::exec-expr-pure new-test compst))
         (new-then-result (c::exec-expr-pure new-then compst))
         (old-test-value (c::expr-value->value old-test-result))
         (old-then-value (c::expr-value->value old-then-result))
         (new-test-value (c::expr-value->value new-test-result))
         (new-then-value (c::expr-value->value new-then-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type-test (c::type-of-value old-test-value))
         (type-then (c::type-of-value old-then-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-test-result))
                    (not (c::errorp new-then-result))
                    (equal old-test-value new-test-value)
                    (equal old-then-value new-then-value)
                    (c::type-nonchar-integerp type-test)
                    (c::type-nonchar-integerp type-then)
                    (c::test-value old-test-value))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) type-then))))
    :expand ((c::exec-expr-pure (c::expr-cond old-test old-then old-else)
                                compst)
             (c::exec-expr-pure (c::expr-cond new-test new-then new-else)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-false-support-lemma
    (b* ((old (c::expr-cond old-test old-then old-else))
         (new (c::expr-cond new-test new-then new-else))
         (old-test-result (c::exec-expr-pure old-test compst))
         (old-else-result (c::exec-expr-pure old-else compst))
         (new-test-result (c::exec-expr-pure new-test compst))
         (new-else-result (c::exec-expr-pure new-else compst))
         (old-test-value (c::expr-value->value old-test-result))
         (old-else-value (c::expr-value->value old-else-result))
         (new-test-value (c::expr-value->value new-test-result))
         (new-else-value (c::expr-value->value new-else-result))
         (old-result (c::exec-expr-pure old compst))
         (new-result (c::exec-expr-pure new compst))
         (old-value (c::expr-value->value old-result))
         (new-value (c::expr-value->value new-result))
         (type-test (c::type-of-value old-test-value))
         (type-else (c::type-of-value old-else-value)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-test-result))
                    (not (c::errorp new-else-result))
                    (equal old-test-value new-test-value)
                    (equal old-else-value new-else-value)
                    (c::type-nonchar-integerp type-test)
                    (c::type-nonchar-integerp type-else)
                    (not (c::test-value old-test-value)))
               (and (not (c::errorp new-result))
                    (equal old-value new-value)
                    (equal (c::type-of-value old-value) type-else))))
    :expand ((c::exec-expr-pure (c::expr-cond old-test old-then old-else)
                                compst)
             (c::exec-expr-pure (c::expr-cond new-test new-then new-else)
                                compst))
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-test-error-support-lemma
    (implies (c::errorp (c::exec-expr-pure test compst))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst))

  (defruled simpadd0-expr-cond-then-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure test compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure test compst))))
                  (c::test-value
                   (c::expr-value->value (c::exec-expr-pure test compst)))
                  (c::errorp (c::exec-expr-pure then compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  (defruled simpadd0-expr-cond-else-error-support-lemma
    (implies (and (not (c::errorp (c::exec-expr-pure test compst)))
                  (c::type-nonchar-integerp
                   (c::type-of-value
                    (c::expr-value->value (c::exec-expr-pure test compst))))
                  (not (c::test-value
                        (c::expr-value->value (c::exec-expr-pure test compst))))
                  (c::errorp (c::exec-expr-pure else compst)))
             (c::errorp
              (c::exec-expr-pure (c::expr-cond test then else) compst)))
    :expand (c::exec-expr-pure (c::expr-cond test then else) compst)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-initer-single ((expr exprp)
                                (expr-new exprp)
                                (expr-thm-name symbolp)
                                (gin simpadd0-ginp))
  :guard (and (expr-unambp expr)
              (expr-unambp expr-new))
  :returns (mv (initer initerp) (gout simpadd0-goutp))
  :short "Transform an initializer consisting of a single expression."
  (b* (((simpadd0-gin gin) gin)
       (initer (initer-single expr))
       (initer-new (initer-single expr-new))
       ((unless (and expr-thm-name
                     (expr-purep expr)))
        (mv initer-new (simpadd0-gout-no-thm gin)))
       (lemma-instances
        (simpadd0-initer-single-pure-lemma-instances gin.vartys expr))
       (hints
        `(("Goal"
           :in-theory '((:e ldm-initer)
                        (:e ldm-expr)
                        (:e ldm-ident)
                        (:e ldm-type)
                        (:e c::expr-kind)
                        (:e c::initer-single)
                        (:e c::type-nonchar-integerp))
           :use ((:instance ,expr-thm-name)
                 (:instance simpadd0-initer-single-pure-support-lemma
                            (old-expr (mv-nth 1 (ldm-expr ',expr)))
                            (new-expr (mv-nth 1 (ldm-expr ',expr-new))))
                 (:instance simpadd0-initer-single-pure-error-support-lemma
                            (expr (mv-nth 1 (ldm-expr ',expr)))
                            (fenv old-fenv))
                 ,@lemma-instances))))
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

  :prepwork
  ((define simpadd0-initer-single-pure-lemma-instances ((vartys ident-type-mapp)
                                                        (expr exprp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-initer-single-pure-vartys-support-lemma
                       (expr (mv-nth 1 (ldm-expr ',expr)))
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-initer-single-pure-lemma-instances (omap::tail vartys)
                                                        expr)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret initer-unambp-of-simpadd0-initer-single
    (initer-unambp initer)
    :hyp (expr-unambp expr-new))

  (defruled simpadd0-initer-single-pure-support-lemma
    (b* ((old (c::initer-single old-expr))
         (new (c::initer-single new-expr))
         (old-expr-result (c::exec-expr-pure old-expr compst))
         (new-expr-result (c::exec-expr-pure new-expr compst))
         (old-expr-value (c::expr-value->value old-expr-result))
         (new-expr-value (c::expr-value->value new-expr-result))
         ((mv old-result old-compst)
          (c::exec-initer old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-initer new compst new-fenv limit))
         (type (c::type-of-value old-expr-value)))
      (implies (and (not (equal (c::expr-kind old-expr) :call))
                    (not (equal (c::expr-kind new-expr) :call))
                    (not (c::errorp old-result))
                    (not (c::errorp new-expr-result))
                    (equal old-expr-value new-expr-value)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::init-type-of-init-value old-result)
                           (c::init-type-single type)))))
    :expand ((c::exec-initer (c::initer-single old-expr) compst old-fenv limit)
             (c::exec-initer (c::initer-single new-expr) compst new-fenv limit))
    :enable (c::exec-expr-call-or-pure
             c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp
             c::init-type-of-init-value))

  (defruled simpadd0-initer-single-pure-error-support-lemma
    (implies (and (not (equal (c::expr-kind expr) :call))
                  (c::errorp (c::exec-expr-pure expr compst)))
             (c::errorp
              (mv-nth 0 (c::exec-initer
                         (c::initer-single expr) compst fenv limit))))
    :expand (c::exec-initer (c::initer-single expr) compst fenv limit)
    :enable c::exec-expr-call-or-pure)

  (defruled simpadd0-initer-single-pure-vartys-support-lemma
    (implies (not (equal (c::expr-kind expr) :call))
             (b* ((initer (c::initer-single expr))
                  ((mv result compst1)
                   (c::exec-initer initer compst fenv limit)))
               (implies (and (not (c::errorp result))
                             (c::type-nonchar-integerp
                              (c::type-of-value
                               (c::expr-value->value
                                (c::exec-expr-pure expr compst))))
                             (c::compustate-has-var-with-type-p var type compst))
                        (c::compustate-has-var-with-type-p var type compst1))))
    :expand (c::exec-initer (c::initer-single expr) compst fenv limit)
    :enable (c::exec-expr-call-or-pure
             c::compustate-has-var-with-type-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-expr ((expr? expr-optionp)
                            (expr?-new expr-optionp)
                            (expr?-thm-name symbolp)
                            info
                            (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-unambp expr?-new)
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
        (mv (irr-stmt) (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    (and expr?-thm-name
                         (not (expr-purep expr?)))))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (hints
        (if expr?
            `(("Goal"
               :in-theory '((:e ldm-stmt)
                            (:e ldm-expr)
                            (:e ldm-ident)
                            (:e ldm-type-option-set)
                            (:e c::expr-kind)
                            (:e c::stmt-expr)
                            (:e set::insert))
               :use ((:instance
                      ,expr?-thm-name
                      (limit (- limit 2)))
                     (:instance
                      simpadd0-stmt-expr-asg-support-lemma
                      (old-expr (mv-nth 1 (ldm-expr ',expr?)))
                      (new-expr (mv-nth 1 (ldm-expr ',expr?-new))))
                     (:instance
                      simpadd0-stmt-expr-asg-error-support-lemma
                      (expr (mv-nth 1 (ldm-expr ',expr?)))
                      (fenv old-fenv))
                     ,@(simpadd0-stmt-expr-asg-lemma-instances gin.vartys
                                                               expr?))))
          `(("Goal"
             :in-theory '((:e ldm-stmt)
                          (:e ldm-ident)
                          (:e ldm-type)
                          (:e c::stmt-null)
                          (:e ldm-type-option-set)
                          c::type-option-of-stmt-value
                          (:e set::in)
                          (:e set::insert))
             :use (simpadd0-stmt-null-support-lemma
                   ,@(simpadd0-stmt-null-lemma-instances gin.vartys))))))
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

  :prepwork

  ((define simpadd0-stmt-null-lemma-instances ((vartys ident-type-mapp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-stmt-null-vartys-support-lemma
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-stmt-null-lemma-instances (omap::tail vartys))))
       (cons lemma-instance lemma-instances)))

   (define simpadd0-stmt-expr-asg-lemma-instances ((vartys ident-type-mapp)
                                                   (expr exprp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-stmt-expr-asg-vartys-support-lemma
                       (expr (mv-nth 1 (ldm-expr ',expr)))
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-stmt-expr-asg-lemma-instances (omap::tail vartys) expr)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-expr
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new)
    :hints (("Goal" :in-theory (enable irr-stmt))))

  (defruled simpadd0-stmt-null-support-lemma
    (b* ((old (c::stmt-null))
         (new (c::stmt-null))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (set::in (c::type-option-of-stmt-value old-result)
                             (set::insert nil nil)))))
    :enable c::exec-stmt)

  (defruled simpadd0-stmt-null-vartys-support-lemma
    (b* ((stmt (c::stmt-null))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::exec-stmt
             c::compustate-has-var-with-type-p))

  (defruled simpadd0-stmt-expr-asg-support-lemma
    (b* ((old (c::stmt-expr old-expr))
         (new (c::stmt-expr new-expr))
         (old-expr-compst (c::exec-expr-asg
                           old-expr compst old-fenv (- limit 2)))
         (new-expr-compst (c::exec-expr-asg
                           new-expr compst new-fenv (- limit 2)))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (and (not (equal (c::expr-kind old-expr) :call))
                    (not (equal (c::expr-kind new-expr) :call))
                    (not (c::errorp old-result))
                    (not (c::errorp new-expr-compst))
                    (equal old-expr-compst new-expr-compst))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (set::in (c::type-option-of-stmt-value old-result)
                             (set::insert nil nil)))))
    :expand ((c::exec-stmt (c::stmt-expr old-expr) compst old-fenv limit)
             (c::exec-stmt (c::stmt-expr new-expr) compst new-fenv limit))
    :enable (c::exec-expr-call-or-asg))

  (defruled simpadd0-stmt-expr-asg-error-support-lemma
    (implies (and (not (equal (c::expr-kind expr) :call))
                  (c::errorp (c::exec-expr-asg expr compst fenv (- limit 2))))
             (c::errorp
              (mv-nth 0 (c::exec-stmt (c::stmt-expr expr) compst fenv limit))))
    :expand (c::exec-stmt (c::stmt-expr expr) compst fenv limit)
    :enable c::exec-expr-call-or-asg)

  (defruled simpadd0-stmt-expr-asg-vartys-support-lemma
    (b* ((stmt (c::stmt-expr expr))
         (expr-compst1 (c::exec-expr-asg expr compst fenv (- limit 2)))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (not (equal (c::expr-kind expr) :call))
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type expr-compst1))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-stmt (c::stmt-expr expr) compst fenv limit)
    :enable c::exec-expr-call-or-asg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-stmt-return ((expr? expr-optionp)
                              (expr?-new expr-optionp)
                              (expr?-thm-name symbolp)
                              info
                              (gin simpadd0-ginp))
  :guard (and (expr-option-unambp expr?)
              (expr-option-unambp expr?-new)
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
        (mv (irr-stmt) (irr-simpadd0-gout)))
       ((unless (or (not expr?)
                    (and expr?-thm-name
                         (expr-purep expr?))))
        (mv stmt-new (simpadd0-gout-no-thm gin)))
       (lemma-instances (simpadd0-stmt-return-lemma-instances gin.vartys
                                                              expr?))
       (hints (if expr?
                  `(("Goal"
                     :in-theory '((:e ldm-stmt)
                                  (:e ldm-expr-option)
                                  (:e ldm-expr)
                                  (:e ldm-ident)
                                  (:e ldm-type)
                                  (:e ldm-type-option-set)
                                  (:e set::insert)
                                  (:e c::stmt-return)
                                  (:e c::expr-kind)
                                  (:e c::type-nonchar-integerp))
                     :use (,expr?-thm-name
                           (:instance
                            simpadd0-stmt-return-value-support-lemma
                            (old-expr (mv-nth 1 (ldm-expr ',expr?)))
                            (new-expr (mv-nth 1 (ldm-expr ',expr?-new))))
                           (:instance
                            simpadd0-stmt-return-error-support-lemma
                            (expr (mv-nth 1 (ldm-expr ',expr?)))
                            (fenv old-fenv))
                           ,@lemma-instances)))
                `(("Goal"
                   :in-theory '((:e ldm-stmt)
                                (:e ldm-expr-option)
                                (:e ldm-type-option-set)
                                (:e c::stmt-return)
                                (:e c::type-void)
                                (:e set::insert))
                   :use (simpadd0-stmt-return-novalue-support-lemma
                         ,@lemma-instances)))))
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

  :prepwork
  ((define simpadd0-stmt-return-lemma-instances ((vartys ident-type-mapp)
                                                 (expr? expr-optionp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-stmt-return-vartys-support-lemma
                       (expr? (mv-nth 1 (ldm-expr-option ',expr?)))
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-stmt-return-lemma-instances (omap::tail vartys) expr?)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret stmt-unambp-of-simpadd0-stmt-return
    (stmt-unambp stmt)
    :hyp (expr-option-unambp expr?-new)
    :hints (("Goal" :in-theory (enable irr-stmt))))

  (defruled simpadd0-stmt-return-value-support-lemma
    (b* ((old (c::stmt-return old-expr))
         (new (c::stmt-return new-expr))
         (old-expr-result (c::exec-expr-pure old-expr compst))
         (new-expr-result (c::exec-expr-pure new-expr compst))
         (old-expr-value (c::expr-value->value old-expr-result))
         (new-expr-value (c::expr-value->value new-expr-result))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit))
         (type (c::type-of-value old-expr-value)))
      (implies (and old-expr
                    new-expr
                    (not (equal (c::expr-kind old-expr) :call))
                    (not (equal (c::expr-kind new-expr) :call))
                    (not (c::errorp old-result))
                    (not (c::errorp new-expr-result))
                    (equal old-expr-value new-expr-value)
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (c::stmt-value-return->value? old-result)
                    (set::in (c::type-option-of-stmt-value old-result)
                             (set::insert type nil)))))
    :expand ((c::exec-stmt (c::stmt-return old-expr) compst old-fenv limit)
             (c::exec-stmt (c::stmt-return new-expr) compst new-fenv limit))
    :enable (c::exec-expr-call-or-pure
             c::type-of-value
             c::apconvert-expr-value-when-not-array
             c::type-nonchar-integerp
             c::type-option-of-stmt-value
             c::type-of-value-option
             c::value-option-some->val))

  (defruled simpadd0-stmt-return-novalue-support-lemma
    (b* ((old (c::stmt-return nil))
         (new (c::stmt-return nil))
         ((mv old-result old-compst) (c::exec-stmt old compst old-fenv limit))
         ((mv new-result new-compst) (c::exec-stmt new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (set::in (c::type-option-of-stmt-value old-result)
                             (set::insert (c::type-void) nil)))))
    :enable c::exec-stmt)

  (defruled simpadd0-stmt-return-error-support-lemma
    (implies (and expr
                  (not (equal (c::expr-kind expr) :call))
                  (c::errorp (c::exec-expr-pure expr compst)))
             (c::errorp
              (mv-nth 0 (c::exec-stmt (c::stmt-return expr)
                                      compst
                                      fenv
                                      limit))))
    :expand (c::exec-stmt (c::stmt-return expr) compst fenv limit)
    :enable c::exec-expr-call-or-pure)

  (defruled simpadd0-stmt-return-vartys-support-lemma
    (implies (or (not expr?)
                 (not (equal (c::expr-kind expr?) :call)))
             (b* ((stmt (c::stmt-return expr?))
                  ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
               (implies (and (not (c::errorp result))
                             (c::compustate-has-var-with-type-p var type compst))
                        (c::compustate-has-var-with-type-p var type compst1))))
    :expand ((c::exec-stmt (c::stmt-return expr?) compst fenv limit)
             (c::exec-stmt '(:return nil) compst fenv limit))
    :enable (c::compustate-has-var-with-type-p
             c::exec-expr-call-or-pure)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-decl-decl ((extension booleanp)
                            (specs decl-spec-listp)
                            (specs-new decl-spec-listp)
                            (specs-thm-name symbolp)
                            (init initdeclor-listp)
                            (init-new initdeclor-listp)
                            (init-thm-name symbolp)
                            (vartys-post ident-type-mapp)
                            (gin simpadd0-ginp))
  :guard (and (decl-spec-list-unambp specs)
              (decl-spec-list-unambp specs-new)
              (initdeclor-list-unambp init)
              (initdeclor-list-unambp init-new))
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
        (mv (irr-decl) (irr-simpadd0-gout)))
       ((unless (and init-thm-name
                     (decl-block-formalp decl)))
        (mv decl-new gout-no-thm))
       ((unless (decl-block-formalp decl-new))
        (raise "Internal error: ~
                new declaration ~x0 is not in the formalized subset ~
                while old declaration ~x1 is."
               decl-new decl)
        (mv (irr-decl) (irr-simpadd0-gout)))
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
        (mv (irr-decl) (irr-simpadd0-gout)))
       (initer-new (initdeclor->init? initdeclor-new))
       ((unless (equal specs specs-new))
        (raise "Internal error: ~
                new declaration specifiers ~x0 differ from ~
                old declaration specifiers ~x1."
               specs-new specs)
        (mv (irr-decl) (irr-simpadd0-gout)))
       ((mv & tyspecs) (check-decl-spec-list-all-typespec specs))
       ((mv & tyspecseq) (ldm-type-spec-list tyspecs))
       (ctype (c::tyspecseq-to-type tyspecseq))
       ((unless (c::type-nonchar-integerp ctype))
        (mv decl-new gout-no-thm))
       (type (ildm-type ctype))
       (vartys-post (omap::update var type gin.vartys))
       (lemma-instances (simpadd0-decl-decl-lemma-instances
                         gin.vartys var tyspecs initer))
       (hints `(("Goal"
                 :in-theory '((:e ldm-decl-obj)
                              (:e ldm-initer)
                              (:e ldm-type-spec-list)
                              (:e ldm-ident)
                              (:e ldm-type)
                              (:e c::obj-declor-ident)
                              (:e c::scspecseq-none)
                              (:e c::obj-declon)
                              (:e c::tyspecseq-to-type)
                              (:e c::identp))
                 :use ((:instance ,init-thm-name (limit (1- limit)))
                       (:instance
                        simpadd0-decl-decl-support-lemma
                        (var (mv-nth 1 (ldm-ident ',var)))
                        (tyspec (mv-nth 1 (ldm-type-spec-list ',tyspecs)))
                        (old-initer (mv-nth 1 (ldm-initer ',initer)))
                        (new-initer (mv-nth 1 (ldm-initer ',initer-new))))
                       (:instance
                        simpadd0-decl-decl-error-support-lemma
                        (var (mv-nth 1 (ldm-ident ',var)))
                        (tyspec (mv-nth 1 (ldm-type-spec-list ',tyspecs)))
                        (initer (mv-nth 1 (ldm-initer ',initer)))
                        (fenv old-fenv))
                       ,@lemma-instances
                       (:instance
                        simpadd0-decl-decl-vartys-new-support-lemma
                        (var (mv-nth 1 (ldm-ident ',var)))
                        (tyspec (mv-nth 1 (ldm-type-spec-list ',tyspecs)))
                        (initer (mv-nth 1 (ldm-initer ',initer)))
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

  :prepwork
  ((define simpadd0-decl-decl-lemma-instances ((vartys ident-type-mapp)
                                               (var identp)
                                               (tyspecs type-spec-listp)
                                               (initer initerp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var1 type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-decl-decl-vartys-old-support-lemma
                       (var1 (mv-nth 1 (ldm-ident ',var1)))
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))
                       (tyspec (mv-nth 1 (ldm-type-spec-list ',tyspecs)))
                       (initer (mv-nth 1 (ldm-initer ',initer)))
                       (fenv old-fenv)))
          (lemma-instances
           (simpadd0-decl-decl-lemma-instances
            (omap::tail vartys) var tyspecs initer)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret decl-unambp-of-simpadd0-decl-decl
    (decl-unambp decl)
    :hyp (and (decl-spec-list-unambp specs-new)
              (initdeclor-list-unambp init-new))
    :hints (("Goal" :in-theory (enable irr-decl))))

  (defruled simpadd0-decl-decl-support-lemma
    (b* ((declor (c::obj-declor-ident var))
         (old (c::obj-declon (c::scspecseq-none) tyspec declor old-initer))
         (new (c::obj-declon (c::scspecseq-none) tyspec declor new-initer))
         ((mv old-init-value old-init-compst)
          (c::exec-initer old-initer compst old-fenv (1- limit)))
         ((mv new-init-value new-init-compst)
          (c::exec-initer new-initer compst new-fenv (1- limit)))
         (old-compst (c::exec-obj-declon old compst old-fenv limit))
         (new-compst (c::exec-obj-declon new compst new-fenv limit)))
      (implies (and old-initer
                    new-initer
                    (not (c::errorp old-compst))
                    (not (c::errorp new-init-value))
                    (equal old-init-value new-init-value)
                    (equal old-init-compst new-init-compst))
               (and (not (c::errorp new-compst))
                    (equal old-compst new-compst))))
    :expand ((c::exec-obj-declon
              (c::obj-declon
               '(:none) tyspec (c::obj-declor-ident var) old-initer)
              compst old-fenv limit)
             (c::exec-obj-declon
              (c::obj-declon
               '(:none) tyspec (c::obj-declor-ident var) new-initer)
              compst new-fenv limit))
    :enable (c::obj-declon-to-ident+scspec+tyname+init))

  (defruled simpadd0-decl-decl-error-support-lemma
    (b* ((declor (c::obj-declor-ident var))
         (declon (c::obj-declon (c::scspecseq-none) tyspec declor initer)))
      (implies (and initer
                    (c::errorp
                     (mv-nth 0 (c::exec-initer
                                initer compst fenv (1- limit)))))
               (c::errorp (c::exec-obj-declon declon compst fenv limit))))
    :expand (c::exec-obj-declon
             (c::obj-declon
              '(:none) tyspec (c::obj-declor-ident var) initer)
             compst fenv limit)
    :enable c::obj-declon-to-ident+scspec+tyname+init)

  (defruled simpadd0-decl-decl-vartys-old-support-lemma
    (b* ((declor (c::obj-declor-ident var))
         (declon (c::obj-declon (c::scspecseq-none) tyspec declor initer))
         ((mv & compst0) (c::exec-initer initer compst fenv (1- limit)))
         (compst1 (c::exec-obj-declon declon compst fenv limit)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var)
                    (c::identp var1)
                    (not (equal var var1))
                    (c::compustate-has-var-with-type-p var1 type compst0))
               (c::compustate-has-var-with-type-p var1 type compst1)))
    :expand (c::exec-obj-declon
             (c::obj-declon
              '(:none) tyspec (c::obj-declor-ident var) initer)
             compst fenv limit)
    :enable (c::obj-declon-to-ident+scspec+tyname+init
             c::tyspec+declor-to-ident+tyname
             c::obj-declor-to-ident+adeclor
             c::compustate-has-var-with-type-p-of-create-other-var))

  (defruled simpadd0-decl-decl-vartys-new-support-lemma
    (b* ((declor (c::obj-declor-ident var))
         (declon (c::obj-declon (c::scspecseq-none) tyspec declor initer))
         (compst1 (c::exec-obj-declon declon compst fenv limit))
         (type (c::tyspecseq-to-type tyspec)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-obj-declon
             (c::obj-declon
              '(:none) tyspec (c::obj-declor-ident var) initer)
             compst fenv limit)
    :enable (c::compustate-has-var-with-type-p-of-create-same-var
             c::obj-declon-to-ident+scspec+tyname+init
             c::tyspec+declor-to-ident+tyname
             c::obj-declor-to-ident+adeclor
             c::tyname-to-type
             c::tyname-to-type-aux
             c::init-value-to-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-stmt ((stmt stmtp)
                                  (stmt-new stmtp)
                                  (stmt-thm-name symbolp)
                                  info
                                  (gin simpadd0-ginp))
  :guard (and (stmt-unambp stmt)
              (stmt-unambp stmt-new))
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
       (hints `(("Goal"
                 :in-theory '((:e ldm-block-item)
                              (:e ldm-stmt)
                              (:e c::block-item-stmt))
                 :use ((:instance ,stmt-thm-name (limit (1- limit)))
                       (:instance
                        simpadd0-block-item-stmt-support-lemma
                        (old-stmt (mv-nth 1 (ldm-stmt ',stmt)))
                        (new-stmt (mv-nth 1 (ldm-stmt ',stmt-new)))
                        (types (mv-nth 1 (ldm-type-option-set ',types))))
                       (:instance
                        simpadd0-block-item-stmt-error-support-lemma
                        (stmt (mv-nth 1 (ldm-stmt ',stmt)))
                        (fenv old-fenv))
                       ,@(simpadd0-block-item-stmt-lemma-instances gin.vartys
                                                                   stmt)))))
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

  :prepwork
  ((define simpadd0-block-item-stmt-lemma-instances ((vartys ident-type-mapp)
                                                     (stmt stmtp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-block-item-stmt-vartys-support-lemma
                       (stmt (mv-nth 1 (ldm-stmt ',stmt)))
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-block-item-stmt-lemma-instances (omap::tail vartys) stmt)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret block-item-unambp-of-simpadd0-block-item-stmt
    (block-item-unambp item)
    :hyp (stmt-unambp stmt-new))

  (defruled simpadd0-block-item-stmt-support-lemma
    (b* ((old (c::block-item-stmt old-stmt))
         (new (c::block-item-stmt new-stmt))
         ((mv old-stmt-result old-stmt-compst)
          (c::exec-stmt old-stmt compst old-fenv (1- limit)))
         ((mv new-stmt-result new-stmt-compst)
          (c::exec-stmt new-stmt compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-stmt-result))
                    (equal old-stmt-result new-stmt-result)
                    (equal old-stmt-compst new-stmt-compst)
                    (set::in (c::type-option-of-stmt-value old-stmt-result)
                             types))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (set::in (c::type-option-of-stmt-value old-result)
                             types))))
    :expand
    ((c::exec-block-item (c::block-item-stmt old-stmt) compst old-fenv limit)
     (c::exec-block-item (c::block-item-stmt new-stmt) compst new-fenv limit)))

  (defruled simpadd0-block-item-stmt-error-support-lemma
    (implies (c::errorp (mv-nth 0 (c::exec-stmt stmt compst fenv (1- limit))))
             (c::errorp
              (mv-nth 0 (c::exec-block-item
                         (c::block-item-stmt stmt) compst fenv limit))))
    :expand (c::exec-block-item (c::block-item-stmt stmt) compst fenv limit))

  (defruled simpadd0-block-item-stmt-vartys-support-lemma
    (b* ((item (c::block-item-stmt stmt))
         ((mv & stmt-compst1) (c::exec-stmt stmt compst fenv (1- limit)))
         ((mv result compst1) (c::exec-block-item item compst fenv limit)))
      (implies (and (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type stmt-compst1))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-block-item (c::block-item-stmt stmt) compst fenv limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-decl ((decl declp)
                                  (decl-new declp)
                                  (decl-thm-name symbolp)
                                  info
                                  (vartys-post ident-type-mapp)
                                  (gin simpadd0-ginp))
  :guard (and (decl-unambp decl)
              (decl-unambp decl-new))
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
       (lemma-instances
        (simpadd0-block-item-decl-lemma-instances vartys-post decl))
       (hints `(("Goal"
                 :in-theory '((:e ldm-block-item)
                              (:e ldm-decl-obj)
                              (:e ldm-type-option-set)
                              (:e c::block-item-declon)
                              (:e set::insert))
                 :use ((:instance ,decl-thm-name (limit (1- limit)))
                       (:instance
                        simpadd0-block-item-decl-support-lemma
                        (old-declon (mv-nth 1 (ldm-decl-obj ',decl)))
                        (new-declon (mv-nth 1 (ldm-decl-obj ',decl-new))))
                       (:instance
                        simpadd0-block-item-decl-error-support-lemma
                        (declon (mv-nth 1 (ldm-decl-obj ',decl)))
                        (fenv old-fenv))
                       ,@lemma-instances))))
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

  :prepwork
  ((define simpadd0-block-item-decl-lemma-instances ((vartys ident-type-mapp)
                                                     (decl declp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-block-item-decl-vartys-support-lemma
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))
                       (declon (mv-nth 1 (ldm-decl-obj ',decl)))
                       (fenv old-fenv)))
          (lemma-instances
           (simpadd0-block-item-decl-lemma-instances (omap::tail vartys) decl)))
       (cons lemma-instance lemma-instances))))

  ///

  (defret block-item-unambp-of-simpadd0-block-item-decl
    (block-item-unambp item)
    :hyp (decl-unambp decl-new)
    :hints (("Goal" :in-theory (enable (:e irr-block-item)))))

  (defruled simpadd0-block-item-decl-support-lemma
    (b* ((old (c::block-item-declon old-declon))
         (new (c::block-item-declon new-declon))
         (old-declon-compst
          (c::exec-obj-declon old-declon compst old-fenv (1- limit)))
         (new-declon-compst
          (c::exec-obj-declon new-declon compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-declon-compst))
                    (equal old-declon-compst new-declon-compst))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (set::in (c::type-option-of-stmt-value old-result)
                             (set::insert nil nil)))))
    :expand ((c::exec-block-item
              (c::block-item-declon old-declon) compst old-fenv limit)
             (c::exec-block-item
              (c::block-item-declon new-declon) compst new-fenv limit)))

  (defruled simpadd0-block-item-decl-error-support-lemma
    (implies (c::errorp (c::exec-obj-declon declon compst fenv (1- limit)))
             (c::errorp (mv-nth 0 (c::exec-block-item
                                   (c::block-item-declon declon)
                                   compst fenv limit))))
    :expand (c::exec-block-item
             (c::block-item-declon declon) compst fenv limit))

  (defruled simpadd0-block-item-decl-vartys-support-lemma
    (b* ((item (c::block-item-declon declon))
         (declon-compst (c::exec-obj-declon declon compst fenv (1- limit)))
         ((mv result compst1) (c::exec-block-item item compst fenv limit)))
      (implies (and (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type declon-compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-block-item
             (c::block-item-declon declon) compst fenv limit)))

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
       (vartys-lemma-instances
        (simpadd0-block-item-list-empty-lemma-instances gin.vartys))
       (hints `(("Goal"
                 :in-theory '((:e ldm-block-item-list)
                              (:e ldm-type)
                              (:e ldm-type-option-set)
                              (:e ldm-ident)
                              (:e set::in)
                              c::type-option-of-stmt-value)
                 :use (simpadd0-block-item-list-empty-support-lemma
                       ,@vartys-lemma-instances))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm items
                                 items
                                 gin.vartys
                                 gin.vartys
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (make-simpadd0-gout :events (cons thm-event gin.events)
                        :thm-index thm-index
                        :thm-name thm-name
                        :vartys gin.vartys))
  :hooks (:fix)

  :prepwork
  ((define simpadd0-block-item-list-empty-lemma-instances
     ((vartys ident-type-mapp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance simpadd0-block-item-list-empty-vartys-support-lemma
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-block-item-list-empty-lemma-instances (omap::tail vartys))))
       (cons lemma-instance lemma-instances))))

  ///

  (defruled simpadd0-block-item-list-empty-support-lemma
    (b* ((old nil)
         (new nil)
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (not (c::errorp old-result))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :enable c::exec-block-item-list)

  (defruled simpadd0-block-item-list-empty-vartys-support-lemma
    (b* ((items nil)
         ((mv result compst1)
          (c::exec-block-item-list items compst fenv limit)))
      (implies (and (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::exec-block-item-list
             c::compustate-has-var-with-type-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-block-item-list-cons ((item block-itemp)
                                       (item-new block-itemp)
                                       (item-thm-name symbolp)
                                       (items block-item-listp)
                                       (items-new block-item-listp)
                                       (items-thm-name symbolp)
                                       (vartys-post ident-type-mapp)
                                       (gin simpadd0-ginp))
  :guard (and (block-item-unambp item)
              (block-item-unambp item-new)
              (block-item-list-unambp items)
              (block-item-list-unambp items-new))
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
     both the first item and (the list of) the rest of the items.")
   (xdoc::p
    "The @('vartys-post') variable-type map passed as input
     is the one at the end of the execution of
     the @(tsee cons) list of block items."))
  (b* (((simpadd0-gin gin) gin)
       (item (block-item-fix item))
       (items (block-item-list-fix items))
       (item-new (block-item-fix item-new))
       (items-new (block-item-list-fix items-new))
       (item+items (cons item items))
       (item+items-new (cons item-new items-new))
       (gout-no-thm (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                          :vartys vartys-post))
       ((unless (and item-thm-name
                     items-thm-name))
        (mv item+items-new gout-no-thm))
       (first-types (block-item-types item))
       ((unless (= (set::cardinality first-types) 1))
        (mv item+items-new gout-no-thm))
       (first-type (set::head first-types))
       (rest-types (block-item-list-types items))
       ((unless (= (set::cardinality rest-types) 1))
        (mv item+items-new gout-no-thm))
       (rest-type (set::head rest-types))
       ((mv support-lemma support-lemma-vartys)
        (cond
         ((not first-type)
          (cond
           ((not rest-type)
            (mv 'simpadd0-block-item-list-cons-rest-none-support-lemma
                'simpadd0-block-item-list-cons-rest-vartys-support-lemma))
           ((type-case rest-type :void)
            (mv 'simpadd0-block-item-list-cons-rest-novalue-support-lemma
                'simpadd0-block-item-list-cons-rest-vartys-support-lemma))
           (t (mv 'simpadd0-block-item-list-cons-rest-value-support-lemma
                  'simpadd0-block-item-list-cons-rest-vartys-support-lemma))))
         ((type-case first-type :void)
          (mv 'simpadd0-block-item-list-cons-first-novalue-support-lemma
              'simpadd0-block-item-list-cons-first-vartys-support-lemma))
         (t (mv 'simpadd0-block-item-list-cons-first-value-support-lemma
                'simpadd0-block-item-list-cons-first-vartys-support-lemma))))
       (lemma-instances
        (simpadd0-block-item-list-cons-lemma-instances vartys-post
                                                       support-lemma-vartys
                                                       item
                                                       items))
       (hints
        `(("Goal"
           :in-theory '((:e ldm-block-item)
                        (:e ldm-block-item-list)
                        (:e ldm-ident)
                        (:e ldm-type-option-set)
                        (:e ldm-type)
                        (:e c::type-nonchar-integerp)
                        (:e set::in)
                        c::type-option-of-stmt-value
                        c::type-of-value-option
                        c::value-option-some->val
                        c::value-fix-when-valuep
                        c::valuep-when-value-optionp
                        c::value-optionp-of-stmt-value-return->value?
                        simpadd0-set-lemma
                        (:e set::cardinality)
                        (:e set::head)
                        (:e c::type-void)
                        c::stmt-value-kind-possibilities
                        (:t c::type-of-value)
                        simpadd0-type-of-value-not-void-lemma)
           :use ((:instance
                  ,item-thm-name
                  (limit (1- limit)))
                 (:instance
                  ,items-thm-name
                  (compst
                   (mv-nth 1 (c::exec-block-item
                              (mv-nth 1 (ldm-block-item ',item))
                              compst old-fenv (1- limit))))
                  (limit (1- limit)))
                 (:instance
                  ,support-lemma
                  (old-item (mv-nth 1 (ldm-block-item ',item)))
                  (old-items (mv-nth 1 (ldm-block-item-list ',items)))
                  (new-item (mv-nth 1 (ldm-block-item ',item-new)))
                  (new-items (mv-nth 1 (ldm-block-item-list ',items-new))))
                 (:instance
                  simpadd0-block-item-list-cons-first-error-support-lemma
                  (item (mv-nth 1 (ldm-block-item ',item)))
                  (items (mv-nth 1 (ldm-block-item-list ',items)))
                  (fenv old-fenv))
                 (:instance
                  simpadd0-block-item-list-cons-rest-error-support-lemma
                  (item (mv-nth 1 (ldm-block-item ',item)))
                  (items (mv-nth 1 (ldm-block-item-list ',items)))
                  (fenv old-fenv))
                 ,@lemma-instances))))
       ((mv thm-event thm-name thm-index)
        (gen-block-item-list-thm item+items
                                 item+items-new
                                 gin.vartys
                                 vartys-post
                                 gin.const-new
                                 gin.thm-index
                                 hints)))
    (mv item+items-new
        (make-simpadd0-gout :events (cons thm-event gin.events)
                            :thm-index thm-index
                            :thm-name thm-name
                            :vartys vartys-post)))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))

  :prepwork
  ((define simpadd0-block-item-list-cons-lemma-instances
     ((vartys ident-type-mapp)
      (lemma symbolp)
      (item block-itemp)
      (items block-item-listp))
     :returns (lemma-instances true-listp)
     :parents nil
     (b* (((when (omap::emptyp vartys)) nil)
          ((mv var type) (omap::head vartys))
          (lemma-instance
           `(:instance ,lemma
                       (item (mv-nth 1 (ldm-block-item ',item)))
                       (items (mv-nth 1 (ldm-block-item-list ',items)))
                       (fenv old-fenv)
                       (var (mv-nth 1 (ldm-ident ',var)))
                       (type (mv-nth 1 (ldm-type ',type)))))
          (lemma-instances
           (simpadd0-block-item-list-cons-lemma-instances (omap::tail vartys)
                                                          lemma
                                                          item
                                                          items)))
       (cons lemma-instance lemma-instances))))

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

  (defruled simpadd0-block-item-list-cons-first-value-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-item (c::stmt-value-return->value? old-item-result))
         (val (c::stmt-value-return->value? old-result))
         (type (c::type-of-value val-item)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    val-item
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    val
                    (equal (c::type-of-value val) type))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-first-novalue-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-item (c::stmt-value-return->value? old-item-result))
         (val (c::stmt-value-return->value? old-result)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (equal old-item-result new-item-result)
                    (equal old-item-compst new-item-compst)
                    (equal (c::stmt-value-kind old-item-result) :return)
                    (not val-item))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not val))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-value-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list
           old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list
           new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-items (c::stmt-value-return->value? old-items-result))
         (val (c::stmt-value-return->value? old-result))
         (type (c::type-of-value val-items)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :return)
                    val-items
                    (c::type-nonchar-integerp type))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    val
                    (equal (c::type-of-value val) type))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-novalue-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit))
         (val-items (c::stmt-value-return->value? old-items-result))
         (val (c::stmt-value-return->value? old-result)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :return)
                    (not val-items))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :return)
                    (not val))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-rest-none-support-lemma
    (b* ((old (cons old-item old-items))
         (new (cons new-item new-items))
         ((mv old-item-result old-item-compst)
          (c::exec-block-item old-item compst old-fenv (1- limit)))
         ((mv new-item-result new-item-compst)
          (c::exec-block-item new-item compst new-fenv (1- limit)))
         ((mv old-items-result old-items-compst)
          (c::exec-block-item-list
           old-items old-item-compst old-fenv (1- limit)))
         ((mv new-items-result new-items-compst)
          (c::exec-block-item-list
           new-items new-item-compst new-fenv (1- limit)))
         ((mv old-result old-compst)
          (c::exec-block-item-list old compst old-fenv limit))
         ((mv new-result new-compst)
          (c::exec-block-item-list new compst new-fenv limit)))
      (implies (and (not (c::errorp old-result))
                    (not (c::errorp new-item-result))
                    (not (c::errorp new-items-result))
                    (equal old-item-result new-item-result)
                    (equal old-items-result new-items-result)
                    (equal old-item-compst new-item-compst)
                    (equal old-items-compst new-items-compst)
                    (equal (c::stmt-value-kind old-item-result) :none)
                    (equal (c::stmt-value-kind old-items-result) :none))
               (and (not (c::errorp new-result))
                    (equal old-result new-result)
                    (equal old-compst new-compst)
                    (equal (c::stmt-value-kind old-result) :none))))
    :expand ((c::exec-block-item-list
              (cons old-item old-items) compst old-fenv limit)
             (c::exec-block-item-list
              (cons new-item new-items) compst new-fenv limit)))

  (defruled simpadd0-block-item-list-cons-first-error-support-lemma
    (implies (c::errorp
              (mv-nth 0 (c::exec-block-item item compst fenv (1- limit))))
             (c::errorp
              (mv-nth 0 (c::exec-block-item-list
                         (cons item items) compst fenv limit))))
    :expand (c::exec-block-item-list (cons item items) compst fenv limit))

  (defruled simpadd0-block-item-list-cons-rest-error-support-lemma
    (b* (((mv result compst1) (c::exec-block-item item compst fenv (1- limit))))
      (implies (and (not (c::errorp result))
                    (equal (c::stmt-value-kind result) :none)
                    (c::errorp (mv-nth 0 (c::exec-block-item-list
                                          items compst1 fenv (1- limit)))))
               (c::errorp
                (mv-nth 0 (c::exec-block-item-list
                           (cons item items) compst fenv limit)))))
    :expand (c::exec-block-item-list (cons item items) compst fenv limit))

  (defruled simpadd0-block-item-list-cons-first-vartys-support-lemma
    (b* ((item+items (cons item items))
         ((mv result0 compst0)
          (c::exec-block-item item compst fenv (1- limit)))
         ((mv result2 compst2)
          (c::exec-block-item-list item+items compst fenv limit)))
      (implies (and (not (c::errorp result2))
                    (equal (c::stmt-value-kind result0) :return)
                    (c::compustate-has-var-with-type-p var type compst0))
               (c::compustate-has-var-with-type-p var type compst2)))
    :enable c::exec-block-item-list)

  (defruled simpadd0-block-item-list-cons-rest-vartys-support-lemma
    (b* ((item+items (cons item items))
         ((mv result0 compst0)
          (c::exec-block-item item compst fenv (1- limit)))
         ((mv & compst1)
          (c::exec-block-item-list items compst0 fenv (1- limit)))
         ((mv result2 compst2)
          (c::exec-block-item-list item+items compst fenv limit)))
      (implies (and (not (c::errorp result2))
                    (equal (c::stmt-value-kind result0) :none)
                    (c::compustate-has-var-with-type-p var type compst1))
               (c::compustate-has-var-with-type-p var type compst2)))
    :enable c::exec-block-item-list))

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
    :guard (expr-unambp expr)
    :returns (mv (new-expr exprp) (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an expression."
    (b* (((simpadd0-gin gin) gin))
      (expr-case
       expr
       :ident (simpadd0-expr-ident expr.ident
                                   (coerce-var-info expr.info)
                                   gin)
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
                              (coerce-expr-unary-info expr.info)
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
                             (coerce-tyname-info (tyname->info expr.type))
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
                               (coerce-expr-binary-info expr.info)
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
    :guard (expr-list-unambp exprs)
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
    :guard (expr-option-unambp expr?)
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
    :guard (const-expr-unambp cexpr)
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
    :guard (const-expr-option-unambp cexpr?)
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
    :guard (genassoc-unambp genassoc)
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
    :guard (genassoc-list-unambp genassocs)
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
    :guard (member-designor-unambp memdes)
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
    :guard (type-spec-unambp tyspec)
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
                   (simpadd0-enumspec tyspec.spec gin))
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
    :guard (spec/qual-unambp specqual)
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
    :guard (spec/qual-list-unambp specquals)
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
    :guard (align-spec-unambp alignspec)
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
    :guard (decl-spec-unambp declspec)
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
    :guard (decl-spec-list-unambp declspecs)
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
    :guard (initer-unambp initer)
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
    :guard (initer-option-unambp initer?)
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
    :guard (desiniter-unambp desiniter)
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
    :guard (desiniter-list-unambp desiniters)
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
    :guard (designor-unambp designor)
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
    :guard (designor-list-unambp designors)
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
    :guard (declor-unambp declor)
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
    :guard (declor-option-unambp declor?)
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
    :guard (dirdeclor-unambp dirdeclor)
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
    :guard (absdeclor-unambp absdeclor)
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
    :guard (absdeclor-option-unambp absdeclor?)
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
    :guard (dirabsdeclor-unambp dirabsdeclor)
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
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
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
    :guard (param-declon-unambp paramdecl)
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
                             :declor new-declor)
          (change-simpadd0-gout (simpadd0-gout-no-thm gin)
                                :vartys gout-declor.vartys)))
    :measure (param-declon-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon-list ((paramdecls param-declon-listp)
                                      (gin simpadd0-ginp))
    :guard (param-declon-list-unambp paramdecls)
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
    :guard (param-declor-unambp paramdeclor)
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
            (info (coerce-param-declor-nonabstract-info paramdeclor.info))
            (type (c$::param-declor-nonabstract-info->type info))
            (post-vartys (omap::update (c$::declor->ident paramdeclor.declor)
                                       type
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
    :guard (tyname-unambp tyname)
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
    :guard (struni-spec-unambp struni-spec)
    :returns (mv (new-struni-spec struni-specp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure or union specifier."
    (b* (((simpadd0-gin gin) gin)
         ((struni-spec struni-spec) struni-spec)
         ((mv new-members (simpadd0-gout gout-members))
          (simpadd0-structdecl-list struni-spec.members gin))
         (gin (simpadd0-gin-update gin gout-members)))
      (mv (make-struni-spec :name? struni-spec.name?
                            :members new-members)
          (simpadd0-gout-no-thm gin)))
    :measure (struni-spec-count struni-spec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl ((structdecl structdeclp)
                               (gin simpadd0-ginp))
    :guard (structdecl-unambp structdecl)
    :returns (mv (new-structdecl structdeclp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declaration."
    (b* (((simpadd0-gin gin) gin))
      (structdecl-case
       structdecl
       :member (b* (((mv new-specqual (simpadd0-gout gout-specqual))
                     (simpadd0-spec/qual-list structdecl.specqual gin))
                    (gin (simpadd0-gin-update gin gout-specqual))
                    ((mv new-declor (simpadd0-gout gout-declor))
                     (simpadd0-structdeclor-list structdecl.declor gin))
                    (gin (simpadd0-gin-update gin gout-declor)))
                 (mv (make-structdecl-member
                      :extension structdecl.extension
                      :specqual new-specqual
                      :declor new-declor
                      :attrib structdecl.attrib)
                     (simpadd0-gout-no-thm gin)))
       :statassert (b* (((mv new-structdecl (simpadd0-gout gout-structdecl))
                         (simpadd0-statassert structdecl.unwrap gin))
                        (gin (simpadd0-gin-update gin gout-structdecl)))
                     (mv (structdecl-statassert new-structdecl)
                         (simpadd0-gout-no-thm gin)))
       :empty (mv (structdecl-empty) (simpadd0-gout-no-thm gin))))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdecl-list ((structdecls structdecl-listp)
                                    (gin simpadd0-ginp))
    :guard (structdecl-list-unambp structdecls)
    :returns (mv (new-structdecls structdecl-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarations."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdecls))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-structdecl (simpadd0-gout gout-structdecl))
          (simpadd0-structdecl (car structdecls) gin))
         (gin (simpadd0-gin-update gin gout-structdecl))
         ((mv new-structdecls (simpadd0-gout gout-structdecls))
          (simpadd0-structdecl-list (cdr structdecls) gin))
         (gin (simpadd0-gin-update gin gout-structdecls)))
      (mv (cons new-structdecl new-structdecls)
          (simpadd0-gout-no-thm gin)))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor ((structdeclor structdeclorp)
                                 (gin simpadd0-ginp))
    :guard (structdeclor-unambp structdeclor)
    :returns (mv (new-structdeclor structdeclorp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declarator."
    (b* (((simpadd0-gin gin) gin)
         ((structdeclor structdeclor) structdeclor)
         ((mv new-declor? (simpadd0-gout gout-declor?))
          (simpadd0-declor-option structdeclor.declor? gin))
         (gin (simpadd0-gin-update gin gout-declor?))
         ((mv new-expr? (simpadd0-gout gout-expr?))
          (simpadd0-const-expr-option structdeclor.expr? gin))
         (gin (simpadd0-gin-update gin gout-expr?)))
      (mv (make-structdeclor :declor? new-declor?
                             :expr? new-expr?)
          (simpadd0-gout-no-thm gin)))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-structdeclor-list ((structdeclors structdeclor-listp)
                                      (gin simpadd0-ginp))
    :guard (structdeclor-list-unambp structdeclors)
    :returns (mv (new-structdeclors structdeclor-listp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarators."
    (b* (((simpadd0-gin gin) gin)
         ((when (endp structdeclors))
          (mv nil (simpadd0-gout-no-thm gin)))
         ((mv new-structdeclor (simpadd0-gout gout-structdeclor))
          (simpadd0-structdeclor (car structdeclors) gin))
         (gin (simpadd0-gin-update gin gout-structdeclor))
         ((mv new-structdeclors (simpadd0-gout gout-structdeclors))
          (simpadd0-structdeclor-list (cdr structdeclors) gin))
         (gin (simpadd0-gin-update gin gout-structdeclors)))
      (mv (cons new-structdeclor new-structdeclors)
          (simpadd0-gout-no-thm gin)))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumspec ((enumspec enumspecp) (gin simpadd0-ginp))
    :guard (enumspec-unambp enumspec)
    :returns (mv (new-enumspec enumspecp)
                 (gout simpadd0-goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumeration specifier."
    (b* (((simpadd0-gin gin) gin)
         ((enumspec enumspec) enumspec)
         ((mv new-list (simpadd0-gout gout-list))
          (simpadd0-enumer-list enumspec.list gin))
         (gin (simpadd0-gin-update gin gout-list)))
      (mv (make-enumspec :name enumspec.name
                         :list new-list
                         :final-comma enumspec.final-comma)
          (simpadd0-gout-no-thm gin)))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp) (gin simpadd0-ginp))
    :guard (enumer-unambp enumer)
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
    :guard (enumer-list-unambp enumers)
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
    :guard (statassert-unambp statassert)
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
    :guard (initdeclor-unambp initdeclor)
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
         (info (coerce-initdeclor-info initdeclor.info))
         (type (c$::initdeclor-info->type info))
         (post-vartys (if (and (not (c$::initdeclor-info->typedefp info))
                               (type-formalp type)
                               (not (type-case type :void))
                               (not (type-case type :char)))
                          (omap::update (c$::declor->ident initdeclor.declor)
                                        type
                                        gout-init?.vartys)
                        gout-init?.vartys)))
      (mv (make-initdeclor :declor new-declor
                           :asm? initdeclor.asm?
                           :attribs initdeclor.attribs
                           :init? new-init?
                           :info info)
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
    :guard (initdeclor-list-unambp initdeclors)
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
    :guard (decl-unambp decl)
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
    :guard (decl-list-unambp decls)
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
    :guard (label-unambp label)
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
    :guard (stmt-unambp stmt)
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
                   (mv (stmt-compound new-items)
                       (simpadd0-gout-no-thm gin)))
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
             (mv (make-stmt-if :test new-test
                               :then new-then)
                 (simpadd0-gout-no-thm gin)))
       :ifelse (b* (((mv new-test (simpadd0-gout gout-test))
                     (simpadd0-expr stmt.test gin))
                    (gin (simpadd0-gin-update gin gout-test))
                    ((mv new-then (simpadd0-gout gout-then))
                     (simpadd0-stmt stmt.then gin))
                    (gin (simpadd0-gin-update gin gout-then))
                    ((mv new-else (simpadd0-gout gout-else))
                     (simpadd0-stmt stmt.else gin))
                    (gin (simpadd0-gin-update gin gout-else)))
                 (mv (make-stmt-ifelse :test new-test
                                       :then new-then
                                       :else new-else)
                     (simpadd0-gout-no-thm gin)))
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
                (mv (make-stmt-while :test new-test
                                     :body new-body)
                    (simpadd0-gout-no-thm gin)))
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
    :guard (block-item-unambp item)
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
    :guard (block-item-list-unambp items)
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
                                     gout-items.vartys
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
    (defret structdecl-unambp-of-simpadd0-structdecl
      (structdecl-unambp new-structdecl)
      :fn simpadd0-structdecl)
    (defret structdecl-list-unambp-of-simpadd0-structdecl-list
      (structdecl-list-unambp new-structdecls)
      :fn simpadd0-structdecl-list)
    (defret structdeclor-unambp-of-simpadd0-structdeclor
      (structdeclor-unambp new-structdeclor)
      :fn simpadd0-structdeclor)
    (defret structdeclor-list-unambp-of-simpadd0-structdeclor-list
      (structdeclor-list-unambp new-structdeclors)
      :fn simpadd0-structdeclor-list)
    (defret enumspec-unambp-of-simpadd0-enumspec
      (enumspec-unambp new-enumspec)
      :fn simpadd0-enumspec)
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
                                       simpadd0-structdecl
                                       simpadd0-structdecl-list
                                       simpadd0-structdeclor
                                       simpadd0-structdeclor-list
                                       simpadd0-enumspec
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

  (verify-guards simpadd0-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp) (gin simpadd0-ginp))
  :guard (fundef-unambp fundef)
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
       (info (coerce-fundef-info fundef.info))
       ((mv new-spec (simpadd0-gout gout-spec))
        (simpadd0-decl-spec-list fundef.spec gin))
       (gin (simpadd0-gin-update gin gout-spec))
       ((mv new-declor (simpadd0-gout gout-declor))
        (simpadd0-declor fundef.declor gin))
       (gin (simpadd0-gin-update gin gout-declor))
       (type (c$::fundef-info->type info))
       (vartys-with-fun (if (and (type-formalp type)
                                 (not (type-case type :void))
                                 (not (type-case type :char)))
                            (omap::update (c$::declor->ident fundef.declor)
                                          type
                                          gout-declor.vartys)
                          gout-declor.vartys))
       ((mv new-decls (simpadd0-gout gout-decls))
        (simpadd0-decl-list fundef.decls (change-simpadd0-gin
                                          gin :vartys vartys-with-fun)))
       (gin (simpadd0-gin-update gin gout-decls))
       (vartys (vartys-from-valid-table
                (c$::fundef-info->table-body-start info)))
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
        (mv (irr-fundef) (irr-simpadd0-gout)))
       (fun (ident->unwrap (dirdeclor-ident->ident dirdeclor)))
       ((unless (stringp fun))
        (raise "Internal error: non-string identifier ~x0." fun)
        (mv (irr-fundef) (irr-simpadd0-gout)))
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
                        c::errorp-of-error))))
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
    (fundef-unambp new-fundef)
    :hints (("Goal" :in-theory (enable (:e irr-fundef))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp) (gin simpadd0-ginp))
  :guard (extdecl-unambp extdecl)
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
    (extdecl-unambp new-extdecl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp)
                               (gin simpadd0-ginp))
  :guard (extdecl-list-unambp extdecls)
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
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp) (gin simpadd0-ginp))
  :guard (transunit-unambp tunit)
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
    (transunit-unambp new-tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath-transunit-map ((map filepath-transunit-mapp)
                                         (gin simpadd0-ginp))
  :guard (filepath-transunit-map-unambp map)
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
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep)
                                     (gin simpadd0-ginp))
  :guard (transunit-ensemble-unambp tunits)
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
    (transunit-ensemble-unambp new-tunits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-code-ensemble ((code code-ensemblep)
                                (gin simpadd0-ginp))
  :guard (code-ensemble-unambp code)
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
    (code-ensemble-unambp new-code)
    :hints
    (("Goal" :in-theory (enable c$::code-ensemble-unambp-of-code-ensemble)))))

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
                                                    const-new
                                                    state)
  :returns (mv erp (event pseudo-event-formp))
  :parents (simpadd0-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code-old const-new)
        (simpadd0-process-inputs const-old const-new (w state))))
    (simpadd0-gen-everything code-old const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fn (const-old const-new (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (simpadd0-implementation)
  :short "Event expansion of @(tsee simpadd0)."
  (b* (((mv erp event)
        (simpadd0-process-inputs-and-gen-everything const-old
                                                    const-new
                                                    state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection simpadd0-macro-definition
  :parents (simpadd0-implementation)
  :short "Definition of the @(tsee simpadd0) macro."
  (defmacro simpadd0 (const-old const-new)
    `(make-event
      (simpadd0-fn ',const-old ',const-new 'simpadd0 state))))
