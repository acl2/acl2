; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-list-has-no-duplicates" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/std/basic/mbt-dollar" :dir :system)
(include-book "kestrel/std/system/apply-fn-into-ifs" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/std/system/ibody" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/util/defiso" :dir :system)
(include-book "kestrel/utilities/directed-untranslate" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)

(include-book "utilities/defaults-table")
(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")
(include-book "utilities/untranslate-specifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 isodata

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old'),
   @('isomaps'),
   @('predicate'),
   @('new-name'),
   @('new-enable'),
   @('old-to-new-name'),
   @('old-to-new-enable'),
   @('new-to-old-name'),
   @('new-to-old-enable'),
   @('newp-of-new-name'),
   @('newp-of-new-enable'),
   @('verify-guards'),
   @('untranslate'),
   @('hints'),
   @('print'), and
   @('show-only')
   are the homonymous inputs to @(tsee isodata),
   before being validated.
   These formal parameters have no types because they may be any values."

  "@('old$'),
   @('predicate$'),
   @('new-enable$'),
   @('old-to-new-enable$'),
   @('new-to-old-enable$'),
   @('newp-of-new-enable$'),
   @('verify-guards$'),
   @('untranslate$'),
   @('hints$'),
   @('print$'), and
   @('show-only$')
   are the result of processing
   the homonymous inputs (without the @('$')).
   Some are identical to the corresponding inputs,
   but they have types implied by their successful validation,
   performed when they are processed."

  "@('new$') is the result of processing @('new-name')."

  "@('old-to-new$') is the result of processing @('old-to-new-name')."

  "@('new-to-old$') is the result of processing @('new-to-old-name')."

  "@('newp-of-new$') is the result of processing @('newp-of-new-name')."

  "@('m') is the number of results of @('old')."

  "@('arg-isomaps') is an alist
   from formal arguments of @('old')
   to isomorphic mapping records that specify
   how the associated formal arguments must be transformed.
   There are never duplicate keys.
   When input processing is complete,
   the keys are exactly all the formal arguments of @('old'), in order.
   @('arg-isomaps') results from processing @('isomaps')."

  "@('res-isomaps') is an alist
   from positive integers from 1 to @('m')
   to isomorphic mapping records that specify
   how the result with the associated (1-based) indices
   must be transformed.
   There are never duplicate keys.
   When input processing is complete:
   if some results are transformed,
   the keys are exactly all the integers from 1 to @('m'), in order;
   if no results are transformed,
   the alist is @('nil').
   @('res-isomaps') results from processing @('isomaps')."

  "@('appcond-thm-names') is an alist
   from the applicability condition keywords
   to the corresponding theorem names."

  "@('old-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the old function."

  "@('new-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the new function."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing isodata)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate isodata-isomap
  :short "Information about an isomorphic mapping according to which
          (some of) the target function's arguments and results
          are transformed."
  :long
  (xdoc::topstring-p
   "This aggregate is somewhat similar to @(tsee defmapping-infop),
    and in fact it corresponds
    either to an existing @(tsee defiso) that is referenced
    in an @('isok') input of @(tsee isodata),
    or to a locally generated @(tsee defiso) that is determined
    in the @('isok') input of @(tsee isodata).
    However, this aggregate is not stored in any table;
    it has some fields in common (except for their names)
    with @(tsee defmapping-infop),
    but it has a few extra fields and omits a few fields.
    This aggregate is only for @(tsee isodata)'s internal use.")
  ((isoname "Name of the @(tsee defiso)." symbolp)
   (localp "Flag saying whether the @(tsee defiso) is locally generated or not."
           booleanp)
   (oldp "Recognizer of the old representation." pseudo-termfnp)
   (newp "Recognizer of the new representation." pseudo-termfnp)
   (forth "Conversion from old to new representation." pseudo-termfnp)
   (back "Conversion from new to old representation." pseudo-termfnp)
   (forth-image "Name of the @(':alpha-image') theorem of the @(tsee defiso)."
                symbolp)
   (back-image "Name of the @(':beta-image') theorem of the @(tsee defiso)."
               symbolp)
   (back-of-forth "Name of the @(':beta-of-alpha') theorem
                   of the @(tsee defiso)."
                  symbolp)
   (forth-of-back "Name of the @(':alpha-of-beta') theorem
                   of the @(tsee defiso)."
                  symbolp)
   (forth-injective "Name of the @(':alpha-injective') theorem
                     of the @(tsee defiso)."
                    symbolp)
   (back-injective "Name of the @(':beta-injective') theorem
                    of the @(tsee defiso)."
                   symbolp)
   (oldp-guard "Name of the @(':doma-guard') theorem
                of the @(tsee defiso), if present (otherwise @('nil'))."
               symbolp)
   (newp-guard "Name of the @(':domb-guard') theorem
                of the @(tsee defiso), if present (otherwise @('nil'))."
               symbolp)
   (forth-guard "Name of the @(':alpha-guard') theorem
                of the @(tsee defiso), if present (otherwise @('nil'))."
                symbolp)
   (back-guard "Name of the @(':beta-guard') theorem
                of the @(tsee defiso), if present (otherwise @('nil'))."
               symbolp)
   (hints "Optional hints for the @(tsee defiso),
           if locally generated (otherwise @('nil'))."
          keyword-value-listp))
  :pred isodata-isomapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist isodata-isomap-listp (x)
  :short "Recognize lists of isomorphic mapping records."
  (isodata-isomapp x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist isodata-symbol-isomap-alistp (x)
  :short "Recognize alists from symbols to isomorphic mapping records."
  :key (symbolp x)
  :val (isodata-isomapp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule isodata-symbolp-of-key-of-symbol-isomap-alist
    (implies (isodata-symbol-isomap-alistp x)
             (symbolp (car (assoc-equal k x)))))

  (defrule isodata-isomapp-of-val-of-symbol-isomap-alist
    (implies (and (isodata-symbol-isomap-alistp x)
                  (consp (assoc-equal k x)))
             (isodata-isomapp (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist isodata-pos-isomap-alistp (x)
  :short "Recognize alists
          from positive integers to isomorphic mapping records."
  :key (posp x)
  :val (isodata-isomapp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  ///

  (defrule isodata-posp-of-key-of-pos-isomap-alist
    (implies (and (isodata-pos-isomap-alistp x)
                  (consp (assoc-equal k x)))
             (posp (car (assoc-equal k x)))))

  (defrule isodata-isomapp-of-val-of-pos-isomap-alist
    (implies (and (isodata-pos-isomap-alistp x)
                  (consp (assoc-equal k x)))
             (isodata-isomapp (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-old (old predicate verify-guards ctx state)
  :returns (mv erp
               (old$ "A @(tsee symbolp) that is
                      the name of the target function
                      of the transformation,
                      denoted by the @('old') input.")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* (((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-is-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-is-defined$ old$ description t nil))
       ((er &) (ensure-function-has-args$ old$ description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       ((er &) (if (eq predicate t)
                   (ensure-function-number-of-results$ old$ 1
                                                       description t nil)
                 (value nil)))
       (recursive (recursivep old$ nil (w state)))
       ((er &) (if recursive
                   (ensure-function-singly-recursive$ old$
                                                      description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-known-measure$ old$
                                                   description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-not-in-termination-thm$ old$
                                                            description t nil)
                 (value nil)))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-is-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value nil))))
    (value old$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-res (res (m posp) (err-msg-preamble msgp) ctx state)
  :returns (mv erp (j posp) state)
  :short "Process a result specification in the @('isomap') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Recall that @('m') is the number of results of @('old').")
   (xdoc::p
    "We check that the result specification is a keyword @(':resultj'),
     where @('j') is a positive integer not exceeding @('m').
     We return @('j'), if successful.")
   (xdoc::p
    "If @('m') is 1, we also accept the keyword @(':result'),
     treating it the same as @(':result1')."))
  (b* ((err-msg (msg "~@0 But ~x1 is none of those." err-msg-preamble res))
       ((unless (keywordp res)) (er-soft+ ctx t 1 err-msg-preamble res))
       ((when (and (= m 1) (eq res :result))) (value 1))
       (name (symbol-name res))
       ((unless (and (> (length name) 6)
                     (equal (subseq name 0 6) "RESULT")))
        (er-soft+ ctx t 1 "~@0" err-msg))
       (j (str::strval (subseq name 6 (length name))))
       ((unless j) (er-soft+ ctx t 1 "~@0" err-msg))
       ((unless (and (<= 1 j) (<= j m))) (er-soft+ ctx t 1 "~@0" err-msg)))
    (value j)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-arg/res-list
  ((arg/res-list "The @('arg/res-listk') component of @('isomaps').")
   (k posp "The @('k') in @('arg/res-listk').")
   (old$ symbolp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple @('(args ress)') satisfying
                        @('(typed-tuplep symbol-listp pos-listp result)').")
               state)
  :verify-guards nil
  :short "Process an @('arg/res-list') component of the @('isomaps') input."
  :long
  (xdoc::topstring
   (xdoc::P
    "If the processing is successful,
     the @('args') result is
     the list of arguments of @('old') in @('arg/res-list'),
     and the @('ress') result is
     the list of 1-based indices of results of @('old') in @('arg/res-list')."))
  (b* ((wrld (w state))
       (x1...xn (formals old$ wrld))
       (m (number-of-results old$ wrld))
       (err-msg-part (if (= m 1)
                         (msg "must be either a formal argument of ~x0, ~
                               or the keyword @(':RESULT'),
                               or the keyword @(':RESULT1')."
                              old$)
                       (msg "must be either a formal argument of ~x0, ~
                             or a keyword :RESULTj where j is ~
                             a positive integer not exceeding ~
                             the number of results ~x1 of ~x0."
                            old$ m))))
    (if (atom arg/res-list)
        (if (member-eq arg/res-list x1...xn)
            (value (list (list arg/res-list) nil))
          (b* ((err-msg-preamble (msg "Since the ~n0 ARG/RES-LIST component ~
                                       of the second input ~
                                       is not a list, it ~@1"
                                      (list k) err-msg-part))
               ((er j) (isodata-process-res arg/res-list m
                                            err-msg-preamble ctx state)))
            (value (list nil (list j)))))
      (b* (((er &) (ensure-value-is-symbol-list$
                    arg/res-list
                    (msg "Since the ~n0 ARG/RES component of the second input ~
                          is not an atom, it"
                         (list k))
                    t nil))
           ((er &) (ensure-list-has-no-duplicates$
                    arg/res-list
                    (msg "The list ~x0 that is ~
                          the ~n1 ARG/RES-LIST component of the second input"
                         arg/res-list (list k))
                    t nil))
           (err-msg-preamble (msg "Each element ~
                                   of the ~n0 ARG/RES-LIST component ~
                                   of the second input ~
                                   must be ~@1"
                                  (list k) err-msg-part)))
        (isodata-process-arg/res-list-aux arg/res-list x1...xn m
                                          err-msg-preamble ctx state))))

  :prepwork
  ((define isodata-process-arg/res-list-aux ((arg/res-list symbol-listp)
                                             (x1...xn symbol-listp)
                                             (m posp)
                                             (err-msg-preamble msgp)
                                             ctx
                                             state)
     :returns (mv erp
                  result ; tuple (SYMBOL-LISTP POS-LISTP)
                  state)
     (b* (((when (endp arg/res-list)) (value (list nil nil)))
          (arg/res (car arg/res-list))
          ((when (member-eq arg/res x1...xn))
           (b* (((er (list args ress)) (isodata-process-arg/res-list-aux
                                        (cdr arg/res-list) x1...xn m
                                        err-msg-preamble ctx state)))
             (value (list (cons arg/res args) ress))))
          ((er j) (isodata-process-res arg/res m err-msg-preamble ctx state))
          ((er (list args ress)) (isodata-process-arg/res-list-aux
                                  (cdr arg/res-list) x1...xn m
                                  err-msg-preamble ctx state)))
       (value (list args (cons j ress)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-fresh-defiso-name-with-*s-suffix ((name symbolp)
                                                  (wrld plist-worldp))
  :returns (fresh-name "A @(tsee symbolp).")
  :mode :program
  :short "Suffix a name with as many @('*')s as needed
          to make it a valid name for a new @(tsee defiso)."
  :long
  (xdoc::topstring
   (xdoc::p
    "A name is valid for a new @(tsee defiso)
     if it is not already a key in the @(tsee defiso) table.")
   (xdoc::p
    "We use this function for generating local @(tsee defiso)s.")
   (xdoc::p
    "If the input name is already valid, no @('*')s are added."))
  (b* ((table (table-alist *defmapping-table-name* wrld)))
    (isodata-fresh-defiso-name-with-*s-suffix-aux name table))

  :prepwork
  ((define isodata-fresh-defiso-name-with-*s-suffix-aux ((name symbolp)
                                                         (table alistp))
     :returns fresh-name ; SYMBOLP
     :mode :program
     (if (consp (assoc-eq name table))
         (isodata-fresh-defiso-name-with-*s-suffix-aux (packn-pos (list name '*)
                                                                  name)
                                                       table)
       name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-fresh-defiso-thm-names ((isoname symbolp)
                                        (verify-guards$ booleanp)
                                        (names-to-avoid symbol-listp)
                                        (wrld plist-worldp))
  :returns (mv (forth-image "A @(tsee symbolp).")
               (back-image "A @(tsee symbolp).")
               (back-of-forth "A @(tsee symbolp).")
               (forth-of-back "A @(tsee symbolp).")
               (oldp-guard "A @(tsee symbolp).")
               (newp-guard "A @(tsee symbolp).")
               (forth-guard "A @(tsee symbolp).")
               (back-guard "A @(tsee symbolp).")
               (forth-injective "A @(tsee symbolp).")
               (back-injective "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Return fresh @(tsee defiso) theorem names."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as the @(':thm-names') input
     of a @(tsee defiso) that @(tsee isodata) generates locally,
     when the @('iso') input is not a name.")
   (xdoc::p
    "In order for the generated @(tsee defiso) to succeed,
     we supply explicit fresh theorem names to use.
     These are returned by this function.")
   (xdoc::p
    "We append the keyword (without colon) that denotes the theorem
     at the end of the @(tsee defiso) name
     (which is generated by @(tsee isodata-fresh-defiso-name-with-*s-suffix),
     and add enough @('$') characters, if needed, to make them fresh.
     We expect that adding @('$') characters will rarely be necessary.")
   (xdoc::p
    "The names of the guard-related theorems are @('nil')
     if guards must not be verified, since
     those theorems are not generated or used in that case."))
  (b* ((prefix (add-suffix isoname "-"))
       ((mv forth-image names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :alpha-image))
         nil
         names-to-avoid
         wrld))
       ((mv back-image names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :beta-image))
         nil
         names-to-avoid
         wrld))
       ((mv back-of-forth names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :beta-of-alpha))
         nil
         names-to-avoid
         wrld))
       ((mv forth-of-back names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :alpha-of-beta))
         nil
         names-to-avoid
         wrld))
       ((mv oldp-guard names-to-avoid)
        (if verify-guards$
            (fresh-logical-name-with-$s-suffix
             (add-suffix prefix (symbol-name :doma-guard))
             nil
             names-to-avoid
             wrld)
          (mv nil names-to-avoid)))
       ((mv newp-guard names-to-avoid)
        (if verify-guards$
            (fresh-logical-name-with-$s-suffix
             (add-suffix prefix (symbol-name :domb-guard))
             nil
             names-to-avoid
             wrld)
          (mv nil names-to-avoid)))
       ((mv forth-guard names-to-avoid)
        (if verify-guards$
            (fresh-logical-name-with-$s-suffix
             (add-suffix prefix (symbol-name :alpha-guard))
             nil
             names-to-avoid
             wrld)
          (mv nil names-to-avoid)))
       ((mv back-guard names-to-avoid)
        (if verify-guards$
            (fresh-logical-name-with-$s-suffix
             (add-suffix prefix (symbol-name :beta-guard))
             nil
             names-to-avoid
             wrld)
          (mv nil names-to-avoid)))
       ((mv forth-injective names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :alpha-injective))
         nil
         names-to-avoid
         wrld))
       ((mv back-injective names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix prefix (symbol-name :beta-injective))
         nil
         names-to-avoid
         wrld)))
    (mv forth-image
        back-image
        back-of-forth
        forth-of-back
        oldp-guard
        newp-guard
        forth-guard
        back-guard
        forth-injective
        back-injective
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-iso ((iso "The @('isok') component of @('isomaps').")
                             (k posp "The @('k') in @('isok').")
                             (old$ symbolp)
                             (verify-guards$ booleanp)
                             (names-to-avoid symbol-listp)
                             ctx
                             state)
  :returns (mv erp
               (result "A tuple @('(isomap updated-names-to-avoid)')
                        satisfying @('(typed-tuplep isodata-isomapp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process an @('iso') component of the @('isomaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('iso') is the name of an existing @(tsee defiso),
     the @('names-to-avoid') argument is returned unchanged,
     because we are not generating any fresh theorem names in this case.")
   (xdoc::p
    "If instead @('iso') is a list
     @('(oldp newp forth back)') or @('(oldp newp forth back :hints ...)'),
     the @('names-to-avoid') argument is augmented with
     the names of the theorems that
     will be generated by the local @(tsee defiso).")
   (xdoc::p
    "When @('iso') is the name of an existing @(tsee defiso),
     to check whether its @(':guard-thms') is @('t'),
     which is required when @('verify-guards$') is @('t'),
     we check whether one of the @('...-guard') theorems
     recorded in the @(tsee defiso) is not @('nil').
     We pick @('doma-guard'),
     but any of the other three would work as well.")
   (xdoc::p
    "When @('iso') is not the name of an existing @(tsee defiso),
     and instead we generate a local one as part of @(tsee isodata),
     we use @(tsee defiso)'s input processing code,
     and then we check that the functions are all unary and single-valued;
     given the constraints already checked
     by the @(tsee defiso) input processing code,
     here it suffices to check that the two domains are unary.
     We cannot just generate the @(tsee defiso) later;
     we need the actual (translated) functions
     to use them in the events generated by @(tsee isodata) proper.
     When we call @(tsee defiso)'s input processing functions,
     we set the context @('ctx') to the one for the @(tsee defiso) call,
     so that the error message is appropriate.
     (When the generated @(tsee defiso) call is actually submitted,
     these input processing steps will be repeated,
     but will succeed since they have been already performed here;
     and they should be quite fast to execute.)
     The name of this local @(tsee defiso) is a combination
     that involves @('old') and @('k'),
     to make the name of the @(tsee defiso) readable
     (in case of errors due to failed applicability conditions)
     and unique within the @(tsee encapsulate) generated by @(tsee isodata).")
   (xdoc::p
    "If the processing is successful,
     we return the isomorphic mapping record specified by @('iso')."))
  (if (atom iso)
      (b* (((er &) (ensure-value-is-symbol$
                    iso
                    (msg "The ~n0 ISO component ~x1 ~
                          of the second input ~
                          must be a symbol or a list. ~
                          Since it is an atom,"
                         (list k) iso)
                    t nil))
           (info (defiso-lookup iso (w state)))
           ((unless info)
            (er-soft+ ctx t nil
                      "The ~n0 ISO component of the second input, ~
                       which is the symbol ~x1, ~
                       must be the name of an existing DEFISO, ~
                       but no DEFISO with this name exists.  ~
                       See :DOC DEFISO."
                      (list k) iso))
           ((defmapping-info info) info)
           ((when (and verify-guards$
                       (null info.doma-guard)))
            (er-soft+ ctx t nil
                      "Since the :VERIFY-GUARDS input is T, ~
                       or it is (perhaps by default) :AUTO ~
                       and the target function ~x0 is guard-verified, ~
                       the DEFISO ~x1 must include ~
                       the guard-related theorems, ~
                       but it does not.  ~
                       See :DOC DEFISO."
                      old$ iso))
           (isomap (make-isodata-isomap
                    :isoname iso
                    :localp nil
                    :oldp info.doma
                    :newp info.domb
                    :forth info.alpha
                    :back info.beta
                    :forth-image info.alpha-image
                    :back-image info.beta-image
                    :back-of-forth info.beta-of-alpha
                    :forth-of-back info.alpha-of-beta
                    :forth-injective info.alpha-injective
                    :back-injective info.beta-injective
                    :oldp-guard info.doma-guard
                    :newp-guard info.domb-guard
                    :forth-guard info.alpha-guard
                    :back-guard info.beta-guard
                    :hints nil)))
        (value (list isomap names-to-avoid)))
    (b* ((wrld (w state))
         (isoname (packn-pos (list 'defiso-isodata- old$ '- k) old$))
         (isoname (isodata-fresh-defiso-name-with-*s-suffix isoname wrld))
         ((mv forth-image
              back-image
              back-of-forth
              forth-of-back
              oldp-guard
              newp-guard
              forth-guard
              back-guard
              forth-injective
              back-injective
              names-to-avoid)
          (isodata-fresh-defiso-thm-names isoname
                                          verify-guards$
                                          names-to-avoid
                                          wrld))
         ((unless (true-listp iso))
          (er-soft+ ctx t nil
                    "The ~n0 ISO component ~x1 of the second input ~
                     must be a symbol or a list. ~
                     Since it is not an atom, it must be a list."
                    (list k) iso))
         ((unless (or (= (len iso) 4)
                      (= (len iso) 6)))
          (er-soft+ ctx t nil
                    "The ~n0 ISO component ~x1 of the second input ~
                     must be a list of length 4 or 6."
                    (list k) iso))
         (oldp (first iso))
         (newp (second iso))
         (forth (third iso))
         (back (fourth iso))
         ((unless (or (= (len iso) 4)
                      (eq (fifth iso) :hints)))
          (er-soft+ ctx t nil
                    "The fifth component ~x0 ~
                     of the ~n1 ISO component ~x2 ~
                     of the second input ~
                     must be the keyword :HINTS."
                    (fifth iso) (list k) iso))
         (hints (and (= (len iso) 6) (sixth iso)))
         (ctx-defiso (cons 'defiso isoname))
         ((er (list oldp$ newp$ forth$ back$))
          (acl2::defmapping-process-functions
           oldp newp forth back verify-guards$ ctx-defiso state))
         (oldp-arity (arity oldp$ wrld))
         ((unless (= oldp-arity 1))
          (er-soft+ ctx t nil
                    "The first component ~x0 ~
                     of the ~n1 ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x2 arguments instead."
                    oldp (list k) oldp-arity))
         (newp-arity (arity newp$ wrld))
         ((unless (= newp-arity 1))
          (er-soft+ ctx t nil
                    "The second component ~x0 ~
                     of the ~n1 ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x2 arguments instead."
                    newp (list k) newp-arity))
         (isomap (make-isodata-isomap
                  :isoname isoname
                  :localp t
                  :oldp oldp$
                  :newp newp$
                  :forth forth$
                  :back back$
                  :forth-image forth-image
                  :back-image back-image
                  :back-of-forth back-of-forth
                  :forth-of-back forth-of-back
                  :forth-injective forth-injective
                  :back-injective back-injective
                  :oldp-guard oldp-guard
                  :newp-guard newp-guard
                  :forth-guard forth-guard
                  :back-guard back-guard
                  :hints hints)))
      (value (list isomap names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-arg/res-list-iso
  ((arg/res-list-iso "The @('(arg/res-listk isok)') component of @('isomaps').")
   (k posp "The @('k') in @('(arg/res-listk isok)').")
   (old$ symbolp)
   (verify-guards$ booleanp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (names-to-avoid symbol-listp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-isomaps res-isomaps updated-names-to-avoid)')
                        satisfying @('(typed-tuplep isodata-symbol-isomap-alistp
                                                    isodata-pos-isomap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process an @('(arg/res-list iso)') component
          of the @('isomaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('arg-isomaps') and @('res-isomaps') inputs
     are obtained by having previously called this function
     on @('(arg/res-list1 iso1)'), ..., @('(arg/res-listk-1 isok-1)') in turn.
     When we call this function on @('(arg/res-listk isok)'),
     we extend @('arg-isomaps') and @('res-isomaps')
     with the information in @('(arg/res-listk isok)').
     As we do that, we check that
     the arguments of @('old') in @('arg/res-listk') are not
     already keys in @('arg-isomaps'):
     if any of them did, it would mean that it is already present
     in one of @('(arg/res-list1 iso1)'), ..., @('(arg/res-listk-1 isok-1)'),
     violating the disjointness requirement.
     Similarly, we check that the result indices in @('arg/res-listk') are not
     already keys in @('res-isomaps'):
     if any of them did, it would mean that the same result is already present
     in one of @('(arg/res-list1 iso1)'), ..., @('(arg/res-listk-1 isok-1)'),
     violating the disjointness requirement."))
  (b* (((er &) (ensure-tuple$ arg/res-list-iso 2
                              (msg "The ~n0 component of the second input"
                                   (list k))
                              t nil))
       (arg/res-list (first arg/res-list-iso))
       (iso (second arg/res-list-iso))
       ((er (list args ress)) (isodata-process-arg/res-list
                               arg/res-list k old$ ctx state))
       (arg-overlap (intersection-eq args (strip-cars arg-isomaps)))
       ((when arg-overlap)
        (er-soft+ ctx t nil
                  "The ~n0 component of the second input includes ~&1, ~
                   which are also present in the preceding components. ~
                   This violates the disjointness requirement."
                  (list k) arg-overlap))
       (res-overlap (intersection$ ress (strip-cars res-isomaps)))
       ((when res-overlap)
        (er-soft+ ctx t nil
                  "The ~n0 component of the second input includes ~
                   the ~s1 ~&2, ~
                   which ~s3 also present in the preceding components. ~
                   This violates the disjointness requirement."
                  (list k)
                  (if (= (len res-overlap) 1)
                      "result with index"
                    "results with indices")
                  res-overlap
                  (if (= (len res-overlap) 1)
                      "is"
                    "are")))
       ((er (list isomap names-to-avoid)) (isodata-process-iso iso
                                                               k
                                                               old$
                                                               verify-guards$
                                                               names-to-avoid
                                                               ctx
                                                               state))
       (arg-isomaps
        (isodata-process-arg/res-list-iso-add-args args isomap arg-isomaps))
       (res-isomaps
        (isodata-process-arg/res-list-iso-add-ress ress isomap res-isomaps)))
    (value (list arg-isomaps res-isomaps names-to-avoid)))

  :prepwork

  ((define isodata-process-arg/res-list-iso-add-args
     ((args symbol-listp)
      (isomap isodata-isomapp)
      (arg-isomaps isodata-symbol-isomap-alistp))
     :returns (new-arg-isomaps isodata-symbol-isomap-alistp :hyp :guard)
     (cond ((endp args) arg-isomaps)
           (t (isodata-process-arg/res-list-iso-add-args
               (cdr args)
               isomap
               (acons (car args) isomap arg-isomaps)))))

   (define isodata-process-arg/res-list-iso-add-ress
     ((ress pos-listp)
      (isomap isodata-isomapp)
      (res-isomaps isodata-pos-isomap-alistp))
     :returns (new-res-isomaps isodata-pos-isomap-alistp :hyp :guard)
     (cond ((endp ress) res-isomaps)
           (t (isodata-process-arg/res-list-iso-add-ress
               (cdr ress) isomap (acons (car ress) isomap res-isomaps)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-arg/res-list-iso-list
  ((arg/res-list-iso-list)
   (k posp)
   (old$ symbolp)
   (verify-guards$ booleanp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (names-to-avoid symbol-listp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-isomaps res-isomaps update-names-to-avoid)')
                        satisfying @('(typed-tuplep isodata-symbol-isomap-alistp
                                                    isodata-pos-isomap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Lift @(tsee isodata-process-arg/res-list-iso) to lists."
  (b* (((when (endp arg/res-list-iso-list))
        (value (list arg-isomaps res-isomaps names-to-avoid)))
       ((er (list arg-isomaps res-isomaps names-to-avoid))
        (isodata-process-arg/res-list-iso (car arg/res-list-iso-list)
                                          k
                                          old$
                                          verify-guards$
                                          arg-isomaps
                                          res-isomaps
                                          names-to-avoid
                                          ctx
                                          state)))
    (isodata-process-arg/res-list-iso-list (cdr arg/res-list-iso-list)
                                           (1+ k)
                                           old$
                                           verify-guards$
                                           arg-isomaps
                                           res-isomaps
                                           names-to-avoid
                                           ctx
                                           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-isomaps (isomaps
                                 (old$ symbolp)
                                 (verify-guards$ booleanp)
                                 (names-to-avoid symbol-listp)
                                 ctx
                                 state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-isomaps res-isomaps update-names-to-avoid)')
                        satisfying @('(typed-tuplep isodata-symbol-isomap-alistp
                                                    isodata-pos-isomap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @('isomaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the empty alists for @('arg-isomaps') and @('res-isomap'),
     we repeatedly process each @('(arg/res-listk isok)') element,
     accumulating the processing results
     into @('arg-isomaps') and @('res-isomaps').
     Then we reconstruct a possible larger @('arg-isomaps')
     by going through the formal parameters of @('old') in order,
     and associating them, in the new alist, with
     either the corresponding value in the old alist,
     or the identity isomorphic mapping.
     If the final @('res-isomaps') is not empty,
     we similarly reconstruct a possibly larger @('res-isomaps')
     by going through the integers from 1 to @('m') in order,
     and associating them, in the new alist, with
     either the corresponding value in the old alist,
     or the identity isomorphic mapping."))
  (b* ((wrld (w state))
       ((unless (true-listp isomaps))
        (er-soft+ ctx t nil
                  "The second input must be a true list, ~
                   but it is ~x0 instead." isomaps))
       ((unless (>= (len isomaps) 1))
        (er-soft+ ctx t nil
                  "The second input must be a non-empty list, ~
                   but it is ~x0 instead." isomaps))
       ((er (list arg-isomaps res-isomaps names-to-avoid))
        (isodata-process-arg/res-list-iso-list
         isomaps 1 old$ verify-guards$ nil nil names-to-avoid ctx state))
       (isoname-id
        (isodata-fresh-defiso-name-with-*s-suffix 'defiso-identity wrld))
       ((mv forth-image-id
            back-image-id
            back-of-forth-id
            forth-of-back-id
            oldp-guard-id
            newp-guard-id
            forth-guard-id
            back-guard-id
            forth-injective-id
            back-injective-id
            names-to-avoid)
        (isodata-fresh-defiso-thm-names isoname-id
                                        verify-guards$
                                        names-to-avoid
                                        wrld))
       (isomap-id (make-isodata-isomap
                   :isoname isoname-id
                   :localp t
                   :oldp '(lambda (x) 't)
                   :newp '(lambda (x) 't)
                   :forth '(lambda (x) x)
                   :back '(lambda (x) x)
                   :back-image back-image-id
                   :forth-image forth-image-id
                   :back-of-forth back-of-forth-id
                   :forth-of-back forth-of-back-id
                   :forth-injective forth-injective-id
                   :back-injective back-injective-id
                   :oldp-guard oldp-guard-id
                   :newp-guard newp-guard-id
                   :forth-guard forth-guard-id
                   :back-guard back-guard-id
                   :hints nil))
       (formals (formals old$ wrld))
       (arg-isomaps (isodata-process-isomaps-args formals
                                                  arg-isomaps
                                                  isomap-id))
       (res-isomaps (and res-isomaps
                         (isodata-process-isomaps-ress 1
                                                       (number-of-results
                                                        old$ wrld)
                                                       res-isomaps
                                                       isomap-id))))
    (value (list arg-isomaps res-isomaps names-to-avoid)))

  :prepwork

  ((define isodata-process-isomaps-args
     ((formals symbol-listp)
      (arg-isomaps isodata-symbol-isomap-alistp)
      (isomap-id isodata-isomapp))
     :returns (new-arg-isomaps isodata-symbol-isomap-alistp :hyp :guard)
     (b* (((when (endp formals)) nil)
          (pair (assoc-eq (car formals) arg-isomaps)))
       (if (consp pair)
           (cons pair (isodata-process-isomaps-args (cdr formals)
                                                    arg-isomaps
                                                    isomap-id))
         (acons (car formals)
                isomap-id
                (isodata-process-isomaps-args (cdr formals)
                                              arg-isomaps
                                              isomap-id))))
     :verify-guards nil ; done below
     ///
     (verify-guards isodata-process-isomaps-args
       :hints (("Goal"
                :in-theory
                (enable alistp-when-isodata-symbol-isomap-alistp-rewrite)))))

   (define isodata-process-isomaps-ress ((j posp)
                                         (m posp)
                                         (res-isomaps isodata-pos-isomap-alistp)
                                         (isomap-id isodata-isomapp))
     :returns (new-res-isomaps isodata-pos-isomap-alistp :hyp :guard)
     (b* (((unless (mbt (and (posp j) (posp m)))) nil)
          ((when (> j m)) nil)
          (pair (assoc j res-isomaps)))
       (if (consp pair)
           (cons pair (isodata-process-isomaps-ress (1+ j)
                                                    m
                                                    res-isomaps
                                                    isomap-id))
         (acons j
                isomap-id
                (isodata-process-isomaps-ress (1+ j)
                                              m
                                              res-isomaps
                                              isomap-id))))
     :measure (nfix (- (1+ (pos-fix m)) (pos-fix j)))
     :verify-guards nil ; done below
     ///
     (verify-guards isodata-process-isomaps-ress
       :hints (("Goal"
                :in-theory
                (enable alistp-when-isodata-pos-isomap-alistp-rewrite)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-newp-of-new-name (newp-of-new-name
                                          (new$ symbolp)
                                          (names-to-avoid symbol-listp)
                                          ctx
                                          state)
  :returns (mv erp
               (result "A list @('(newp-of-new$ update-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':newp-of-new-name') input."
  (b* (((er &)
        (ensure-value-is-symbol$
         newp-of-new-name "The :NEWP-OF-NEW-NAME input" t nil))
       (newp-of-new$ (case newp-of-new-name
                       (:auto (add-suffix new$ "-NEW-REPRESENTATION"))
                       (t newp-of-new-name)))
       (description (msg "The name ~x0 of the theorem asserting that ~
                          the new function ~x1 maps ~
                          arguments in the new representation ~
                          to results in the new representation, ~@2,"
                         newp-of-new$
                         new$
                         (if (eq newp-of-new-name :auto)
                             "automatically generated ~
                              since the :NEWP-OF-NEW-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :NEWP-OF-NEW-NAME input")))
       (error-msg? (fresh-namep-msg-weak newp-of-new$ nil (w state)))
       ((when error-msg?)
        (er-soft+ ctx t nil
                  "~@0 must be a valid fresh theorem name. ~@1"
                  description error-msg?))
       ((er &) (ensure-value-is-not-in-list$
                newp-of-new$
                names-to-avoid
                (msg "among the names ~x0 of other events ~
                      generated by this transformation"
                     names-to-avoid)
                description
                t
                nil)))
    (value (list newp-of-new$ (cons newp-of-new$ names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-inputs (old
                                isomaps
                                predicate
                                new-name
                                new-enable
                                old-to-new-name
                                (old-to-new-name-suppliedp booleanp)
                                old-to-new-enable
                                (old-to-new-enable-suppliedp booleanp)
                                new-to-old-name
                                (new-to-old-name-suppliedp booleanp)
                                new-to-old-enable
                                (new-to-old-enable-suppliedp booleanp)
                                newp-of-new-name
                                (newp-of-new-name-suppliedp booleanp)
                                newp-of-new-enable
                                (newp-of-new-enable-suppliedp booleanp)
                                verify-guards
                                untranslate
                                hints
                                print
                                show-only
                                ctx
                                state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    arg-isomaps
                                    res-isomaps
                                    new$
                                    new-enable$
                                    old-to-new$
                                    old-to-new-enable$
                                    new-to-old$
                                    new-to-old-enable$
                                    newp-of-new$
                                    newp-of-new-enable$
                                    verify-guards$
                                    hints$
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         isodata-symbol-isomap-alistp
                                         isodata-pos-isomap-alistp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         evmac-input-hints-p
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((er old$) (isodata-process-old old predicate verify-guards ctx state))
       ((er (list new$ names-to-avoid))
        (process-input-new-name new-name old$ nil ctx state))
       ((er (list old-to-new$ names-to-avoid))
        (process-input-old-to-new-name old-to-new-name
                                       old-to-new-name-suppliedp
                                       old$
                                       new$
                                       names-to-avoid
                                       ctx
                                       state))
       ((er (list new-to-old$ names-to-avoid))
        (process-input-new-to-old-name new-to-old-name
                                       new-to-old-name-suppliedp
                                       old$
                                       new$
                                       names-to-avoid
                                       ctx
                                       state))
       ((er (list newp-of-new$ names-to-avoid))
        (isodata-process-newp-of-new-name newp-of-new-name
                                          new$
                                          names-to-avoid
                                          ctx
                                          state))
       ((er verify-guards$) (process-input-verify-guards verify-guards
                                                         old$
                                                         ctx
                                                         state))
       ((er (list arg-isomaps res-isomaps names-to-avoid))
        (isodata-process-isomaps isomaps
                                 old$
                                 verify-guards$
                                 names-to-avoid
                                 ctx
                                 state))
       ((er &) (ensure-value-is-boolean$ predicate
                                         "The :PREDICATE input" t nil))
       ((er new-enable$) (process-input-new-enable new-enable old$ ctx state))
       ((er old-to-new-enable$) (process-input-old-to-new-enable
                                 old-to-new-enable
                                 old-to-new-enable-suppliedp
                                 ctx
                                 state))
       ((er new-to-old-enable$) (process-input-new-to-old-enable
                                 new-to-old-enable
                                 new-to-old-enable-suppliedp
                                 ctx
                                 state))
       ((when (and old-to-new-enable$
                   new-to-old-enable$))
        (er-soft+ ctx t nil
                  (if old-to-new-enable-suppliedp
                      (if new-to-old-enable-suppliedp
                          "The :OLD-TO-NEW-ENABLE input ~
                           and the :NEW-TO-OLD-ENABLE inputs ~
                           cannot be both T."
                        "Since the default :NEW-TO-OLD-ENABLE input is T, ~
                         the :OLD-TO-NEW-ENABLE input cannot be T.")
                    (if new-to-old-enable-suppliedp
                        "Since the default :OLD-TO-NEW-ENABLE input is T, ~
                         the :NEW-TO-OLD-ENABLE input cannot be T."
                      "Internal error: ~
                       the default :OLD-TO-NEW-ENABLE and :NEW-TO-OLD-ENABLE ~
                       are both T."))))
       ((er &) (ensure-value-is-boolean$ newp-of-new-enable
                                         "The :NEWP-OF-NEW-ENABLE input"
                                         t nil))
       ((when (and newp-of-new-name-suppliedp
                   (not res-isomaps)))
        (er-soft+ ctx t nil
                  "Since no results are being transformed, ~
                   it is an error to supply the :NEWP-OF-NEW-NAME input."))
       ((when (and newp-of-new-enable-suppliedp
                   (not res-isomaps)))
        (er-soft+ ctx t nil
                  "Since no results are being transformed, ~
                   it is an error to supply the :NEWP-OF-NEW-ENABLE input."))
       ((er &) (ensure-is-untranslate-specifier$ untranslate
                                                 "The :UNTRANSLATE input"
                                                 t nil))
       ((er hints$) (evmac-process-input-hints hints ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 arg-isomaps
                 res-isomaps
                 new$
                 new-enable$
                 old-to-new$
                 old-to-new-enable$
                 new-to-old$
                 new-to-old-enable$
                 newp-of-new$
                 newp-of-new-enable
                 verify-guards$
                 hints$
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation isodata
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-defiso ((isomap isodata-isomapp)
                            (verify-guards$ booleanp)
                            (print$ evmac-input-print-p))
  :guard (isodata-isomap->localp isomap)
  :returns (event pseudo-event-formp)
  :short "Generate a local @(tsee defiso)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the @('iso') input is not a name,
     @('isodata') internally generates and uses a @(tsee defiso),
     so that the rest of the generated events can uniformly rely
     on a @(tsee defiso) that has established the isomorphic mapping.")
   (xdoc::p
    "This event is local to the @(tsee encapsulate)
     generated by @('isodata').")
   (xdoc::p
    "Since the @(tsee defiso) is local,
     we normally do not want to print its result or info output.
     But we want to print errors.
     So we pass @(':error') as the @(':print') input.
     However, if @(tsee isodata)'s @(':print') input is @(':all'),
     the we use @(':all') for @(tsee defiso)'s @(':print') input as well.")
   (xdoc::p
    "This is also used for the identity isomorphic mapping,
     which is also locally generated."))
  (b* (((isodata-isomap isomap) isomap)
       (name isomap.isoname)
       (doma isomap.oldp)
       (domb isomap.newp)
       (alpha isomap.forth)
       (beta isomap.back)
       (unconditional nil)
       (guard-thms verify-guards$)
       (nonguard-thm-names (list :alpha-image isomap.forth-image
                                 :beta-image isomap.back-image
                                 :beta-of-alpha isomap.back-of-forth
                                 :alpha-of-beta isomap.forth-of-back
                                 :alpha-injective isomap.forth-injective
                                 :beta-injective isomap.back-injective))
       (guard-thm-names? (and guard-thms
                              (list :doma-guard isomap.oldp-guard
                                    :domb-guard isomap.newp-guard
                                    :alpha-guard isomap.forth-guard
                                    :beta-guard isomap.back-guard)))
       (thm-names (append nonguard-thm-names guard-thm-names?))
       (hints isomap.hints)
       (print (if (eq print$ :all) :all :error)))
    `(local
      (defiso ,name ,doma ,domb ,alpha ,beta
        :unconditional ,unconditional
        :guard-thms ,guard-thms
        :thm-names ,thm-names
        :hints ,hints
        :print ,print))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-defisos ((isomaps isodata-isomap-listp)
                             (verify-guards$ booleanp)
                             (print$ evmac-input-print-p))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the local @(tsee defiso)s from a list."
  (b* (((when (endp isomaps)) nil)
       (isomap (car isomaps)))
    (if (isodata-isomap->localp isomap)
        (cons (isodata-gen-defiso isomap verify-guards$ print$)
              (isodata-gen-defisos (cdr isomaps) verify-guards$ print$))
      (isodata-gen-defisos (cdr isomaps) verify-guards$ print$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection isodata-gen-fn-of-terms
  :short "Generate a function to generate certain kinds of terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function generated by this macro
     generates the list @('((fn1 term1) (fn2 term2) ...)'),
     where @('(term1 term2 ...)') is the @('terms') input of the function,
     and where each @('fnk') is one of
     either @('oldpk'), @('newpk'), @('forthk'), and @('backk')
     or @('oldp_rk'), @('newp_rk'), @('forth_rk'), and @('back_rk').
     The choice of the @('fnk') functions is the input of the macro.
     The @('arg/res-isomaps') input of the generated function
     may be @('arg-isomaps') or @('res-isomaps').")
   (xdoc::@def "isodata-gen-fn-of-terms"))

  (defmacro isodata-gen-fn-of-terms (fn)
    (declare (xargs :guard (member-eq fn '(oldp newp forth back))))
    (b* ((name (packn (list 'isodata-gen- fn '-of-terms)))
         (string (str::downcase-string (symbol-name fn)))
         (selector (packn (list 'isodata-isomap-> fn))))
      `(define ,name ((terms pseudo-term-listp)
                      (arg/res-isomaps isodata-symbol-isomap-alistp))
         :guard (= (len terms) (len arg/res-isomaps))
         :returns (new-terms "A @(tsee pseudo-term-listp).")
         :verify-guards nil
         :short ,(str::cat "Apply the @('"
                           string
                           "k') or @('"
                           string
                           "_rk') function
                            to the corresponding term
                            in a list of terms of length equal to
                            the number of formals or results of @('old').")
         (b* (((when (endp terms)) nil)
              (term (car terms))
              (isomap (cdar arg/res-isomaps))
              (,fn (,selector isomap))
              (new-term (apply-term* ,fn term))
              (new-terms (,name (cdr terms) (cdr arg/res-isomaps))))
           (cons new-term new-terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-fn-of-terms oldp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-fn-of-terms newp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-fn-of-terms forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-fn-of-terms back)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-oldp-of-rec-call-args-under-contexts
  ((rec-calls pseudo-tests-and-call-listp)
   (arg-isomaps isodata-symbol-isomap-alistp))
  :returns (oldp-of-rec-call-args-under-contexts "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the conjunction of the implications,
          in the @(':oldp-of-rec-call-args') applicability condition,
          that correspond to the recursive calls of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function generates the subformula")
   (xdoc::codeblock
    "(and (implies context1<x1,...,xn>"
    "              (and (oldp update1-y1<x1,...,xn>)"
    "                   ..."
    "                   (oldp update1-yp<x1,...,xn>)))"
    "     ..."
    "     (implies contextm<x1,...,xn>"
    "              (and (oldp updatem-y1<x1,...,xn>)"
    "                   ..."
    "                   (oldp updatem-yp<x1,...,xn>))))")
   (xdoc::p
    "of the @(':oldp-of-rec-call-args') applicability condition."))
  (b* (((when (endp rec-calls)) *t*)
       (tests-and-call (car rec-calls))
       (tests (access tests-and-call tests-and-call :tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (context (conjoin tests)))
    (conjoin2
     (implicate context
                (conjoin (isodata-gen-oldp-of-terms (fargs rec-call)
                                                    arg-isomaps)))
     (isodata-gen-oldp-of-rec-call-args-under-contexts (cdr rec-calls)
                                                       arg-isomaps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-result-vars ((old$ symbolp) (m posp))
  :guard (> m 1)
  :returns (vars symbol-listp)
  :short "Generate variables for bounding results of @('old') or @('new')
          when they return multiple results."
  :long
  (xdoc::topstring
   (xdoc::p
    "When @('old') returns multiple results (and so @('new') does too),
     sometimes we need to generate @(tsee mv-let) calls
     that bind the multiple results to variables.
     This function generates these variables,
     which are always the symbols @('result1'), @('result2'), etc.
     It turns out that these symbols are always adequate:
     they are the only variables in the body of generated @(tsee mv-let)s,
     and they are distinct from the symbol @('mv')
     bound by the outer lambda expression in a translated @(tsee mv-let)
     (see @(tsee make-mv-let-call)"))
  (isodata-gen-result-vars-aux old$ 1 m)

  :prepwork
  ((define isodata-gen-result-vars-aux ((old$ symbolp) (j posp) (m posp))
     :returns (vars symbol-listp)
     (b* (((unless (mbt (posp j))) nil)
          ((unless (mbt (posp m))) nil)
          ((when (> j m)) nil)
          (name (str::cat "RESULT" (str::natstr j)))
          (var (intern-in-package-of-symbol name old$))
          (vars (isodata-gen-result-vars-aux old$ (1+ j) m)))
       (cons var vars))
     :measure (nfix (- (1+ (nfix m)) (nfix j))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-appconds ((old$ symbolp)
                              (arg-isomaps isodata-symbol-isomap-alistp)
                              (res-isomaps isodata-pos-isomap-alistp)
                              (predicate$ booleanp)
                              (verify-guards$ booleanp)
                              (wrld plist-worldp))
  :returns (appconds "A @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions."
  (b* ((x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (isodata-gen-oldp-of-terms x1...xn arg-isomaps))
       (oldp-of-x1...xn-conj (conjoin oldp-of-x1...xn))
       (old-guard (uguard old$ wrld))
       (old-call (fcons-term old$ x1...xn)))
    (append
     (make-evmac-appcond?
      :oldp-of-old
      (b* ((m (len res-isomaps)))
        (if (= m 1)
            (b* ((res-isomap (cdar res-isomaps))
                 (oldp-res (isodata-isomap->oldp res-isomap)))
              (implicate oldp-of-x1...xn-conj
                         (fcons-term* oldp-res old-call)))
          (b* ((y1...ym (isodata-gen-result-vars old$ m))
               (oldp-of-y1...ym (isodata-gen-oldp-of-terms
                                 y1...ym res-isomaps)))
            (implicate oldp-of-x1...xn-conj
                       (make-mv-let-call 'mv y1...ym :all old-call
                                         (conjoin oldp-of-y1...ym))))))
      :when res-isomaps)
     (make-evmac-appcond?
      :oldp-when-old
      (implicate old-call
                 oldp-of-x1...xn-conj)
      :when predicate$)
     (make-evmac-appcond?
      :oldp-of-rec-call-args
      (implicate oldp-of-x1...xn-conj
                 (isodata-gen-oldp-of-rec-call-args-under-contexts
                  (recursive-calls old$ wrld)
                  arg-isomaps))
      :when (irecursivep old$ wrld))
     (make-evmac-appcond?
      :old-guard
      (implicate old-guard
                 oldp-of-x1...xn-conj)
      :when (and verify-guards$
                 (not predicate$)))
     (make-evmac-appcond?
      :old-guard-pred
      (implicate oldp-of-x1...xn-conj
                 old-guard)
      :when (and verify-guards$
                 predicate$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines isodata-xform-rec-calls
  :short "Transform all the calls of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Turn each call  @('(old updatej-x1 ... updatej-xn)') inside a term
     into one of the following:")
   (xdoc::ul
    (xdoc::li
     "@('(new (forth1 updatej-x1) ... (forthn updatej-xn))'),
      if no results are transformed.")
    (xdoc::li
     "@('(back_r1 (new (forth1 updatej-x1) ... (forthn updatej-xn)))'),
      if @('old') is single-valued and its result is transformed.")
    (xdoc::li
     "@('(mv-let (y1 ... ym)
           (new (forth1 updatej-x1) ... (forthn updatej-xn))
           (mv (back_r1 y1) ... (back_rm ym)))'),
      if @('old') is multi-valued and some of its results are transformed."))
   (xdoc::p
    "This term transformation is an intermediate step
     in the construction of the body of @('new') from the body of @('old')."))
  :verify-guards nil

  (define isodata-xform-rec-calls ((term pseudo-termp)
                                   (old$ symbolp)
                                   (arg-isomaps isodata-symbol-isomap-alistp)
                                   (res-isomaps isodata-pos-isomap-alistp)
                                   (new$ symbolp))
    :returns new-term ; PSEUDO-TERMP
    (b* (((when (or (variablep term) (fquotep term))) term)
         (fn (ffn-symb term))
         ((when (eq fn old$))
          (b* ((new-call (fcons-term new$
                                     (isodata-gen-forth-of-terms (fargs term)
                                                                 arg-isomaps)))
               ((when (not res-isomaps)) new-call)
               (m (len res-isomaps)))
            (if (= m 1)
                (b* ((back-res (isodata-isomap->back (cdar res-isomaps))))
                  (apply-term* back-res new-call))
              (b* ((y1...ym (isodata-gen-result-vars old$ m))
                   (back-of-y1...ym (isodata-gen-back-of-terms y1...ym
                                                               res-isomaps)))
                (make-mv-let-call 'mv y1...ym :all new-call
                                  (fcons-term 'mv back-of-y1...ym))))))
         ((when (symbolp fn))
          (fcons-term fn
                      (isodata-xform-rec-calls-lst (fargs term)
                                                   old$
                                                   arg-isomaps
                                                   res-isomaps
                                                   new$)))
         (new-fn (make-lambda (lambda-formals fn)
                              (isodata-xform-rec-calls (lambda-body fn)
                                                       old$
                                                       arg-isomaps
                                                       res-isomaps
                                                       new$))))
      (fcons-term new-fn
                  (isodata-xform-rec-calls-lst (fargs term)
                                               old$
                                               arg-isomaps
                                               res-isomaps
                                               new$))))

  (define isodata-xform-rec-calls-lst
    ((terms pseudo-term-listp)
     (old$ symbolp)
     (arg-isomaps isodata-symbol-isomap-alistp)
     (res-isomaps isodata-pos-isomap-alistp)
     (new$ symbolp))
    :returns new-terms ; PSEUDO-TERM-LISTP
    (cond ((endp terms) nil)
          (t (cons (isodata-xform-rec-calls (car terms)
                                            old$
                                            arg-isomaps
                                            res-isomaps
                                            new$)
                   (isodata-xform-rec-calls-lst (cdr terms)
                                                old$
                                                arg-isomaps
                                                res-isomaps
                                                new$))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection isodata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn
  :short "Generate a function to generate certain kinds of lemma instances."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function generated by this macro
     generates a lemma instance of the form
     @('(:instance lemma (x1 (fn1 x1)) ... (xn (fnn xn)))'),
     where each @('fni') is either @('forthi') or @('backi').
     The choice of the @('fni') functions is the input of the macro.")
   (xdoc::@def "isodata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn"))

  (defmacro isodata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn (fn)
    (declare (xargs :guard (member-eq fn '(forth back))))
    (b* ((name
          (packn
           (list 'isodata-gen-lemma-instance-x1...xn-to- fn '-of-x1...xn)))
         (string (str::downcase-string (symbol-name fn)))
         (fn-of-x1...xn (packn (list fn '-of-x1...xn)))
         (isodata-gen-fn-of-terms (packn (list 'isodata-gen- fn '-of-terms))))
      `(define ,name ((lemma (or (symbolp lemma)
                                 (symbol-listp lemma))
                             "Lemma to generate an instance of.")
                      (old$ symbolp)
                      (arg-isomaps isodata-symbol-isomap-alistp)
                      (wrld plist-worldp))
         :guard (= (len (formals old$ wrld)) (len arg-isomaps))
         :returns (lemma-instance true-listp)
         :verify-guards nil
         :short ,(str::cat "Generate a lemma instance where
                            each variable @('xi') is instantiated with
                            @('(" string "i xi)').")
         (b* ((x1...xn (formals old$ wrld))
              (,fn-of-x1...xn (,isodata-gen-fn-of-terms x1...xn arg-isomaps))
              (inst (alist-to-doublets (pairlis$ x1...xn ,fn-of-x1...xn))))
           `(:instance ,lemma :extra-bindings-ok ,@inst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn back)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-subst-x1...xn-with-back-of-x1...xn
  ((term pseudo-termp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Substitute each formal @('xi') of @('old') in a term
          with the term @('(backi xi)'),
          where @('backi') is the conversion associated to @('xi')."
  (b* ((x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps)))
    (subcor-var x1...xn back-of-x1...xn term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-formal-of-unary ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of an (assumed) unary function."
  (cond ((symbolp fn) (car (formals fn wrld)))
        (t (car (lambda-formals fn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-formal-of-newp ((isomap isodata-isomapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('newp') predicate
          of an isomorphic mapping."
  (isodata-formal-of-unary (isodata-isomap->newp isomap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-formal-of-forth ((isomap isodata-isomapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('forth') conversion
          of an isomorphic mapping."
  (isodata-formal-of-unary (isodata-isomap->forth isomap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-formal-of-back ((isomap isodata-isomapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('back') conversion
          of an isomorphic mapping."
  (isodata-formal-of-unary (isodata-isomap->back isomap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection isodata-gen-thm-instances-to-x1...xn
  :short "Generate a function to generate certain kinds of lemma instances."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function generated by this macro
     generates a list of lemma instances of the form
     @('((:instance thm1 (var1 x1)) ... (:instance thmn (varn xn)))'),
     where each @('thmi') is one of
     @('forthi-image'),
     @('backi-image'),
     @('backi-of-forthi'),
     @('newpi-guard'),
     @('forthi-guard'), and
     @('backi-guard'),
     and where @('vari') is the formal parameter of (respectively)
     @('forthi'),
     @('backi'),
     @('forthi'),
     @('newpi'),
     @('forthi'), and
     @('backi').
     The choice of the @('thmi') theorems is the input of the macro,
     from which the choice of the @('vari') variables is derived.")
   (xdoc::@def "isodata-gen-thm-instances-to-x1...xn"))

  (defmacro isodata-gen-thm-instances-to-x1...xn (thm)
    (declare (xargs :guard (member-eq thm '(forth-image
                                            back-image
                                            back-of-forth
                                            newp-guard
                                            forth-guard
                                            back-guard))))
    (b* ((name (packn (list 'isodata-gen- thm '-instances-to-x1...xn)))
         (thm-selector (packn (list 'isodata-isomap-> thm)))
         (thm-string (case thm
                       (forth-image "forthi-image")
                       (back-image "backi-image")
                       (back-of-forth "backi-of-forthi")
                       (newp-guard "newpi-guard")
                       (forth-guard "forthi-guard")
                       (back-guard "backi-guard")
                       (t (impossible))))
         (fn (case thm
               (forth-image 'forth)
               (back-image 'back)
               (back-of-forth 'forth)
               (newp-guard 'newp)
               (forth-guard 'forth)
               (back-guard 'back)
               (t (impossible))))
         (fn-selector (packn (list 'isodata-isomap-> fn)))
         (fn-string (str::downcase-string (symbol-name fn)))
         (param (packn (list fn '-arg))))
      `(define ,name ((arg-isomaps isodata-symbol-isomap-alistp)
                      (wrld plist-worldp))
         :returns (lemma-instances true-list-listp)
         :verify-guards nil
         :short ,(str::cat "Generate @('n') lemma instances
                            such that the @('i')-th instance
                            is of theorem @('" thm-string "')
                            and instantiates
                            the formal parameter of @('" fn-string "')
                            with @('xi').")
         (b* (((when (endp arg-isomaps)) nil)
              (arg (caar arg-isomaps))
              (isomap (cdar arg-isomaps))
              (,thm (,thm-selector isomap))
              (,param (isodata-formal-of-unary (,fn-selector isomap) wrld))
              (instance (list :instance ,thm
                              :extra-bindings-ok (list ,param arg)))
              (instances (,name (cdr arg-isomaps) wrld)))
           (cons instance instances))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn forth-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn back-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn back-of-forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn newp-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn forth-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-x1...xn back-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection isodata-gen-thm-instances-to-terms-back
  :short "Generate functions to generate certain kinds of lemma instances."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first function generated by this macro
     generates a list of lemma instances of the form
     @('((:instance thm1 (var1 bterm1)) ... (:instance thmn (varn btermn)))'),
     where each @('thmi') is one of
     @('forthi-image'), @('backi-of-forthi'), and @('forthi-guard'),
     where @('vari') is the formal parameter of @('forthi'),
     and where @('btermi') is obtained by replacing
     @('x1'), ..., @('xn') with @('(back1 x1)'), ..., @('(backn xn)')
     in a term @('termi') that is part of
     a list of terms @('term1'), ..., @('termn')
     supplied as input to the function.
     The choice of the @('thmi') theorems is in the input of the macro,
     from which the choice of the @('vari') variables is derived.")
   (xdoc::p
    "The second function generated by this macro
     calls the first function once for each recursively call of @('old').
     Each such call of the first function is passed, as the @('terms') argument,
     the arguments of the corresponding recursive call of @('old').
     Each call of the first function generates @('n') lemma instances,
     thus if there are @('r') recursive calls
     a total of @('r * n') lemma instances are generated,
     which are all concatenated together in one list
     and returned by the second function generated by this macro.")
   (xdoc::@def "isodata-gen-thm-instances-to-terms-back"))

  (defmacro isodata-gen-thm-instances-to-terms-back (thm)
    (declare (xargs :guard (member-eq thm '(forth-image
                                            back-of-forth
                                            forth-guard))))
    (b* ((name1 (packn (list 'isodata-gen- thm '-instances-to-terms-back)))
         (name1-aux (packn (list name1 '-aux)))
         (name2 (packn (list 'isodata-gen-all- thm '-instances-to-terms-back)))
         (name1-string (str::downcase-string (symbol-name name1)))
         (thm-selector (packn (list 'isodata-isomap-> thm)))
         (thm-string (case thm
                       (forth-image "forthi-image")
                       (back-of-forth "backi-of-forthi")
                       (forth-guard "forthi-guard")
                       (t (impossible)))))
      `(progn
         (define ,name1 ((terms pseudo-term-listp)
                         (old$ symbolp)
                         (arg-isomaps isodata-symbol-isomap-alistp)
                         (wrld plist-worldp))
           :guard (= (len terms) (len arg-isomaps))
           :returns (lemma-instances true-list-listp)
           :verify-guards nil
           :short ,(str::cat "Generate @('n') lemma instances
                              such that the @('i')-th instance
                              is of theorem @('" thm-string "')
                              and instantiates
                              the formal parameter of @('forthi')
                              with a given term @('termi') in which
                              @('x1'), ..., @('xn') are replaced with
                              @('(back1 x1)'), ..., @('(backn xn)').")
           (b* ((x1...xn (formals old$ wrld))
                (back-of-x1...xn
                 (isodata-gen-back-of-terms x1...xn arg-isomaps)))
             (,name1-aux terms arg-isomaps x1...xn back-of-x1...xn wrld))
           :prepwork
           ((define ,name1-aux ((terms pseudo-term-listp)
                                (arg-isomaps isodata-symbol-isomap-alistp)
                                (x1...xn symbol-listp)
                                (back-of-x1...xn pseudo-term-listp)
                                (wrld plist-worldp))
              :guard (= (len terms) (len arg-isomaps))
              :returns (lemma-instances true-list-listp)
              :verify-guards nil
              (b* (((when (endp terms)) nil)
                   (term (car terms))
                   (isomap (cdar arg-isomaps))
                   (,thm (,thm-selector isomap))
                   (var (isodata-formal-of-forth isomap wrld))
                   (term-with-back (subcor-var x1...xn back-of-x1...xn term))
                   (instance (list :instance ,thm
                                   :extra-bindings-ok
                               (list var term-with-back)))
                   (instances (,name1-aux (cdr terms)
                                          (cdr arg-isomaps)
                                          x1...xn
                                          back-of-x1...xn
                                          wrld)))
                (cons instance instances)))))
         (define ,name2 ((rec-calls pseudo-tests-and-call-listp)
                         (old$ symbolp)
                         (arg-isomaps isodata-symbol-isomap-alistp)
                         (wrld plist-worldp))
           :returns (lemma-instances true-list-listp)
           :verify-guards nil
           :short ,(str::cat "Generate the concatenation of
                              all the @('n * r') lemma instances generated by
                              @('" name1-string "')
                              for all the recursive call arguments of @('old')
                              passed as the @('terms') input.")
           (b* (((when (endp rec-calls)) nil)
                (tests-and-call (car rec-calls))
                (rec-call (access tests-and-call tests-and-call :call))
                (updates (fargs rec-call))
                (instances (,name1 updates old$ arg-isomaps wrld))
                (more-instances (,name2 (cdr rec-calls) old$ arg-isomaps wrld)))
             (append instances more-instances)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-terms-back forth-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-terms-back back-of-forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(isodata-gen-thm-instances-to-terms-back forth-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate a lemma instance
          for each @('j')-th recursive call of @('old'),
          where each formal @('xi') of @('old') is instantiated with
          @('updatej-xi<(back1 x1),...,(backn xn)>'),
          i.e. the corresponding argument of the recursive call
          in which @('x1'), ..., @('xn') are replaced with
          @('(back1 x1)'), ..., @('(backn xn)')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (rec-call-args (fargs rec-call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (inst (alist-to-doublets (pairlis$ x1...xn rec-call-args-back)))
       (instance `(:instance ,lemma :extra-bindings-ok ,@inst))
       (instances (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back
                   lemma (cdr rec-calls) old$ arg-isomaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate a lemma instance
          for each @('j')-th recursive call of @('old'),
          where each formal @('xi') of @('old') is instantiated with
          @('(forthi updatej-xi<(back1 x1),...,(backn xn)>)'),
          i.e. @('forthi') applied to
          the corresponding arguments of the recursive call
          in which @('x1'), ..., @('xn') are replaced with
          @('(back1 x1)'), ..., @('(backn xn)')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (rec-call-args (fargs rec-call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (forth-rec-call-args-back
        (isodata-gen-forth-of-terms rec-call-args-back arg-isomaps))
       (inst (alist-to-doublets (pairlis$ x1...xn forth-rec-call-args-back)))
       (instance `(:instance ,lemma :extra-bindings-ok ,@inst))
       (instances
        (isodata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         lemma (cdr rec-calls) old$ arg-isomaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-rec-calls-back
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (old$ symbolp)
   (rec-calls pseudo-tests-and-call-listp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          a variable is instantiated with
          each recursive call of @('old'),
          with @('x1'), ..., @('xn') in such calls
          replaced with @('(back1 x1)'), ..., @('(backn xn)')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (rec-call-back (subcor-var x1...xn back-of-x1...xn rec-call))
       (instance `(:instance ,lemma :extra-bindings-ok (,var ,rec-call-back)))
       (instances (isodata-gen-lemma-instances-var-to-rec-calls-back
                   lemma var old$ (cdr rec-calls) arg-isomaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          a variable is instantiated with
          a call of the new function
          on @('forth1'), ..., @('forthn') applied to
          the arguments of a recursive call of @('old'),
          with @('x1'), ..., @('xn') in such arguments
          replaced with @('(back1 x1)'), ..., @('(backn xn)')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (rec-call-args (fargs rec-call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (forth-of-rec-call-args-back
        (isodata-gen-forth-of-terms rec-call-args-back arg-isomaps))
       (new-call (fcons-term new$ forth-of-rec-call-args-back))
       (instance `(:instance ,lemma :extra-bindings-ok (,var ,new-call)))
       (instances
        (isodata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
         lemma var (cdr rec-calls) old$ arg-isomaps new$ wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-back-of-forth-instances-to-mv-nth
  ((terms pseudo-term-listp)
   (res-isomaps isodata-pos-isomap-alistp)
   (wrld plist-worldp))
  :guard (= (len terms) (len res-isomaps))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate @('m') lemma instances
          such that the @('j')-th instance
          is of theorem @('back_rj-of-forth_rj')
          and instantiates
          the formal parameter of @('forth_rj')
          with @('(mv-nth j-1 ...)') applied to
          a given term @('termj')."
  (b* (((when (endp terms)) nil)
       (term (car terms))
       (j (caar res-isomaps))
       (isomap (cdar res-isomaps))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (var (isodata-formal-of-forth isomap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,back-of-forth
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (isodata-gen-back-of-forth-instances-to-mv-nth
                   (cdr terms)
                   (cdr res-isomaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-all-back-of-forth-instances-to-mv-nth
  ((rec-calls pseudo-tests-and-call-listp)
   (res-isomaps isodata-pos-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the concatenation of
          all the @('n * r') lemma instances generated by
          @('isodata-gen-back-of-forth-instances-to-mv-nth')
          for all the recursive call arguments of @('old')
          passed as the @('terms') input."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (updates (fargs rec-call))
       (instances (isodata-gen-back-of-forth-instances-to-mv-nth
                   updates res-isomaps wrld))
       (more-instances (isodata-gen-all-back-of-forth-instances-to-mv-nth
                        (cdr rec-calls) res-isomaps wrld)))
    (append instances more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-forth-image-instances-to-mv-nth
  ((term pseudo-termp)
   (res-isomaps isodata-pos-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate @('m') lemma instances
          such that the @('j')-th instance
          is of theorem @('forth_rj-image')
          and instantiates
          the formal parameter of @('forth_rj')
          with @('(mv-nth j-1 ...)') applied to
          a given term @('term')."
  (b* (((when (endp res-isomaps)) nil)
       (j (caar res-isomaps))
       (isomap (cdar res-isomaps))
       (forth-image (isodata-isomap->forth-image isomap))
       (var (isodata-formal-of-forth isomap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,forth-image
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (isodata-gen-forth-image-instances-to-mv-nth
                   term
                   (cdr res-isomaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-forth-guard-instances-to-mv-nth
  ((term pseudo-termp)
   (res-isomaps isodata-pos-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate @('m') lemma instances
          such that the @('j')-th instance
          is of theorem @('forth_rj-guard')
          and instantiates
          the formal parameter of @('forth_rj')
          with @('(mv-nth j-1 ...)') applied to
          a given term @('term')."
  (b* (((when (endp res-isomaps)) nil)
       (j (caar res-isomaps))
       (isomap (cdar res-isomaps))
       (forth-guard (isodata-isomap->back-of-forth isomap))
       (var (isodata-formal-of-forth isomap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,forth-guard
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (isodata-gen-forth-guard-instances-to-mv-nth
                   term
                   (cdr res-isomaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-back-guard-instances-to-mv-nth
  ((term pseudo-termp)
   (res-isomaps isodata-pos-isomap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate @('m') lemma instances
          such that the @('j')-th instance
          is of theorem @('back_rj-guard')
          and instantiates
          the formal parameter of @('back_rj')
          with @('(mv-nth j-1 ...)') applied to
          a given term @('term')."
  (b* (((when (endp res-isomaps)) nil)
       (j (caar res-isomaps))
       (isomap (cdar res-isomaps))
       (back-guard (isodata-isomap->back-guard isomap))
       (var (isodata-formal-of-back isomap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,back-guard
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (isodata-gen-back-guard-instances-to-mv-nth
                   term
                   (cdr res-isomaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-all-back-guard-instances-to-mv-nth
  ((old$ symbolp)
   (rec-calls pseudo-tests-and-call-listp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the concatenation of
          all the @('n * r') lemma instances generated by
          @('isodata-gen-back-guard-instances-to-mv-nth')
          for all the terms, passed as the @('term') input,
          of the form
          @('(new ... (forthi updatek-xi<...,(back xi),...>) ...)'),
          corresponding to all the recursive calls of @('old')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (updates (fargs rec-call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (updates-back (subcor-var-lst x1...xn back-of-x1...xn updates))
       (forth-updates-back (isodata-gen-forth-of-terms updates-back
                                                       arg-isomaps))
       (new-forth-updates-back (fcons-term new$ forth-updates-back))
       (instances (isodata-gen-back-guard-instances-to-mv-nth
                   new-forth-updates-back res-isomaps wrld))
       (more-instances
        (isodata-gen-all-back-guard-instances-to-mv-nth
         old$ (cdr rec-calls) arg-isomaps res-isomaps new$ wrld)))
    (append instances more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-guard ((old$ symbolp)
                                  (arg-isomaps isodata-symbol-isomap-alistp)
                                  (predicate$ booleanp)
                                  (wrld plist-worldp))
  :returns (new-guard "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the guard of the new function."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps)))
    (if predicate$
        (conjoin newp-of-x1...xn)
      (b* ((old-guard (uguard old$ wrld))
           (old-guard-with-back-of-x1...xn
            (isodata-gen-subst-x1...xn-with-back-of-x1...xn old-guard
                                                            old$
                                                            arg-isomaps
                                                            wrld)))
        (conjoin (append newp-of-x1...xn
                         (list old-guard-with-back-of-x1...xn)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-pred ((old$ symbolp)
                                      (arg-isomaps isodata-symbol-isomap-alistp)
                                      (res-isomaps isodata-pos-isomap-alistp)
                                      (new$ symbolp)
                                      (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function,
          when @(':predicate') is @('t')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('old') is non-executable,
     its body is obtained by removing
     the ``non-executable wrapper''.")
   (xdoc::p
    "First we transform any recursive calls via @('isodata-xform-rec-calls'),
     which causes no change if @('old') is not recursive.
     Then we replace @('x1'), ..., @('xn')
     with @('(back1 x1)'), ..., @('(backn xn)').
     Finally, we conjoin the result
     with @('(newp1 x1)'), ..., @('(newpn xn)')."))
  (b* ((x1...xn (formals old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls
         old-body old$ arg-isomaps res-isomaps new$))
       (old-body-with-back-of-x1...xn
        (isodata-gen-subst-x1...xn-with-back-of-x1...xn
         old-body-with-new-rec-calls
         old$
         arg-isomaps
         wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn)))
    (if (equal newp-of-x1...xn-conj *t*)
        old-body-with-back-of-x1...xn
      (conjoin2 `(mbt$ ,newp-of-x1...xn-conj)
                old-body-with-back-of-x1...xn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-nonpred
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   compatibility
   (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function,
          when @(':predicate') is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('old') is non-executable,
     its body is obtained
     by removing the ``non-executable wrapper''.")
   (xdoc::p
    "First we transform any recursive calls via @('isodata-xform-rec-calls'),
     which causes no change if @('old') is not recursive,
     and then we replace @('x1'), ..., @('xn')
     with @('(back1 x1)'), ..., @('(backn xn)');
     the resulting term is the code of the new function's body (see below).
     Then we construct an @(tsee if) as follows.
     The test is the conjunction of @('(newp1 x1)'), ..., @('(newpn xn)').
     The `else' branch is @('nil') or @('(mv nil ... nil')),
     depending on whether @('old') returns single or multiple results.
     For the `then' branch, there are three cases:
     (i) if no results are transformed, we use the core term above;
     (ii) if @('old') is single-valued and its (only) result is transformed,
     we apply the @('back') mapping of the result to the core term above; and
     (iii) if @('old') is multi-valued and some results are transformed,
     we bind the core term above to an @(tsee mv-let)
     and we apply the @('back') mappings of the results to the bound variables.
     The @(tsee if) is the final result,
     unless its test is just @('t'),
     in which case we omit test and `else' branch.
     If the compatibility flag is set and @('old') is non-recursive,
     we omit test and `else' branch as well;
     this is temporary.")
   (xdoc::p
    "The `else' branch should use quoted @('nil')s,
     but we use unquoted ones just so that the untranslation
     does not turn the @(tsee if) into an @(tsee and).
     Technically, the unquoted @('nil')s are ``variable'' (symbols),
     and thus untranslation leaves them alone."))
  (b* ((x1...xn (formals old$ wrld))
       (m (number-of-results old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls
         old-body old$ arg-isomaps res-isomaps new$))
       (old-body-with-back-of-x1...xn
        (isodata-gen-subst-x1...xn-with-back-of-x1...xn
         old-body-with-new-rec-calls
         old$
         arg-isomaps
         wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn))
       (then-branch
        (cond ((endp res-isomaps) old-body-with-back-of-x1...xn)
              ((endp (cdr res-isomaps))
               (apply-fn-into-ifs (isodata-isomap->forth (cdar res-isomaps))
                                  old-body-with-back-of-x1...xn))
              (t (b* ((y1...ym (isodata-gen-result-vars old$ m))
                      (forth-of-y1...ym (isodata-gen-forth-of-terms
                                         y1...ym res-isomaps)))
                   (make-mv-let-call 'mv y1...ym :all
                                     old-body-with-back-of-x1...xn
                                     (fcons-term 'mv forth-of-y1...ym))))))
       (else-branch (if (> m 1)
                        (fcons-term 'mv (repeat m nil))
                      nil)))
    (cond ((and compatibility
                (not (recursivep old$ nil wrld)) then-branch))
          ((equal newp-of-x1...xn-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-x1...xn-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body ((old$ symbolp)
                                 (arg-isomaps isodata-symbol-isomap-alistp)
                                 (res-isomaps isodata-pos-isomap-alistp)
                                 (predicate$ booleanp)
                                 (new$ symbolp)
                                 compatibility
                                 (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function."
  (if predicate$
      (isodata-gen-new-fn-body-pred old$ arg-isomaps res-isomaps new$ wrld)
    (isodata-gen-new-fn-body-nonpred
     old$ arg-isomaps res-isomaps new$ compatibility wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-measure ((old$ symbolp)
                                    (arg-isomaps isodata-symbol-isomap-alistp)
                                    (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the measure of the function, if recursive."
  (b* ((old-measure (measure old$ wrld)))
    (isodata-gen-subst-x1...xn-with-back-of-x1...xn old-measure
                                                    old$
                                                    arg-isomaps
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-termination-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the termination of the new function,
          if recursive."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (instance-termination-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:termination-theorem ,old$) old$ arg-isomaps wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args old$ arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-termination-thm-old
             ,@instances-back-image
             ,instance-oldp-of-rec-call-args
             ,@instances-back-of-forth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn ((old$ symbolp)
                            (arg-isomaps isodata-symbol-isomap-alistp)
                            (res-isomaps isodata-pos-isomap-alistp)
                            (predicate$ booleanp)
                            (new$ symbolp)
                            (new-enable$ booleanp)
                            (verify-guards$ booleanp)
                            (untranslate$ untranslate-specifier-p)
                            compatibility
                            (appcond-thm-names symbol-symbol-alistp)
                            (wrld plist-worldp))
  :returns (mv (new-fn-local-event "A @(tsee pseudo-event-formp).")
               (new-fn-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the new function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the new function is determined by
     whether the new function must be
     enabled or not, and non-executable or not.
     We make it non-executable if and only if @('old') is non-executable.")
   (xdoc::p
    "The new function has the same formal arguments as the old function.")
   (xdoc::p
    "If the new function is recursive,
     its well-founded relation is the same as the old function's.
     The new function uses all ruler extenders,
     in case the old function's termination depends on any ruler extender.")
   (xdoc::p
    "Guard verification is deferred;
     see @(tsee isodata-gen-new-fn-verify-guards).")
   (xdoc::p
    "If the old function returns a multi-value result,
     we adjust the body of the new function to do the same."))
  (b* ((macro (function-intro-macro new-enable$ (non-executablep old$ wrld)))
       (formals (formals old$ wrld))
       (body (isodata-gen-new-fn-body old$ arg-isomaps res-isomaps
                                      predicate$ new$ compatibility wrld))
       (body (if (> (number-of-results old$ wrld) 1)
                 (mvify body)
               body))
       (body (case untranslate$
               (:nice
                (directed-untranslate
                 (ibody old$ wrld) (ubody old$ wrld) body nil nil wrld))
               (:nice-expanded
                (directed-untranslate-no-lets
                 (ibody old$ wrld) (ubody old$ wrld) body nil nil wrld))
               (nil body)
               (t (untranslate body nil wrld))))
       (guard (isodata-gen-new-fn-guard old$ arg-isomaps predicate$ wrld))
       (guard (conjoin (flatten-ands-in-lit guard)))
       (guard (untranslate guard nil wrld))
       (recursive (recursivep old$ nil wrld))
       (wfrel? (if recursive
                   (well-founded-relation old$ wrld)
                 nil))
       (measure? (if recursive
                     (isodata-gen-new-fn-measure old$ arg-isomaps wrld)
                   nil))
       (termination-hints? (if recursive
                               (isodata-gen-new-fn-termination-hints
                                appcond-thm-names old$ arg-isomaps wrld)
                             nil))
       (local-event
        `(local
          (,macro ,new$ (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  :guard ,guard
                                  :verify-guards nil))
                  ,body)))
       (exported-event
        `(,macro ,new$ (,@formals)
                 (declare (xargs ,@(and recursive
                                        (list :well-founded-relation wfrel?
                                              :measure measure?
                                              :ruler-extenders :all))
                                 :guard ,guard
                                 :verify-guards ,verify-guards$))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-formula
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (new-to-old-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the new function in terms of the old function."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call (fcons-term old$ back-of-x1...xn))
       (new-call (fcons-term new$ x1...xn))
       (consequent
        (case (len res-isomaps)
          (0 `(equal ,new-call ,old-call))
          (1 (b* ((forth-res (isodata-isomap->forth (cdar res-isomaps)))
                  (forth-of-old-call (apply-term* forth-res old-call)))
               `(equal ,new-call ,forth-of-old-call)))
          (t (b* ((mv-nths-of-new-call (make-mv-nth-calls new-call
                                                          (len res-isomaps)))
                  (mv-nths-of-old-call (make-mv-nth-calls old-call
                                                          (len res-isomaps)))
                  (forth-of-mv-nths-of-old-call
                   (isodata-gen-forth-of-terms mv-nths-of-old-call
                                               res-isomaps)))
               (conjoin-equalities mv-nths-of-new-call
                                   forth-of-mv-nths-of-old-call))))))
    (implicate (conjoin newp-of-x1...xn)
               consequent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-nonrec ((old-fn-unnorm-name symbolp)
                                                 (new-fn-unnorm-name symbolp))
  :returns (hints true-listp)
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are not recursive."
  `(("Goal" :in-theory '(,old-fn-unnorm-name ,new-fn-unnorm-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-0res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and no result is being transformed."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld)))
    `(("Goal"
       :in-theory '(,old-fn-unnorm-name
                    ,new-fn-unnorm-name
                    (:induction ,new$))
       :induct (,new$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-call-args
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-1res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and the result of a single-value function is being transformed."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-oldp-of-old
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back
         oldp-of-old
         rec-calls
         old$
         arg-isomaps
         wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (res-isomap (cdar res-isomaps))
       (back-of-forth-res (isodata-isomap->back-of-forth res-isomap))
       (var (isodata-formal-of-forth res-isomap wrld))
       (instances-back-of-forth-res
        (isodata-gen-lemma-instances-var-to-rec-calls-back back-of-forth-res
                                                           var
                                                           old$
                                                           rec-calls
                                                           arg-isomaps
                                                           wrld)))
    `(("Goal"
       :in-theory '(,old-fn-unnorm-name
                    ,new-fn-unnorm-name
                    (:induction ,new$))
       :induct (,new$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-call-args
              ,@instances-oldp-of-old
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth
              ,@instances-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and some result of a multi-value function is being transformed."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-oldp-of-old
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back
         oldp-of-old
         rec-calls
         old$
         arg-isomaps
         wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-back-of-forth-res
        (isodata-gen-all-back-of-forth-instances-to-mv-nth rec-calls
                                                           res-isomaps
                                                           wrld)))
    `(("Goal"
       :in-theory '(,old-fn-unnorm-name
                    ,new-fn-unnorm-name
                    (:induction ,new$))
       :induct (,new$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-call-args
              ,@instances-oldp-of-old
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth
              ,@instances-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function."
  (if (recursivep old$ nil wrld)
      (case (len res-isomaps)
        (0 (isodata-gen-new-to-old-thm-hints-rec-0res appcond-thm-names
                                                      old$
                                                      arg-isomaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld))
        (1 (isodata-gen-new-to-old-thm-hints-rec-1res appcond-thm-names
                                                      old$
                                                      arg-isomaps
                                                      res-isomaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld))
        (t (isodata-gen-new-to-old-thm-hints-rec-mres appcond-thm-names
                                                      old$
                                                      arg-isomaps
                                                      res-isomaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld)))
    (isodata-gen-new-to-old-thm-hints-nonrec old-fn-unnorm-name
                                             new-fn-unnorm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (new-to-old$ symbolp)
   (new-to-old-enable$ booleanp)
   (appcond-thm-names symbol-symbol-alistp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (mv (new-to-old-local-event "A @(tsee pseudo-event-formp).")
               (new-to-old-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the @('new-to-old') theorem."
  (b* ((formula (isodata-gen-new-to-old-thm-formula old$
                                                    arg-isomaps
                                                    res-isomaps
                                                    new$
                                                    wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-new-to-old-thm-hints appcond-thm-names
                                                old$
                                                arg-isomaps
                                                res-isomaps
                                                new$
                                                old-fn-unnorm-name
                                                new-fn-unnorm-name
                                                wrld)))
    (evmac-generate-defthm new-to-old$
                           :formula formula
                           :hints hints
                           :enable new-to-old-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-formula
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (old-to-new-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the old function in terms of the new function."
  (b* ((x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (isodata-gen-oldp-of-terms x1...xn arg-isomaps))
       (forth-of-x1...xn (isodata-gen-forth-of-terms x1...xn arg-isomaps))
       (new-call (fcons-term new$ forth-of-x1...xn))
       (old-call (fcons-term old$ x1...xn))
       (consequent
        (case (len res-isomaps)
          (0 `(equal ,old-call ,new-call))
          (1 (b* ((back-res (isodata-isomap->back (cdar res-isomaps)))
                  (back-of-new-call (apply-term* back-res new-call)))
               `(equal ,old-call ,back-of-new-call)))
          (t (b* ((mv-nths-of-old-call (make-mv-nth-calls old-call
                                                          (len res-isomaps)))
                  (mv-nths-of-new-call (make-mv-nth-calls new-call
                                                          (len res-isomaps)))
                  (back-of-mv-nths-of-new-call
                   (isodata-gen-back-of-terms mv-nths-of-new-call
                                              res-isomaps)))
               (conjoin-equalities mv-nths-of-old-call
                                   back-of-mv-nths-of-new-call))))))
    (implicate (conjoin oldp-of-x1...xn)
               consequent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-hints-0res
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when no result is being transformed."
  (b* ((instances-forth-image
        (isodata-gen-forth-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-back-of-forth-instances-to-x1...xn arg-isomaps wrld))
       (instance-new-to-old
        (isodata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-isomaps
                                                                wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-hints-1res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when the result of a single-valued function is being transformed."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-forth-image
        (isodata-gen-forth-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-back-of-forth-instances-to-x1...xn arg-isomaps wrld))
       (instance-new-to-old
        (isodata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-isomaps
                                                                wrld))
       (res-isomap (cdar res-isomaps))
       (back-of-forth-res (isodata-isomap->back-of-forth res-isomap))
       (var (isodata-formal-of-forth res-isomap wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (instance-back-of-forth-res
        `(:instance ,back-of-forth-res :extra-bindings-ok (,var ,old-call))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old
             ,oldp-of-old
             ,instance-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-hints-mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when some result of a multi-valued function is being transformed."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-forth-image
        (isodata-gen-forth-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-back-of-forth-instances-to-x1...xn arg-isomaps wrld))
       (instance-new-to-old
        (isodata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-isomaps
                                                                wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (instances-back-of-forth-res
        (isodata-gen-back-of-forth-instances-to-mv-nth
         (repeat (len res-isomaps) old-call)
         res-isomaps
         wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old
             ,oldp-of-old
             ,@instances-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function."
  (case (len res-isomaps)
    (0 (isodata-gen-old-to-new-thm-hints-0res old$
                                              arg-isomaps
                                              new-to-old$
                                              wrld))
    (1 (isodata-gen-old-to-new-thm-hints-1res appcond-thm-names
                                              old$
                                              arg-isomaps
                                              res-isomaps
                                              new-to-old$
                                              wrld))
    (t (isodata-gen-old-to-new-thm-hints-mres appcond-thm-names
                                              old$
                                              arg-isomaps
                                              res-isomaps
                                              new-to-old$
                                              wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-to-new-enable$ booleanp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (mv (old-to-new-local-event "A @(tsee pseudo-event-formp).")
               (old-to-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the @('old-to-new') theorem."
  (b* ((formula (isodata-gen-old-to-new-thm-formula
                 old$ arg-isomaps res-isomaps new$ wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-old-to-new-thm-hints appcond-thm-names
                                                old$
                                                arg-isomaps
                                                res-isomaps
                                                new-to-old$
                                                wrld)))
    (evmac-generate-defthm old-to-new$
                           :formula formula
                           :hints hints
                           :enable old-to-new-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm-formula
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-isomaps)
  :returns (formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn))
       (new-call (fcons-term new$ x1...xn))
       (m (len res-isomaps)))
    (if (= m 1)
        (b* ((res-isomap (cdar res-isomaps))
             (newp-res (isodata-isomap->newp res-isomap)))
          (implicate newp-of-x1...xn-conj
                     (fcons-term* newp-res new-call)))
      (b* ((y1...ym (isodata-gen-result-vars new$ m))
           (newp-of-y1...ym (isodata-gen-newp-of-terms y1...ym res-isomaps)))
        (implicate newp-of-x1...xn-conj
                   (make-mv-let-call 'mv y1...ym :all new-call
                                     (conjoin newp-of-y1...ym)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-isomaps)
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to prove the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-image
        (if (= (len res-isomaps) 1)
            (b* ((res-isomap (cdar res-isomaps))
                 (forth-image-res (isodata-isomap->forth-image res-isomap))
                 (var (isodata-formal-of-forth res-isomap wrld)))
              `((:instance ,forth-image-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (isodata-gen-forth-image-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-isomaps
                                                       wrld))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-back-image
             ,instance-oldp-of-old
             ,@instances-forth-image
             ,new-to-old$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (new-to-old$ symbolp)
   (newp-of-new$ symbolp)
   (newp-of-new-enable$ booleanp)
   (appcond-thm-names symbol-symbol-alistp)
   (wrld plist-worldp))
  :guard (consp res-isomaps)
  :returns (mv (newp-of-new-local-event "A @(tsee pseudo-event-formp).")
               (newp-of-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that says that
          the new function maps values in the new representation
          to values in the old representation."
  (b* ((formula (isodata-gen-newp-of-new-thm-formula old$
                                                     arg-isomaps
                                                     res-isomaps
                                                     new$
                                                     wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-newp-of-new-thm-hints appcond-thm-names
                                                 old$
                                                 arg-isomaps
                                                 res-isomaps
                                                 new-to-old$
                                                 wrld)))
    (evmac-generate-defthm newp-of-new$
                           :formula formula
                           :hints hints
                           :enable newp-of-new-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-pred-nonrec
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when non-recursive and when @(':predicate') is @('t')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((old-guard-pred (cdr (assoc-eq :old-guard-pred appcond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn old-guard-pred
                                                               old$
                                                               arg-isomaps
                                                               wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard
             ,instance-old-guard-pred
             ,@instances-back-image)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-pred-rec
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when recursive and when @(':predicate') is @('t')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     appcond-thm-names)))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred
                              appcond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-guard
        (isodata-gen-forth-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn old-guard-pred
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-new-to-old
        (isodata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         new-to-old$
         rec-calls
         old$
         arg-isomaps
         wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-newp-guard
             ,@instances-forth-guard
             ,@instances-back-guard
             ,@instances-forth-image
             ,@instances-back-image
             ,@instances-back-of-forth
             ,instance-guard-thm-old
             ,instance-old-guard-pred
             ,instance-oldp-of-rec-call-args
             ,@instances-new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-pred
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('t')."
  (if (recursivep old$ nil wrld)
      (isodata-gen-new-fn-verify-guards-hints-pred-rec appcond-thm-names
                                                       old$
                                                       arg-isomaps
                                                       new-to-old$
                                                       wrld)
    (isodata-gen-new-fn-verify-guards-hints-pred-nonrec appcond-thm-names
                                                        old$
                                                        arg-isomaps
                                                        wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-0res
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and no result is being transformed."
  (b* ((instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-1res/mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (old-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :guard (consp res-isomaps)
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and some result is being transformed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-guard-res
        (if (= (len res-isomaps) 1)
            (b* ((res-isomap (cdar res-isomaps))
                 (forth-guard-res (isodata-isomap->forth-guard res-isomap))
                 (var (isodata-formal-of-forth res-isomap wrld)))
              `((:instance ,forth-guard-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (isodata-gen-forth-guard-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-isomaps
                                                       wrld)))
       (instance-old-fn-unnorm-name
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         old-fn-unnorm-name
         old$
         arg-isomaps
         wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard
             ,@instances-back-image
             ,instance-oldp-of-old
             ,@instances-forth-guard-res
             ,instance-old-fn-unnorm-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-rec-0res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (old-to-new$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') does not include @(':result')."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-guard
        (isodata-gen-all-forth-guard-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-old-to-new
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back old-to-new$
                                                                   rec-calls
                                                                   old$
                                                                   arg-isomaps
                                                                   wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-newp-guard
             ,@instances-forth-guard
             ,@instances-back-guard
             ,@instances-forth-image
             ,@instances-back-image
             ,@instances-back-of-forth
             ,instance-guard-thm-old
             ,instance-oldp-of-rec-call-args
             ,@instances-old-to-new)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-rec-1res/mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-isomaps)
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') includes @(':result')."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (rec-calls (recursive-calls old$ wrld))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instances-newp-guard
        (isodata-gen-newp-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-guard
        (isodata-gen-all-forth-guard-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-guard
        (isodata-gen-back-guard-instances-to-x1...xn arg-isomaps wrld))
       (instances-forth-image
        (isodata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-isomaps
                                                             wrld))
       (instances-back-image
        (isodata-gen-back-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-isomaps
         wrld))
       (instances-old-to-new
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back old-to-new$
                                                                   rec-calls
                                                                   old$
                                                                   arg-isomaps
                                                                   wrld))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-isomaps
                                                               wrld))
       (instance-old-fn-unnorm-name
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         old-fn-unnorm-name
         old$
         arg-isomaps
         wrld))
       (instances-newp-of-new
        (isodata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         newp-of-new$
         rec-calls
         old$
         arg-isomaps
         wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-guard-res
        (if (= (len res-isomaps) 1)
            (b* ((res-isomap (cdar res-isomaps))
                 (forth-guard-res (isodata-isomap->forth-guard res-isomap))
                 (var (isodata-formal-of-forth res-isomap wrld)))
              `((:instance ,forth-guard-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (isodata-gen-forth-guard-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-isomaps
                                                       wrld)))
       (instances-back-guard-res
        (if (= (len res-isomaps) 1)
            (b* ((res-isomap (cdar res-isomaps))
                 (back-guard-res (isodata-isomap->back-guard res-isomap))
                 (var (isodata-formal-of-back res-isomap wrld)))
              (isodata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
               back-guard-res
               var
               rec-calls
               old$
               arg-isomaps
               new$
               wrld))
          (isodata-gen-all-back-guard-instances-to-mv-nth old$
                                                          rec-calls
                                                          arg-isomaps
                                                          res-isomaps
                                                          new$
                                                          wrld))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-newp-guard
             ,@instances-forth-guard
             ,@instances-back-guard
             ,@instances-forth-image
             ,@instances-back-image
             ,@instances-back-of-forth
             ,instance-guard-thm-old
             ,instance-oldp-of-rec-call-args
             ,@instances-old-to-new
             ,instance-oldp-of-old
             ,instance-old-fn-unnorm-name
             ,@instances-newp-of-new
             ,@instances-forth-guard-res
             ,@instances-back-guard-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('nil')."
  (if (recursivep old$ nil wrld)
      (if (consp res-isomaps)
          (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-1res/mres
           appcond-thm-names
           old$
           arg-isomaps
           res-isomaps
           new$
           old-to-new$
           old-fn-unnorm-name
           newp-of-new$
           wrld)
        (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-0res
         appcond-thm-names
         old$
         arg-isomaps
         old-to-new$
         wrld))
    (if (consp res-isomaps)
        (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-1res/mres
         appcond-thm-names
         old$
         arg-isomaps
         res-isomaps
         old-fn-unnorm-name
         wrld)
      (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-0res old$
                                                                  arg-isomaps
                                                                  wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (predicate$ booleanp)
   (new-to-old$ symbolp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function."
  (if predicate$
      (isodata-gen-new-fn-verify-guards-hints-pred appcond-thm-names
                                                   old$
                                                   arg-isomaps
                                                   new-to-old$
                                                   wrld)
    (isodata-gen-new-fn-verify-guards-hints-nonpred appcond-thm-names
                                                    old$
                                                    arg-isomaps
                                                    res-isomaps
                                                    new$
                                                    old-to-new$
                                                    old-fn-unnorm-name
                                                    newp-of-new$
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (predicate$ booleanp)
   (new$ symbolp)
   (new-to-old$ symbolp)
   (old-to-new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new$ symbolp)
   (wrld plist-worldp))
  :returns (new-fn-verify-guards-event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the event to verify the guards of the new function."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned elsewhere,
     the verification of the guards of the new function,
     when it has to take place,
     is deferred when the function is introduced.
     The reason is that, as shown in the design notes,
     the guard verification proof for the recursive case
     uses the theorem that relates the old and new functions:
     thus, the theorem must be proved before guard verification,
     and the new function must be introduced before proving the theorem.
     In the non-recursive case, we could avoid deferring guard verification,
     but we defer it anyhow for uniformity.")
   (xdoc::p
    "The guard verification event
     is local to the @(tsee encapsulate) generated by the transformation.
     This keeps the event history after the transformation ``clean'',
     without implementation-specific proof hints
     that may refer to local events of the @(tsee encapsulate)
     that do not exist in the history after the transformation."))
  (b* ((hints (isodata-gen-new-fn-verify-guards-hints appcond-thm-names
                                                      old$
                                                      arg-isomaps
                                                      res-isomaps
                                                      predicate$
                                                      new-to-old$
                                                      new$
                                                      old-to-new$
                                                      old-fn-unnorm-name
                                                      newp-of-new$
                                                      wrld))
       (event `(local (verify-guards ,new$ :hints ,hints))))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-everything
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (predicate$ booleanp)
   (new$ symbolp)
   (new-enable$ booleanp)
   (old-to-new$ symbolp)
   (old-to-new-enable$ booleanp)
   (new-to-old$ symbolp)
   (new-to-old-enable$ symbolp)
   (newp-of-new$ symbolp)
   (newp-of-new-enable$ symbolp)
   (verify-guards$ booleanp)
   (untranslate$ untranslate-specifier-p)
   (hints$ symbol-truelist-alistp)
   (print$ evmac-input-print-p)
   (show-only$ booleanp)
   compatibility
   (names-to-avoid symbol-listp)
   (call pseudo-event-formp)
   ctx
   state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the top-level event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a @(tsee progn) that consists of
     the expansion of @(tsee isodata) (the @(tsee encapsulate)),
     followed by an event to extend the transformation table,
     optionally followed by events to print the exported events
     (if specified by the @(':print') input).
     The @(tsee progn) ends with @(':invisible')
     to avoid printing a return value.")
   (xdoc::p
    "The @(tsee encapsulate) starts with some implicitly local events to
     ensure logic mode and
     avoid errors due to ignored or irrelevant formals
     in the generated function.
     Other implicitly local events remove any default and override hints,
     to prevent such hints from sabotaging the generated proofs;
     this removal is done after proving the applicability conditions,
     in case their proofs rely on the default or override hints.")
   (xdoc::p
    "The @(tsee encapsulate) also includes events
     to locally install the non-normalized definitions
     of the old and new functions,
     because the generated proofs are based on the unnormalized bodies.")
   (xdoc::p
    "The @(tsee encapsulate) is stored into the transformation table,
     associated to the call to the transformation.
     Thus, the table event and (if present) the screen output events
     (which are in the @(tsee progn) but not in the @(tsee encapsulate))
     are not stored into the transformation table,
     because they carry no additional information,
     and because otherwise the table event would have to contain itself.")
   (xdoc::p
    "If @(':print') is @(':all'),
     the @(tsee encapsulate) is wrapped to show ACL2's output
     in response to the submitted events.
     If @(':print') is @(':result') or @(':info') or @(':all'),
     the @(tsee progn) includes events to print
     the exported events on the screen without hints;
     these are the same event forms
     that are introduced non-locally and redundantly in the @(tsee encapsulate).
     If @(':print') is @(':info') or @(':all'),
     a blank line is printed just before the result, for visual separation;
     if @(':print') is @(':result'),
     the blank line is not printed.")
   (xdoc::p
    "If @(':show-only') is @('t'),
     the @(tsee encapsulate) is just printed on the screen
     and not returned as part of the event to submit,
     which in this case is just an @(':invisible') form.
     In this case, if @(':print') is @(':info') or @(':all'),
     a blank line is printed just before the @(tsee encapsulate),
     for visual separation."))
  (b* ((wrld (w state))
       (isomaps (append (strip-cdrs arg-isomaps)
                        (strip-cdrs res-isomaps)))
       (isomaps (remove-duplicates-equal isomaps))
       (defiso-events (isodata-gen-defisos isomaps verify-guards$ print$))
       (appconds (isodata-gen-appconds old$
                                       arg-isomaps
                                       res-isomaps
                                       predicate$
                                       verify-guards$
                                       wrld))
       ((er (list appcond-thm-events
                  appcond-thm-names
                  names-to-avoid))
        (evmac-appcond-theorems-no-extra-hints
         appconds hints$ names-to-avoid print$ ctx state))
       ((mv old-fn-unnorm-event
            old-fn-unnorm-name
            names-to-avoid)
        (install-not-normalized-event old$ t names-to-avoid wrld))
       ((mv new-fn-local-event
            new-fn-exported-event)
        (isodata-gen-new-fn old$
                            arg-isomaps
                            res-isomaps
                            predicate$
                            new$
                            new-enable$
                            verify-guards$
                            untranslate$
                            compatibility
                            appcond-thm-names
                            wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name
            &)
        (install-not-normalized-event new$ t names-to-avoid wrld))
       ((mv new-to-old-thm-local-event
            new-to-old-thm-exported-event)
        (isodata-gen-new-to-old-thm old$
                                    arg-isomaps
                                    res-isomaps
                                    new$
                                    new-to-old$
                                    new-to-old-enable$
                                    appcond-thm-names
                                    old-fn-unnorm-name
                                    new-fn-unnorm-name
                                    wrld))
       ((mv newp-of-new-thm-local-event?
            newp-of-new-thm-exported-event?)
        (if (consp res-isomaps)
            (isodata-gen-newp-of-new-thm old$
                                         arg-isomaps
                                         res-isomaps
                                         new$
                                         new-to-old$
                                         newp-of-new$
                                         newp-of-new-enable$
                                         appcond-thm-names
                                         wrld)
          (mv nil nil)))
       (newp-of-new-thm-local-event? (and newp-of-new-thm-local-event?
                                          (list
                                           newp-of-new-thm-local-event?)))
       (newp-of-new-thm-exported-event? (and newp-of-new-thm-exported-event?
                                             (list
                                              newp-of-new-thm-exported-event?)))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event)
        (isodata-gen-old-to-new-thm appcond-thm-names
                                    old$
                                    arg-isomaps
                                    res-isomaps
                                    new$
                                    old-to-new$
                                    old-to-new-enable$
                                    new-to-old$
                                    wrld))
       (new-fn-verify-guards-event? (and verify-guards$
                                         (list
                                          (isodata-gen-new-fn-verify-guards
                                           appcond-thm-names
                                           old$
                                           arg-isomaps
                                           res-isomaps
                                           predicate$
                                           new$
                                           new-to-old$
                                           old-to-new$
                                           old-fn-unnorm-name
                                           newp-of-new$
                                           wrld))))
       (theory-invariant `(theory-invariant (incompatible
                                             (:rewrite ,new-to-old$)
                                             (:rewrite ,old-to-new$))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@defiso-events
                             ,@appcond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,old-fn-unnorm-event
                             ,new-fn-local-event
                             ,new-fn-unnorm-event
                             ,new-to-old-thm-local-event
                             ,old-to-new-thm-local-event
                             ,@newp-of-new-thm-local-event?
                             ,@new-fn-verify-guards-event?
                             ,new-fn-exported-event
                             ,new-to-old-thm-exported-event
                             ,old-to-new-thm-exported-event
                             ,@newp-of-new-thm-exported-event?
                             ,theory-invariant
                             ,new-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        (value '(value-triple :invisible)))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result
        (and
         (member-eq print$ '(:result :info :all))
         `(,@(and (member-eq print$ '(:info :all))
                  '((cw-event "~%")))
           (cw-event "~x0~|" ',new-fn-exported-event)
           (cw-event "~x0~|" ',new-to-old-thm-exported-event)
           (cw-event "~x0~|" ',old-to-new-thm-exported-event)
           ,@(and newp-of-new-thm-exported-event?
                  `((cw-event "~x0~|"
                              ',(car newp-of-new-thm-exported-event?))))))))
    (value
     `(progn
        ,encapsulate+
        ,transformation-table-event
        ,@print-result
        (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-fn (old
                    isomaps
                    predicate
                    new-name
                    new-enable
                    old-to-new-name
                    (old-to-new-name-suppliedp booleanp)
                    old-to-new-enable
                    (old-to-new-enable-suppliedp booleanp)
                    new-to-old-name
                    (new-to-old-name-suppliedp booleanp)
                    new-to-old-enable
                    (new-to-old-enable-suppliedp booleanp)
                    newp-of-new-name
                    (newp-of-new-name-suppliedp booleanp)
                    newp-of-new-enable
                    (newp-of-new-enable-suppliedp booleanp)
                    verify-guards
                    untranslate
                    hints
                    print
                    show-only
                    compatibility
                    (call pseudo-event-formp)
                    ctx
                    state)
  :returns (mv erp
               (event-form "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (isodata-implementation)
  :short "Check redundancy,
          process the inputs, and
          generate the event to submit."
  :long
  (xdoc::topstring-p
   "If this call to the transformation is redundant,
    a message to that effect is printed on the screen.
    If the transformation is redundant and @(':show-only') is @('t'),
    the @(tsee encapsulate), retrieved from the table, is shown on the screen.
    Do nothing if this invocation of the transformation is redundant.")
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old$
                  arg-isomaps
                  res-isomaps
                  new$
                  new-enable$
                  old-to-new$
                  old-to-new-enable$
                  new-to-old$
                  new-to-old-enable$
                  newp-of-new$
                  newp-of-new-enable$
                  verify-guards$
                  hints$
                  names-to-avoid))
        (isodata-process-inputs old
                                isomaps
                                predicate
                                new-name
                                new-enable
                                old-to-new-name
                                old-to-new-name-suppliedp
                                old-to-new-enable
                                old-to-new-enable-suppliedp
                                new-to-old-name
                                new-to-old-name-suppliedp
                                new-to-old-enable
                                new-to-old-enable-suppliedp
                                newp-of-new-name
                                newp-of-new-name-suppliedp
                                newp-of-new-enable
                                newp-of-new-enable-suppliedp
                                verify-guards
                                untranslate
                                hints
                                print
                                show-only
                                ctx
                                state))
       ((er event) (isodata-gen-everything old$
                                           arg-isomaps
                                           res-isomaps
                                           predicate
                                           new$
                                           new-enable$
                                           old-to-new$
                                           old-to-new-enable$
                                           new-to-old$
                                           new-to-old-enable$
                                           newp-of-new$
                                           newp-of-new-enable$
                                           verify-guards$
                                           untranslate
                                           hints$
                                           print
                                           show-only
                                           compatibility
                                           names-to-avoid
                                           call
                                           ctx
                                           state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection isodata-macro-definition
  :parents (isodata-implementation)
  :short "Definition of the @(tsee isodata) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee isodata-fn).")
   (xdoc::@def "isodata"))
  (defmacro isodata (&whole
                     call
                     ;; mandatory inputs:
                     old
                     isomaps
                     ;; optional inputs:
                     &key
                     (predicate 'nil)
                     (new-name ':auto)
                     (new-enable ':auto)
                     (old-to-new-name 'nil old-to-new-name-suppliedp)
                     (old-to-new-enable 'nil old-to-new-enable-suppliedp)
                     (new-to-old-name 'nil new-to-old-name-suppliedp)
                     (new-to-old-enable 'nil new-to-old-enable-suppliedp)
                     (newp-of-new-name ':auto newp-of-new-name-suppliedp)
                     (newp-of-new-enable 't newp-of-new-enable-suppliedp)
                     (verify-guards ':auto)
                     (untranslate ':nice)
                     (hints 'nil)
                     (print ':result)
                     (show-only 'nil)
                     (compatibility 'nil))
    `(make-event-terse (isodata-fn ',old
                                   ',isomaps
                                   ',predicate
                                   ',new-name
                                   ',new-enable
                                   ',old-to-new-name
                                   ,old-to-new-name-suppliedp
                                   ',old-to-new-enable
                                   ,old-to-new-enable-suppliedp
                                   ',new-to-old-name
                                   ,new-to-old-name-suppliedp
                                   ',new-to-old-enable
                                   ,new-to-old-enable-suppliedp
                                   ',newp-of-new-name
                                   ,newp-of-new-name-suppliedp
                                   ',newp-of-new-enable
                                   ,newp-of-new-enable-suppliedp
                                   ',verify-guards
                                   ',untranslate
                                   ',hints
                                   ',print
                                   ',show-only
                                   ',compatibility
                                   ',call
                                   (cons 'isodata ',old)
                                   state)
                       :suppress-errors ,(not print))))
