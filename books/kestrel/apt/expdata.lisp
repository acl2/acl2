; APT (Automated Program Transformations) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/std/basic/mbt-dollar" :dir :system)
(include-book "kestrel/std/system/apply-fn-into-ifs" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/std/system/ibody" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/util/defsurj" :dir :system)
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

 expdata

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old'),
   @('surjmaps'),
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
   are the homonymous inputs to @(tsee expdata),
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

  "@('arg-surjmaps') is an alist
   from formal arguments of @('old')
   to surjective mapping records that specify
   how the associated formal arguments must be transformed.
   There are never duplicate keys.
   When input processing is complete,
   the keys are exactly all the formal arguments of @('old'), in order.
   @('arg-surjmaps') results from processing @('surjmaps')."

  "@('res-surjmaps') is an alist
   from positive integers from 1 to @('m')
   to surjective mapping records that specify
   how the result with the associated (1-based) indices
   must be transformed.
   There are never duplicate keys.
   When input processing is complete:
   if some results are transformed,
   the keys are exactly all the integers from 1 to @('m'), in order;
   if no results are transformed,
   the alist is @('nil').
   @('res-surjmaps') results from processing @('surjmaps')."

  "@('appcond-thm-names') is an alist
   from the applicability condition keywords
   to the corresponding theorem names."

  "@('old-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the old function."

  "@('new-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the new function."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing expdata)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate expdata-surjmap
  :short "Information about a surjective mapping according to which
          (some of) the target function's arguments and results
          are transformed."
  :long
  (xdoc::topstring-p
   "This aggregate is somewhat similar to @(tsee defmapping-infop),
    and in fact it corresponds
    either to an existing @(tsee defsurj) that is referenced
    in an @('surjk') input of @(tsee expdata),
    or to a locally generated @(tsee defsurj) that is determined
    in the @('surjk') input of @(tsee expdata).
    However, this aggregate is not stored in any table;
    it has some fields in common (except for their names)
    with @(tsee defmapping-infop),
    but it has a few extra fields and omits a few fields.
    This aggregate is only for @(tsee expdata)'s internal use.
    Note that there are no @('forth-of-back') and @('back-injective') theorems,
    because the corresponding theorems are not in the @(tsee defsurj).")
  ((surjname "Name of the @(tsee defsurj)." symbolp)
   (localp "Flag saying whether the @(tsee defsurj) is
            locally generated or not."
           booleanp)
   (oldp "Recognizer of the old representation,
          i.e. the @('domb') domain of the @(tsee defsurj)."
         pseudo-termfnp)
   (newp "Recognizer of the new representation,
          i.e. the @('doma') domain of the @(tsee defsurj)."
         pseudo-termfnp)
   (forth "Conversion from old to new representation,
           i.e. the @('beta') conversion of the @(tsee defsurj)."
          pseudo-termfnp)
   (back "Conversion from new to old representation,
          i.e. the @('alpha') conversion of the @(tsee defsurj)."
         pseudo-termfnp)
   (forth-image "Name of the @(':beta-image') theorem of the @(tsee defsurj)."
                symbolp)
   (back-image "Name of the @(':alpha-image') theorem of the @(tsee defsurj)."
               symbolp)
   (back-of-forth "Name of the @(':alpha-of-beta') theorem
                   of the @(tsee defsurj)."
                  symbolp)
   (forth-injective "Name of the @(':beta-injective') theorem
                     of the @(tsee defsurj)."
                    symbolp)
   (oldp-guard "Name of the @(':domb-guard') theorem
                of the @(tsee defsurj), if present (otherwise @('nil'))."
               symbolp)
   (newp-guard "Name of the @(':doma-guard') theorem
                of the @(tsee defsurj), if present (otherwise @('nil'))."
               symbolp)
   (forth-guard "Name of the @(':beta-guard') theorem
                of the @(tsee defsurj), if present (otherwise @('nil'))."
                symbolp)
   (back-guard "Name of the @(':alpha-guard') theorem
                of the @(tsee defsurj), if present (otherwise @('nil'))."
               symbolp)
   (hints "Optional hints for the @(tsee defsurj),
           if locally generated (otherwise @('nil'))."
          keyword-value-listp))
  :pred expdata-surjmapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expdata-surjmap-listp (x)
  :short "Recognize lists of surjective mapping records."
  (expdata-surjmapp x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist expdata-symbol-surjmap-alistp (x)
  :short "Recognize alists from symbols to surjective mapping records."
  :key (symbolp x)
  :val (expdata-surjmapp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule expdata-symbolp-of-key-of-symbol-surjmap-alist
    (implies (expdata-symbol-surjmap-alistp x)
             (symbolp (car (assoc-equal k x)))))

  (defrule expdata-surjmapp-of-val-of-symbol-surjmap-alist
    (implies (and (expdata-symbol-surjmap-alistp x)
                  (consp (assoc-equal k x)))
             (expdata-surjmapp (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist expdata-pos-surjmap-alistp (x)
  :short "Recognize alists
          from positive integers to surjective mapping records."
  :key (posp x)
  :val (expdata-surjmapp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  ///

  (defrule expdata-posp-of-key-of-pos-surjmap-alist
    (implies (and (expdata-pos-surjmap-alistp x)
                  (consp (assoc-equal k x)))
             (posp (car (assoc-equal k x)))))

  (defrule expdata-surjmapp-of-val-of-pos-surjmap-alist
    (implies (and (expdata-pos-surjmap-alistp x)
                  (consp (assoc-equal k x)))
             (expdata-surjmapp (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-old (old predicate verify-guards ctx state)
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

(define expdata-process-res (res (m posp) (err-msg-preamble msgp) ctx state)
  :returns (mv erp (j posp) state)
  :short "Process a result specification in the @('surjmap') input."
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

(define expdata-process-arg/res-list
  ((arg/res-list "The @('arg/res-listk') component of @('surjmaps').")
   (k posp "The @('k') in @('arg/res-listk').")
   (old$ symbolp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple @('(args ress)') satisfying
                        @('(typed-tuplep symbol-listp pos-listp result)').")
               state)
  :verify-guards nil
  :short "Process an @('arg/res-list') component of the @('surjmaps') input."
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
               ((er j) (expdata-process-res arg/res-list m
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
        (expdata-process-arg/res-list-aux arg/res-list x1...xn m
                                          err-msg-preamble ctx state))))

  :prepwork
  ((define expdata-process-arg/res-list-aux ((arg/res-list symbol-listp)
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
           (b* (((er (list args ress)) (expdata-process-arg/res-list-aux
                                        (cdr arg/res-list) x1...xn m
                                        err-msg-preamble ctx state)))
             (value (list (cons arg/res args) ress))))
          ((er j) (expdata-process-res arg/res m err-msg-preamble ctx state))
          ((er (list args ress)) (expdata-process-arg/res-list-aux
                                  (cdr arg/res-list) x1...xn m
                                  err-msg-preamble ctx state)))
       (value (list args (cons j ress)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-fresh-defsurj-name-with-*s-suffix ((name symbolp)
                                                   (wrld plist-worldp))
  :returns (fresh-name "A @(tsee symbolp).")
  :mode :program
  :short "Suffix a name with as many @('*')s as needed
          to make it a valid name for a new @(tsee defsurj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "A name is valid for a new @(tsee defsurj)
     if it is not already a key in the @(tsee defsurj) table.")
   (xdoc::p
    "We use this function for generating local @(tsee defsurj)s.")
   (xdoc::p
    "If the input name is already valid, no @('*')s are added."))
  (b* ((table (table-alist *defmapping-table-name* wrld)))
    (expdata-fresh-defsurj-name-with-*s-suffix-aux name table))

  :prepwork
  ((define expdata-fresh-defsurj-name-with-*s-suffix-aux ((name symbolp)
                                                          (table alistp))
     :returns fresh-name ; SYMBOLP
     :mode :program
     (if (consp (assoc-eq name table))
         (expdata-fresh-defsurj-name-with-*s-suffix-aux (packn-pos
                                                         (list name '*)
                                                         name)
                                                        table)
       name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-fresh-defsurj-thm-names ((surjname symbolp)
                                         (verify-guards$ booleanp)
                                         (names-to-avoid symbol-listp)
                                         (wrld plist-worldp))
  :returns (mv (forth-image "A @(tsee symbolp).")
               (back-image "A @(tsee symbolp).")
               (back-of-forth "A @(tsee symbolp).")
               (oldp-guard "A @(tsee symbolp).")
               (newp-guard "A @(tsee symbolp).")
               (forth-guard "A @(tsee symbolp).")
               (back-guard "A @(tsee symbolp).")
               (forth-injective "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Return fresh @(tsee defsurj) theorem names."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as the @(':thm-names') input
     of a @(tsee defsurj) that @(tsee expdata) generates locally,
     when the @('surj') input is not a name.")
   (xdoc::p
    "In order for the generated @(tsee defsurj) to succeed,
     we supply explicit fresh theorem names to use.
     These are returned by this function.")
   (xdoc::p
    "We append the keyword (without colon) that denotes the theorem
     at the end of the @(tsee defsurj) name
     (which is generated by @(tsee expdata-fresh-defsurj-name-with-*s-suffix),
     and add enough @('$') characters, if needed, to make them fresh.
     We expect that adding @('$') characters will rarely be necessary.")
   (xdoc::p
    "The names of the guard-related theorems are @('nil')
     if guards must not be verified, since
     those theorems are not generated or used in that case."))
  (b* ((prefix (add-suffix surjname "-"))
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
         wrld)))
    (mv forth-image
        back-image
        back-of-forth
        oldp-guard
        newp-guard
        forth-guard
        back-guard
        forth-injective
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-surj ((surj
                               "The @('surjk') component of @('surjmaps').")
                              (k posp "The @('k') in @('surjk').")
                              (old$ symbolp)
                              (verify-guards$ booleanp)
                              (names-to-avoid symbol-listp)
                              ctx
                              state)
  :returns (mv erp
               (result "A tuple @('(surjmap updated-names-to-avoid)')
                        satisfying @('(typed-tuplep expdata-surjmapp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process a @('surj') component of the @('surjmaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('surj') is the name of an existing @(tsee defsurj),
     the @('names-to-avoid') argument is returned unchanged,
     because we are not generating any fresh theorem names in this case.")
   (xdoc::p
    "If instead @('surj') is a list
     @('(oldp newp forth back)') or @('(oldp newp forth back :hints ...)'),
     the @('names-to-avoid') argument is augmented with
     the names of the theorems that
     will be generated by the local @(tsee defsurj).")
   (xdoc::p
    "When @('surj') is the name of an existing @(tsee defsurj),
     to check whether its @(':guard-thms') is @('t'),
     which is required when @('verify-guards$') is @('t'),
     we check whether one of the @('...-guard') theorems
     recorded in the @(tsee defsurj) is not @('nil').
     We pick @('doma-guard'),
     but any of the other three would work as well.")
   (xdoc::p
    "When @('surj') is not the name of an existing @(tsee defsurj),
     and instead we generate a local one as part of @(tsee expdata),
     we use @(tsee defsurj)'s input processing code,
     and then we check that the functions are all unary and single-valued;
     given the constraints already checked
     by the @(tsee defsurj) input processing code,
     here it suffices to check that the two domains are unary.
     We cannot just generate the @(tsee defsurj) later;
     we need the actual (translated) functions
     to use them in the events generated by @(tsee expdata) proper.
     When we call @(tsee defsurj)'s input processing functions,
     we set the context @('ctx') to the one for the @(tsee defsurj) call,
     so that the error message is appropriate.
     (When the generated @(tsee defsurj) call is actually submitted,
     these input processing steps will be repeated,
     but will succeed since they have been already performed here;
     and they should be quite fast to execute.)
     The name of this local @(tsee defsurj) is a combination
     that involves @('old') and @('k'),
     to make the name of the @(tsee defsurj) readable
     (in case of errors due to failed applicability conditions)
     and unique within the @(tsee encapsulate) generated by @(tsee expdata).")
   (xdoc::p
    "If the processing is successful,
     we return the surjective mapping record specified by @('surj')."))
  (if (atom surj)
      (b* (((er &) (ensure-value-is-symbol$
                    surj
                    (msg "The ~n0 SURJ component ~x1 ~
                          of the second input ~
                          must be a symbol or a list. ~
                          Since it is an atom,"
                         (list k) surj)
                    t nil))
           (info (defsurj-lookup surj (w state)))
           ((unless info)
            (er-soft+ ctx t nil
                      "The ~n0 SURJ component of the second input, ~
                       which is the symbol ~x1, ~
                       must be the name of an existing DEFSURJ, ~
                       but no DEFSURJ with this name exists.  ~
                       See :DOC DEFSURJ."
                      (list k) surj))
           ((defmapping-info info) info)
           ((when (and verify-guards$
                       (null info.doma-guard)))
            (er-soft+ ctx t nil
                      "Since the :VERIFY-GUARDS input is T, ~
                       or it is (perhaps by default) :AUTO ~
                       and the target function ~x0 is guard-verified, ~
                       the DEFSURJ ~x1 must include ~
                       the guard-related theorems, ~
                       but it does not.  ~
                       See :DOC DEFSURJ."
                      old$ surj))
           (surjmap (make-expdata-surjmap
                     :surjname surj
                     :localp nil
                     :oldp info.domb
                     :newp info.doma
                     :forth info.beta
                     :back info.alpha
                     :forth-image info.beta-image
                     :back-image info.alpha-image
                     :back-of-forth info.alpha-of-beta
                     :forth-injective info.alpha-injective
                     :oldp-guard info.domb-guard
                     :newp-guard info.doma-guard
                     :forth-guard info.beta-guard
                     :back-guard info.alpha-guard
                     :hints nil)))
        (value (list surjmap names-to-avoid)))
    (b* ((wrld (w state))
         (surjname (packn-pos (list 'defsurj-expdata- old$ '- k) old$))
         (surjname (expdata-fresh-defsurj-name-with-*s-suffix surjname wrld))
         ((mv forth-image
              back-image
              back-of-forth
              oldp-guard
              newp-guard
              forth-guard
              back-guard
              forth-injective
              names-to-avoid)
          (expdata-fresh-defsurj-thm-names surjname
                                           verify-guards$
                                           names-to-avoid
                                           wrld))
         ((unless (true-listp surj))
          (er-soft+ ctx t nil
                    "The ~n0 SURJ component ~x1 of the second input ~
                     must be a symbol or a list. ~
                     Since it is not an atom, it must be a list."
                    (list k) surj))
         ((unless (or (= (len surj) 4)
                      (= (len surj) 6)))
          (er-soft+ ctx t nil
                    "The ~n0 SURJ component ~x1 of the second input ~
                     must be a list of length 4 or 6."
                    (list k) surj))
         (oldp (first surj))
         (newp (second surj))
         (forth (third surj))
         (back (fourth surj))
         ((unless (or (= (len surj) 4)
                      (eq (fifth surj) :hints)))
          (er-soft+ ctx t nil
                    "The fifth component ~x0 ~
                     of the ~n1 SURJ component ~x2 ~
                     of the second input ~
                     must be the keyword :HINTS."
                    (fifth surj) (list k) surj))
         (hints (and (= (len surj) 6) (sixth surj)))
         (ctx-defsurj (cons 'defsurj surjname))
         ((er (list newp$ oldp$ back$ forth$))
          (acl2::defmapping-process-functions
           newp oldp back forth verify-guards$ ctx-defsurj state))
         (oldp-arity (arity oldp$ wrld))
         ((unless (= oldp-arity 1))
          (er-soft+ ctx t nil
                    "The first component ~x0 ~
                     of the ~n1 SURJ component ~
                     of the third input ~
                     must have one argument, but it has ~x2 arguments instead."
                    oldp (list k) oldp-arity))
         (newp-arity (arity newp$ wrld))
         ((unless (= newp-arity 1))
          (er-soft+ ctx t nil
                    "The second component ~x0 ~
                     of the ~n1 SURJ component ~
                     of the third input ~
                     must have one argument, but it has ~x2 arguments instead."
                    newp (list k) newp-arity))
         (surjmap (make-expdata-surjmap
                   :surjname surjname
                   :localp t
                   :oldp oldp$
                   :newp newp$
                   :forth forth$
                   :back back$
                   :forth-image forth-image
                   :back-image back-image
                   :back-of-forth back-of-forth
                   :forth-injective forth-injective
                   :oldp-guard oldp-guard
                   :newp-guard newp-guard
                   :forth-guard forth-guard
                   :back-guard back-guard
                   :hints hints)))
      (value (list surjmap names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-arg/res-list-surj
  ((arg/res-list-surj "The @('(arg/res-listk surjk)') component of @('surjmaps').")
   (k posp "The @('k') in @('(arg/res-listk surjk)').")
   (old$ symbolp)
   (verify-guards$ booleanp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (names-to-avoid symbol-listp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-surjmaps res-surjmaps updated-names-to-avoid)')
                        satisfying @('(typed-tuplep expdata-symbol-surjmap-alistp
                                                    expdata-pos-surjmap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process an @('(arg/res-list surj)') component
          of the @('surjmaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('arg-surjmaps') and @('res-surjmaps') inputs
     are obtained by having previously called this function
     on @('(arg/res-list1 surj1)'), ..., @('(arg/res-listk-1 surjk-1)') in turn.
     When we call this function on @('(arg/res-listk surjk)'),
     we extend @('arg-surjmaps') and @('res-surjmaps')
     with the information in @('(arg/res-listk surjk)').
     As we do that, we check that
     the arguments of @('old') in @('arg/res-listk') are not
     already keys in @('arg-surjmaps'):
     if any of them did, it would mean that it is already present
     in one of @('(arg/res-list1 surj1)'), ..., @('(arg/res-listk-1 surjk-1)'),
     violating the disjointness requirement.
     Similarly, we check that the result indices in @('arg/res-listk') are not
     already keys in @('res-surjmaps'):
     if any of them did, it would mean that the same result is already present
     in one of @('(arg/res-list1 surj1)'), ..., @('(arg/res-listk-1 surjk-1)'),
     violating the disjointness requirement."))
  (b* (((er &) (ensure-tuple$ arg/res-list-surj 2
                              (msg "The ~n0 component of the second input"
                                   (list k))
                              t nil))
       (arg/res-list (first arg/res-list-surj))
       (surj (second arg/res-list-surj))
       ((er (list args ress)) (expdata-process-arg/res-list
                               arg/res-list k old$ ctx state))
       (arg-overlap (intersection-eq args (strip-cars arg-surjmaps)))
       ((when arg-overlap)
        (er-soft+ ctx t nil
                  "The ~n0 component of the second input includes ~&1, ~
                   which are also present in the preceding components. ~
                   This violates the disjointness requirement."
                  (list k) arg-overlap))
       (res-overlap (intersection$ ress (strip-cars res-surjmaps)))
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
       ((er (list surjmap names-to-avoid)) (expdata-process-surj surj
                                                                 k
                                                                 old$
                                                                 verify-guards$
                                                                 names-to-avoid
                                                                 ctx
                                                                 state))
       (arg-surjmaps
        (expdata-process-arg/res-list-surj-add-args args surjmap arg-surjmaps))
       (res-surjmaps
        (expdata-process-arg/res-list-surj-add-ress ress surjmap res-surjmaps)))
    (value (list arg-surjmaps res-surjmaps names-to-avoid)))

  :prepwork

  ((define expdata-process-arg/res-list-surj-add-args
     ((args symbol-listp)
      (surjmap expdata-surjmapp)
      (arg-surjmaps expdata-symbol-surjmap-alistp))
     :returns (new-arg-surjmaps expdata-symbol-surjmap-alistp :hyp :guard)
     (cond ((endp args) arg-surjmaps)
           (t (expdata-process-arg/res-list-surj-add-args
               (cdr args)
               surjmap
               (acons (car args) surjmap arg-surjmaps)))))

   (define expdata-process-arg/res-list-surj-add-ress
     ((ress pos-listp)
      (surjmap expdata-surjmapp)
      (res-surjmaps expdata-pos-surjmap-alistp))
     :returns (new-res-surjmaps expdata-pos-surjmap-alistp :hyp :guard)
     (cond ((endp ress) res-surjmaps)
           (t (expdata-process-arg/res-list-surj-add-ress
               (cdr ress) surjmap (acons (car ress) surjmap res-surjmaps)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-arg/res-list-surj-list
  ((arg/res-list-surj-list)
   (k posp)
   (old$ symbolp)
   (verify-guards$ booleanp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (names-to-avoid symbol-listp)
   ctx
   state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-surjmaps res-surjmaps updated-names-to-avoid)')
                        satisfying @('(typed-tuplep expdata-symbol-surjmap-alistp
                                                    expdata-pos-surjmap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Lift @(tsee expdata-process-arg/res-list-surj) to lists."
  (b* (((when (endp arg/res-list-surj-list))
        (value (list arg-surjmaps res-surjmaps names-to-avoid)))
       ((er (list arg-surjmaps res-surjmaps names-to-avoid))
        (expdata-process-arg/res-list-surj (car arg/res-list-surj-list)
                                           k
                                           old$
                                           verify-guards$
                                           arg-surjmaps
                                           res-surjmaps
                                           names-to-avoid
                                           ctx
                                           state)))
    (expdata-process-arg/res-list-surj-list (cdr arg/res-list-surj-list)
                                            (1+ k)
                                            old$
                                            verify-guards$
                                            arg-surjmaps
                                            res-surjmaps
                                            names-to-avoid
                                            ctx
                                            state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-surjmaps (surjmaps
                                  (old$ symbolp)
                                  (verify-guards$ booleanp)
                                  (names-to-avoid symbol-listp)
                                  ctx
                                  state)
  :returns (mv erp
               (result "A tuple
                        @('(arg-surjmaps res-surjmaps updated-names-to-avoid)')
                        satisfying @('(typed-tuplep expdata-symbol-surjmap-alistp
                                                    expdata-pos-surjmap-alistp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @('surjmaps') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the empty alists for @('arg-surjmaps') and @('res-surjmap'),
     we repeatedly process each @('(arg/res-listk surjk)') element,
     accumulating the processing results
     into @('arg-surjmaps') and @('res-surjmaps').
     Then we reconstruct a possible larger @('arg-surjmaps')
     by going through the formal parameters of @('old') in order,
     and associating them, in the new alist, with
     either the corresponding value in the old alist,
     or the identity surjective mapping.
     If the final @('res-surjmaps') is not empty,
     we similarly reconstruct a possibly larger @('res-surjmaps')
     by going through the integers from 1 to @('m') in order,
     and associating them, in the new alist, with
     either the corresponding value in the old alist,
     or the identity surjective mapping."))
  (b* ((wrld (w state))
       ((unless (true-listp surjmaps))
        (er-soft+ ctx t nil
                  "The second input must be a true list, ~
                   but it is ~x0 instead." surjmaps))
       ((unless (>= (len surjmaps) 1))
        (er-soft+ ctx t nil
                  "The second input must be a non-empty list, ~
                   but it is ~x0 instead." surjmaps))
       ((er (list arg-surjmaps res-surjmaps names-to-avoid))
        (expdata-process-arg/res-list-surj-list
         surjmaps 1 old$ verify-guards$ nil nil names-to-avoid ctx state))
       (surjname-id
        (expdata-fresh-defsurj-name-with-*s-suffix 'defsurj-identity wrld))
       ((mv forth-image-id
            back-image-id
            back-of-forth-id
            oldp-guard-id
            newp-guard-id
            forth-guard-id
            back-guard-id
            forth-injective-id
            names-to-avoid)
        (expdata-fresh-defsurj-thm-names surjname-id
                                         verify-guards$
                                         names-to-avoid
                                         wrld))
       (surjmap-id (make-expdata-surjmap
                    :surjname surjname-id
                    :localp t
                    :oldp '(lambda (x) 't)
                    :newp '(lambda (x) 't)
                    :forth '(lambda (x) x)
                    :back '(lambda (x) x)
                    :back-image back-image-id
                    :forth-image forth-image-id
                    :back-of-forth back-of-forth-id
                    :forth-injective forth-injective-id
                    :oldp-guard oldp-guard-id
                    :newp-guard newp-guard-id
                    :forth-guard forth-guard-id
                    :back-guard back-guard-id
                    :hints nil))
       (formals (formals old$ wrld))
       (arg-surjmaps (expdata-process-surjmaps-args formals
                                                    arg-surjmaps
                                                    surjmap-id))
       (res-surjmaps (and res-surjmaps
                          (expdata-process-surjmaps-ress 1
                                                         (number-of-results
                                                          old$ wrld)
                                                         res-surjmaps
                                                         surjmap-id))))
    (value (list arg-surjmaps res-surjmaps names-to-avoid)))

  :prepwork

  ((define expdata-process-surjmaps-args
     ((formals symbol-listp)
      (arg-surjmaps expdata-symbol-surjmap-alistp)
      (surjmap-id expdata-surjmapp))
     :returns (new-arg-surjmaps expdata-symbol-surjmap-alistp :hyp :guard)
     (b* (((when (endp formals)) nil)
          (pair (assoc-eq (car formals) arg-surjmaps)))
       (if (consp pair)
           (cons pair (expdata-process-surjmaps-args (cdr formals)
                                                     arg-surjmaps
                                                     surjmap-id))
         (acons (car formals)
                surjmap-id
                (expdata-process-surjmaps-args (cdr formals)
                                               arg-surjmaps
                                               surjmap-id))))
     :verify-guards nil ; done below
     ///
     (verify-guards expdata-process-surjmaps-args
       :hints (("Goal"
                :in-theory
                (enable alistp-when-expdata-symbol-surjmap-alistp-rewrite)))))

   (define expdata-process-surjmaps-ress ((j posp)
                                          (m posp)
                                          (res-surjmaps expdata-pos-surjmap-alistp)
                                          (surjmap-id expdata-surjmapp))
     :returns (new-res-surjmaps expdata-pos-surjmap-alistp :hyp :guard)
     (b* (((unless (mbt (and (posp j) (posp m)))) nil)
          ((when (> j m)) nil)
          (pair (assoc j res-surjmaps)))
       (if (consp pair)
           (cons pair (expdata-process-surjmaps-ress (1+ j)
                                                     m
                                                     res-surjmaps
                                                     surjmap-id))
         (acons j
                surjmap-id
                (expdata-process-surjmaps-ress (1+ j)
                                               m
                                               res-surjmaps
                                               surjmap-id))))
     :measure (nfix (- (1+ (pos-fix m)) (pos-fix j)))
     :verify-guards nil ; done below
     ///
     (verify-guards expdata-process-surjmaps-ress
       :hints (("Goal"
                :in-theory
                (enable alistp-when-expdata-pos-surjmap-alistp-rewrite)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-process-newp-of-new-name (newp-of-new-name
                                          (new$ symbolp)
                                          (names-to-avoid symbol-listp)
                                          ctx
                                          state)
  :returns (mv erp
               (result "A list @('(newp-of-new$ updated-new-names-to-avoid)')
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

(define expdata-process-inputs (old
                                surjmaps
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
                                    arg-surjmaps
                                    res-surjmaps
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
                                         expdata-symbol-surjmap-alistp
                                         expdata-pos-surjmap-alistp
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
  (b* (((er old$) (expdata-process-old old predicate verify-guards ctx state))
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
        (expdata-process-newp-of-new-name newp-of-new-name
                                          new$
                                          names-to-avoid
                                          ctx
                                          state))
       ((er verify-guards$) (process-input-verify-guards verify-guards
                                                         old$
                                                         ctx
                                                         state))
       ((er (list arg-surjmaps res-surjmaps names-to-avoid))
        (expdata-process-surjmaps surjmaps
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
                   (not res-surjmaps)))
        (er-soft+ ctx t nil
                  "Since no results are being transformed, ~
                   it is an error to supply the :NEWP-OF-NEW-NAME input."))
       ((when (and newp-of-new-enable-suppliedp
                   (not res-surjmaps)))
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
                 arg-surjmaps
                 res-surjmaps
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

(xdoc::evmac-topic-event-generation expdata
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-defsurj ((surjmap expdata-surjmapp)
                             (verify-guards$ booleanp)
                             (print$ evmac-input-print-p))
  :guard (expdata-surjmap->localp surjmap)
  :returns (event pseudo-event-formp)
  :short "Generate a local @(tsee defsurj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the @('surj') input is not a name,
     @('expdata') internally generates and uses a @(tsee defsurj),
     so that the rest of the generated events can uniformly rely
     on a @(tsee defsurj) that has established the surjective mapping.")
   (xdoc::p
    "This event is local to the @(tsee encapsulate)
     generated by @('expdata').")
   (xdoc::p
    "Since the @(tsee defsurj) is local,
     we normally do not want to print its result or info output.
     But we want to print errors.
     So we pass @(':error') as the @(':print') input.
     However, if @(tsee expdata)'s @(':print') input is @(':all'),
     the we use @(':all') for @(tsee defsurj)'s @(':print') input as well.")
   (xdoc::p
    "This is also used for the identity surjective mapping,
     which is also locally generated."))
  (b* (((expdata-surjmap surjmap) surjmap)
       (name surjmap.surjname)
       (doma surjmap.newp)
       (domb surjmap.oldp)
       (alpha surjmap.back)
       (beta surjmap.forth)
       (unconditional nil)
       (guard-thms verify-guards$)
       (nonguard-thm-names (list :alpha-image surjmap.back-image
                                 :beta-image surjmap.forth-image
                                 :alpha-of-beta surjmap.back-of-forth
                                 :beta-injective surjmap.forth-injective))
       (guard-thm-names? (and guard-thms
                              (list :doma-guard surjmap.newp-guard
                                    :domb-guard surjmap.oldp-guard
                                    :alpha-guard surjmap.back-guard
                                    :beta-guard surjmap.forth-guard)))
       (thm-names (append nonguard-thm-names guard-thm-names?))
       (hints surjmap.hints)
       (print (if (eq print$ :all) :all :error)))
    `(local
      (defsurj ,name ,doma ,domb ,alpha ,beta
        :unconditional ,unconditional
        :guard-thms ,guard-thms
        :thm-names ,thm-names
        :hints ,hints
        :print ,print))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-defsurjs ((surjmaps expdata-surjmap-listp)
                              (verify-guards$ booleanp)
                              (print$ evmac-input-print-p))
  :returns (events pseudo-event-form-listp)
  :short "Generate all the local @(tsee defsurj)s from a list."
  (b* (((when (endp surjmaps)) nil)
       (surjmap (car surjmaps)))
    (if (expdata-surjmap->localp surjmap)
        (cons (expdata-gen-defsurj surjmap verify-guards$ print$)
              (expdata-gen-defsurjs (cdr surjmaps) verify-guards$ print$))
      (expdata-gen-defsurjs (cdr surjmaps) verify-guards$ print$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expdata-gen-fn-of-terms
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
     The @('arg/res-surjmaps') input of the generated function
     may be @('arg-surjmaps') or @('res-surjmaps').")
   (xdoc::@def "expdata-gen-fn-of-terms"))

  (defmacro expdata-gen-fn-of-terms (fn)
    (declare (xargs :guard (member-eq fn '(oldp newp forth back))))
    (b* ((name (packn (list 'expdata-gen- fn '-of-terms)))
         (string (str::downcase-string (symbol-name fn)))
         (selector (packn (list 'expdata-surjmap-> fn))))
      `(define ,name ((terms pseudo-term-listp)
                      (arg/res-surjmaps expdata-symbol-surjmap-alistp))
         :guard (= (len terms) (len arg/res-surjmaps))
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
              (surjmap (cdar arg/res-surjmaps))
              (,fn (,selector surjmap))
              (new-term (apply-term* ,fn term))
              (new-terms (,name (cdr terms) (cdr arg/res-surjmaps))))
           (cons new-term new-terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-fn-of-terms oldp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-fn-of-terms newp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-fn-of-terms forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-fn-of-terms back)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-oldp-of-rec-call-args-under-contexts
  ((rec-calls pseudo-tests-and-call-listp)
   (arg-surjmaps expdata-symbol-surjmap-alistp))
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
                (conjoin (expdata-gen-oldp-of-terms (fargs rec-call)
                                                    arg-surjmaps)))
     (expdata-gen-oldp-of-rec-call-args-under-contexts (cdr rec-calls)
                                                       arg-surjmaps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-result-vars ((old$ symbolp) (m posp))
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
  (expdata-gen-result-vars-aux old$ 1 m)

  :prepwork
  ((define expdata-gen-result-vars-aux ((old$ symbolp) (j posp) (m posp))
     :returns (vars symbol-listp)
     (b* (((unless (mbt (posp j))) nil)
          ((unless (mbt (posp m))) nil)
          ((when (> j m)) nil)
          (name (str::cat "RESULT" (str::nat-to-dec-string j)))
          (var (intern-in-package-of-symbol name old$))
          (vars (expdata-gen-result-vars-aux old$ (1+ j) m)))
       (cons var vars))
     :measure (nfix (- (1+ (nfix m)) (nfix j))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-appconds ((old$ symbolp)
                              (arg-surjmaps expdata-symbol-surjmap-alistp)
                              (res-surjmaps expdata-pos-surjmap-alistp)
                              (predicate$ booleanp)
                              (verify-guards$ booleanp)
                              (wrld plist-worldp))
  :returns (appconds "A @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions."
  (b* ((x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (expdata-gen-oldp-of-terms x1...xn arg-surjmaps))
       (oldp-of-x1...xn-conj (conjoin oldp-of-x1...xn))
       (old-guard (uguard old$ wrld))
       (old-call (fcons-term old$ x1...xn)))
    (append
     (make-evmac-appcond?
      :oldp-of-old
      (b* ((m (len res-surjmaps)))
        (if (= m 1)
            (b* ((res-surjmap (cdar res-surjmaps))
                 (oldp-res (expdata-surjmap->oldp res-surjmap)))
              (implicate oldp-of-x1...xn-conj
                         (fcons-term* oldp-res old-call)))
          (b* ((y1...ym (expdata-gen-result-vars old$ m))
               (oldp-of-y1...ym (expdata-gen-oldp-of-terms
                                 y1...ym res-surjmaps)))
            (implicate oldp-of-x1...xn-conj
                       (make-mv-let-call 'mv y1...ym :all old-call
                                         (conjoin oldp-of-y1...ym))))))
      :when res-surjmaps)
     (make-evmac-appcond?
      :oldp-when-old
      (implicate old-call
                 oldp-of-x1...xn-conj)
      :when predicate$)
     (make-evmac-appcond?
      :oldp-of-rec-call-args
      (implicate oldp-of-x1...xn-conj
                 (expdata-gen-oldp-of-rec-call-args-under-contexts
                  (recursive-calls old$ wrld)
                  arg-surjmaps))
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

(defines expdata-xform-rec-calls
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

  (define expdata-xform-rec-calls ((term pseudo-termp)
                                   (old$ symbolp)
                                   (arg-surjmaps expdata-symbol-surjmap-alistp)
                                   (res-surjmaps expdata-pos-surjmap-alistp)
                                   (new$ symbolp))
    :returns new-term ; PSEUDO-TERMP
    (b* (((when (or (variablep term) (fquotep term))) term)
         (fn (ffn-symb term))
         ((when (eq fn old$))
          (b* ((new-call (fcons-term new$
                                     (expdata-gen-forth-of-terms (fargs term)
                                                                 arg-surjmaps)))
               ((when (not res-surjmaps)) new-call)
               (m (len res-surjmaps)))
            (if (= m 1)
                (b* ((back-res (expdata-surjmap->back (cdar res-surjmaps))))
                  (apply-term* back-res new-call))
              (b* ((y1...ym (expdata-gen-result-vars old$ m))
                   (back-of-y1...ym (expdata-gen-back-of-terms y1...ym
                                                               res-surjmaps)))
                (make-mv-let-call 'mv y1...ym :all new-call
                                  (fcons-term 'mv back-of-y1...ym))))))
         ((when (symbolp fn))
          (fcons-term fn
                      (expdata-xform-rec-calls-lst (fargs term)
                                                   old$
                                                   arg-surjmaps
                                                   res-surjmaps
                                                   new$)))
         (new-fn (make-lambda (lambda-formals fn)
                              (expdata-xform-rec-calls (lambda-body fn)
                                                       old$
                                                       arg-surjmaps
                                                       res-surjmaps
                                                       new$))))
      (fcons-term new-fn
                  (expdata-xform-rec-calls-lst (fargs term)
                                               old$
                                               arg-surjmaps
                                               res-surjmaps
                                               new$))))

  (define expdata-xform-rec-calls-lst
    ((terms pseudo-term-listp)
     (old$ symbolp)
     (arg-surjmaps expdata-symbol-surjmap-alistp)
     (res-surjmaps expdata-pos-surjmap-alistp)
     (new$ symbolp))
    :returns new-terms ; PSEUDO-TERM-LISTP
    (cond ((endp terms) nil)
          (t (cons (expdata-xform-rec-calls (car terms)
                                            old$
                                            arg-surjmaps
                                            res-surjmaps
                                            new$)
                   (expdata-xform-rec-calls-lst (cdr terms)
                                                old$
                                                arg-surjmaps
                                                res-surjmaps
                                                new$))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expdata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn
  :short "Generate a function to generate certain kinds of lemma instances."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function generated by this macro
     generates a lemma instance of the form
     @('(:instance lemma (x1 (fn1 x1)) ... (xn (fnn xn)))'),
     where each @('fni') is either @('forthi') or @('backi').
     The choice of the @('fni') functions is the input of the macro.")
   (xdoc::@def "expdata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn"))

  (defmacro expdata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn (fn)
    (declare (xargs :guard (member-eq fn '(forth back))))
    (b* ((name
          (packn
           (list 'expdata-gen-lemma-instance-x1...xn-to- fn '-of-x1...xn)))
         (string (str::downcase-string (symbol-name fn)))
         (fn-of-x1...xn (packn (list fn '-of-x1...xn)))
         (expdata-gen-fn-of-terms (packn (list 'expdata-gen- fn '-of-terms))))
      `(define ,name ((lemma (or (symbolp lemma)
                                 (symbol-listp lemma))
                             "Lemma to generate an instance of.")
                      (old$ symbolp)
                      (arg-surjmaps expdata-symbol-surjmap-alistp)
                      (wrld plist-worldp))
         :guard (= (len (formals old$ wrld)) (len arg-surjmaps))
         :returns (lemma-instance true-listp)
         :verify-guards nil
         :short ,(str::cat "Generate a lemma instance where
                            each variable @('xi') is instantiated with
                            @('(" string "i xi)').")
         (b* ((x1...xn (formals old$ wrld))
              (,fn-of-x1...xn (,expdata-gen-fn-of-terms x1...xn arg-surjmaps))
              (inst (alist-to-doublets (pairlis$ x1...xn ,fn-of-x1...xn))))
           `(:instance ,lemma :extra-bindings-ok ,@inst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-lemma-instance-x1...xn-to-fn-of-x1...xn back)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-subst-x1...xn-with-back-of-x1...xn
  ((term pseudo-termp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (wrld plist-worldp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Substitute each formal @('xi') of @('old') in a term
          with the term @('(backi xi)'),
          where @('backi') is the conversion associated to @('xi')."
  (b* ((x1...xn (formals old$ wrld))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps)))
    (subcor-var x1...xn back-of-x1...xn term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-formal-of-unary ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of an (assumed) unary function."
  (cond ((symbolp fn) (car (formals fn wrld)))
        (t (car (lambda-formals fn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-formal-of-newp ((surjmap expdata-surjmapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('newp') predicate
          of a surjective mapping."
  (expdata-formal-of-unary (expdata-surjmap->newp surjmap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-formal-of-forth ((surjmap expdata-surjmapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('forth') conversion
          of a surjective mapping."
  (expdata-formal-of-unary (expdata-surjmap->forth surjmap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-formal-of-back ((surjmap expdata-surjmapp) (wrld plist-worldp))
  :returns (var "A @(tsee symbolp).")
  :verify-guards nil
  :short "Formal argument of the @('back') conversion
          of a surjective mapping."
  (expdata-formal-of-unary (expdata-surjmap->back surjmap) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expdata-gen-thm-instances-to-x1...xn
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
   (xdoc::@def "expdata-gen-thm-instances-to-x1...xn"))

  (defmacro expdata-gen-thm-instances-to-x1...xn (thm)
    (declare (xargs :guard (member-eq thm '(forth-image
                                            back-image
                                            back-of-forth
                                            newp-guard
                                            forth-guard
                                            back-guard))))
    (b* ((name (packn (list 'expdata-gen- thm '-instances-to-x1...xn)))
         (thm-selector (packn (list 'expdata-surjmap-> thm)))
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
         (fn-selector (packn (list 'expdata-surjmap-> fn)))
         (fn-string (str::downcase-string (symbol-name fn)))
         (param (packn (list fn '-arg))))
      `(define ,name ((arg-surjmaps expdata-symbol-surjmap-alistp)
                      (wrld plist-worldp))
         :returns (lemma-instances true-list-listp)
         :verify-guards nil
         :short ,(str::cat "Generate @('n') lemma instances
                            such that the @('i')-th instance
                            is of theorem @('" thm-string "')
                            and instantiates
                            the formal parameter of @('" fn-string "')
                            with @('xi').")
         (b* (((when (endp arg-surjmaps)) nil)
              (arg (caar arg-surjmaps))
              (surjmap (cdar arg-surjmaps))
              (,thm (,thm-selector surjmap))
              (,param (expdata-formal-of-unary (,fn-selector surjmap) wrld))
              (instance (list :instance ,thm
                              :extra-bindings-ok (list ,param arg)))
              (instances (,name (cdr arg-surjmaps) wrld)))
           (cons instance instances))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn forth-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn back-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn back-of-forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn newp-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn forth-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-x1...xn back-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expdata-gen-thm-instances-to-terms-back
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
   (xdoc::@def "expdata-gen-thm-instances-to-terms-back"))

  (defmacro expdata-gen-thm-instances-to-terms-back (thm)
    (declare (xargs :guard (member-eq thm '(forth-image
                                            back-of-forth
                                            forth-guard))))
    (b* ((name1 (packn (list 'expdata-gen- thm '-instances-to-terms-back)))
         (name1-aux (packn (list name1 '-aux)))
         (name2 (packn (list 'expdata-gen-all- thm '-instances-to-terms-back)))
         (name1-string (str::downcase-string (symbol-name name1)))
         (thm-selector (packn (list 'expdata-surjmap-> thm)))
         (thm-string (case thm
                       (forth-image "forthi-image")
                       (back-of-forth "backi-of-forthi")
                       (forth-guard "forthi-guard")
                       (t (impossible)))))
      `(progn
         (define ,name1 ((terms pseudo-term-listp)
                         (old$ symbolp)
                         (arg-surjmaps expdata-symbol-surjmap-alistp)
                         (wrld plist-worldp))
           :guard (= (len terms) (len arg-surjmaps))
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
                 (expdata-gen-back-of-terms x1...xn arg-surjmaps)))
             (,name1-aux terms arg-surjmaps x1...xn back-of-x1...xn wrld))
           :prepwork
           ((define ,name1-aux ((terms pseudo-term-listp)
                                (arg-surjmaps expdata-symbol-surjmap-alistp)
                                (x1...xn symbol-listp)
                                (back-of-x1...xn pseudo-term-listp)
                                (wrld plist-worldp))
              :guard (= (len terms) (len arg-surjmaps))
              :returns (lemma-instances true-list-listp)
              :verify-guards nil
              (b* (((when (endp terms)) nil)
                   (term (car terms))
                   (surjmap (cdar arg-surjmaps))
                   (,thm (,thm-selector surjmap))
                   (var (expdata-formal-of-forth surjmap wrld))
                   (term-with-back (subcor-var x1...xn back-of-x1...xn term))
                   (instance (list :instance ,thm
                                   :extra-bindings-ok
                                   (list var term-with-back)))
                   (instances (,name1-aux (cdr terms)
                                          (cdr arg-surjmaps)
                                          x1...xn
                                          back-of-x1...xn
                                          wrld)))
                (cons instance instances)))))
         (define ,name2 ((rec-calls pseudo-tests-and-call-listp)
                         (old$ symbolp)
                         (arg-surjmaps expdata-symbol-surjmap-alistp)
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
                (instances (,name1 updates old$ arg-surjmaps wrld))
                (more-instances (,name2 (cdr rec-calls) old$ arg-surjmaps wrld)))
             (append instances more-instances)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-terms-back forth-image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-terms-back back-of-forth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(expdata-gen-thm-instances-to-terms-back forth-guard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (inst (alist-to-doublets (pairlis$ x1...xn rec-call-args-back)))
       (instance `(:instance ,lemma :extra-bindings-ok ,@inst))
       (instances (expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back
                   lemma (cdr rec-calls) old$ arg-surjmaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (forth-rec-call-args-back
        (expdata-gen-forth-of-terms rec-call-args-back arg-surjmaps))
       (inst (alist-to-doublets (pairlis$ x1...xn forth-rec-call-args-back)))
       (instance `(:instance ,lemma :extra-bindings-ok ,@inst))
       (instances
        (expdata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         lemma (cdr rec-calls) old$ arg-surjmaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-lemma-instances-var-to-rec-calls-back
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (old$ symbolp)
   (rec-calls pseudo-tests-and-call-listp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (rec-call-back (subcor-var x1...xn back-of-x1...xn rec-call))
       (instance `(:instance ,lemma :extra-bindings-ok (,var ,rec-call-back)))
       (instances (expdata-gen-lemma-instances-var-to-rec-calls-back
                   lemma var old$ (cdr rec-calls) arg-surjmaps wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls pseudo-tests-and-call-listp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (rec-call-args-back
        (subcor-var-lst x1...xn back-of-x1...xn rec-call-args))
       (forth-of-rec-call-args-back
        (expdata-gen-forth-of-terms rec-call-args-back arg-surjmaps))
       (new-call (fcons-term new$ forth-of-rec-call-args-back))
       (instance `(:instance ,lemma :extra-bindings-ok (,var ,new-call)))
       (instances
        (expdata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
         lemma var (cdr rec-calls) old$ arg-surjmaps new$ wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-back-of-forth-instances-to-mv-nth
  ((terms pseudo-term-listp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (wrld plist-worldp))
  :guard (= (len terms) (len res-surjmaps))
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
       (j (caar res-surjmaps))
       (surjmap (cdar res-surjmaps))
       (back-of-forth (expdata-surjmap->back-of-forth surjmap))
       (var (expdata-formal-of-forth surjmap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,back-of-forth
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (expdata-gen-back-of-forth-instances-to-mv-nth
                   (cdr terms)
                   (cdr res-surjmaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-all-back-of-forth-instances-to-mv-nth
  ((rec-calls pseudo-tests-and-call-listp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the concatenation of
          all the @('n * r') lemma instances generated by
          @('expdata-gen-back-of-forth-instances-to-mv-nth')
          for all the recursive call arguments of @('old')
          passed as the @('terms') input."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (updates (fargs rec-call))
       (instances (expdata-gen-back-of-forth-instances-to-mv-nth
                   updates res-surjmaps wrld))
       (more-instances (expdata-gen-all-back-of-forth-instances-to-mv-nth
                        (cdr rec-calls) res-surjmaps wrld)))
    (append instances more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-forth-image-instances-to-mv-nth
  ((term pseudo-termp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
  (b* (((when (endp res-surjmaps)) nil)
       (j (caar res-surjmaps))
       (surjmap (cdar res-surjmaps))
       (forth-image (expdata-surjmap->forth-image surjmap))
       (var (expdata-formal-of-forth surjmap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,forth-image
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (expdata-gen-forth-image-instances-to-mv-nth
                   term
                   (cdr res-surjmaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-forth-guard-instances-to-mv-nth
  ((term pseudo-termp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
  (b* (((when (endp res-surjmaps)) nil)
       (j (caar res-surjmaps))
       (surjmap (cdar res-surjmaps))
       (forth-guard (expdata-surjmap->back-of-forth surjmap))
       (var (expdata-formal-of-forth surjmap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,forth-guard
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (expdata-gen-forth-guard-instances-to-mv-nth
                   term
                   (cdr res-surjmaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-back-guard-instances-to-mv-nth
  ((term pseudo-termp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
  (b* (((when (endp res-surjmaps)) nil)
       (j (caar res-surjmaps))
       (surjmap (cdar res-surjmaps))
       (back-guard (expdata-surjmap->back-guard surjmap))
       (var (expdata-formal-of-back surjmap wrld))
       (mv-nth-of-term (fcons-term* 'mv-nth (1- j) term))
       (instance `(:instance ,back-guard
                   :extra-bindings-ok (,var ,mv-nth-of-term)))
       (instances (expdata-gen-back-guard-instances-to-mv-nth
                   term
                   (cdr res-surjmaps)
                   wrld)))
    (cons instance instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-all-back-guard-instances-to-mv-nth
  ((old$ symbolp)
   (rec-calls pseudo-tests-and-call-listp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the concatenation of
          all the @('n * r') lemma instances generated by
          @('expdata-gen-back-guard-instances-to-mv-nth')
          for all the terms, passed as the @('term') input,
          of the form
          @('(new ... (forthi updatek-xi<...,(back xi),...>) ...)'),
          corresponding to all the recursive calls of @('old')."
  (b* (((when (endp rec-calls)) nil)
       (tests-and-call (car rec-calls))
       (rec-call (access tests-and-call tests-and-call :call))
       (updates (fargs rec-call))
       (x1...xn (formals old$ wrld))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (updates-back (subcor-var-lst x1...xn back-of-x1...xn updates))
       (forth-updates-back (expdata-gen-forth-of-terms updates-back
                                                       arg-surjmaps))
       (new-forth-updates-back (fcons-term new$ forth-updates-back))
       (instances (expdata-gen-back-guard-instances-to-mv-nth
                   new-forth-updates-back res-surjmaps wrld))
       (more-instances
        (expdata-gen-all-back-guard-instances-to-mv-nth
         old$ (cdr rec-calls) arg-surjmaps res-surjmaps new$ wrld)))
    (append instances more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-guard ((old$ symbolp)
                                  (arg-surjmaps expdata-symbol-surjmap-alistp)
                                  (predicate$ booleanp)
                                  (wrld plist-worldp))
  :returns (new-guard "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the guard of the new function."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (expdata-gen-newp-of-terms x1...xn arg-surjmaps)))
    (if predicate$
        (conjoin newp-of-x1...xn)
      (b* ((old-guard (uguard old$ wrld))
           (old-guard-with-back-of-x1...xn
            (expdata-gen-subst-x1...xn-with-back-of-x1...xn old-guard
                                                            old$
                                                            arg-surjmaps
                                                            wrld)))
        (conjoin (append newp-of-x1...xn
                         (list old-guard-with-back-of-x1...xn)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-body-pred ((old$ symbolp)
                                      (arg-surjmaps expdata-symbol-surjmap-alistp)
                                      (res-surjmaps expdata-pos-surjmap-alistp)
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
    "First we transform any recursive calls via @('expdata-xform-rec-calls'),
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
        (expdata-xform-rec-calls
         old-body old$ arg-surjmaps res-surjmaps new$))
       (old-body-with-back-of-x1...xn
        (expdata-gen-subst-x1...xn-with-back-of-x1...xn
         old-body-with-new-rec-calls
         old$
         arg-surjmaps
         wrld))
       (newp-of-x1...xn (expdata-gen-newp-of-terms x1...xn arg-surjmaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn)))
    (if (equal newp-of-x1...xn-conj *t*)
        old-body-with-back-of-x1...xn
      (conjoin2 `(mbt$ ,newp-of-x1...xn-conj)
                old-body-with-back-of-x1...xn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-body-nonpred
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
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
    "First we transform any recursive calls via @('expdata-xform-rec-calls'),
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
     in which case we omit test and `else' branch.")
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
        (expdata-xform-rec-calls
         old-body old$ arg-surjmaps res-surjmaps new$))
       (old-body-with-back-of-x1...xn
        (expdata-gen-subst-x1...xn-with-back-of-x1...xn
         old-body-with-new-rec-calls
         old$
         arg-surjmaps
         wrld))
       (newp-of-x1...xn (expdata-gen-newp-of-terms x1...xn arg-surjmaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn))
       (then-branch
        (cond ((endp res-surjmaps) old-body-with-back-of-x1...xn)
              ((endp (cdr res-surjmaps))
               (apply-fn-into-ifs (expdata-surjmap->forth (cdar res-surjmaps))
                                  old-body-with-back-of-x1...xn))
              (t (b* ((y1...ym (expdata-gen-result-vars old$ m))
                      (forth-of-y1...ym (expdata-gen-forth-of-terms
                                         y1...ym res-surjmaps)))
                   (make-mv-let-call 'mv y1...ym :all
                                     old-body-with-back-of-x1...xn
                                     (fcons-term 'mv forth-of-y1...ym))))))
       (else-branch (if (> m 1)
                        (fcons-term 'mv (repeat m nil))
                      nil)))
    (cond ((not (recursivep old$ nil wrld)) then-branch)
          ((equal newp-of-x1...xn-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-x1...xn-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-body ((old$ symbolp)
                                 (arg-surjmaps expdata-symbol-surjmap-alistp)
                                 (res-surjmaps expdata-pos-surjmap-alistp)
                                 (predicate$ booleanp)
                                 (new$ symbolp)
                                 (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function."
  (if predicate$
      (expdata-gen-new-fn-body-pred old$ arg-surjmaps res-surjmaps new$ wrld)
    (expdata-gen-new-fn-body-nonpred
     old$ arg-surjmaps res-surjmaps new$ wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-measure ((old$ symbolp)
                                    (arg-surjmaps expdata-symbol-surjmap-alistp)
                                    (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the measure of the function, if recursive."
  (b* ((old-measure (measure old$ wrld)))
    (expdata-gen-subst-x1...xn-with-back-of-x1...xn old-measure
                                                    old$
                                                    arg-surjmaps
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-termination-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the termination of the new function,
          if recursive."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (instance-termination-thm-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:termination-theorem ,old$) old$ arg-surjmaps wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instance-oldp-of-rec-call-args
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args old$ arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-termination-thm-old
             ,@instances-back-image
             ,instance-oldp-of-rec-call-args
             ,@instances-back-of-forth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn ((old$ symbolp)
                            (arg-surjmaps expdata-symbol-surjmap-alistp)
                            (res-surjmaps expdata-pos-surjmap-alistp)
                            (predicate$ booleanp)
                            (new$ symbolp)
                            (new-enable$ booleanp)
                            (verify-guards$ booleanp)
                            (untranslate$ untranslate-specifier-p)
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
     see @(tsee expdata-gen-new-fn-verify-guards).")
   (xdoc::p
    "If the old function returns a multi-value result,
     we adjust the body of the new function to do the same."))
  (b* ((macro (function-intro-macro new-enable$ (non-executablep old$ wrld)))
       (formals (formals old$ wrld))
       (body (expdata-gen-new-fn-body old$ arg-surjmaps res-surjmaps
                                      predicate$ new$ wrld))
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
               ((nil) body)
               (t (untranslate body nil wrld))))
       (guard (expdata-gen-new-fn-guard old$ arg-surjmaps predicate$ wrld))
       (guard (conjoin (flatten-ands-in-lit guard)))
       (guard (untranslate guard nil wrld))
       (recursive (recursivep old$ nil wrld))
       (wfrel? (if recursive
                   (well-founded-relation old$ wrld)
                 nil))
       (measure? (if recursive
                     (expdata-gen-new-fn-measure old$ arg-surjmaps wrld)
                   nil))
       (termination-hints? (if recursive
                               (expdata-gen-new-fn-termination-hints
                                appcond-thm-names old$ arg-surjmaps wrld)
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

(define expdata-gen-new-to-old-thm-formula
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (new-to-old-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the new function in terms of the old function."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (expdata-gen-newp-of-terms x1...xn arg-surjmaps))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (old-call (fcons-term old$ back-of-x1...xn))
       (new-call (fcons-term new$ x1...xn))
       (consequent
        (case (len res-surjmaps)
          (0 `(equal ,new-call ,old-call))
          (1 (b* ((forth-res (expdata-surjmap->forth (cdar res-surjmaps)))
                  (forth-of-old-call (apply-term* forth-res old-call)))
               `(equal ,new-call ,forth-of-old-call)))
          (t (b* ((mv-nths-of-new-call (make-mv-nth-calls new-call
                                                          (len res-surjmaps)))
                  (mv-nths-of-old-call (make-mv-nth-calls old-call
                                                          (len res-surjmaps)))
                  (forth-of-mv-nths-of-old-call
                   (expdata-gen-forth-of-terms mv-nths-of-old-call
                                               res-surjmaps)))
               (conjoin-equalities mv-nths-of-new-call
                                   forth-of-mv-nths-of-old-call))))))
    (implicate (conjoin newp-of-x1...xn)
               consequent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-to-old-thm-hints-nonrec ((old-fn-unnorm-name symbolp)
                                                 (new-fn-unnorm-name symbolp))
  :returns (hints true-listp)
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are not recursive."
  `(("Goal" :in-theory '(,old-fn-unnorm-name ,new-fn-unnorm-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-to-old-thm-hints-rec-0res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
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

(define expdata-gen-new-to-old-thm-hints-rec-1res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-oldp-of-old
        (expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back
         oldp-of-old
         rec-calls
         old$
         arg-surjmaps
         wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (res-surjmap (cdar res-surjmaps))
       (back-of-forth-res (expdata-surjmap->back-of-forth res-surjmap))
       (var (expdata-formal-of-forth res-surjmap wrld))
       (instances-back-of-forth-res
        (expdata-gen-lemma-instances-var-to-rec-calls-back back-of-forth-res
                                                           var
                                                           old$
                                                           rec-calls
                                                           arg-surjmaps
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

(define expdata-gen-new-to-old-thm-hints-rec-mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-oldp-of-old
        (expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back
         oldp-of-old
         rec-calls
         old$
         arg-surjmaps
         wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-back-of-forth-res
        (expdata-gen-all-back-of-forth-instances-to-mv-nth rec-calls
                                                           res-surjmaps
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

(define expdata-gen-new-to-old-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function."
  (if (recursivep old$ nil wrld)
      (case (len res-surjmaps)
        (0 (expdata-gen-new-to-old-thm-hints-rec-0res appcond-thm-names
                                                      old$
                                                      arg-surjmaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld))
        (1 (expdata-gen-new-to-old-thm-hints-rec-1res appcond-thm-names
                                                      old$
                                                      arg-surjmaps
                                                      res-surjmaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld))
        (t (expdata-gen-new-to-old-thm-hints-rec-mres appcond-thm-names
                                                      old$
                                                      arg-surjmaps
                                                      res-surjmaps
                                                      new$
                                                      old-fn-unnorm-name
                                                      new-fn-unnorm-name
                                                      wrld)))
    (expdata-gen-new-to-old-thm-hints-nonrec old-fn-unnorm-name
                                             new-fn-unnorm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-to-old-thm
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
  (b* ((formula (expdata-gen-new-to-old-thm-formula old$
                                                    arg-surjmaps
                                                    res-surjmaps
                                                    new$
                                                    wrld))
       (formula (untranslate formula t wrld))
       (hints (expdata-gen-new-to-old-thm-hints appcond-thm-names
                                                old$
                                                arg-surjmaps
                                                res-surjmaps
                                                new$
                                                old-fn-unnorm-name
                                                new-fn-unnorm-name
                                                wrld)))
    (evmac-generate-defthm new-to-old$
                           :formula formula
                           :hints hints
                           :enable new-to-old-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-old-to-new-thm-formula
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :returns (old-to-new-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the old function in terms of the new function."
  (b* ((x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (expdata-gen-oldp-of-terms x1...xn arg-surjmaps))
       (forth-of-x1...xn (expdata-gen-forth-of-terms x1...xn arg-surjmaps))
       (new-call (fcons-term new$ forth-of-x1...xn))
       (old-call (fcons-term old$ x1...xn))
       (consequent
        (case (len res-surjmaps)
          (0 `(equal ,old-call ,new-call))
          (1 (b* ((back-res (expdata-surjmap->back (cdar res-surjmaps)))
                  (back-of-new-call (apply-term* back-res new-call)))
               `(equal ,old-call ,back-of-new-call)))
          (t (b* ((mv-nths-of-old-call (make-mv-nth-calls old-call
                                                          (len res-surjmaps)))
                  (mv-nths-of-new-call (make-mv-nth-calls new-call
                                                          (len res-surjmaps)))
                  (back-of-mv-nths-of-new-call
                   (expdata-gen-back-of-terms mv-nths-of-new-call
                                              res-surjmaps)))
               (conjoin-equalities mv-nths-of-old-call
                                   back-of-mv-nths-of-new-call))))))
    (implicate (conjoin oldp-of-x1...xn)
               consequent)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-old-to-new-thm-hints-0res
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when no result is being transformed."
  (b* ((instances-forth-image
        (expdata-gen-forth-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-back-of-forth-instances-to-x1...xn arg-surjmaps wrld))
       (instance-new-to-old
        (expdata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-surjmaps
                                                                wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-old-to-new-thm-hints-1res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when the result of a single-valued function is being transformed."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-forth-image
        (expdata-gen-forth-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-back-of-forth-instances-to-x1...xn arg-surjmaps wrld))
       (instance-new-to-old
        (expdata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-surjmaps
                                                                wrld))
       (res-surjmap (cdar res-surjmaps))
       (back-of-forth-res (expdata-surjmap->back-of-forth res-surjmap))
       (var (expdata-formal-of-forth res-surjmap wrld))
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

(define expdata-gen-old-to-new-thm-hints-mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when some result of a multi-valued function is being transformed."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-forth-image
        (expdata-gen-forth-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-back-of-forth-instances-to-x1...xn arg-surjmaps wrld))
       (instance-new-to-old
        (expdata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old$
                                                                old$
                                                                arg-surjmaps
                                                                wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (instances-back-of-forth-res
        (expdata-gen-back-of-forth-instances-to-mv-nth
         (repeat (len res-surjmaps) old-call)
         res-surjmaps
         wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old
             ,oldp-of-old
             ,@instances-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-old-to-new-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function."
  (case (len res-surjmaps)
    (0 (expdata-gen-old-to-new-thm-hints-0res old$
                                              arg-surjmaps
                                              new-to-old$
                                              wrld))
    (1 (expdata-gen-old-to-new-thm-hints-1res appcond-thm-names
                                              old$
                                              arg-surjmaps
                                              res-surjmaps
                                              new-to-old$
                                              wrld))
    (t (expdata-gen-old-to-new-thm-hints-mres appcond-thm-names
                                              old$
                                              arg-surjmaps
                                              res-surjmaps
                                              new-to-old$
                                              wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-old-to-new-thm
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-to-new-enable$ booleanp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (mv (old-to-new-local-event "A @(tsee pseudo-event-formp).")
               (old-to-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the @('old-to-new') theorem."
  (b* ((formula (expdata-gen-old-to-new-thm-formula
                 old$ arg-surjmaps res-surjmaps new$ wrld))
       (formula (untranslate formula t wrld))
       (hints (expdata-gen-old-to-new-thm-hints appcond-thm-names
                                                old$
                                                arg-surjmaps
                                                res-surjmaps
                                                new-to-old$
                                                wrld)))
    (evmac-generate-defthm old-to-new$
                           :formula formula
                           :hints hints
                           :enable old-to-new-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-newp-of-new-thm-formula
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-surjmaps)
  :returns (formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (expdata-gen-newp-of-terms x1...xn arg-surjmaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn))
       (new-call (fcons-term new$ x1...xn))
       (m (len res-surjmaps)))
    (if (= m 1)
        (b* ((res-surjmap (cdar res-surjmaps))
             (newp-res (expdata-surjmap->newp res-surjmap)))
          (implicate newp-of-x1...xn-conj
                     (fcons-term* newp-res new-call)))
      (b* ((y1...ym (expdata-gen-result-vars new$ m))
           (newp-of-y1...ym (expdata-gen-newp-of-terms y1...ym res-surjmaps)))
        (implicate newp-of-x1...xn-conj
                   (make-mv-let-call 'mv y1...ym :all new-call
                                     (conjoin newp-of-y1...ym)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-newp-of-new-thm-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-surjmaps)
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to prove the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instance-oldp-of-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-image
        (if (= (len res-surjmaps) 1)
            (b* ((res-surjmap (cdar res-surjmaps))
                 (forth-image-res (expdata-surjmap->forth-image res-surjmap))
                 (var (expdata-formal-of-forth res-surjmap wrld)))
              `((:instance ,forth-image-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (expdata-gen-forth-image-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-surjmaps
                                                       wrld))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-back-image
             ,instance-oldp-of-old
             ,@instances-forth-image
             ,new-to-old$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-newp-of-new-thm
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (new-to-old$ symbolp)
   (newp-of-new$ symbolp)
   (newp-of-new-enable$ booleanp)
   (appcond-thm-names symbol-symbol-alistp)
   (wrld plist-worldp))
  :guard (consp res-surjmaps)
  :returns (mv (newp-of-new-local-event "A @(tsee pseudo-event-formp).")
               (newp-of-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that says that
          the new function maps values in the new representation
          to values in the old representation."
  (b* ((formula (expdata-gen-newp-of-new-thm-formula old$
                                                     arg-surjmaps
                                                     res-surjmaps
                                                     new$
                                                     wrld))
       (formula (untranslate formula t wrld))
       (hints (expdata-gen-newp-of-new-thm-hints appcond-thm-names
                                                 old$
                                                 arg-surjmaps
                                                 res-surjmaps
                                                 new-to-old$
                                                 wrld)))
    (evmac-generate-defthm newp-of-new$
                           :formula formula
                           :hints hints
                           :enable newp-of-new-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards-hints-pred-nonrec
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instance-old-guard-pred
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn old-guard-pred
                                                               old$
                                                               arg-surjmaps
                                                               wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard
             ,instance-old-guard-pred
             ,@instances-back-image)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards-hints-pred-rec
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-guard
        (expdata-gen-forth-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instance-old-guard-pred
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn old-guard-pred
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-new-to-old
        (expdata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         new-to-old$
         rec-calls
         old$
         arg-surjmaps
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

(define expdata-gen-new-fn-verify-guards-hints-pred
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (new-to-old$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('t')."
  (if (recursivep old$ nil wrld)
      (expdata-gen-new-fn-verify-guards-hints-pred-rec appcond-thm-names
                                                       old$
                                                       arg-surjmaps
                                                       new-to-old$
                                                       wrld)
    (expdata-gen-new-fn-verify-guards-hints-pred-nonrec appcond-thm-names
                                                        old$
                                                        arg-surjmaps
                                                        wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards-hints-nonpred-nonrec-0res
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and no result is being transformed."
  (b* ((instance-guard-thm-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards-hints-nonpred-nonrec-1res/mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (old-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :guard (consp res-surjmaps)
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
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instance-oldp-of-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-guard-res
        (if (= (len res-surjmaps) 1)
            (b* ((res-surjmap (cdar res-surjmaps))
                 (forth-guard-res (expdata-surjmap->forth-guard res-surjmap))
                 (var (expdata-formal-of-forth res-surjmap wrld)))
              `((:instance ,forth-guard-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (expdata-gen-forth-guard-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-surjmaps
                                                       wrld)))
       (instance-old-fn-unnorm-name
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         old-fn-unnorm-name
         old$
         arg-surjmaps
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

(define expdata-gen-new-fn-verify-guards-hints-nonpred-rec-0res
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (old-to-new$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('surjmaps') does not include @(':result')."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (instance-guard-thm-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-guard
        (expdata-gen-all-forth-guard-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-old-to-new
        (expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back old-to-new$
                                                                   rec-calls
                                                                   old$
                                                                   arg-surjmaps
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

(define expdata-gen-new-fn-verify-guards-hints-nonpred-rec-1res/mres
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
   (new$ symbolp)
   (old-to-new$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new$ symbolp)
   (wrld plist-worldp))
  :guard (consp res-surjmaps)
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('surjmaps') includes @(':result')."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old appcond-thm-names)))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args appcond-thm-names)))
       (rec-calls (recursive-calls old$ wrld))
       (instance-guard-thm-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn `(:guard-theorem
                                                                 ,old$)
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instances-newp-guard
        (expdata-gen-newp-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-guard
        (expdata-gen-all-forth-guard-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-guard
        (expdata-gen-back-guard-instances-to-x1...xn arg-surjmaps wrld))
       (instances-forth-image
        (expdata-gen-all-forth-image-instances-to-terms-back rec-calls
                                                             old$
                                                             arg-surjmaps
                                                             wrld))
       (instances-back-image
        (expdata-gen-back-image-instances-to-x1...xn arg-surjmaps wrld))
       (instances-back-of-forth
        (expdata-gen-all-back-of-forth-instances-to-terms-back rec-calls
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instance-oldp-of-rec-call-args
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         oldp-of-rec-call-args
         old$
         arg-surjmaps
         wrld))
       (instances-old-to-new
        (expdata-gen-lemma-instances-x1...xn-to-rec-call-args-back old-to-new$
                                                                   rec-calls
                                                                   old$
                                                                   arg-surjmaps
                                                                   wrld))
       (instance-oldp-of-old
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn oldp-of-old
                                                               old$
                                                               arg-surjmaps
                                                               wrld))
       (instance-old-fn-unnorm-name
        (expdata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         old-fn-unnorm-name
         old$
         arg-surjmaps
         wrld))
       (instances-newp-of-new
        (expdata-gen-lemma-instances-x1...xn-to-forth-rec-call-args-back
         newp-of-new$
         rec-calls
         old$
         arg-surjmaps
         wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (expdata-gen-back-of-terms x1...xn arg-surjmaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (instances-forth-guard-res
        (if (= (len res-surjmaps) 1)
            (b* ((res-surjmap (cdar res-surjmaps))
                 (forth-guard-res (expdata-surjmap->forth-guard res-surjmap))
                 (var (expdata-formal-of-forth res-surjmap wrld)))
              `((:instance ,forth-guard-res
                 :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
          (expdata-gen-forth-guard-instances-to-mv-nth old-call-of-back-x1...xn
                                                       res-surjmaps
                                                       wrld)))
       (instances-back-guard-res
        (if (= (len res-surjmaps) 1)
            (b* ((res-surjmap (cdar res-surjmaps))
                 (back-guard-res (expdata-surjmap->back-guard res-surjmap))
                 (var (expdata-formal-of-back res-surjmap wrld)))
              (expdata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
               back-guard-res
               var
               rec-calls
               old$
               arg-surjmaps
               new$
               wrld))
          (expdata-gen-all-back-guard-instances-to-mv-nth old$
                                                          rec-calls
                                                          arg-surjmaps
                                                          res-surjmaps
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

(define expdata-gen-new-fn-verify-guards-hints-nonpred
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
      (if (consp res-surjmaps)
          (expdata-gen-new-fn-verify-guards-hints-nonpred-rec-1res/mres
           appcond-thm-names
           old$
           arg-surjmaps
           res-surjmaps
           new$
           old-to-new$
           old-fn-unnorm-name
           newp-of-new$
           wrld)
        (expdata-gen-new-fn-verify-guards-hints-nonpred-rec-0res
         appcond-thm-names
         old$
         arg-surjmaps
         old-to-new$
         wrld))
    (if (consp res-surjmaps)
        (expdata-gen-new-fn-verify-guards-hints-nonpred-nonrec-1res/mres
         appcond-thm-names
         old$
         arg-surjmaps
         res-surjmaps
         old-fn-unnorm-name
         wrld)
      (expdata-gen-new-fn-verify-guards-hints-nonpred-nonrec-0res old$
                                                                  arg-surjmaps
                                                                  wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards-hints
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
      (expdata-gen-new-fn-verify-guards-hints-pred appcond-thm-names
                                                   old$
                                                   arg-surjmaps
                                                   new-to-old$
                                                   wrld)
    (expdata-gen-new-fn-verify-guards-hints-nonpred appcond-thm-names
                                                    old$
                                                    arg-surjmaps
                                                    res-surjmaps
                                                    new$
                                                    old-to-new$
                                                    old-fn-unnorm-name
                                                    newp-of-new$
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expdata-gen-new-fn-verify-guards
  ((appcond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
  (b* ((hints (expdata-gen-new-fn-verify-guards-hints appcond-thm-names
                                                      old$
                                                      arg-surjmaps
                                                      res-surjmaps
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

(define expdata-gen-everything
  ((old$ symbolp)
   (arg-surjmaps expdata-symbol-surjmap-alistp)
   (res-surjmaps expdata-pos-surjmap-alistp)
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
     the expansion of @(tsee expdata) (the @(tsee encapsulate)),
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
       (surjmaps (append (strip-cdrs arg-surjmaps)
                         (strip-cdrs res-surjmaps)))
       (surjmaps (remove-duplicates-equal surjmaps))
       (defsurj-events (expdata-gen-defsurjs surjmaps verify-guards$ print$))
       (appconds (expdata-gen-appconds old$
                                       arg-surjmaps
                                       res-surjmaps
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
        (expdata-gen-new-fn old$
                            arg-surjmaps
                            res-surjmaps
                            predicate$
                            new$
                            new-enable$
                            verify-guards$
                            untranslate$
                            appcond-thm-names
                            wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name
            &)
        (install-not-normalized-event new$ t names-to-avoid wrld))
       ((mv new-to-old-thm-local-event
            new-to-old-thm-exported-event)
        (expdata-gen-new-to-old-thm old$
                                    arg-surjmaps
                                    res-surjmaps
                                    new$
                                    new-to-old$
                                    new-to-old-enable$
                                    appcond-thm-names
                                    old-fn-unnorm-name
                                    new-fn-unnorm-name
                                    wrld))
       ((mv newp-of-new-thm-local-event?
            newp-of-new-thm-exported-event?)
        (if (consp res-surjmaps)
            (expdata-gen-newp-of-new-thm old$
                                         arg-surjmaps
                                         res-surjmaps
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
        (expdata-gen-old-to-new-thm appcond-thm-names
                                    old$
                                    arg-surjmaps
                                    res-surjmaps
                                    new$
                                    old-to-new$
                                    old-to-new-enable$
                                    new-to-old$
                                    wrld))
       (new-fn-verify-guards-event? (and verify-guards$
                                         (list
                                          (expdata-gen-new-fn-verify-guards
                                           appcond-thm-names
                                           old$
                                           arg-surjmaps
                                           res-surjmaps
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
                             ,@defsurj-events
                             ,@appcond-thm-events
                             (evmac-prepare-proofs)
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

(define expdata-fn (old
                    surjmaps
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
                    (call pseudo-event-formp)
                    ctx
                    state)
  :returns (mv erp
               (event-form "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (expdata-implementation)
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
                  arg-surjmaps
                  res-surjmaps
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
        (expdata-process-inputs old
                                surjmaps
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
       ((er event) (expdata-gen-everything old$
                                           arg-surjmaps
                                           res-surjmaps
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
                                           names-to-avoid
                                           call
                                           ctx
                                           state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expdata-macro-definition
  :parents (expdata-implementation)
  :short "Definition of the @(tsee expdata) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee expdata-fn).")
   (xdoc::@def "expdata"))
  (defmacro expdata (&whole
                     call
                     ;; mandatory inputs:
                     old
                     surjmaps
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
                     (show-only 'nil))
    `(make-event-terse (expdata-fn ',old
                                   ',surjmaps
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
                                   ',call
                                   (cons 'expdata ',old)
                                   state)
                       :suppress-errors ,(not print))))
