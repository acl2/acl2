; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

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
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/untranslate-specifiers")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 isodata

 :item-state t

 :item-wrld t

 :item-ctx t

 :items

 ("@('old'),
   @('isomaps'),
   @('predicate'),
   @('new-name'),
   @('new-enable'),
   @('thm-name'),
   @('thm-enable'),
   @('non-executable'),
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
   @('new-name$'),
   @('new-enable$'),
   @('thm-name$'),
   @('thm-enable$'),
   @('non-executable'),
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

  "@('arg-isomaps') is an alist
   from formal arguments of @('old')
   to isomorphic mapping records that specify
   how the associated formal arguments must be transformed.
   There are never duplicate keys.
   When input processing is complete,
   the keys are exactly all the formal arguments of @('old'), in order."

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
   Currently this is turned into @('res-isomaps?') (see below)
   at the end of input processing,
   since the implementation does not yet support
   the transformation of results of multi-valued functions;
   this support will be added soon."

  "@('res-isomap?') is the isomorphic mapping record for the function result,
   or @('nil') if the result is not transformed.
   This is currently obtained from @('res-isomaps'),
   after ensuring the this alist contains no more than one pair,
   because the implementation does not yet support
   the transformation of results of multi-valued functions;
   this support will be added soon."

  "@('res-isomap') is the isomorphic mapping record for the function result.
   This is the same as @('res-isomap?'), when that is not @('nil')."

  "@('app-cond-thm-names') is an alist
   from the applicability condition keywords
   to the corresponding theorem names."

  "@('old-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the old function."

  "@('new-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the new function."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing
 isodata
 (xdoc::p
  "The input processing part of @(tsee isodata) has been already extended
   to support the transformation of results of multi-valued functions,
   by allowing keywords @(':resultj'), where @('j') is a positive integer,
   as part of the @('arg/res-listk') components of the @('isomaps') input,
   and by also allowing @(':result') as an abbreviation of @(':result1')
   when the function is single-valued.
   However, the rest of the transformation has not been extended yet,
   and therefore at the end of input processing we ensure that
   only results of single-valued functions are isomorphically transformed.
   This final input pocessing code will be removed
   once the rest of the transformation has been extended."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate isodata-isomap
  :short "Information about an isomorphic mapping according to which
          (some of) the target function's arguments and results
          are transformed."
  :long
  (xdoc::topstring-p
   "This aggregate is somewhat similar to @(tsee acl2::defiso-infop),
    and in fact it corresponds
    either to an existing @(tsee defiso) that is referenced
    in an @('isok') input of @(tsee isodata),
    or to a locally generated @(tsee defiso) that is determined
    in the @('isok') input of @(tsee isodata).
    However, this aggregate is not stored in any table;
    it has some fields in common (except for their names)
    with @(tsee acl2::defiso-infop),
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

(define isodata-maybe-isomapp (x)
  :short "Recognize isomorphic mapping records and @('nil')."
  (or (isodata-isomapp x)
      (null x))
  ///
  (defrule isodata-maybe-isomapp-when-isomapp
    (implies (isodata-isomapp x)
             (isodata-maybe-isomapp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist isodata-isomap-listp (x)
  :short "Recognize true lists of isomorphic mapping records."
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
             (isodata-isomapp (cdr (assoc-equal k x)))))

  (defruled alistp-when-isodata-symbol-isomap-alistp-rewrite
    (implies (isodata-symbol-isomap-alistp x)
             (alistp x))))

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
             (isodata-isomapp (cdr (assoc-equal k x)))))

  (defruled alistp-when-isodata-pos-isomap-alistp-rewrite
    (implies (isodata-pos-isomap-alistp x)
             (alistp x))))

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
       ((er &) (ensure-function-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-defined$ old$ description t nil))
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
                   (ensure-function-guard-verified$
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
      (b* (((er &) (ensure-symbol-list$
                    arg/res-list
                    (msg "Since the ~n0 ARG/RES component of the second input ~
                          is not an atom, it"
                         (list k))
                    t nil))
           ((er &) (ensure-list-no-duplicates$
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
  (b* ((table (table-alist *defiso-table-name* wrld)))
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
               (new-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Return fresh @(tsee defiso) theorem names."
  :long
  (xdoc::topstring
   (xdoc::p
    "These will be used as the @(':thm-names') input
     of a @(tsee defiso) that @(tsee isodata) will generate locally,
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
       (forth-image (fresh-logical-name-with-$s-suffix
                     (add-suffix prefix (symbol-name :alpha-image))
                     nil
                     names-to-avoid
                     wrld))
       (names-to-avoid (cons forth-image names-to-avoid))
       (back-image (fresh-logical-name-with-$s-suffix
                    (add-suffix prefix (symbol-name :beta-image))
                    nil
                    names-to-avoid
                    wrld))
       (names-to-avoid (cons back-image names-to-avoid))
       (back-of-forth (fresh-logical-name-with-$s-suffix
                       (add-suffix prefix (symbol-name :beta-of-alpha))
                       nil
                       names-to-avoid
                       wrld))
       (names-to-avoid (cons back-of-forth names-to-avoid))
       (forth-of-back (fresh-logical-name-with-$s-suffix
                       (add-suffix prefix (symbol-name :alpha-of-beta))
                       nil
                       names-to-avoid
                       wrld))
       (names-to-avoid (cons forth-of-back names-to-avoid))
       (oldp-guard (and verify-guards$
                        (fresh-logical-name-with-$s-suffix
                         (add-suffix prefix (symbol-name :doma-guard))
                         nil
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons oldp-guard names-to-avoid)
                         names-to-avoid))
       (newp-guard (and verify-guards$
                        (fresh-logical-name-with-$s-suffix
                         (add-suffix prefix (symbol-name :domb-guard))
                         nil
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons newp-guard names-to-avoid)
                         names-to-avoid))
       (forth-guard (and verify-guards$
                         (fresh-logical-name-with-$s-suffix
                          (add-suffix prefix (symbol-name :alpha-guard))
                          nil
                          names-to-avoid
                          wrld)))
       (names-to-avoid (if verify-guards$
                           (cons forth-guard names-to-avoid)
                         names-to-avoid))
       (back-guard (and verify-guards$
                        (fresh-logical-name-with-$s-suffix
                         (add-suffix prefix (symbol-name :beta-guard))
                         nil
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons back-guard names-to-avoid)
                         names-to-avoid))
       (forth-injective (fresh-logical-name-with-$s-suffix
                         (add-suffix prefix (symbol-name :alpha-injective))
                         nil
                         names-to-avoid
                         wrld))
       (names-to-avoid (cons forth-injective names-to-avoid))
       (back-injective (fresh-logical-name-with-$s-suffix
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
               (result "A tuple @('(isomap names-to-avoid)')
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
     and then we check that they are all unary and single-valued;
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
      (b* (((er &) (ensure-symbol$ iso
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
           ((defiso-info info) info)
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
          (acl2::defiso-process-functions
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
               (result "A tuple @('(arg-isomaps res-isomaps names-to-avoid)')
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
               (result "A tuple @('(arg-isomaps res-isomaps names-to-avoid)')
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
               (result "A tuple @('(arg-isomaps res-isomaps names-to-avoid)')
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

(define isodata-process-thm-name (thm-name
                                  (old$ symbolp)
                                  (new-name$ symbolp)
                                  ctx
                                  state)
  :returns (mv erp
               (thm-name$ "A @(tsee symbolp)
                           to use for the theorem
                           that relates the old and new functions.")
               state)
  :mode :program
  :short "Process the @(':thm-name') input."
  (b* (((er &) (ensure-symbol$ thm-name "The :THM-NAME input" t nil))
       (name (if (eq thm-name :auto)
                 (make-paired-name old$ new-name$ 2 (w state))
               thm-name))
       (description (msg "The name ~x0 of the theorem ~
                          that relates the target function ~x1 ~
                          to the new function ~x2, ~
                          ~@3,"
                         name old$ new-name$
                         (if (eq thm-name :auto)
                             "automatically generated ~
                              since the :THM-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :THM-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil))
       ((er &) (ensure-symbol-different$
                name new-name$
                (msg "the name ~x0 of the new function ~
                      (determined by the :NEW-NAME input)."
                     new-name$)
                description
                t nil)))
    (value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *isodata-app-cond-keywords*
  :short "Keywords that identify the applicability conditions."
  '(:oldp-of-old
    :oldp-when-old
    :oldp-of-rec-call-args
    :old-guard
    :old-guard-pred)
  ///

  (defruled keyword-listp-of-*isodata-app-cond-keywords*
    (keyword-listp *isodata-app-cond-keywords*))

  (defruled no-duplicatesp-eq-of-*isodata-app-cond-keywords*
    (no-duplicatesp-eq *isodata-app-cond-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-app-cond-keywordp (x)
  :returns (yes/no booleanp)
  :short "Recognize the keywords of the applicability conditions."
  (and (member-eq x *isodata-app-cond-keywords*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist isodata-app-cond-keyword-listp (x)
  (isodata-app-cond-keywordp x)
  :short "Recognize true lists of the keywords of the applicability conditions."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-app-cond-present-p ((keyword isodata-app-cond-keywordp)
                                    (old$ symbolp)
                                    (res-isomaps isodata-pos-isomap-alistp)
                                    (predicate$ booleanp)
                                    (verify-guards$ booleanp)
                                    (wrld plist-worldp))
  :returns (yes/no booleanp :hyp (and (booleanp res$)
                                      (booleanp predicate$)
                                      (booleanp verify-guards$)))
  :short "Check if an applicability condition is present."
  (case keyword
    (:oldp-of-old (and res-isomaps t))
    (:oldp-when-old predicate$)
    (:oldp-of-rec-call-args (and (irecursivep old$ wrld) t))
    (:old-guard (and verify-guards$ (not predicate$)))
    (:old-guard-pred (and verify-guards$ predicate$))
    (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable isodata-app-cond-keywordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-app-cond-present-keywords
  ((old$ symbolp)
   (res-isomaps isodata-pos-isomap-alistp)
   (predicate$ booleanp)
   (verify-guards$ booleanp)
   (wrld plist-worldp))
  :returns (present-keywords isodata-app-cond-keyword-listp)
  :short "Keywords of the applicability conditions that are present."
  (isodata-app-cond-present-keywords-aux *isodata-app-cond-keywords*
                                         old$
                                         res-isomaps
                                         predicate$
                                         verify-guards$
                                         wrld)

  :prepwork
  ((define isodata-app-cond-present-keywords-aux
     ((keywords isodata-app-cond-keyword-listp)
      (old$ symbolp)
      (res-isomaps isodata-pos-isomap-alistp)
      (predicate$ booleanp)
      (verify-guards$ booleanp)
      (wrld plist-worldp))
     :returns (present-keywords isodata-app-cond-keyword-listp
                                :hyp (isodata-app-cond-keyword-listp keywords))
     :parents nil
     (if (endp keywords)
         nil
       (if (isodata-app-cond-present-p (car keywords)
                                       old$
                                       res-isomaps
                                       predicate$
                                       verify-guards$
                                       wrld)
           (cons (car keywords)
                 (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                        old$
                                                        res-isomaps
                                                        predicate$
                                                        verify-guards$
                                                        wrld))
         (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                old$
                                                res-isomaps
                                                predicate$
                                                verify-guards$
                                                wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-inputs (old
                                isomaps
                                predicate
                                new-name
                                new-enable
                                thm-name
                                thm-enable
                                non-executable
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
                                    new-name$
                                    new-enable$
                                    thm-name$
                                    non-executable$
                                    verify-guards$
                                    hints$
                                    app-cond-keywords
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         isodata-symbol-isomap-alistp
                                         isodata-pos-isomap-alistp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         symbol-alistp
                                         keyword-listp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((wrld (w state))
       ((er old$) (isodata-process-old old predicate verify-guards ctx state))
       ((er new-name$) (process-input-new-name new-name old$ ctx state))
       ((er thm-name$) (isodata-process-thm-name
                        thm-name old$ new-name$ ctx state))
       ((er verify-guards$) (ensure-boolean-or-auto-and-return-boolean$
                             verify-guards
                             (guard-verified-p old$ wrld)
                             "The :VERIFY-GUARDS input" t nil))
       (names-to-avoid (list new-name$ thm-name$))
       ((er (list arg-isomaps res-isomaps names-to-avoid))
        (isodata-process-isomaps
         isomaps old$ verify-guards$ names-to-avoid ctx state))
       ((er &) (ensure-boolean$ predicate "The :PREDICATE input" t nil))
       ((er new-enable$) (ensure-boolean-or-auto-and-return-boolean$
                          new-enable
                          (fundef-enabledp old$ state)
                          "The :NEW-ENABLE input"
                          t nil))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((er non-executable$) (ensure-boolean-or-auto-and-return-boolean$
                              non-executable
                              (non-executablep old$ wrld)
                              "The :NON-EXECUTABLE input" t nil))
       (app-cond-keywords (isodata-app-cond-present-keywords
                           old$ res-isomaps predicate verify-guards$ wrld))
       ((er &) (ensure-is-untranslate-specifier$ untranslate
                                                 "The :UNTRANSLATE input"
                                                 t nil))
       ((er hints$) (evmac-process-input-hints
                     hints app-cond-keywords ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 arg-isomaps
                 res-isomaps
                 new-name$
                 new-enable$
                 thm-name$
                 non-executable$
                 verify-guards$
                 hints$
                 app-cond-keywords
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-reprocess-res-isomaps ((res-isomaps isodata-pos-isomap-alistp)
                                       (old$ symbolp)
                                       ctx
                                       state)
  :returns (mv erp
               (res-isomap? "An @(tsee isodata-maybe-isomapp).")
               state)
  :verify-guards nil
  :short "Transitional ending input processing step."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the discussion in "
    (xdoc::seetopic "isodata-input-processing"
                    "the top-level topic about input processing")
    ".")
   (xdoc::p
    "Here we check that @('res-isomaps') is
     either empty (i.e. no results are transformed)
     or a singleton; in the second case, also that @('old') is single-valued.
     If these checks pass, we change the format of @('res-isomaps')
     to a @(tsee isodata-maybe-isomapp),
     for compatibility with the rest of the implementation of the transformation
     (which will be extended shortly)."))
  (b* (((when (null res-isomaps)) (value nil))
       (m (number-of-results old$ (w state)))
       ((when (> m 1)) (er-soft+ ctx t nil
                                 "The transformation of results ~
                                  of multi-valued functions ~
                                  is not yet supported.")))
    (value (cdar res-isomaps))))

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

(define isodata-gen-result-vars ((old$ symbolp)
                                 (vars-to-avoid symbol-listp)
                                 (wrld plist-worldp))
  :returns (vars "A @(tsee symbol-listp).")
  :mode :program
  :short "Generate fresh variables for bounding results of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "When @('old') returns multiple results,
     sometimes we need to generate @(tsee mv-let) calls
     that bind the multiple results to variables.
     This function generates these variables,
     ensuring that they are distinct from each other
     and also distinct from a list of variables passed as input.")
   (xdoc::p
    "The default generated variables are @('result1'), @('result2'), etc.
     These are generated in order.
     If any of these would result in a conflict with the passed variable,
     we append a @('$') and possibly a number,
     e.g. @('result2$') if @('result2') are in the list to avoid,
     and @('result2$0') if both @('result2') and @('result2$')
     are in the list to avoid."))
  (b* ((m (number-of-results old$ wrld)))
    (isodata-gen-result-vars-aux old$ 1 m vars-to-avoid))

  :prepwork
  ((define isodata-gen-result-vars-aux ((old$ symbolp)
                                        (j posp)
                                        (m posp)
                                        (vars-to-avoid symbol-listp))
     :returns vars ; SYMBOL-LISTP
     :mode :program
     (b* (((unless (mbt (posp j))) nil)
          ((unless (mbt (posp m))) nil)
          ((when (> j m)) nil)
          (name (str::cat "RESULT" (str::natstr j)))
          (var (genvar old$ name nil vars-to-avoid))
          (var (if (equal (symbol-name var) name)
                   var
                 (genvar old$ (str::cat name "$") nil vars-to-avoid)))
          (vars (isodata-gen-result-vars-aux old$
                                             (1+ j)
                                             m
                                             (cons var vars-to-avoid))))
       (cons var vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-app-cond-formula ((app-cond isodata-app-cond-keywordp)
                                      (old$ symbolp)
                                      (arg-isomaps isodata-symbol-isomap-alistp)
                                      (res-isomaps isodata-pos-isomap-alistp)
                                      state)
  :returns (formula "An untranslated term.")
  :mode :program
  :short "Generate the formula of the specified applicability condition."
  (b* ((wrld (w state))
       (x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (isodata-gen-oldp-of-terms x1...xn arg-isomaps))
       (oldp-of-x1...xn-conj (conjoin oldp-of-x1...xn))
       (formula
        (case app-cond
          (:oldp-of-old
           (b* ((m (len res-isomaps))
                (old-call (fcons-term old$ x1...xn)))
             (if (= m 1)
                 (b* ((res-isomap (cdar res-isomaps))
                      (oldp-res (isodata-isomap->oldp res-isomap)))
                   (implicate oldp-of-x1...xn-conj
                              (fcons-term* oldp-res old-call)))
               (b* ((y1...ym (isodata-gen-result-vars old$ x1...xn wrld))
                    (oldp-of-y1...ym (isodata-gen-oldp-of-terms y1...ym
                                                                res-isomaps)))
                 (implicate oldp-of-x1...xn-conj
                            (make-mv-let-call 'mv y1...ym :all old-call
                                              (conjoin oldp-of-y1...ym)))))))
          (:oldp-when-old
           (implicate `(,old$ ,@x1...xn)
                      oldp-of-x1...xn-conj))
          (:oldp-of-rec-call-args
           (implicate oldp-of-x1...xn-conj
                      (isodata-gen-oldp-of-rec-call-args-under-contexts
                       (recursive-calls old$ wrld)
                       arg-isomaps)))
          (:old-guard
           (b* ((old-guard-formula (uguard old$ wrld)))
             (implicate old-guard-formula
                        oldp-of-x1...xn-conj)))
          (:old-guard-pred
           (b* ((old-guard-formula (uguard old$ wrld)))
             (implicate oldp-of-x1...xn-conj
                        old-guard-formula)))
          (t (impossible)))))
    (untranslate formula t wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-app-cond ((app-cond isodata-app-cond-keywordp)
                              (old$ symbolp)
                              (arg-isomaps isodata-symbol-isomap-alistp)
                              (res-isomaps isodata-pos-isomap-alistp)
                              (hints$ symbol-alistp)
                              (print$ evmac-input-print-p)
                              (names-to-avoid symbol-listp)
                              ctx
                              state)
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (thm-name "A @(tsee symbolp) that is the name of the theorem."))
  :mode :program
  :short "Generate a theorem for the specified applicability condition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem has no rule classes,
     because it is used via @(':use') hints
     in the generated proofs in other events.")
   (xdoc::p
    "This is a local event,
     because it is only used internally in the @(tsee encapsulate).
     The event is wrapped into a @(tsee try-event)
     in order to provide a terse error message if the proof fails
     (unless @(':print') is @(':all'), in which case everything is printed).
     In addition,
     if @(':print') is @(':info') or @(':all'),
     the event is preceded and followed by events to print progress messages.")
   (xdoc::p
    "The name of the theorem is obtained by
     putting the keyword that names the applicability condition
     into the \"APT\" package
     and adding @('$') as needed to avoid name clashes.
     However, if the applicability condition is a @(tsee defiso) one,
     its name is supplied by the caller."))
  (b* ((wrld (w state))
       (thm-name (fresh-logical-name-with-$s-suffix (intern-in-package-of-symbol
                                                     (symbol-name app-cond)
                                                     (pkg-witness "APT"))
                                                    nil
                                                    names-to-avoid
                                                    wrld))
       (formula (isodata-gen-app-cond-formula app-cond
                                              old$
                                              arg-isomaps
                                              res-isomaps
                                              state))
       (hints (cdr (assoc-eq app-cond hints$)))
       (defthm `(defthm ,thm-name ,formula :hints ,hints :rule-classes nil))
       (error-msg (msg
                   "The proof of the ~x0 applicability condition fails:~%~x1~|"
                   app-cond formula))
       (try-defthm (try-event defthm ctx t nil error-msg))
       (print-progress-p (member-eq print$ '(:info :all)))
       (progress-start? (and print-progress-p
                             `((cw-event
                                "~%Attempting to prove the ~x0 ~
                                 applicability condition:~%~x1~|"
                                ',app-cond ',formula))))
       (progress-end? (and print-progress-p
                           `((cw-event "Done.~%"))))
       (event `(local (progn ,@progress-start?
                             ,try-defthm
                             ,@progress-end?))))
    (mv event thm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-app-conds ((app-conds isodata-app-cond-keyword-listp)
                               (old$ symbolp)
                               (arg-isomaps isodata-symbol-isomap-alistp)
                               (res-isomaps isodata-pos-isomap-alistp)
                               (hints$ symbol-alistp)
                               (print$ evmac-input-print-p)
                               (names-to-avoid symbol-listp)
                               ctx
                               state)
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (thm-names "A @(tsee symbol-symbol-alistp)
                           from keywords that identify applicability conditions
                           to the names of the corresponding theorems event."))
  :mode :program
  :short "Generate theorems for the specified applicability conditions."
  (b* (((when (endp app-conds)) (mv nil nil))
       (app-cond (car app-conds))
       ((mv event thm-name) (isodata-gen-app-cond app-cond
                                                  old$
                                                  arg-isomaps
                                                  res-isomaps
                                                  hints$
                                                  print$
                                                  names-to-avoid
                                                  ctx
                                                  state))
       (names-to-avoid (cons thm-name names-to-avoid))
       ((mv events thm-names) (isodata-gen-app-conds (cdr app-conds)
                                                     old$
                                                     arg-isomaps
                                                     res-isomaps
                                                     hints$
                                                     print$
                                                     names-to-avoid
                                                     ctx
                                                     state)))
    (mv (cons event events)
        (acons app-cond thm-name thm-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines isodata-xform-rec-calls
  :verify-guards nil
  :short "Transform all the calls to @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Turn each call  @('(old updatej-x1 ... updatej-xn)') inside a term
     into @('(back-res (new (forth1 updatej-x1) ... (forthn updatej-xn)))')
     or @('(new (forth1 updatej-x1) ... (forthn updatej-xn))'),
     depending on whether @(':result') is in @('isomaps') or not.
     where @('forthi') is the conversion for the argument @('xi')
     and @('back-res') is the conversion for the result.
     This is an intermediate step in the construction of
     the body of the new function from the body of @('old')."))

  (define isodata-xform-rec-calls ((term pseudo-termp)
                                   (old$ symbolp)
                                   (arg-isomaps isodata-symbol-isomap-alistp)
                                   (res-isomap? isodata-maybe-isomapp)
                                   (new-name$ symbolp))
    :returns new-term ; PSEUDO-TERMP
    (if (or (variablep term)
            (fquotep term))
        term
      (b* ((fn (ffn-symb term)))
        (if (symbolp fn)
            (if (eq fn old$)
                (b* ((new-call (cons-term
                                new-name$
                                (isodata-gen-forth-of-terms (fargs term)
                                                            arg-isomaps))))
                  (if res-isomap?
                      (b* ((back (isodata-isomap->back res-isomap?)))
                        (apply-term* back new-call))
                    new-call))
              (cons-term
               fn
               (isodata-xform-rec-calls-lst (fargs term)
                                            old$
                                            arg-isomaps
                                            res-isomap?
                                            new-name$)))
          (b* ((new-fn (make-lambda
                        (lambda-formals fn)
                        (isodata-xform-rec-calls (lambda-body fn)
                                                 old$
                                                 arg-isomaps
                                                 res-isomap?
                                                 new-name$))))
            (cons-term new-fn
                       (isodata-xform-rec-calls-lst (fargs term)
                                                    old$
                                                    arg-isomaps
                                                    res-isomap?
                                                    new-name$)))))))

  (define isodata-xform-rec-calls-lst ((terms pseudo-term-listp)
                                       (old$ symbolp)
                                       (arg-isomaps isodata-symbol-isomap-alistp)
                                       (res-isomap? isodata-maybe-isomapp)
                                       (new-name$ symbolp))
    :returns new-terms ; PSEUDO-TERM-LISTP
    (if (endp terms)
        nil
      (cons (isodata-xform-rec-calls (car terms)
                                     old$
                                     arg-isomaps
                                     res-isomap?
                                     new-name$)
            (isodata-xform-rec-calls-lst (cdr terms)
                                         old$
                                         arg-isomaps
                                         res-isomap?
                                         new-name$)))))

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
     the arguments of the corresponding recursively call of @('old'.
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
                              with @('xi').")
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
   (new-name$ symbolp)
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
       (new-call (fcons-term new-name$ forth-of-rec-call-args-back))
       (instance `(:instance ,lemma :extra-bindings-ok (,var ,new-call)))
       (instances
        (isodata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
         lemma var (cdr rec-calls) old$ arg-isomaps new-name$ wrld)))
    (cons instance instances)))

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
                                      (res-isomap? isodata-maybe-isomapp)
                                      (new-name$ symbolp)
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
     Then we replace @('y1'), ..., @('yp')
     with @('(back y1)'), ..., @('(back yp)').
     Finally, we conjoin the result
     with @('(newp y1)'), ..., @('(newp yp)')."))
  (b* ((x1...xn (formals old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls
         old-body old$ arg-isomaps res-isomap? new-name$))
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

(define isodata-gen-new-fn-body-nonpred-nonrec
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   compatibility
   (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function,
          when non-recursive and when @(':predicate') is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('old') is non-executable,
     its body is obtained
     by removing the ``non-executable wrapper''."))
  (b* ((x1...xn (formals old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-back-of-x1...xn
        (isodata-gen-subst-x1...xn-with-back-of-x1...xn old-body
                                                        old$
                                                        arg-isomaps
                                                        wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn))
       (then-branch (if res-isomap?
                        (apply-fn-into-ifs (isodata-isomap->forth res-isomap?)
                                           old-body-with-back-of-x1...xn)
                      old-body-with-back-of-x1...xn))
       (else-branch (b* ((n (number-of-results old$ wrld)))
                      (if (> n 1)
                          (cons 'mv (repeat n nil))
                        nil))))
    (cond (compatibility then-branch)
          ((equal newp-of-x1...xn-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-x1...xn-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-nonpred-rec
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function,
          when recursive and when @(':predicate') is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('old') is non-executable,
     its body is obtained
     by removing the ``non-executable wrapper''.")
   (xdoc::p
    "First we transform the recursive calls via @('isodata-xform-rec-calls').
     Then we replace @('y1'), ..., @('yp')
     with @('(back y1)'), ..., @('(back yp)').
     Finally,
     we put the result into the &lsquo;then&rsquo; branch of an @(tsee if)
     whose condition is the conjunction of
     @('(newp y1)'), ..., @('(newp yp)').
     The @('nil') in the &lsquo;else&rsquo; branch of the @(tsee if)
     is actually a variable name in the pseudo-term returned by this function,
     but it has the desired effect that
     the untranslation of the @(tsee if) in @(tsee isodata-gen-everything)
     does not turn the @(tsee if) into an @(tsee and)."))
  (b* ((x1...xn (formals old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls
         old-body old$ arg-isomaps res-isomap? new-name$))
       (old-body-with-back-of-x1...xn
        (isodata-gen-subst-x1...xn-with-back-of-x1...xn
         old-body-with-new-rec-calls
         old$
         arg-isomaps
         wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (then-branch (if res-isomap?
                        (apply-fn-into-ifs (isodata-isomap->forth res-isomap?)
                                           old-body-with-back-of-x1...xn)
                      old-body-with-back-of-x1...xn))
       (else-branch (b* ((n (number-of-results old$ wrld)))
                      (if (> n 1)
                          (cons 'mv (repeat n nil))
                        nil)))
       (newp-of-x1...xn-conj (conjoin newp-of-x1...xn)))
    (cond ((equal newp-of-x1...xn-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-x1...xn-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body ((old$ symbolp)
                                 (arg-isomaps isodata-symbol-isomap-alistp)
                                 (res-isomap? isodata-maybe-isomapp)
                                 (predicate$ booleanp)
                                 (new-name$ symbolp)
                                 compatibility
                                 (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function."
  (if predicate$
      (isodata-gen-new-fn-body-pred old$ arg-isomaps res-isomap? new-name$ wrld)
    (if (recursivep old$ nil wrld)
        (isodata-gen-new-fn-body-nonpred-rec
         old$ arg-isomaps res-isomap? new-name$ wrld)
      (isodata-gen-new-fn-body-nonpred-nonrec
       old$ arg-isomaps res-isomap? compatibility wrld))))

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
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the termination of the new function,
          if recursive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args app-cond-thm-names)))
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
                            (res-isomap? isodata-maybe-isomapp)
                            (predicate$ booleanp)
                            (new-name$ symbolp)
                            (new-enable$ booleanp)
                            (non-executable$ booleanp)
                            (verify-guards$ booleanp)
                            (untranslate$ untranslate-specifier-p)
                            compatibility
                            (app-cond-thm-names symbol-symbol-alistp)
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
     enabled or not, and non-executable or not.")
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
  (b* ((macro (function-intro-macro new-enable$ non-executable$))
       (formals (formals old$ wrld))
       (body (isodata-gen-new-fn-body old$ arg-isomaps res-isomap?
                                      predicate$ new-name$ compatibility wrld))
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
                                app-cond-thm-names old$ arg-isomaps wrld)
                             nil))
       (local-event
        `(local
          (,macro ,new-name$ (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  :guard ,guard
                                  :verify-guards nil))
                  ,body)))
       (exported-event
        `(,macro ,new-name$ (,@formals)
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
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (wrld plist-worldp))
  :returns (new-to-old-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the new function in terms of the old function."
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call (fcons-term old$ back-of-x1...xn)))
    (implicate (conjoin newp-of-x1...xn)
               `(equal (,new-name$ ,@x1...xn)
                       ,(if res-isomap?
                            (apply-term* (isodata-isomap->forth res-isomap?)
                                         old-call)
                          old-call)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-nonrec ((old-fn-unnorm-name symbolp)
                                                 (new-fn-unnorm-name symbolp))
  :returns (hints true-listp)
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are not recursive."
  `(("Goal" :in-theory '(,old-fn-unnorm-name ,new-fn-unnorm-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-nonres
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and @('isomaps') does not include @(':result')."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args app-cond-thm-names)))
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
                    (:induction ,new-name$))
       :induct (,new-name$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-call-args
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-res
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap isodata-isomapp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and @('isomaps') includes @(':result')."
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args app-cond-thm-names)))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
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
                    (:induction ,new-name$))
       :induct (,new-name$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-call-args
              ,@instances-oldp-of-old
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth
              ,@instances-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function."
  (if (recursivep old$ nil wrld)
      (if res-isomap?
          (isodata-gen-new-to-old-thm-hints-rec-res app-cond-thm-names
                                                    old$
                                                    arg-isomaps
                                                    res-isomap?
                                                    new-name$
                                                    old-fn-unnorm-name
                                                    new-fn-unnorm-name
                                                    wrld)
        (isodata-gen-new-to-old-thm-hints-rec-nonres app-cond-thm-names
                                                     old$
                                                     arg-isomaps
                                                     new-name$
                                                     old-fn-unnorm-name
                                                     new-fn-unnorm-name
                                                     wrld))
    (isodata-gen-new-to-old-thm-hints-nonrec old-fn-unnorm-name
                                             new-fn-unnorm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (names-to-avoid symbol-listp)
   (app-cond-thm-names symbol-symbol-alistp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem."))
  :mode :program
  :short "Generate the theorem
          that expresses the new function in terms of the old function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only locally for now."))
  (b* ((name (fresh-logical-name-with-$s-suffix 'new-to-old
                                                nil
                                                names-to-avoid
                                                wrld))
       (formula (isodata-gen-new-to-old-thm-formula old$
                                                    arg-isomaps
                                                    res-isomap?
                                                    new-name$
                                                    wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-new-to-old-thm-hints app-cond-thm-names
                                                old$
                                                arg-isomaps
                                                res-isomap?
                                                new-name$
                                                old-fn-unnorm-name
                                                new-fn-unnorm-name
                                                wrld))
       (event `(local
                (defthmd ,name
                  ,formula
                  :hints ,hints))))
    (mv event name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-formula
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (wrld plist-worldp))
  :returns (old-to-new-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that relates the old and new function."
  (b* ((x1...xn (formals old$ wrld))
       (oldp-of-x1...xn (isodata-gen-oldp-of-terms x1...xn arg-isomaps))
       (forth-of-x1...xn (isodata-gen-forth-of-terms x1...xn arg-isomaps))
       (new-call (fcons-term new-name$ forth-of-x1...xn)))
    (implicate (conjoin oldp-of-x1...xn)
               `(equal (,old$ ,@x1...xn)
                       ,(if res-isomap?
                            (apply-term* (isodata-isomap->back res-isomap?)
                                         new-call)
                          new-call)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-nonres-hints
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when @('isomaps') does not include @(':result')."
  (b* ((instances-forth-image
        (isodata-gen-forth-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-back-of-forth-instances-to-x1...xn arg-isomaps wrld))
       (instance-new-to-old
        (isodata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old
                                                                old$
                                                                arg-isomaps
                                                                wrld)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-res-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when @('isomaps') includes @(':result')."
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instances-forth-image
        (isodata-gen-forth-image-instances-to-x1...xn arg-isomaps wrld))
       (instances-back-of-forth
        (isodata-gen-back-of-forth-instances-to-x1...xn arg-isomaps wrld))
       (instance-new-to-old
        (isodata-gen-lemma-instance-x1...xn-to-forth-of-x1...xn new-to-old
                                                                old$
                                                                arg-isomaps
                                                                wrld))
       (back-of-forth-res (isodata-isomap->back-of-forth res-isomap))
       (var (isodata-formal-of-forth res-isomap wrld))
       (instance-back-of-forth-res
        `(:instance ,back-of-forth-res
          :extra-bindings-ok (,var (,old$ ,@(formals old$ wrld))))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old
             ,oldp-of-old
             ,instance-back-of-forth-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function."
  (if res-isomap?
      (isodata-gen-old-to-new-thm-res-hints app-cond-thm-names
                                            old$
                                            arg-isomaps
                                            res-isomap?
                                            new-to-old
                                            wrld)
    (isodata-gen-old-to-new-thm-nonres-hints old$
                                             arg-isomaps
                                             new-to-old
                                             wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (thm-name$ symbolp)
   (thm-enable$ booleanp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (mv (old-to-new-local-event "A @(tsee pseudo-event-formp).")
               (old-to-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the old and new functions."
  :long
  (xdoc::topstring-p
   "The macro used to introduce the theorem is determined by
    whether the theorem must be enabled or not.")
  (b* ((macro (theorem-intro-macro thm-enable$))
       (formula (isodata-gen-old-to-new-thm-formula
                 old$ arg-isomaps res-isomap? new-name$ wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-old-to-new-thm-hints app-cond-thm-names
                                                old$
                                                arg-isomaps
                                                res-isomap?
                                                new-to-old
                                                wrld))
       (local-event `(local
                      (,macro ,thm-name$
                              ,formula
                              :hints ,hints)))
       (exported-event `(,macro ,thm-name$
                                ,formula)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm-formula
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (wrld plist-worldp))
  :guard res-isomap?
  :returns (formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  :long
  (xdoc::topstring-p
   "This is the theorem @($f'A'B'$) in the design notes.
    It is generated only if @('isomaps') includes @(':result').")
  (b* ((x1...xn (formals old$ wrld))
       (newp-of-x1...xn (isodata-gen-newp-of-terms x1...xn arg-isomaps)))
    (implicate (conjoin newp-of-x1...xn)
               `(,(isodata-isomap->newp res-isomap?)
                 (,new-name$ ,@x1...xn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to prove the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  :long
  (xdoc::topstring-p
   "This is the theorem @($f'A'B'$) in the design notes.
    It is generated only if @('isomaps') includes @(':result').")
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
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
       (forth-image-res (isodata-isomap->forth-image res-isomap))
       (var (isodata-formal-of-forth res-isomap wrld))
       (instance-forth-image
        `(:instance ,forth-image-res
          :extra-bindings-ok (,var ,old-call-of-back-x1...xn))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-back-image
             ,instance-oldp-of-old
             ,instance-forth-image
             ,new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (new-to-old symbolp)
   (names-to-avoid symbol-listp)
   (app-cond-thm-names symbol-symbol-alistp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem."))
  :mode :program
  :short "Generate the theorem that says that
          the new function maps values in the new representation
          to values in the old representation."
  :long
  (xdoc::topstring-p
   "This is the theorem @($f'A'B'$) in the design notes.
    It is generated only if @('isomaps') includes @(':result').")
  (b* ((name (fresh-logical-name-with-$s-suffix 'newp-of-new
                                                nil
                                                names-to-avoid
                                                wrld))
       (formula (isodata-gen-newp-of-new-thm-formula old$
                                                     arg-isomaps
                                                     res-isomap?
                                                     new-name$
                                                     wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-newp-of-new-thm-hints app-cond-thm-names
                                                 old$
                                                 arg-isomaps
                                                 res-isomap?
                                                 new-to-old
                                                 wrld))
       (event `(local
                (defthmd ,name
                  ,formula
                  :hints ,hints))))
    (mv event name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-pred-nonrec
  ((app-cond-thm-names symbol-symbol-alistp)
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
  (b* ((old-guard-pred (cdr (assoc-eq :old-guard-pred app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old symbolp)
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
                                     app-cond-thm-names)))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred
                              app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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
         new-to-old
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
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('t')."
  (if (recursivep old$ nil wrld)
      (isodata-gen-new-fn-verify-guards-hints-pred-rec app-cond-thm-names
                                                       old$
                                                       arg-isomaps
                                                       new-to-old
                                                       wrld)
    (isodata-gen-new-fn-verify-guards-hints-pred-nonrec app-cond-thm-names
                                                        old$
                                                        arg-isomaps
                                                        wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-nonres
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') does not include @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-res
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (old-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') includes @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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
             ,instance-old-fn-unnorm-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-rec-nonres
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') does not include @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back thm-name$
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

(define isodata-gen-new-fn-verify-guards-hints-nonpred-rec-res
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap isodata-isomapp)
   (new-name$ symbolp)
   (thm-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('isomaps') includes @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (oldp-of-rec-call-args
        (cdr (assoc-eq :oldp-of-rec-call-args app-cond-thm-names)))
       (rec-calls (recursive-calls old$ wrld))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-x1...xn-to-back-of-x1...xn
         `(:guard-theorem ,old$)
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
        (isodata-gen-lemma-instances-x1...xn-to-rec-call-args-back thm-name$
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
         newp-of-new
         rec-calls
         old$
         arg-isomaps
         wrld))
       (x1...xn (formals old$ wrld))
       (old-call (fcons-term old$ x1...xn))
       (back-of-x1...xn (isodata-gen-back-of-terms x1...xn arg-isomaps))
       (old-call-of-back-x1...xn (subcor-var x1...xn back-of-x1...xn old-call))
       (forth-guard-res (isodata-isomap->forth-guard res-isomap))
       (var (isodata-formal-of-forth res-isomap wrld))
       (instance-forth-guard-res
        `(:instance ,forth-guard-res
          :extra-bindings-ok (,var ,old-call-of-back-x1...xn)))
       (back-guard (isodata-isomap->back-guard res-isomap))
       (var (isodata-formal-of-back res-isomap wrld))
       (instances-back-guard-res
        (isodata-gen-lemma-instances-var-to-new-forth-rec-call-args-back
         back-guard
         var
         rec-calls
         old$
         arg-isomaps
         new-name$
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
             ,@instances-old-to-new
             ,instance-oldp-of-old
             ,instance-old-fn-unnorm-name
             ,@instances-newp-of-new
             ,instance-forth-guard-res
             ,@instances-back-guard-res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (new-name$ symbolp)
   (thm-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('nil')."
  (if (recursivep old$ nil wrld)
      (if res-isomap?
          (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-res
           app-cond-thm-names
           old$
           arg-isomaps
           res-isomap?
           new-name$
           thm-name$
           old-fn-unnorm-name
           newp-of-new
           wrld)
        (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-nonres
         app-cond-thm-names
         old$
         arg-isomaps
         thm-name$
         wrld))
    (if res-isomap?
        (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-res
         app-cond-thm-names
         old$
         arg-isomaps
         old-fn-unnorm-name
         wrld)
      (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-nonres old$
                                                                    arg-isomaps
                                                                    wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (predicate$ booleanp)
   (new-to-old symbolp)
   (new-name$ symbolp)
   (thm-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function."
  (if predicate$
      (isodata-gen-new-fn-verify-guards-hints-pred app-cond-thm-names
                                                   old$
                                                   arg-isomaps
                                                   new-to-old
                                                   wrld)
    (isodata-gen-new-fn-verify-guards-hints-nonpred app-cond-thm-names
                                                    old$
                                                    arg-isomaps
                                                    res-isomap?
                                                    new-name$
                                                    thm-name$
                                                    old-fn-unnorm-name
                                                    newp-of-new
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (predicate$ booleanp)
   (new-name$ symbolp)
   (new-to-old symbolp)
   (thm-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (newp-of-new symbolp)
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
     This keeps the event history after the transformation &ldquo;clean&rdquo;,
     without implementation-specific proof hints
     that may refer to local events of the @(tsee encapsulate)
     that do not exist in the history after the transformation."))
  (b* ((hints (isodata-gen-new-fn-verify-guards-hints app-cond-thm-names
                                                      old$
                                                      arg-isomaps
                                                      res-isomap?
                                                      predicate$
                                                      new-to-old
                                                      new-name$
                                                      thm-name$
                                                      old-fn-unnorm-name
                                                      newp-of-new
                                                      wrld))
       (event `(local (verify-guards ,new-name$ :hints ,hints))))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-everything
  ((old$ symbolp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   (res-isomaps isodata-pos-isomap-alistp)
   (res-isomap? isodata-maybe-isomapp)
   (predicate$ booleanp)
   (new-name$ symbolp)
   (new-enable$ booleanp)
   (thm-name$ symbolp)
   (thm-enable$ booleanp)
   (non-executable$ booleanp)
   (verify-guards$ booleanp)
   (untranslate$ untranslate-specifier-p)
   (hints$ symbol-truelist-alistp)
   (print$ evmac-input-print-p)
   (show-only$ booleanp)
   compatibility
   (names-to-avoid symbol-listp)
   (app-conds isodata-app-cond-keyword-listp)
   (call pseudo-event-formp)
   ctx
   state)
  :returns (event "A @(tsee pseudo-event-formp).")
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
                        (and res-isomap? (list res-isomap?))))
       (isomaps (remove-duplicates-equal isomaps))
       (defiso-events (isodata-gen-defisos isomaps verify-guards$ print$))
       ((mv app-cond-thm-events
            app-cond-thm-names)
        (isodata-gen-app-conds app-conds
                               old$
                               arg-isomaps
                               res-isomaps
                               hints$
                               print$
                               names-to-avoid
                               ctx
                               state))
       (names-to-avoid (append names-to-avoid
                               (strip-cdrs app-cond-thm-names)))
       ((mv old-fn-unnorm-event
            old-fn-unnorm-name)
        (install-not-normalized-event old$ t names-to-avoid wrld))
       (names-to-avoid (cons old-fn-unnorm-name names-to-avoid))
       ((mv new-fn-local-event
            new-fn-exported-event)
        (isodata-gen-new-fn old$
                            arg-isomaps
                            res-isomap?
                            predicate$
                            new-name$
                            new-enable$
                            non-executable$
                            verify-guards$
                            untranslate$
                            compatibility
                            app-cond-thm-names
                            wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name)
        (install-not-normalized-event new-name$ t names-to-avoid wrld))
       ((mv new-to-old-thm-event
            new-to-old)
        (isodata-gen-new-to-old-thm old$
                                    arg-isomaps
                                    res-isomap?
                                    new-name$
                                    names-to-avoid
                                    app-cond-thm-names
                                    old-fn-unnorm-name
                                    new-fn-unnorm-name
                                    wrld))
       (names-to-avoid (cons new-to-old names-to-avoid))
       ((mv newp-of-new-thm-event?
            newp-of-new?)
        (if res-isomap?
            (isodata-gen-newp-of-new-thm old$
                                         arg-isomaps
                                         res-isomap?
                                         new-name$
                                         new-to-old
                                         names-to-avoid
                                         app-cond-thm-names
                                         wrld)
          (mv nil nil)))
       (newp-of-new-thm-event? (and newp-of-new-thm-event?
                                    (list newp-of-new-thm-event?)))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event)
        (isodata-gen-old-to-new-thm app-cond-thm-names
                                    old$
                                    arg-isomaps
                                    res-isomap?
                                    new-name$
                                    thm-name$
                                    thm-enable$
                                    new-to-old
                                    wrld))
       (new-fn-verify-guards-event? (and verify-guards$
                                         (list
                                          (isodata-gen-new-fn-verify-guards
                                           app-cond-thm-names
                                           old$
                                           arg-isomaps
                                           res-isomap?
                                           predicate$
                                           new-name$
                                           new-to-old
                                           thm-name$
                                           old-fn-unnorm-name
                                           newp-of-new?
                                           wrld))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@defiso-events
                             ,@app-cond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,old-fn-unnorm-event
                             ,new-fn-local-event
                             ,new-fn-unnorm-event
                             ,new-to-old-thm-event
                             ,@newp-of-new-thm-event?
                             ,old-to-new-thm-local-event
                             ,@new-fn-verify-guards-event?
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print$ '(:result :info :all))
                      `(,@(and (member-eq print$ '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-fn-exported-event)
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-fn (old
                    isomaps
                    predicate
                    new-name
                    new-enable
                    thm-name
                    thm-enable
                    non-executable
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
                  new-name$
                  new-enable$
                  thm-name$
                  non-executable$
                  verify-guards$
                  hints$
                  app-cond-keywords
                  names-to-avoid))
        (isodata-process-inputs old
                                isomaps
                                predicate
                                new-name
                                new-enable
                                thm-name
                                thm-enable
                                non-executable
                                verify-guards
                                untranslate
                                hints
                                print
                                show-only
                                ctx
                                state))
       ((er res-isomap?)
        (isodata-reprocess-res-isomaps res-isomaps old$ ctx state))
       (event (isodata-gen-everything old$
                                      arg-isomaps
                                      res-isomaps
                                      res-isomap?
                                      predicate
                                      new-name$
                                      new-enable$
                                      thm-name$
                                      thm-enable
                                      non-executable$
                                      verify-guards$
                                      untranslate
                                      hints$
                                      print
                                      show-only
                                      compatibility
                                      names-to-avoid
                                      app-cond-keywords
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
                     (thm-name ':auto)
                     (thm-enable 't)
                     (non-executable ':auto)
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
                                   ',thm-name
                                   ',thm-enable
                                   ',non-executable
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
