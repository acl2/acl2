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
(include-book "kestrel/std/system/ibody" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/util/defiso" :dir :system)
(include-book "kestrel/utilities/directed-untranslate" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/system/install-not-normalized-event" :dir :system)
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
   @('args/res-iso'),
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

  "@('args$') is the sublist of the @('args/res') part of @('arg/res-iso')
   that excludes @(':result'), if present."

  "@('res$') is @('t') if @('args/res') includes @(':result'),
   @('nil') otherwise."

  "@('isomap') is a record containing the information about
   the isomorphic mapping to use to transform
   the arguments and result of @('old')
   (according to @('args$') and @('res$'))."

  "@('arg-isomaps') is an alist from the formal arguments of @('old')
   to isomorphic mapping records that specify
   how each formal argument must be transformed."

  "@('res-isomap?') is either @('isomap') (if @('res$') is @('t'))
   or @('nil') (if @('res$') is @('nil'))."

  "@('app-cond-thm-names') is an alist
   from the applicability condition keywords
   to the corresponding theorem names."

  "@('old-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the old function."

  "@('new-fn-unnorm-name') is the name of the theorem
   that installs the non-normalized definition of the new function."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing isodata)

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

(define isodata-process-args/res (args/res (old$ symbolp) ctx state)
  :returns (mv erp
               (result "A tuple @('(args$ res$)') satisfying
                        @('(typed-tuplep symbol-listp booleanp result)').")
               state)
  :mode :program
  :short "Process the @('args/res') component of the @('args/res-iso') input."
  (b* ((wrld (w state))
       (formals (formals old$ wrld)))
    (cond ((member-eq args/res formals)
           (value (list (list args/res) nil)))
          ((eq args/res :result)
           (value (list nil t)))
          (t (b* (((er &) (ensure-symbol-list$
                           args/res
                           (msg "Since the ARGS/RES component ~
                                 of the second input is ~
                                 neither a formal argument of ~x0 ~
                                 nor the keyword :RESULT, it"
                                old$)
                           t nil))
                  ((er &) (ensure-list-no-duplicates$
                           args/res
                           (msg "The list ~x0 that is ~
                                 the ARGS/RES component of the second input"
                                args/res)
                           t nil))
                  ((mv args$ res$) (if (member-eq :result args/res)
                                       (mv (remove1-eq :result args/res) t)
                                     (mv args/res nil)))
                  ((er &) (ensure-list-subset$
                           args$
                           formals
                           (msg "The list ~x0 that is ~
                                 the ARGS/RES component of the second input, ~
                                 except for the keyword :RESULT (if present),"
                                args/res)
                           t nil))
                  ((when (and res$
                              (> (number-of-results old$ wrld) 1)))
                   (er-soft+ ctx t nil
                             "Since the ARGS/RES component ~
                              of the second input includes :RESULT, ~
                              the target function ~x0 must be single-valued"
                             old$)))
               (value (list args$ res$)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate isodata-isomap
  :short "Information about an isomorphic mapping
          according to which the target function's
          arguments and/or results are transformed."
  :long
  (xdoc::topstring-p
   "This is somewhat similar to @(tsee acl2::defiso-infop),
    and in fact it corresponds to
    either an existing @(tsee defiso) that is referenced
    in the @('args/res-iso') input of @(tsee isodata),
    or a locally generated @(tsee defiso) that is determined
    in the @('args/res-iso') input of @(tsee isodata).
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
  :true-listp nil
  :keyp-of-nil t
  :valp-of-nil nil)

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

(define isodata-process-iso (iso
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
  :short "Process the @('iso') component of the @('args/res-iso') input."
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
     the names of these theorems,
     which will be generated by the local @(tsee defiso).")
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
     We cannot just generate the @(tsee defiso):
     we need the actual (translated) functions
     to use them in the events generated by @(tsee isodata) proper.
     When we call @(tsee defiso)'s input processing functions,
     we set the context @('ctx') to the one for the @(tsee defiso) call,
     so that the error message is appropriate.
     (When the generated @(tsee defiso) call is actually submitted,
     these input processing steps will be repeated,
     but will succeed since they have been already performed here;
     and they should be quite fast to execute.)"))
  (if (atom iso)
      (b* (((er &) (ensure-symbol$ iso
                                   (msg "The ISO component ~x0 ~
                                         of the second input ~
                                         must be a symbol or a list. ~
                                         Since it is an atom,"
                                        iso)
                                   t nil))
           (info (defiso-lookup iso (w state)))
           ((unless info)
            (er-soft+ ctx t nil
                      "The ISO component of the second input, ~
                       which is the symbol ~x0, ~
                       must be the name of an existing DEFISO, ~
                       but no DEFISO with this name exists.  ~
                       See :DOC DEFISO."
                      iso))
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
    (b* ((iso$ (packn-pos (list 'defiso-isodata- old$) old$))
         (iso$ (isodata-fresh-defiso-name-with-*s-suffix iso$ (w state)))
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
          (isodata-fresh-defiso-thm-names
           iso$ verify-guards$ names-to-avoid (w state)))
         ((unless (true-listp iso))
          (er-soft+ ctx t nil
                    "The ISO component ~x0 of the second input ~
                     must be a symbol or a list. ~
                     Since it is not an atom, it must be a list." iso))
         ((unless (or (= (len iso) 4)
                      (= (len iso) 6)))
          (er-soft+ ctx t nil
                    "The ISO component ~x0 of the second input ~
                     must be a list of length 4 or 6." iso))
         (oldp (first iso))
         (newp (second iso))
         (forth (third iso))
         (back (fourth iso))
         ((unless (or (= (len iso) 4)
                      (eq (fifth iso) :hints)))
          (er-soft+ ctx t nil
                    "The fifth component ~x0 ~
                     of the ISO component ~x1 ~
                     of the second input ~
                     must be the keyword :HINTS." (fifth iso) iso))
         (hints (and (= (len iso) 6) (sixth iso)))
         (ctx-defiso (cons 'defiso iso$))
         ((er (list oldp$ newp$ forth$ back$))
          (acl2::defiso-process-functions
           oldp newp forth back verify-guards$ ctx-defiso state))
         (oldp-arity (arity oldp$ (w state)))
         ((unless (= oldp-arity 1))
          (er-soft+ ctx t nil
                    "The first component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 arguments instead."
                    oldp oldp-arity))
         (newp-arity (arity newp$ (w state)))
         ((unless (= newp-arity 1))
          (er-soft+ ctx t nil
                    "The second component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 arguments instead."
                    newp newp-arity))
         (isomap (make-isodata-isomap
                  :isoname iso$
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

(define isodata-process-args/res-iso (args/res-iso
                                      (old$ symbolp)
                                      (verify-guards$ booleanp)
                                      (names-to-avoid symbol-listp)
                                      ctx
                                      state)
  :returns (mv erp
               (result "A tuple @('(args$
                                    res$
                                    isomap
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbol-listp
                                         booleanp
                                         isodata-isomapp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process the @('args/res-iso') input."
  (b* (((er &) (ensure-doublet-list$ args/res-iso "The second input" t nil))
       (len (len args/res-iso))
       ((unless (= len 1))
        (er-soft+ ctx t nil
                  "The list of doublets ~x0 passed as second input ~
                   must contain exactly one element, ~
                   but it contains ~x1 elements instead."
                  args/res-iso
                  len))
       (args/res-iso (car args/res-iso))
       (args/res (first args/res-iso))
       (iso (second args/res-iso))
       ((er (list args$ res$))
        (isodata-process-args/res args/res old$ ctx state))
       ((er (list isomap names-to-avoid))
        (isodata-process-iso iso old$ verify-guards$ names-to-avoid ctx state)))
    (value (list args$ res$ isomap names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-reprocess-args/res-iso ((old$ symbolp)
                                        (args$ symbol-listp)
                                        (res$ booleanp)
                                        (isomap isodata-isomapp)
                                        (verify-guards$ booleanp)
                                        (names-to-avoid symbol-listp)
                                        (wrld plist-worldp))
  :returns (mv (arg-isomaps "An @(tsee isodata-symbol-isomap-alistp).")
               (res-isomap? "An @(tsee isodata-maybe-isomapp).")
               (names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Reprocess the @('args/res-iso') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts the result of processing the @('args/res-iso') input
     in a more general and extensible form,
     namely (i) an alist from the target function's formal arguments
     to isomorphic mapping records
     and (ii) an optional isomorphic mapping record for the function's result.
     Currently each such record is
     either the one specified in the @('args/res-iso') input
     or one for the identity mapping over all values:
     the former applies to the arguments in @('args$')
     and to the result if @('res$') is @('t'),
     while the latter applied to the other formal arguments
     and to the result if @('res$') is @('nil').
     However, this format allows for different isomorphic mappings
     for different arguments and the result,
     which will be supported in future versions of @(tsee isodata).")
   (xdoc::p
    "We construct the record for the identity isomorphic mapping here.
     The corresponding @(tsee defiso) is always expected to succeed.
     We include the guard theorems, regardless of @(':verify-guards'),
     since those are also expected to alwyas hold."))
  (b* ((iso-id (isodata-fresh-defiso-name-with-*s-suffix 'defiso-identity wrld))
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
        (isodata-fresh-defiso-thm-names
         iso-id verify-guards$ names-to-avoid wrld))
       (isomap-id (make-isodata-isomap
                   :isoname iso-id
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
       (arg-isomaps (isodata-reprocess-args/res-iso-aux formals
                                                        args$
                                                        isomap
                                                        isomap-id))
       (res-isomap? (and res$ isomap)))
    (mv arg-isomaps res-isomap? names-to-avoid))

  :prepwork
  ((define isodata-reprocess-args/res-iso-aux ((formals symbol-listp)
                                               (args$ symbol-listp)
                                               (isomap isodata-isomapp)
                                               (isomap-id isodata-isomapp))
     :returns (arg-isomaps isodata-symbol-isomap-alistp
                           :hyp (and (symbol-listp formals)
                                     (isodata-isomapp isomap)
                                     (isodata-isomapp isomap-id)))
     (cond ((endp formals) nil)
           ((member-eq (car formals) args$)
            (acons (car formals)
                   isomap
                   (isodata-reprocess-args/res-iso-aux (cdr formals)
                                                       args$
                                                       isomap
                                                       isomap-id)))
           (t (acons (car formals)
                     isomap-id
                     (isodata-reprocess-args/res-iso-aux (cdr formals)
                                                         args$
                                                         isomap
                                                         isomap-id)))))))

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
                                    (res$ booleanp)
                                    (predicate$ booleanp)
                                    (verify-guards$ booleanp)
                                    (wrld plist-worldp))
  :returns (yes/no booleanp :hyp (and (booleanp res$)
                                      (booleanp predicate$)
                                      (booleanp verify-guards$)))
  :short "Check if an applicability condition is present."
  (case keyword
    (:oldp-of-old res$)
    (:oldp-when-old predicate$)
    (:oldp-of-rec-call-args (and (irecursivep old$ wrld) t))
    (:old-guard (and verify-guards$ (not predicate$)))
    (:old-guard-pred (and verify-guards$ predicate$))
    (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable isodata-app-cond-keywordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-app-cond-present-keywords ((old$ symbolp)
                                           (res$ booleanp)
                                           (predicate$ booleanp)
                                           (verify-guards$ booleanp)
                                           (wrld plist-worldp))
  :returns (present-keywords isodata-app-cond-keyword-listp)
  :short "Keywords of the applicability conditions that are present."
  (isodata-app-cond-present-keywords-aux *isodata-app-cond-keywords*
                                         old$
                                         res$
                                         predicate$
                                         verify-guards$
                                         wrld)

  :prepwork
  ((define isodata-app-cond-present-keywords-aux
     ((keywords isodata-app-cond-keyword-listp)
      (old$ symbolp)
      (res$ booleanp)
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
                                       res$
                                       predicate$
                                       verify-guards$
                                       wrld)
           (cons (car keywords)
                 (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                        old$
                                                        res$
                                                        predicate$
                                                        verify-guards$
                                                        wrld))
         (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                old$
                                                res$
                                                predicate$
                                                verify-guards$
                                                wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-process-inputs (old
                                args/res-iso
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
                                    args$
                                    res$
                                    isomap
                                    arg-isomaps
                                    res-isomap?
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
                                         symbol-listp
                                         booleanp
                                         isodata-isomapp
                                         isodata-symbol-isomap-alistp
                                         isodata-maybe-isomapp
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
  :long
  (xdoc::topstring-p
   "As a transitional step towards supporting
    multiple isomorphic mappings instead of just one,
    we also return the results of reprocessing the @('args/res-iso') input
    into the more general form.")
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
       ((er (list args$ res$ isomap names-to-avoid))
        (isodata-process-args/res-iso
         args/res-iso old$ verify-guards$ names-to-avoid ctx state))
       ((mv arg-isomaps res-isomap? names-to-avoid)
        (isodata-reprocess-args/res-iso
         old$ args$ res$ isomap verify-guards$ names-to-avoid wrld))
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
                           old$ res$ predicate verify-guards$ wrld))
       ((er &) (ensure-is-untranslate-specifier$ untranslate
                                                 "The :UNTRANSLATE input"
                                                 t nil))
       ((er hints$) (evmac-process-input-hints
                     hints app-cond-keywords ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 args$
                 res$
                 isomap
                 arg-isomaps
                 res-isomap?
                 new-name$
                 new-enable$
                 thm-name$
                 non-executable$
                 verify-guards$
                 hints$
                 app-cond-keywords
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

(define isodata-gen-var-a ((forth$ pseudo-termfnp)
                           (wrld plist-worldp))
  :returns (x "A @(tsee symbolp).")
  :verify-guards nil
  :short "Generate the variable @('a') to use in
          some of the applicability conditions."
  :long
  (xdoc::topstring-p
   "We use the (unique) formal parameter of
    the conversion from the old representation to the new representation.")
  (car (cond ((symbolp forth$) (formals forth$ wrld))
             (t (lambda-formals forth$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-var-b ((back$ pseudo-termfnp)
                           (wrld plist-worldp))
  :returns (b "A @(tsee symbolp).")
  :verify-guards nil
  :short "Generate the variable @('b') to use in
          some of the applicability conditions."
  :long
  (xdoc::topstring-p
   "We use the (unique) formal parameter of
    the conversion from the new representation to the old representation.")
  (car (cond ((symbolp back$) (formals back$ wrld))
             (t (lambda-formals back$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-oldp-of-args
  ((arg-isomaps isodata-symbol-isomap-alistp))
  :returns (oldp-of-args "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the conjunction of the terms obtained by applying
          the old representation predicates to the corresponding formals."
  (conjoin (isodata-gen-oldp-of-args-aux arg-isomaps))

  :prepwork
  ((define isodata-gen-oldp-of-args-aux
     ((arg-isomaps isodata-symbol-isomap-alistp))
     :returns terms ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (b* (((when (endp arg-isomaps)) nil)
          (formal (caar arg-isomaps))
          (isomap (cdar arg-isomaps))
          (oldp (isodata-isomap->oldp isomap))
          (term (apply-term oldp (list formal)))
          (terms (isodata-gen-oldp-of-args-aux (cdr arg-isomaps))))
       (cons term terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-get-rec-call-args-transformed
  ((rec-call pseudo-termp "A recursive call of @('old').")
   (old$ symbolp)
   (args$ symbol-listp)
   (wrld plist-worldp))
  :returns (transformed-args$ "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :short "Obtain the actual arguments of a recursive call of @('old')
          that correspond to the formal arguments @('args') of @('old')
          whose representation is being transformed."
  :long
  (xdoc::topstring-p
   "Recall that the elements of @('args') are not necessarily
    in the order in which they occur among the formals of @('old').
    So to find the actual arguments among the ones of @('rec-call')
    that corresponds to an element of @('args'),
    we use the position of that element among the formals of @('old').")
  (if (endp args$)
      nil
    (b* ((pos (position (car args$) (formals old$ wrld)))
         (rec-call-arg (nth pos (fargs rec-call))))
      (cons rec-call-arg
            (isodata-get-rec-call-args-transformed rec-call
                                                   old$
                                                   (cdr args$)
                                                   wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-oldp-of-rec-call-args
  ((rec-call pseudo-term-listp "A recursive call of @('old').")
   (arg-isomaps isodata-symbol-isomap-alistp))
  :returns (oldp-of-rec-call-args "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the conjunction of the terms obtained
          by applying @('oldp')
          to the arguments passed to a recursive call of @('old')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function generates a subformula")
   (xdoc::codeblock
    "(and (oldp updateJ-y1<x1,...,xn>)"
    "     ..."
    "     (oldp updateJ-yp<x1,...,xn>))")
   (xdoc::p
    "of the @(':oldp-of-rec-call-args') applicability condition."))
  (conjoin
   (isodata-gen-oldp-of-rec-call-args-aux (fargs rec-call) arg-isomaps))

  :prepwork
  ((define isodata-gen-oldp-of-rec-call-args-aux
     ((args pseudo-term-listp)
      (arg-isomaps isodata-symbol-isomap-alistp))
     :guard (= (len args) (len arg-isomaps))
     :returns oldp-of-args ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (b* (((when (endp args)) nil)
          (arg (car args))
          (isomap (cdar arg-isomaps))
          (oldp (isodata-isomap->oldp isomap))
          (term (apply-term oldp (list arg)))
          (terms (isodata-gen-oldp-of-rec-call-args-aux (cdr args)
                                                        (cdr arg-isomaps))))
       (cons term terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-oldp-of-rec-call-args-under-contexts
  ((rec-calls-with-tests pseudo-tests-and-call-listp)
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
    "     (implies contextM<x1,...,xn>"
    "              (and (oldp updatem-y1<x1,...,xn>)"
    "                   ..."
    "                   (oldp updatem-yp<x1,...,xn>))))")
   (xdoc::p
    "of the @(':oldp-of-rec-call-args') applicability condition."))
  (if (endp rec-calls-with-tests)
      *t*
    (b* ((tests-and-call (car rec-calls-with-tests))
         (tests (access tests-and-call tests-and-call :tests))
         (rec-call (access tests-and-call tests-and-call :call))
         (context (conjoin tests))
         (rest (cdr rec-calls-with-tests)))
      (conjoin2
       (implicate context
                  (isodata-gen-oldp-of-rec-call-args rec-call
                                                     arg-isomaps))
       (isodata-gen-oldp-of-rec-call-args-under-contexts rest
                                                         arg-isomaps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-app-cond-formula
  ((app-cond isodata-app-cond-keywordp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (arg-isomaps isodata-symbol-isomap-alistp)
   state)
  :returns (formula "An untranslated term.")
  :mode :program
  :short "Generate the formula of the specified applicability condition."
  (b* ((wrld (w state))
       (oldp$ (isodata-isomap->oldp isomap)))
    (case app-cond
      (:oldp-of-old
       (untranslate
        (implicate (conjoin (apply-unary-to-terms oldp$ args$))
                   `(,oldp$ (,old$ ,@(formals old$ wrld))))
        t wrld))
      (:oldp-when-old
       (untranslate
        (implicate `(,old$ ,@(formals old$ wrld))
                   (conjoin (apply-unary-to-terms oldp$ args$)))
        t wrld))
      (:oldp-of-rec-call-args
       (untranslate
        (b* ((rec-calls-with-tests (recursive-calls old$ wrld))
             (oldp-of-args (isodata-gen-oldp-of-args arg-isomaps)))
          (implicate oldp-of-args
                     (isodata-gen-oldp-of-rec-call-args-under-contexts
                      rec-calls-with-tests
                      arg-isomaps)))
        t wrld))
      (:old-guard
       (untranslate
        (b* ((old-guard-formula (uguard old$ wrld))
             (oldp-of-args (apply-unary-to-terms oldp$ args$)))
          (implicate old-guard-formula
                     (conjoin oldp-of-args)))
        t wrld))
      (:old-guard-pred
       (untranslate
        (b* ((old-guard-formula (uguard old$ wrld))
             (oldp-of-args (apply-unary-to-terms oldp$ args$)))
          (implicate (conjoin oldp-of-args)
                     old-guard-formula))
        t wrld))
      (t (impossible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-app-cond ((app-cond isodata-app-cond-keywordp)
                              (old$ symbolp)
                              (args$ symbol-listp)
                              (isomap isodata-isomapp)
                              (arg-isomaps isodata-symbol-isomap-alistp)
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
                                              args$
                                              isomap
                                              arg-isomaps
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
                               (args$ symbol-listp)
                               (isomap isodata-isomapp)
                               (arg-isomaps isodata-symbol-isomap-alistp)
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
                                                  args$
                                                  isomap
                                                  arg-isomaps
                                                  hints$
                                                  print$
                                                  names-to-avoid
                                                  ctx
                                                  state))
       (names-to-avoid (cons thm-name names-to-avoid))
       ((mv events thm-names) (isodata-gen-app-conds (cdr app-conds)
                                                     old$
                                                     args$
                                                     isomap
                                                     arg-isomaps
                                                     hints$
                                                     print$
                                                     names-to-avoid
                                                     ctx
                                                     state)))
    (mv (cons event events)
        (acons app-cond thm-name thm-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-apply-forth-to-rec-call-args
  ((rec-call-args pseudo-termp "All the actual arguments
                                of a recursive call of @('old')
                                that @('forth') must be applied to.")
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (wrld plist-worldp))
  :returns (new-rec-call-args "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate a term that applies @('forth')
          to the actual arguments @('rec-call-args')
          of a recursive call of @('old')
          that correspond to the formal arguments @('args$')
          of @('old')."
  :long
  (xdoc::topstring-p
   "The body of the generated function
    includes subterms of the form @('(forth updatej-yk)'),
    where @('forth') is applied to the actual arguments of each recursive call
    that correspond to the formal arguments of @('old')
    whose representation is being transformed.
    This function iterates through each @('yk') of @('args$'),
    replacing each of the corresponding elements @('updatej-yk')
    of @('rec-call-args')
    with @('(forth updatej-yk)').
    The @('rec-call-args') argument of this function is like an accumulator
    for the resulting new arguments.")
  (if (endp args$)
      rec-call-args
    (b* ((pos (position (car args$) (formals old$ wrld)))
         (rec-call-arg (nth pos rec-call-args))
         (forth$ (isodata-isomap->forth isomap))
         (forth-of-rec-call-arg (apply-term* forth$ rec-call-arg))
         (new-rec-call-args
          (update-nth pos forth-of-rec-call-arg rec-call-args)))
      (isodata-gen-apply-forth-to-rec-call-args new-rec-call-args
                                                old$
                                                (cdr args$)
                                                isomap
                                                wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines isodata-xform-rec-calls-in-term
  :verify-guards nil
  :short "Transform all the calls to @('old') in term/terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "Turn each @('(old ... updatej-y1 ... updatej-yp ...)') inside a term into
     @('(back (new ... (forth updatej-y1) ... (forth updatej-yp) ...))') or
     @('(new ... (forth updatej-y1) ... (forth updatej-yp) ...)'),
     depending on whether @(':result') is in @('args/res-iso') or not.
     This is an intermediate step
     in the construction of the body of the generated function
     from the body of @('old').")
   (xdoc::p
    "The term is initially the body of @('old'),
     then subterms of it in the recursive calls."))

  (define isodata-xform-rec-calls-in-term ((term pseudo-termp)
                                           (old$ symbolp)
                                           (args$ symbol-listp)
                                           (res$ booleanp)
                                           (isomap isodata-isomapp)
                                           (new-name$ symbolp)
                                           (wrld plist-worldp))
    :returns new-term ; PSEUDO-TERMP
    (if (or (variablep term)
            (fquotep term))
        term
      (b* ((fn (ffn-symb term)))
        (if (symbolp fn)
            (if (eq fn old$)
                (b* ((new-call (cons-term
                                new-name$
                                (isodata-gen-apply-forth-to-rec-call-args
                                 (fargs term) old$ args$ isomap wrld))))
                  (if res$
                      (b* ((back$ (isodata-isomap->back isomap)))
                        (apply-term* back$ new-call))
                    new-call))
              (cons-term
               fn
               (isodata-xform-rec-calls-in-terms (fargs term)
                                                 old$
                                                 args$
                                                 res$
                                                 isomap
                                                 new-name$
                                                 wrld)))
          (b* ((new-fn (make-lambda
                        (lambda-formals fn)
                        (isodata-xform-rec-calls-in-term (lambda-body fn)
                                                         old$
                                                         args$
                                                         res$
                                                         isomap
                                                         new-name$
                                                         wrld))))
            (cons-term new-fn
                       (isodata-xform-rec-calls-in-terms (fargs term)
                                                         old$
                                                         args$
                                                         res$
                                                         isomap
                                                         new-name$
                                                         wrld)))))))

  (define isodata-xform-rec-calls-in-terms ((terms pseudo-term-listp)
                                            (old$ symbolp)
                                            (args$ symbol-listp)
                                            (res$ booleanp)
                                            (isomap isodata-isomapp)
                                            (new-name$ symbolp)
                                            (wrld plist-worldp))
    :returns new-terms ; PSEUDO-TERM-LISTP
    (if (endp terms)
        nil
      (cons (isodata-xform-rec-calls-in-term (car terms)
                                             old$
                                             args$
                                             res$
                                             isomap
                                             new-name$
                                             wrld)
            (isodata-xform-rec-calls-in-terms (cdr terms)
                                              old$
                                              args$
                                              res$
                                              isomap
                                              new-name$
                                              wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-terms
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (terms pseudo-term-listp "Terms to instantiate @('var') with."))
  :returns (lemma-instances true-list-listp)
  :short "Generate lemma instances where
          a variable is instantiated with
          each of the terms in a list."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(... (:instance lemma (var termi)) ...)'),
    where @('termi') is an element of @('terms').")
  (cond ((endp terms) nil)
        (t (cons `(:instance ,lemma :extra-bindings-ok (,var ,(car terms)))
                 (isodata-gen-lemma-instances-var-to-terms lemma
                                                           var
                                                           (cdr terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instance-y1...yp-to-back/forth
  ((lemma (or (symbolp lemma)
              (symbol-listp lemma)) "Lemma to generate an instance of.")
   (args$ symbol-listp)
   (back$/forth$ pseudo-termfnp))
  :returns (lemma-instance true-listp)
  :verify-guards nil
  :short "Generate a lemma instance where
          @('y1'), ..., @('yp') are instantiated with
          either @('(back y1)'), ..., @('(back yp)')
          or @('(forth y1)'), ..., @('(forth yp)')."
  :long
  (xdoc::topstring-p
   "The result is either
    @('(:instance lemma (y1 (back y1)) ... (yp (back yp)))') or
    @('(:instance lemma (y1 (forth y1)) ... (yp (forth yp)))').
    Note that if @('lemma') is a guard or termination theorem,
    it is a list of symbols, not a single symbol.")
  (b* ((back/forth-of-args (apply-unary-to-terms back$/forth$ args$))
       (instantiation (alist-to-doublets (pairlis$ args$ back/forth-of-args))))
    `(:instance ,lemma :extra-bindings-ok ,@instantiation)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-update-y1...yp
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls-with-tests pseudo-tests-and-call-listp)
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          a variable is instantiated with
          each of the arguments of each recursive call of @('old')
          that correspond to @('y1'), ..., @('yp'),
          with @('y1'), ..., @('yp') in such terms
          replaced with @('(back y1)'), ..., @('(back yp)')."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(...
        (:instance lemma (var updatej-yh<...,(back y1),...,(back yp),...>))
        ...)'),
    with @('j') going from 1 to @('m')
    and @('h') going from 1 to @('p').")
  (b* (((when (endp rec-calls-with-tests)) nil)
       (tests-and-call (car rec-calls-with-tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (update-y1...yp
        (isodata-get-rec-call-args-transformed rec-call old$ args$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$))
       (update-y1...yp-back (subcor-var-lst args$ back-of-args update-y1...yp))
       (instances
        (isodata-gen-lemma-instances-var-to-terms lemma
                                                  var
                                                  update-y1...yp-back))
       (more-instances (isodata-gen-lemma-instances-var-to-update-y1...yp
                        lemma
                        var
                        (cdr rec-calls-with-tests)
                        old$
                        args$
                        back$
                        wrld)))
    (append instances more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-x1...xn-to-update-x1...xn
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls-with-tests pseudo-tests-and-call-listp)
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ pseudo-termfnp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          @('x1'), ..., @('xn') are instantiated with
          the arguments of each recursive call of @('old'),
          with @('y1'), ..., @('yp') in such arguments
          replaced with @('(back y1)'), ..., @('(back yp)')."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(...
        (:instance lemma (x1 updatej-x1<...,(back y1),...,(back yp),...>)
                         ...
                         (xn updatej-xn<...,(back y1),...,(back yp),...>))
        ...)'),
    with @('j') going from 1 to @('m').")
  (b* (((when (endp rec-calls-with-tests)) nil)
       (tests-and-call (car rec-calls-with-tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (update-x1...xn (fargs rec-call))
       (back-of-args (apply-unary-to-terms back$ args$))
       (update-x1...xn-back (subcor-var-lst args$ back-of-args update-x1...xn))
       (instantiation
        (alist-to-doublets (pairlis$ (formals old$ wrld) update-x1...xn-back)))
       (instance `(:instance ,lemma :extra-bindings-ok ,@instantiation))
       (more-instances (isodata-gen-lemma-instances-x1...xn-to-update-x1...xn
                        lemma
                        (cdr rec-calls-with-tests)
                        old$
                        args$
                        back$
                        wrld)))
    (cons instance more-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls-with-tests pseudo-tests-and-call-listp)
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          @('x1'), ..., @('xn') are instantiated with
          the arguments of each recursive call of @('old'),
          with @('y1'), ..., @('yp') in such arguments
          replaced with @('(back y1)'), ..., @('(back yp)'),
          and with @('forth') around those arguments
          that are being transformed."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(...
        (:instance lemma
                   (x1 updatej-x1<...,(back y1),...,(back yp),...>)
                   ...
                   (y1 (forth updatej-y1<...,(back y1),...,(back yp),...>))
                   ...
                   (yp (forth updatej-yp<...,(back y1),...,(back yp),...>))
                   ...
                   (xn updatej-xn<...,(back y1),...,(back yp),...>))
        ...)'),
    with @('j') going from 1 to @('m').")
  (b* (((when (endp rec-calls-with-tests)) nil)
       (tests-and-call (car rec-calls-with-tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (rec-call-args (fargs rec-call))
       (back-of-args (apply-unary-to-terms back$ args$))
       (rec-call-back-args
        (subcor-var-lst args$ back-of-args rec-call-args))
       (forth-rec-call-back-args
        (isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn-aux
         args$ (formals old$ wrld) rec-call-back-args forth$))
       (formals-to-forth-rec-calls-of-back-args
        (alist-to-doublets
         (pairlis$ (formals old$ wrld) forth-rec-call-back-args))))
    (cons
     `(:instance ,lemma
       :extra-bindings-ok
       ,@formals-to-forth-rec-calls-of-back-args)
     (isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn
      lemma (cdr rec-calls-with-tests)
      old$ args$ forth$ back$ wrld)))

  :prepwork
  ((define isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn-aux
     ((args$ symbol-listp)
      (formals symbol-listp)
      (terms pseudo-term-listp)
      (forth$ pseudo-termfnp))
     :guard (= (len terms) (len formals))
     :returns new-terms ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (b* (((when (endp formals)) nil)
          (x (car formals))
          (term (car terms))
          (new-term (if (member-eq x args$)
                        (apply-term* forth$ term)
                      term))
          (new-terms
           (isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn-aux
            args$ (cdr formals) (cdr terms) forth$)))
       (cons new-term new-terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-rec-calls
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls-with-tests pseudo-tests-and-call-listp)
   (args$ symbol-listp)
   (back$ pseudo-termfnp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          a variable is instantiated with
          each recursive call of @('old'),
          with @('y1'), ..., @('yp') in such calls
          replaced with @('(back y1)'), ..., @('(back yp)')."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(...
        (:instance lemma
                   (var (old updatej-x1<...,(back y1),...,(back yp),...>
                             ...
                             updatej-xn<...,(back y1),...,(back yp),...>)))
        ...)'),
    with @('j') going from 1 to @('m').")
  (b* (((when (endp rec-calls-with-tests)) nil)
       (tests-and-call (car rec-calls-with-tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (back-of-args (apply-unary-to-terms back$ args$))
       (rec-call-back (subcor-var args$ back-of-args rec-call))
       (lemma-instance `(:instance ,lemma :extra-bindings-ok
                         (,var ,rec-call-back)))
       (lemma-instances (isodata-gen-lemma-instances-var-to-rec-calls
                         lemma var (cdr rec-calls-with-tests) args$ back$)))
    (cons lemma-instance lemma-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-lemma-instances-var-to-new-forth-update
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls-with-tests pseudo-tests-and-call-listp)
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (new-name$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances where
          a variable is instantiated with
          a call of the new function
          on the arguments of a recursive call of @('old'),
          with @('y1'), ..., @('yp') in such arguments
          replaced with @('(back y1)'), ..., @('(back yp)'),
          and with @('forth') around those arguments
          that are being transformed."
  :long
  (xdoc::topstring-p
   "The result is a list
    @('(...
        (:instance lemma
                   (var (new updatej-x1<...,(back y1),...,(back yp),...>
                             ...
                             (forth updatej-y1<...,(back y1),...,(back yp),...>)
                             ...
                             (forth updatej-yp<...,(back y1),...,(back yp),...>)
                             ...
                             updatej-xn<...,(back y1),...,(back yp),...>)))
        ...)'),
    with @('j') going from 1 to @('m').")
  (b* (((when (endp rec-calls-with-tests)) nil)
       (tests-and-call (car rec-calls-with-tests))
       (rec-call (access tests-and-call tests-and-call :call))
       (rec-call-args (fargs rec-call))
       (rec-call-args-back
        (subcor-var-lst args$ (apply-unary-to-terms back$ args$) rec-call-args))
       (rec-call-args-back-forth
        (isodata-gen-lemma-instances-var-to-new-forth-update-aux
         args$ (formals old$ wrld) rec-call-args-back forth$))
       (new-call (fcons-term new-name$ rec-call-args-back-forth))
       (lemma-instance `(:instance ,lemma :extra-bindings-ok (,var ,new-call)))
       (lemma-instances (isodata-gen-lemma-instances-var-to-new-forth-update
                         lemma var (cdr rec-calls-with-tests)
                         old$ args$ forth$ back$ new-name$ wrld)))
    (cons lemma-instance lemma-instances))

  :prepwork
  ((define isodata-gen-lemma-instances-var-to-new-forth-update-aux
     ((args$ symbol-listp)
      (formals symbol-listp)
      (terms pseudo-term-listp)
      (forth$ pseudo-termfnp))
     :guard (= (len terms) (len formals))
     :returns new-terms ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (b* (((when (endp formals)) nil)
          (x (car formals))
          (term (car terms))
          (new-term (if (member-eq x args$)
                        (apply-term* forth$ term)
                      term))
          (new-terms (isodata-gen-lemma-instances-var-to-new-forth-update-aux
                      args$ (cdr formals) (cdr terms) forth$)))
       (cons new-term new-terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-guard ((old$ symbolp)
                                  (args$ symbol-listp)
                                  (isomap isodata-isomapp)
                                  (predicate$ booleanp)
                                  (wrld plist-worldp))
  :returns (new-guard "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the guard of the new function."
  (b* ((newp$ (isodata-isomap->newp isomap))
       (back$ (isodata-isomap->back isomap))
       (newp-of-args (apply-unary-to-terms newp$ args$)))
    (if predicate$
        (conjoin newp-of-args)
      (b* ((old-guard (guard old$ nil wrld))
           (back-of-args (apply-unary-to-terms back$ args$))
           (old-guard-with-back-of-args
            (subcor-var args$ back-of-args old-guard)))
        (conjoin (append newp-of-args
                         (list old-guard-with-back-of-args)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-pred ((old$ symbolp)
                                      (args$ symbol-listp)
                                      (res$ booleanp)
                                      (isomap isodata-isomapp)
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
    "First we transform any recursive calls
     via @('isodata-xform-rec-calls-in-term'),
     which causes no change if @('old') is not recursive.
     Then we replace @('y1'), ..., @('yp')
     with @('(back y1)'), ..., @('(back yp)').
     Finally, we conjoin the result
     with @('(newp y1)'), ..., @('(newp yp)')."))
  (b* ((newp$ (isodata-isomap->newp isomap))
       (back$ (isodata-isomap->back isomap))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls-in-term
         old-body old$ args$ res$ isomap new-name$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args
        (subcor-var args$ back-of-args old-body-with-new-rec-calls))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (newp-of-args-conj (conjoin newp-of-args)))
    (if (equal newp-of-args-conj *t*)
        old-body-with-back-of-args
      (conjoin2 `(mbt$ ,newp-of-args-conj)
                old-body-with-back-of-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-nonpred-nonrec ((old$ symbolp)
                                                (args$ symbol-listp)
                                                (res$ booleanp)
                                                (isomap isodata-isomapp)
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
  (b* ((newp$ (isodata-isomap->newp isomap))
       (forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args (subcor-var args$ back-of-args old-body))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (then-branch (if res$
                        (apply-fn-into-ifs forth$ old-body-with-back-of-args)
                      old-body-with-back-of-args))
       (else-branch (b* ((n (number-of-results old$ wrld)))
                      (if (> n 1)
                          (cons 'mv (repeat n nil))
                        nil)))
       (newp-of-args-conj (conjoin newp-of-args)))
    (cond (compatibility then-branch)
          ((equal newp-of-args-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-args-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body-nonpred-rec ((old$ symbolp)
                                             (args$ symbol-listp)
                                             (res$ booleanp)
                                             (isomap pseudo-termfnp)
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
    "First we transform the recursive calls
     via @('isodata-xform-rec-calls-in-term').
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
  (b* ((newp$ (isodata-isomap->newp isomap))
       (forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (body old$ nil wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls-in-term
         old-body old$ args$ res$ isomap new-name$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args
        (subcor-var args$ back-of-args old-body-with-new-rec-calls))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (then-branch (if res$
                        (apply-fn-into-ifs forth$ old-body-with-back-of-args)
                      old-body-with-back-of-args))
       (else-branch (b* ((n (number-of-results old$ wrld)))
                      (if (> n 1)
                          (cons 'mv (repeat n nil))
                        nil)))
       (newp-of-args-conj (conjoin newp-of-args)))
    (cond ((equal newp-of-args-conj *t*) then-branch)
          (t `(if (mbt$ ,newp-of-args-conj)
                  ,then-branch
                ,else-branch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-body ((old$ symbolp)
                                 (args$ symbol-listp)
                                 (res$ booleanp)
                                 (isomap pseudo-termfnp)
                                 (predicate$ booleanp)
                                 (new-name$ symbolp)
                                 compatibility
                                 (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function."
  (if predicate$
      (isodata-gen-new-fn-body-pred old$ args$ res$ isomap new-name$ wrld)
    (if (recursivep old$ nil wrld)
        (isodata-gen-new-fn-body-nonpred-rec
         old$ args$ res$ isomap new-name$ wrld)
      (isodata-gen-new-fn-body-nonpred-nonrec
       old$ args$ res$ isomap compatibility wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-measure ((old$ symbolp)
                                    (args$ symbol-listp)
                                    (isomap pseudo-termfnp)
                                    (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the measure of the function, if recursive."
  (b* ((back$ (isodata-isomap->back isomap))
       (old-measure (measure old$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$)))
    (subcor-var args$ back-of-args old-measure)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-termination-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
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
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (instance-termination-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth
         `(:termination-theorem ,old$)
         args$
         back$))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-termination-thm-old
             ,@instances-back-image
             ,instance-oldp-of-rec-call-args
             ,@instances-back-of-forth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn ((old$ symbolp)
                            (args$ symbol-listp)
                            (res$ booleanp)
                            (isomap isodata-isomapp)
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
       (body (isodata-gen-new-fn-body
              old$ args$ res$ isomap predicate$ new-name$ compatibility wrld))
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
       (guard (isodata-gen-new-fn-guard old$ args$ isomap predicate$ wrld))
       (guard (conjoin (flatten-ands-in-lit guard)))
       (guard (untranslate guard nil wrld))
       (recursive (recursivep old$ nil wrld))
       (wfrel? (if recursive
                   (well-founded-relation old$ wrld)
                 nil))
       (measure? (if recursive
                     (isodata-gen-new-fn-measure old$ args$ isomap wrld)
                   nil))
       (termination-hints? (if recursive
                               (isodata-gen-new-fn-termination-hints
                                app-cond-thm-names old$ args$ isomap wrld)
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

(define isodata-gen-new-to-old-thm-formula ((old$ symbolp)
                                            (args$ symbol-listp)
                                            (res$ booleanp)
                                            (isomap isodata-isomapp)
                                            (new-name$ symbolp)
                                            (wrld plist-worldp))
  :returns (new-to-old-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the new function in terms of the old function."
  (b* ((newp$ (isodata-isomap->newp isomap))
       (forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (formals (formals old$ wrld))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-call (subcor-var args$ back-of-args `(,old$ ,@formals))))
    (implicate (conjoin newp-of-args)
               `(equal (,new-name$ ,@formals)
                       ,(if res$
                            (apply-term* forth$ old-call)
                          old-call)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-nonrec ((old-fn-unnorm-name symbolp)
                                                 (new-fn-unnorm-name symbolp))
  :returns (hints true-listp)
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are not recursive."
  `(("Goal"
     :in-theory '(,old-fn-unnorm-name ,new-fn-unnorm-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm-hints-rec-nonres
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and @('args/res') does not include @(':result')."
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-image
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive
          and @('args/res') includes @(':result')."
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-oldp-of-old
        (isodata-gen-lemma-instances-x1...xn-to-update-x1...xn oldp-of-old
                                                               rec-calls
                                                               old$
                                                               args$
                                                               back$
                                                               wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-image
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-of-forth-res
        (isodata-gen-lemma-instances-var-to-rec-calls back-of-forth
                                                      a
                                                      rec-calls
                                                      args$
                                                      back$)))
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
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp)
   (new-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function."
  (if (recursivep old$ nil wrld)
      (if res$
          (isodata-gen-new-to-old-thm-hints-rec-res app-cond-thm-names
                                                    old$
                                                    args$
                                                    isomap
                                                    new-name$
                                                    old-fn-unnorm-name
                                                    new-fn-unnorm-name
                                                    wrld)
        (isodata-gen-new-to-old-thm-hints-rec-nonres app-cond-thm-names
                                                     old$
                                                     args$
                                                     isomap
                                                     new-name$
                                                     old-fn-unnorm-name
                                                     new-fn-unnorm-name
                                                     wrld))
    (isodata-gen-new-to-old-thm-hints-nonrec old-fn-unnorm-name
                                             new-fn-unnorm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-to-old-thm ((old$ symbolp)
                                    (args$ symbol-listp)
                                    (res$ booleanp)
                                    (isomap isodata-isomapp)
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
                                                    args$
                                                    res$
                                                    isomap
                                                    new-name$
                                                    wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-new-to-old-thm-hints app-cond-thm-names
                                                old$
                                                args$
                                                res$
                                                isomap
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

(define isodata-gen-old-to-new-thm-formula ((old$ symbolp)
                                            (args$ symbol-listp)
                                            (res$ booleanp)
                                            (isomap isodata-isomapp)
                                            (new-name$ symbolp)
                                            (wrld plist-worldp))
  :returns (old-to-new-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that relates the old and new function."
  (b* ((oldp$ (isodata-isomap->oldp isomap))
       (forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (formals (formals old$ wrld))
       (oldp-of-args (apply-unary-to-terms oldp$ args$))
       (forth-of-args (apply-unary-to-terms forth$ args$))
       (new-call
        (subcor-var args$ forth-of-args `(,new-name$ ,@formals))))
    (implicate (conjoin oldp-of-args)
               `(equal (,old$ ,@formals)
                       ,(if res$
                            (apply-term* back$ new-call)
                          new-call)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-nonres-hints
  ((args$ symbol-listp)
   (isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when @('args/res') does not include @(':result')."
  (b* ((forth$ (isodata-isomap->forth isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-terms forth-image
                                                  a
                                                  args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-terms back-of-forth
                                                  a
                                                  args$))
       (instance-new-to-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth new-to-old
                                                          args$
                                                          forth$)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm-res-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function,
          when @('args/res') includes @(':result')."
  (b* ((forth$ (isodata-isomap->forth isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-terms forth-image
                                                  a
                                                  args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-terms back-of-forth
                                                  a
                                                  args$))
       (instance-new-to-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth new-to-old
                                                          args$
                                                          forth$))
       (instance-back-of-forth-res
        `(:instance ,back-of-forth
          :extra-bindings-ok (,a (,old$ ,@(formals old$ wrld))))))
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
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function."
  (if res$
      (isodata-gen-old-to-new-thm-res-hints app-cond-thm-names
                                            old$
                                            args$
                                            isomap
                                            new-to-old
                                            wrld)
    (isodata-gen-old-to-new-thm-nonres-hints args$
                                             isomap
                                             new-to-old
                                             wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-old-to-new-thm ((app-cond-thm-names symbol-symbol-alistp)
                                    (old$ symbolp)
                                    (args$ symbol-listp)
                                    (res$ booleanp)
                                    (isomap isodata-isomapp)
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
                 old$ args$ res$ isomap new-name$ wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-old-to-new-thm-hints app-cond-thm-names
                                                old$
                                                args$
                                                res$
                                                isomap
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

(define isodata-gen-newp-of-new-thm-formula ((old$ symbolp)
                                             (args$ symbol-listp)
                                             (isomap isodata-isomapp)
                                             (new-name$ symbolp)
                                             (wrld plist-worldp))
  :returns (formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that says that the new function maps
          values in the new representation
          to values in the old representation."
  :long
  (xdoc::topstring-p
   "This is the theorem @($f'A'B'$) in the design notes.
    It is generated only if @('args/res') includes @(':result').")
  (b* ((newp$ (isodata-isomap->newp isomap))
       (newp-of-args (apply-unary-to-terms newp$ args$)))
    (implicate (conjoin newp-of-args)
               `(,newp$ (,new-name$ ,@(formals old$ wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
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
    It is generated only if @('args/res') includes @(':result').")
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-old
                                                          args$
                                                          back$))
       (old-call (fcons-term old$ (formals old$ wrld)))
       (old-call-of-back-args
        (subcor-var args$ (apply-unary-to-terms back$ args$) old-call))
       (instance-forth-image
        `(:instance ,forth-image
          :extra-bindings-ok (,a ,old-call-of-back-args))))
    `(("Goal"
       :in-theory nil
       :use (,@instances-back-image
             ,instance-oldp-of-old
             ,instance-forth-image
             ,new-to-old)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-newp-of-new-thm ((old$ symbolp)
                                     (args$ symbol-listp)
                                     (isomap isodata-isomapp)
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
    It is generated only if @('args/res') includes @(':result').")
  (b* ((name (fresh-logical-name-with-$s-suffix 'newp-of-new
                                                nil
                                                names-to-avoid
                                                wrld))
       (formula (isodata-gen-newp-of-new-thm-formula old$
                                                     args$
                                                     isomap
                                                     new-name$
                                                     wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-newp-of-new-thm-hints app-cond-thm-names
                                                 old$
                                                 args$
                                                 isomap
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when non-recursive and when @(':predicate') is @('t')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((back$ (isodata-isomap->back isomap))
       (back-image (isodata-isomap->back-image isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (b (isodata-gen-var-b back$ wrld))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth `(:guard-theorem ,old$)
                                                          args$
                                                          back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-y1...yp-to-back/forth old-guard-pred
                                                          args$
                                                          back$)))
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
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
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (forth-guard (isodata-isomap->forth-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred
                              app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth
         `(:guard-theorem ,old$)
         args$
         back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-forth-guard
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-guard
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-image
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-y1...yp-to-back/forth old-guard-pred
                                                          args$
                                                          back$))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-new-to-old
        (isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn new-to-old
                                                                     rec-calls
                                                                     old$
                                                                     args$
                                                                     forth$
                                                                     back$
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('t')."
  (if (recursivep old$ nil wrld)
      (isodata-gen-new-fn-verify-guards-hints-pred-rec app-cond-thm-names
                                                       old$
                                                       args$
                                                       isomap
                                                       new-to-old
                                                       wrld)
    (isodata-gen-new-fn-verify-guards-hints-pred-nonrec app-cond-thm-names
                                                        old$
                                                        args$
                                                        isomap
                                                        wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-nonres
  ((old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and when @('args/res') does not include @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((back$ (isodata-isomap->back isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (b (isodata-gen-var-b back$ wrld))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth
         `(:guard-theorem ,old$)
         args$
         back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-res
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (old-fn-unnorm-name symbolp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when the function is not recursive,
          when @(':predicate') is @('nil'),
          and when @('args/res') includes @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((back$ (isodata-isomap->back isomap))
       (back-image (isodata-isomap->back-image isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth
         `(:guard-theorem ,old$)
         args$
         back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-old
                                                          args$
                                                          back$))
       (instance-old-fn-unnorm-name
        (isodata-gen-lemma-instance-y1...yp-to-back/forth old-fn-unnorm-name
                                                          args$
                                                          back$)))
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when the function is recursive,
          when @(':predicate') is @('nil'),
          and when @('args/res') does not include @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (forth-guard (isodata-isomap->forth-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (rec-calls (recursive-calls old$ wrld))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth `(:guard-theorem ,old$)
                                                          args$
                                                          back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-forth-guard
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-guard
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-image
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-old-to-new
        (isodata-gen-lemma-instances-x1...xn-to-update-x1...xn thm-name$
                                                               rec-calls
                                                               old$
                                                               args$
                                                               back$
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
   (args$ symbol-listp)
   (isomap isodata-isomapp)
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
          and when @('args/res') includes @(':result')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((forth$ (isodata-isomap->forth isomap))
       (back$ (isodata-isomap->back isomap))
       (forth-image (isodata-isomap->forth-image isomap))
       (back-image (isodata-isomap->back-image isomap))
       (back-of-forth (isodata-isomap->back-of-forth isomap))
       (newp-guard (isodata-isomap->newp-guard isomap))
       (forth-guard (isodata-isomap->forth-guard isomap))
       (back-guard (isodata-isomap->back-guard isomap))
       (a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-old (cdr (assoc-eq :oldp-of-old app-cond-thm-names)))
       (oldp-of-rec-call-args (cdr (assoc-eq :oldp-of-rec-call-args
                                     app-cond-thm-names)))
       (rec-calls (recursive-calls old$ wrld))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth
         `(:guard-theorem ,old$)
         args$
         back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-var-to-terms newp-guard
                                                  b
                                                  args$))
       (instances-forth-guard
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-guard
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-guard
        (isodata-gen-lemma-instances-var-to-terms back-guard
                                                  b
                                                  args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-var-to-update-y1...yp forth-image
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-var-to-terms back-image
                                                  b
                                                  args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-var-to-update-y1...yp back-of-forth
                                                           a
                                                           rec-calls
                                                           old$
                                                           args$
                                                           back$
                                                           wrld))
       (instance-oldp-of-rec-call-args
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-rec-call-args
                                                          args$
                                                          back$))
       (instances-old-to-new
        (isodata-gen-lemma-instances-x1...xn-to-update-x1...xn thm-name$
                                                               rec-calls
                                                               old$
                                                               args$
                                                               back$
                                                               wrld))
       (instance-oldp-of-old
        (isodata-gen-lemma-instance-y1...yp-to-back/forth oldp-of-old
                                                          args$
                                                          back$))
       (instance-old-fn-unnorm-name
        (isodata-gen-lemma-instance-y1...yp-to-back/forth old-fn-unnorm-name
                                                          args$
                                                          back$))
       (instances-newp-of-new
        (isodata-gen-lemma-instances-x1...xn-to-forth-update-x1...xn newp-of-new
                                                                     rec-calls
                                                                     old$
                                                                     args$
                                                                     forth$
                                                                     back$
                                                                     wrld))
       (old-call (fcons-term old$ (formals old$ wrld)))
       (old-call-of-back-args
        (subcor-var args$ (apply-unary-to-terms back$ args$) old-call))
       (instance-forth-guard-res
        `(:instance ,forth-guard
          :extra-bindings-ok (,a ,old-call-of-back-args)))
       (instances-back-guard-res
        (isodata-gen-lemma-instances-var-to-new-forth-update back-guard
                                                             b
                                                             rec-calls
                                                             old$
                                                             args$
                                                             forth$
                                                             back$
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
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
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
      (if res$
          (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-res
           app-cond-thm-names
           old$
           args$
           isomap
           new-name$
           thm-name$
           old-fn-unnorm-name
           newp-of-new
           wrld)
        (isodata-gen-new-fn-verify-guards-hints-nonpred-rec-nonres
         app-cond-thm-names
         old$
         args$
         isomap
         thm-name$
         wrld))
    (if res$
        (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-res
         app-cond-thm-names
         old$
         args$
         isomap
         old-fn-unnorm-name
         wrld)
      (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec-nonres
       old$
       args$
       isomap
       wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards-hints
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
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
                                                   args$
                                                   isomap
                                                   new-to-old
                                                   wrld)
    (isodata-gen-new-fn-verify-guards-hints-nonpred app-cond-thm-names
                                                    old$
                                                    args$
                                                    res$
                                                    isomap
                                                    new-name$
                                                    thm-name$
                                                    old-fn-unnorm-name
                                                    newp-of-new
                                                    wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define isodata-gen-new-fn-verify-guards
  ((app-cond-thm-names symbol-symbol-alistp)
   (old$ symbolp)
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
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
                                                      args$
                                                      res$
                                                      isomap
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
   (args$ symbol-listp)
   (res$ booleanp)
   (isomap isodata-isomapp)
   (arg-isomaps isodata-symbol-isomap-alistp)
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
       (defiso-events (isodata-gen-defisos isomaps verify-guards$ print$))
       ((mv app-cond-thm-events
            app-cond-thm-names)
        (isodata-gen-app-conds app-conds
                               old$
                               args$
                               isomap
                               arg-isomaps
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
                            args$
                            res$
                            isomap
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
                                    args$
                                    res$
                                    isomap
                                    new-name$
                                    names-to-avoid
                                    app-cond-thm-names
                                    old-fn-unnorm-name
                                    new-fn-unnorm-name
                                    wrld))
       (names-to-avoid (cons new-to-old names-to-avoid))
       ((mv newp-of-new-thm-event?
            newp-of-new?)
        (if res$
            (isodata-gen-newp-of-new-thm old$
                                         args$
                                         isomap
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
                                    args$
                                    res$
                                    isomap
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
                                           args$
                                           res$
                                           isomap
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
                    args/res-iso
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
                  args$
                  res$
                  isomap
                  arg-isomaps
                  res-isomap?
                  new-name$
                  new-enable$
                  thm-name$
                  non-executable$
                  verify-guards$
                  hints$
                  app-cond-keywords
                  names-to-avoid))
        (isodata-process-inputs old
                                args/res-iso
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
       (event (isodata-gen-everything old$
                                      args$
                                      res$
                                      isomap
                                      arg-isomaps
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
                     args/res-iso
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
                                   ',args/res-iso
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
