; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/apt/utilities/transformation-table" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/std/system/ibody" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/util/defiso" :dir :system)
(include-book "kestrel/utilities/directed-untranslate" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/system/install-not-norm-event" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "utilities/untranslate-specifiers")
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 isodata

 :items

 ("@('state') is the ACL2 @(see state)."

  "@('wrld') is the ACL2 @(see world)."

  "@('ctx') is the context used for errors."

  "@('old'),
   @('args-iso'),
   @('predicate'),
   @('new-name'),
   @('new-enable'),
   @('thm-name'),
   @('thm-enable'),
   @('non-executable'),
   @('normalize'),
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
   @('normalize'),
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

  "@('args$') is the result of processing
   the @('args') component of the @('args-iso') input."

  "@('iso$') is the @('iso') component of the @('args-iso') input
   if @('iso') is the name of a @(tsee defiso);
   otherwise, it is the fresh @(tsee defiso) name
   internally generated and used by @(tsee isodata)."

  "@('oldp$'),
   @('newp$'),
   @('forth$'), and
   @('back$'),
   are the domains and conversions
   of the @(tsee defiso) referenced or generated
   by the @('iso') component of the @('args-iso') input."

  "@('forth-image'),
   @('back-image'),
   @('back-of-forth'),
   @('forth-of-back'),
   @('oldp-guard'),
   @('newp-guard'),
   @('forth-guard'),
   @('back-guard'),
   @('forth-injective'), and
   @('back-injective')
   are the theorems
   of the @(tsee defiso) referenced or generated
   by the @('iso') component of the @('args-iso') input.
   The @('...-guard') ones are @('nil') if absent."

  "@('namedp') is
   @('t') if @('iso) is the name of an existing @(tsee defiso),
   @('nil') otherwise."

  "@('iso-hints') are the hints that are part of
   the @('iso') component of the @('args-iso') input,
   when @('iso') is not a name."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing isodata)

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

(define isodata-process-args (args (old$ symbolp) ctx state)
  :returns (mv erp
               (args$ "A @(tsee symbol-listp) that is
                       the list of formal arguments
                       whose representation is to be transformed.")
               state)
  :mode :program
  :short "Process the @('args') component of the @('args-iso') input."
  :long
  (xdoc::topstring-p
   "If @('args') is a single formal argument of @('old'),
    return the singleton list with that formal argument.")
  (b* ((formals (formals old$ (w state))))
    (cond ((member-eq args formals)
           (value (list args)))
          ((symbolp args)
           (er-soft+ ctx t nil
                     "The ARGS component of the second input must be ~
                      a formal argument or a list of formal arguments ~
                      of the target function ~x0.  ~
                      The symbol ~x1 is not a formal argument of ~x0."
                     old$ args))
          (t (b* (((er &) (ensure-symbol-list$
                           args
                           "Since the ARGS component of the second input ~
                            is not a symbol, it"
                           t nil))
                  (description (msg "The list ~x0 of the formal arguments ~
                                     of the target function ~x1 ~
                                     whose representation is to be transformed"
                                    args old$))
                  ((er &) (ensure-list-subset$ args formals description t nil))
                  ((er &) (ensure-list-no-duplicates$ args description t nil)))
               (value args))))))

(define isodata-fresh-defiso-name ((old$ symbolp) (wrld plist-worldp))
  :returns (fresh-defiso-name "A @(tsee symbolp).")
  :mode :program
  :short "Return a fresh @(tsee defiso) name."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, one that is not a key in the @(tsee defiso) table.
     This will be eventually used as the name of a @(tsee defiso)
     that @(tsee isodata) will generate locally,
     when the @('iso') input is not a name.")
   (xdoc::p
    "We start with a name of the form @('defiso-isodata-<old>'),
     where @('<old>') is the @('old') input of @(tsee isodata),
     and we add as many @('*') characters at the end to make it fresh.
     We expect that it will be rarely necessary to add @('*') characters.
     The name is in the package of @('old')."))
  (b* ((name (packn-pos (list 'defiso-isodata- old$) old$))
       (table (table-alist *defiso-table-name* wrld)))
    (isodata-fresh-defiso-name-aux name table))

  :prepwork
  ((define isodata-fresh-defiso-name-aux ((name symbolp) (table alistp))
     :returns name-with-possibly-added-suffix ; SYMBOLP
     :mode :program
     (if (consp (assoc-eq name table))
         (isodata-fresh-defiso-name-aux (packn-pos (list name '*) name)
                                        table)
       name))))

(define isodata-fresh-defiso-thm-names ((iso$ symbolp)
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
     (which is generated by @(tsee isodata-fresh-defiso-name),
     and add enough @('$') characters, if needed, to make them fresh.
     We expect that adding @('$') characters will rarely be necessary.")
   (xdoc::p
    "The names of the guard-related theorems are @('nil')
     if guards must not be verified, since
     those theorems are not generated or used in that case."))
  (b* ((iso$ (add-suffix iso$ "-"))
       (forth-image (fresh-name-in-world-with-$s
                     (add-suffix iso$ (symbol-name :alpha-image))
                     names-to-avoid
                     wrld))
       (names-to-avoid (cons forth-image names-to-avoid))
       (back-image (fresh-name-in-world-with-$s
                    (add-suffix iso$ (symbol-name :beta-image))
                    names-to-avoid
                    wrld))
       (names-to-avoid (cons back-image names-to-avoid))
       (back-of-forth (fresh-name-in-world-with-$s
                       (add-suffix iso$ (symbol-name :beta-of-alpha))
                       names-to-avoid
                       wrld))
       (names-to-avoid (cons back-of-forth names-to-avoid))
       (forth-of-back (fresh-name-in-world-with-$s
                       (add-suffix iso$ (symbol-name :alpha-of-beta))
                       names-to-avoid
                       wrld))
       (names-to-avoid (cons forth-of-back names-to-avoid))
       (oldp-guard (and verify-guards$
                        (fresh-name-in-world-with-$s
                         (add-suffix iso$ (symbol-name :doma-guard))
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons oldp-guard names-to-avoid)
                         names-to-avoid))
       (newp-guard (and verify-guards$
                        (fresh-name-in-world-with-$s
                         (add-suffix iso$ (symbol-name :domb-guard))
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons newp-guard names-to-avoid)
                         names-to-avoid))
       (forth-guard (and verify-guards$
                         (fresh-name-in-world-with-$s
                          (add-suffix iso$ (symbol-name :alpha-guard))
                          names-to-avoid
                          wrld)))
       (names-to-avoid (if verify-guards$
                           (cons forth-guard names-to-avoid)
                         names-to-avoid))
       (back-guard (and verify-guards$
                        (fresh-name-in-world-with-$s
                         (add-suffix iso$ (symbol-name :beta-guard))
                         names-to-avoid
                         wrld)))
       (names-to-avoid (if verify-guards$
                           (cons back-guard names-to-avoid)
                         names-to-avoid))
       (forth-injective (fresh-name-in-world-with-$s
                         (add-suffix iso$ (symbol-name :alpha-injective))
                         names-to-avoid
                         wrld))
       (names-to-avoid (cons forth-injective names-to-avoid))
       (back-injective (fresh-name-in-world-with-$s
                        (add-suffix iso$ (symbol-name :beta-injective))
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

(define isodata-process-iso (iso
                             (old$ symbolp)
                             (verify-guards$ booleanp)
                             (names-to-avoid symbol-listp)
                             ctx
                             state)
  :returns (mv erp
               (result "A tuple @('(iso$
                                    oldp$
                                    newp$
                                    forth$
                                    back$
                                    forth-image
                                    back-image
                                    back-of-forth
                                    forth-of-back
                                    oldp-guard
                                    new-guard
                                    forth-guard
                                    back-guard
                                    forth-injective
                                    back-injective
                                    namedp
                                    iso-hints
                                    named-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         booleanp
                                         acl2::any-p
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process the @('iso') component of the @('args-iso') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('iso') is the name of an existing @(tsee defiso),
     we return @('iso') itself as the @('iso$') result,
     the first domain of @('iso') as the @('oldp$') result,
     the second domain of @('iso') as the @('newp$') result,
     the first conversion of @('iso') as the @('forth$') result,
     the second conversion of @('iso') as the @('back$') result,
     the name of the @(':alpha-image') theorem of @('iso')
     as the @('forth-image') result,
     the name of the @(':alpha-image') theorem of @('iso')
     as the @('forth-image') result,
     the name of the @(':beta-image') theorem of @('iso')
     as the @('back-image') result,
     the name of the @(':beta-of-alpha') theorem of @('iso')
     as the @('back-of-forth') result,
     the name of the @(':alpha-of-beta') theorem of @('iso')
     as the @('forth-of-back') result,
     the name of the @(':doma-guard') theorem of @('iso')
     as the @('oldp-guard') result (@('nil') if absent),
     the name of the @(':domb-guard') theorem of @('iso')
     as the @('newp-guard') result (@('nil') if absent),
     the name of the @(':alpha-guard') theorem of @('iso')
     as the @('forth-guard') result (@('nil') if absent),
     the name of the @(':beta-guard') theorem of @('iso')
     as the @('back-guard') result (@('nil') if absent),
     the name of the @(':alpha-injective') theorem of @('iso')
     as the @('forth-injective') result,
     the name of the @(':beta-injective') theorem of @('iso')
     as the @('back-injective') result,
     @('t') as the @('namedp') result, and
     @('nil') as the @('iso-hints') result.
     These function and theorem names are retrieved
     from the @(tsee defiso) information
     recorded in the ACL2 world.
     The @('names-to-avoid') argument is returned unchanged,
     because we are not generating any fresh theorem names in this case.")
   (xdoc::p
    "If instead @('iso') is a list
     @('(oldp newp forth back)') or @('(oldp newp forth back :hints ...)'),
     we return a fresh @(tsee defiso) name as the @('iso$') result,
     the four functions denoted by
     the honomymous elements (without the @('$')) of the @('iso') list
     as the four function results,
     fresh @(tsee defiso) theorem names
     as the theorem name results,
     @('nil') as the @('namedp') result,
     and what follows @(':hints') as the @('iso-hints') result
     (@('nil') if there is no @(':hints')).
     The @('names-to-avoid') argument is augmented with
     the names of these theorems,
     which will be generated by the local @(tsee defiso).")
   (xdoc::p
    "Thus, either way we return
     the recognizers of the old and new representation,
     the conversions between them,
     and the relevant theorems about them,
     whether they were supplied in a @(tsee defiso)
     or directly in this @(tsee isodata).")
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
     we use @(tsee defiso)'s input processing functions
     to process the four functions,
     and then we check that they are all unary and single-valued.
     We cannot just generate the @(tsee defiso):
     we need the actual (translated) functions
     to use them in the events generated by @(tsee isodata) proper.
     When we call @(tsee defiso)'s input processing functions,
     we set the context @('ctx') to the one for the @(tsee defiso) call,
     so that the error message is appropriate.
     (When the generated @(tsee defiso) call is submitted,
     these input processing steps will be repeated,
     but will succeed since they have been already performed here."))
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
                      old$ iso)))
        (value (list iso
                     info.doma
                     info.domb
                     info.alpha
                     info.beta
                     info.alpha-image
                     info.beta-image
                     info.beta-of-alpha
                     info.alpha-of-beta
                     info.doma-guard
                     info.domb-guard
                     info.alpha-guard
                     info.beta-guard
                     info.alpha-injective
                     info.beta-injective
                     t
                     nil
                     names-to-avoid)))
    (b* ((iso$ (isodata-fresh-defiso-name old$ (w state)))
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
         (iso-hints (and (= (len iso) 6) (sixth iso)))
         (ctx-defiso (cons 'defiso iso$))
         ((er (list oldp$ oldp-arity oldp-numres))
          (acl2::defiso-process-function
           oldp 2 verify-guards$ ctx-defiso state))
         ((er (list newp$ newp-arity newp-numres))
          (acl2::defiso-process-function
           newp 3 verify-guards$ ctx-defiso state))
         ((er (list forth$ forth-arity forth-numres))
          (acl2::defiso-process-function
           forth 4 verify-guards$ ctx-defiso state))
         ((er (list back$ back-arity back-numres))
          (acl2::defiso-process-function
           back 5 verify-guards$ ctx-defiso state))
         ((unless (= oldp-arity 1))
          (er-soft+ ctx t nil
                    "The first component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 instead."
                    oldp oldp-arity))
         ((unless (= oldp-numres 1))
          (er-soft+ ctx t nil
                    "The first component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one result, but it has ~x1 instead."
                    oldp oldp-numres))
         ((unless (= newp-arity 1))
          (er-soft+ ctx t nil
                    "The second component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 instead."
                    newp newp-arity))
         ((unless (= newp-numres 1))
          (er-soft+ ctx t nil
                    "The second component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one result, but it has ~x1 instead."
                    newp newp-numres))
         ((unless (= forth-arity 1))
          (er-soft+ ctx t nil
                    "The third component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 instead."
                    forth forth-arity))
         ((unless (= forth-numres 1))
          (er-soft+ ctx t nil
                    "The third component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one result, but it has ~x1 instead."
                    forth forth-numres))
         ((unless (= back-arity 1))
          (er-soft+ ctx t nil
                    "The fourth component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one argument, but it has ~x1 instead."
                    back back-arity))
         ((unless (= back-numres 1))
          (er-soft+ ctx t nil
                    "The fourth component ~x0 ~
                     of the ISO component ~
                     of the third input ~
                     must have one result, but it has ~x1 instead."
                    back back-numres)))
      (value (list iso$
                   oldp$
                   newp$
                   forth$
                   back$
                   forth-image
                   back-image
                   back-of-forth
                   forth-of-back
                   oldp-guard
                   newp-guard
                   forth-guard
                   back-guard
                   forth-injective
                   back-injective
                   nil
                   iso-hints
                   names-to-avoid)))))

(define isodata-process-args-iso (args-iso
                                  (old$ symbolp)
                                  (verify-guards$ booleanp)
                                  (names-to-avoid symbol-listp)
                                  ctx
                                  state)
  :returns (mv erp
               (result "A tuple @('(args$
                                    iso$
                                    oldp$
                                    newp$
                                    forth$
                                    back$
                                    forth-image
                                    back-image
                                    back-of-forth
                                    forth-of-back
                                    oldp-guard
                                    new-guard
                                    forth-guard
                                    back-guard
                                    forth-injective
                                    back-injective
                                    namedp
                                    iso-hints
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbol-listp
                                         symbolp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         booleanp
                                         acl2::any-p
                                         symbol-listp
                                         result)'),
                         where @('args$') is
                         the result of @(tsee isodata-process-args)
                         and the other components are
                         results of @(tsee isodata-process-iso).")
               state)
  :mode :program
  :short "Process the @('args-iso') input."
  (b* (((er &) (ensure-doublet-list$ args-iso "The second input" t nil))
       (len (len args-iso))
       ((unless (= len 1))
        (er-soft+ ctx t nil
                  "The list of doublets ~x0 passed as second input ~
                   must contain exactly one element, ~
                   but it contains ~x1 elements instead."
                  args-iso
                  len))
       (args-iso (car args-iso))
       (args (first args-iso))
       (iso (second args-iso))
       ((er args$) (isodata-process-args args old$ ctx state))
       ((er (list iso$
                  oldp$
                  newp$
                  forth$
                  back$
                  forth-image
                  back-image
                  back-of-forth
                  forth-of-back
                  oldp-guard
                  newp-guard
                  forth-guard
                  back-guard
                  forth-injective
                  back-injective
                  namedp
                  iso-hints
                  names-to-avoid))
        (isodata-process-iso iso old$ verify-guards$ names-to-avoid ctx state)))
    (value (list args$
                 iso$
                 oldp$
                 newp$
                 forth$
                 back$
                 forth-image
                 back-image
                 back-of-forth
                 forth-of-back
                 oldp-guard
                 newp-guard
                 forth-guard
                 back-guard
                 forth-injective
                 back-injective
                 namedp
                 iso-hints
                 names-to-avoid))))

(define isodata-process-new-name (new-name (old$ symbolp) ctx state)
  :returns (mv erp
               (new-name$ "A @(tsee symbolp) to use as
                           the name of the new function.")
               state)
  :mode :program
  :short "Process the @(':new-name') input."
  (b* (((er &) (ensure-symbol$ new-name "The :NEW-NAME input" t nil))
       (name (case new-name
               (:auto (next-numbered-name old$ (w state)))
               (t new-name)))
       (description (msg "The name ~x0 of the new function, ~@1,"
                         name
                         (if (eq new-name :auto)
                             "automatically generated ~
                              since the :NEW-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :NEW-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil)))
    (value name)))

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

(defval *isodata-app-cond-keywords*
  :short "Keywords that identify the applicability conditions."
  '(:oldp-when-old
    :oldp-of-rec-calls
    :old-guard
    :old-guard-pred)
  ///

  (defruled keyword-listp-of-*isodata-app-cond-keywords*
    (keyword-listp *isodata-app-cond-keywords*))

  (defruled no-duplicatesp-eq-of-*isodata-app-cond-keywords*
    (no-duplicatesp-eq *isodata-app-cond-keywords*)))

(define isodata-app-cond-keywordp (x)
  :returns (yes/no booleanp)
  :short "Recognize the keywords of the applicability conditions."
  (and (member-eq x *isodata-app-cond-keywords*) t))

(std::deflist isodata-app-cond-keyword-listp (x)
  (isodata-app-cond-keywordp x)
  :short "Recognize true lists of the keywords of the applicability conditions."
  :true-listp t
  :elementp-of-nil nil)

(define isodata-app-cond-present-p ((keyword isodata-app-cond-keywordp)
                                    (old$ symbolp)
                                    (predicate$ booleanp)
                                    (verify-guards$ booleanp)
                                    (wrld plist-worldp))
  :returns (yes/no booleanp :hyp (and (booleanp predicate$)
                                      (booleanp verify-guards$)))
  :short "Check if an applicability condition is present."
  (case keyword
    (:oldp-when-old predicate$)
    (:oldp-of-rec-calls (and (irecursivep old$ wrld) t))
    (:old-guard (and verify-guards$ (not predicate$)))
    (:old-guard-pred (and verify-guards$ predicate$))
    (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable isodata-app-cond-keywordp))))

(define isodata-app-cond-present-keywords ((old$ symbolp)
                                           (predicate$ booleanp)
                                           (verify-guards$ booleanp)
                                           (wrld plist-worldp))
  :returns (present-keywords isodata-app-cond-keyword-listp)
  :short "Keywords of the applicability conditions that are present."
  (isodata-app-cond-present-keywords-aux *isodata-app-cond-keywords*
                                         old$
                                         predicate$
                                         verify-guards$
                                         wrld)

  :prepwork
  ((define isodata-app-cond-present-keywords-aux
     ((keywords isodata-app-cond-keyword-listp)
      (old$ symbolp)
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
                                       predicate$
                                       verify-guards$
                                       wrld)
           (cons (car keywords)
                 (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                        old$
                                                        predicate$
                                                        verify-guards$
                                                        wrld))
         (isodata-app-cond-present-keywords-aux (cdr keywords)
                                                old$
                                                predicate$
                                                verify-guards$
                                                wrld))))))

(define isodata-process-inputs (old
                                args-iso
                                predicate
                                new-name
                                new-enable
                                thm-name
                                thm-enable
                                non-executable
                                normalize
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
                                    iso$
                                    oldp$
                                    newp$
                                    forth$
                                    back$
                                    forth-image
                                    back-image
                                    back-of-forth
                                    forth-of-back
                                    oldp-guard
                                    new-guard
                                    forth-guard
                                    back-guard
                                    forth-injective
                                    back-injective
                                    namedp
                                    iso-hints
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
                                         symbolp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         pseudo-termfnp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         booleanp
                                         acl2::any-p
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
       ((er new-name$) (isodata-process-new-name new-name old$ ctx state))
       ((er thm-name$) (isodata-process-thm-name
                        thm-name old$ new-name$ ctx state))
       ((er verify-guards$) (ensure-boolean-or-auto-and-return-boolean$
                             verify-guards
                             (guard-verified-p old$ wrld)
                             "The :VERIFY-GUARDS input" t nil))
       (names-to-avoid (list new-name$ thm-name$))
       ((er (list args$
                  iso$
                  oldp$
                  newp$
                  forth$
                  back$
                  forth-image
                  back-image
                  back-of-forth
                  forth-of-back
                  oldp-guard
                  newp-guard
                  forth-guard
                  back-guard
                  forth-injective
                  back-injective
                  namedp
                  iso-hints
                  names-to-avoid))
        (isodata-process-args-iso
         args-iso old$ verify-guards$ names-to-avoid ctx state))
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
       ((er &) (ensure-boolean$ normalize "The :NORMALIZE input" t nil))
       (app-cond-keywords (isodata-app-cond-present-keywords
                           old$ predicate verify-guards$ wrld))
       ((er &) (ensure-is-untranslate-specifier$ untranslate
                                                 "The :UNTRANSLATE input"
                                                 t nil))
       ((er hints$) (evmac-process-input-hints
                     hints app-cond-keywords ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 args$
                 iso$
                 oldp$
                 newp$
                 forth$
                 back$
                 forth-image
                 back-image
                 back-of-forth
                 forth-of-back
                 oldp-guard
                 newp-guard
                 forth-guard
                 back-guard
                 forth-injective
                 back-injective
                 namedp
                 iso-hints
                 new-name$
                 new-enable$
                 thm-name$
                 non-executable$
                 verify-guards$
                 hints$
                 app-cond-keywords
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ isodata-event-generation
  :parents (isodata-implementation)
  :short "Event generation performed by @(tsee isodata)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some events are generated in two slightly different forms:
     a form that is local to the generated @(tsee encapsulate),
     and a form that is exported from the @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean''.")
   (xdoc::p
    "Other events are generated only locally in the @(tsee encapsulate),
     without any exported counterparts.
     These have automatically generated fresh names:
     the names used so far
     are threaded through the event generation functions below.")
   (xdoc::p
    "Other events are only exported from the @(tsee encapsulate),
     without any local counterparts."))
  :order-subtopics t
  :default-parent t)

(define isodata-gen-defiso ((iso$ symbolp)
                            (oldp$ pseudo-termfnp)
                            (newp$ pseudo-termfnp)
                            (forth$ pseudo-termfnp)
                            (back$ pseudo-termfnp)
                            (forth-image symbolp)
                            (back-image symbolp)
                            (back-of-forth symbolp)
                            (forth-of-back symbolp)
                            (oldp-guard symbolp)
                            (newp-guard symbolp)
                            (forth-guard symbolp)
                            (back-guard symbolp)
                            (forth-injective symbolp)
                            (back-injective symbolp)
                            (verify-guards$ booleanp)
                            (print$ evmac-input-print-p)
                            iso-hints)
  :returns (event pseudo-event-formp)
  :short "Generate the @(tsee defiso) when @('iso') is not a name."
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
     the we use @(':all') for @(tsee defiso)'s @(':print') input as well."))
  (b* ((name iso$)
       (doma oldp$)
       (domb newp$)
       (alpha forth$)
       (beta back$)
       (unconditional nil)
       (guard-thms verify-guards$)
       (nonguard-thm-names (list :alpha-image forth-image
                                 :beta-image back-image
                                 :beta-of-alpha back-of-forth
                                 :alpha-of-beta forth-of-back
                                 :alpha-injective forth-injective
                                 :beta-injective back-injective))
       (guard-thm-names? (and guard-thms
                              (list :doma-guard oldp-guard
                                    :domb-guard newp-guard
                                    :alpha-guard forth-guard
                                    :beta-guard back-guard)))
       (thm-names (append nonguard-thm-names guard-thm-names?))
       (print (if (eq print$ :all) :all :error)))
    `(local
      (defiso ,name ,doma ,domb ,alpha ,beta
        :unconditional ,unconditional
        :guard-thms ,guard-thms
        :thm-names ,thm-names
        :hints ,iso-hints
        :print ,print))))

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
    (let* ((pos (position (car args$) (formals old$ wrld)))
           (rec-call-arg (nth pos (fargs rec-call))))
      (cons rec-call-arg
            (isodata-get-rec-call-args-transformed rec-call
                                                   old$
                                                   (cdr args$)
                                                   wrld)))))

(define isodata-gen-oldp-of-rec-call
  ((rec-call pseudo-term-listp "A recursive call of @('old').")
   (old$ symbolp)
   (args$ symbol-listp)
   (oldp$ pseudo-termfnp)
   (wrld plist-worldp))
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
    "of the @(':oldp-of-rec-calls') applicability condition."))
  (let ((rec-call-args
         (isodata-get-rec-call-args-transformed
          rec-call old$ args$ wrld)))
    (conjoin (apply-unary-to-terms oldp$ rec-call-args))))

(define isodata-gen-oldp-of-rec-calls-under-contexts
  ((rec-calls-with-tests pseudo-tests-and-call-listp
                         "Result of @('(recursive-calls old$)')")
   (old$ symbolp)
   (args$ symbol-listp)
   (oldp$ pseudo-termfnp)
   (wrld plist-worldp))
  :returns (oldp-of-rec-call-args-under-contexts "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the conjunction of the implications,
          in the @(':oldp-of-rec-calls') applicability condition,
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
    "of the @(':oldp-of-rec-calls') applicability condition."))
  (if (endp rec-calls-with-tests)
      *t*
    (let* ((tests-and-call (car rec-calls-with-tests))
           (tests (access tests-and-call tests-and-call :tests))
           (rec-call (access tests-and-call tests-and-call :call))
           (context (conjoin tests))
           (rest (cdr rec-calls-with-tests)))
      (conjoin2 (implicate context
                           (isodata-gen-oldp-of-rec-call rec-call
                                                         old$
                                                         args$
                                                         oldp$
                                                         wrld))
                (isodata-gen-oldp-of-rec-calls-under-contexts rest
                                                              old$
                                                              args$
                                                              oldp$
                                                              wrld)))))

(define isodata-gen-app-cond-formula ((app-cond isodata-app-cond-keywordp)
                                      (old$ symbolp)
                                      (args$ symbol-listp)
                                      (oldp$ pseudo-termfnp)
                                      state)
  :returns (formula "An untranslated term.")
  :mode :program
  :short "Generate the formula of the specified applicability condition."
  (b* ((wrld (w state)))
    (case app-cond
      (:oldp-when-old
       (untranslate
        (implicate `(,old$ ,@(formals old$ wrld))
                   (conjoin (apply-unary-to-terms oldp$ args$)))
        t wrld))
      (:oldp-of-rec-calls
       (untranslate
        (b* ((rec-calls-with-tests (recursive-calls old$ wrld))
             (oldp-of-args (apply-unary-to-terms oldp$ args$)))
          (implicate (conjoin oldp-of-args)
                     (isodata-gen-oldp-of-rec-calls-under-contexts
                      rec-calls-with-tests
                      old$
                      args$
                      oldp$
                      wrld)))
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

(define isodata-gen-app-cond ((app-cond isodata-app-cond-keywordp)
                              (old$ symbolp)
                              (args$ symbol-listp)
                              (oldp$ pseudo-termfnp)
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
       (thm-name (fresh-name-in-world-with-$s (intern-in-package-of-symbol
                                               (symbol-name app-cond)
                                               (pkg-witness "APT"))
                                              names-to-avoid
                                              wrld))
       (formula (isodata-gen-app-cond-formula app-cond
                                              old$
                                              args$
                                              oldp$
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

(define isodata-gen-app-conds ((app-conds isodata-app-cond-keyword-listp)
                               (old$ symbolp)
                               (args$ symbol-listp)
                               (oldp$ pseudo-termfnp)
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
                                                  oldp$
                                                  hints$
                                                  print$
                                                  names-to-avoid
                                                  ctx
                                                  state))
       (names-to-avoid (cons thm-name names-to-avoid))
       ((mv events thm-names) (isodata-gen-app-conds (cdr app-conds)
                                                     old$
                                                     args$
                                                     oldp$
                                                     hints$
                                                     print$
                                                     names-to-avoid
                                                     ctx
                                                     state)))
    (mv (cons event events)
        (acons app-cond thm-name thm-names))))

(define isodata-gen-apply-forth-to-rec-call-args
  ((rec-call-args pseudo-termp "All the actual arguments
                                of a recursive call of @('old')
                                that @('forth') must be applied to.")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
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
    (let* ((pos (position (car args$) (formals old$ wrld)))
           (rec-call-arg (nth pos rec-call-args))
           (forth-of-rec-call-arg (apply-term* forth$ rec-call-arg))
           (new-rec-call-args
            (update-nth pos forth-of-rec-call-arg rec-call-args)))
      (isodata-gen-apply-forth-to-rec-call-args new-rec-call-args
                                                old$
                                                (cdr args$)
                                                forth$
                                                wrld))))

(defines isodata-xform-rec-calls-in-term/terms
  :flag nil
  :verify-guards nil
  :short "Transform all the calls to @('old') in term/terms."
  :long
  (xdoc::topstring-p
   "Turn each @('(old ... updatej-y1 ... updatej-yp ...)')
    inside a term or terms
    into
    @('(new ... (forth updatej-y1) ... (forth updatej-yp) ...)').
    This is an intermediate step
    in the construction of the body of the generated function
    from the body of @('old').")

  (define isodata-xform-rec-calls-in-term
    ((term pseudo-termp "Term where recursive calls are transformed.")
     (old$ symbolp)
     (args$ symbol-listp)
     (forth$ pseudo-termfnp)
     (new-name$ symbolp)
     (wrld plist-worldp))
    :returns (new-term "A @(tsee pseudo-termp).")
    :short "Transform all the calls to @('old') in @('term')."
    :long
    (xdoc::topstring-p
     "@('term') is initially the body of @('old'),
      then subterms of it in the recursive calls to this function.")
    (if (or (variablep term)
            (fquotep term))
        term
      (let ((fn (ffn-symb term)))
        (if (symbolp fn)
            (if (eq fn old$)
                (cons-term
                 new-name$
                 (isodata-gen-apply-forth-to-rec-call-args (fargs term)
                                                           old$
                                                           args$
                                                           forth$
                                                           wrld))
              (cons-term
               fn
               (isodata-xform-rec-calls-in-terms (fargs term)
                                                 old$
                                                 args$
                                                 forth$
                                                 new-name$
                                                 wrld)))
          (let ((new-fn (make-lambda
                         (lambda-formals fn)
                         (isodata-xform-rec-calls-in-term (lambda-body fn)
                                                          old$
                                                          args$
                                                          forth$
                                                          new-name$
                                                          wrld))))
            (cons-term new-fn
                       (isodata-xform-rec-calls-in-terms (fargs term)
                                                         old$
                                                         args$
                                                         forth$
                                                         new-name$
                                                         wrld)))))))

  (define isodata-xform-rec-calls-in-terms
    ((terms pseudo-term-listp "Terms where recursive calls are transformed.")
     (old$ symbolp)
     (args$ symbol-listp)
     (forth$ pseudo-termfnp)
     (new-name$ symbolp)
     (wrld plist-worldp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    :short "Transform all the calls to @('old') in @('terms')."
    :long
    (xdoc::topstring-p
     "@('terms') are subterms of the body of @('old').")
    (if (endp terms)
        nil
      (cons (isodata-xform-rec-calls-in-term (car terms)
                                             old$
                                             args$
                                             forth$
                                             new-name$
                                             wrld)
            (isodata-xform-rec-calls-in-terms (cdr terms)
                                              old$
                                              args$
                                              forth$
                                              new-name$
                                              wrld)))))

(define isodata-gen-lemma-instances-of-var
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (terms pseudo-term-listp "Terms to instantiate @('var') with."))
  :returns (lemma-instances true-list-listp)
  :short "Generate the lemma instances used in generated proof hints,
          where a variable is instantiated
          with each of the terms in a list."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints
    that use lemma instances of the form @('(:instance lemma (var term))').")
  (cond ((endp terms) nil)
        (t (cons `(:instance ,lemma :extra-bindings-ok (,var ,(car terms)))
                 (isodata-gen-lemma-instances-of-var lemma var (cdr terms))))))

(define isodata-gen-lemma-instance-back/forth-args
  ((lemma (or (symbolp lemma) (symbol-listp lemma))
          "Lemma to generate an instance of.")
   (args$ symbol-listp)
   (back$/forth$ pseudo-termfnp))
  :returns (lemma-instance true-listp)
  :verify-guards nil
  :short "Generate the lemma instance used in generated proof hints,
          where @('y1'), ..., @('yp') are instantiated to
          either @('(back y1)'), ..., @('(back yp)')
          or @('(forth y1)'), ..., @('(forth yp)')."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints
    that use lemma instances of the form
    @('(:instance lemma (y1 (back y1)) ... (yp (back yp)))') or
    @('(:instance lemma (y1 (forth y1)) ... (yp (forth yp)))'),
    where @('lemma') is a theorem name
    or the guard or termination theorem of @('old').
    Note that if it is a guard or termination theorem,
    it is a list of symbols, hence the guard.")
  (b* ((back/forth-of-args (apply-unary-to-terms back$/forth$ args$))
       (args-to-back/forth-of-args (alist-to-doublets
                                    (pairlis$ args$ back/forth-of-args))))
    `(:instance ,lemma :extra-bindings-ok ,@args-to-back/forth-of-args)))

(define isodata-gen-lemma-instances-rec-call
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-call pseudo-termp "A recursive call of @('old')
                           for whose arguments @('var') must be instantiated.")
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the lemma instances used in generated proof hints,
          where @('var') is instantiated to
          the arguments of @('rec-call')
          that correspond to @('y1'), ..., @('yp'),
          with a replacement of @('y1'), ..., @('yp')
          with @('(back y1)'), ..., @('(back yp)')."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints that use lemma instances
    of the form
    @('(:instance lemma (var updatej-yk<...,(back y1),...,(back yp),...>))'),
    where @('lemma') is a theorem name
    and where @('updatej-yk<...,y1,...,yp,...>') is the actual argument
    of the @('j')-th recursive call of @('old')
    that corresponds to the @('yk') formal of @('old')
    whose representation is being transformed.")
  (let* ((rec-call-args (isodata-get-rec-call-args-transformed
                         rec-call old$ args$ wrld))
         (rec-call-args
          (let ((back-of-args (apply-unary-to-terms back$ args$)))
            (subcor-var-lst args$ back-of-args rec-call-args))))
    (isodata-gen-lemma-instances-of-var lemma var rec-call-args)))

(define isodata-gen-lemma-instances-rec-calls
  ((lemma symbolp "Lemma to generate instances of.")
   (var symbolp "Lemma variable to instantiate.")
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Result of @('(recursive-calls old)')
                          initially,
                          then suffix of it in the recursive calls
                          of this function.")
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ symbolp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the lemma instances used in generated proof hints,
          where @('var') is instantiated to
          the arguments of the recursive calls of @('old')
          that correspond to @('y1'), ..., @('yp'),
          with a replacement of @('y1'), ..., @('yp')
          with @('(back y1)'), ..., @('(back yp)')."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints that use lemma instances
    of the form
    @('(:instance lemma (var updatej-yk<...,(back y1),...,(back yp),...>))'),
    where @('lemma') is a theorem name
    and where @('updatei-yk<...,y1,...,yp,...>') is the actual argument
    of the @('j')-th recursive call of @('old')
    that corresponds to the @('yk') formal of @('old')
    whose representation is being transformed.")
  (if (endp rec-calls-with-tests)
      nil
    (let* ((tests-and-call (car rec-calls-with-tests))
           (rec-call (access tests-and-call tests-and-call :call)))
      (append (isodata-gen-lemma-instances-rec-call
               lemma var rec-call old$ args$ back$ wrld)
              (isodata-gen-lemma-instances-rec-calls lemma
                                                     var
                                                     (cdr rec-calls-with-tests)
                                                     old$
                                                     args$
                                                     back$
                                                     wrld)))))

(define isodata-gen-lemma-instances-rec-calls-back-args
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Result of @('(recursive-calls old)')
                          initially,
                          then suffix of it in the recursive calls
                          of this function.")
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ pseudo-termfnp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the lemma instances used in generated proof hints,
          where @('y1'), ..., @('yp') are instantiated to
          @('updatej-y1<...,(back y1),...,(back yp),...>'),
          ...,
          @('updatej-yp<...,(back y1),...,(back yp),...>'),
          for each recursive call of @('old')."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints
    that use lemma instances of the form
    @('(:instance lemma (y1 updatej-y1<...,(back y1),...,(back yp),...>)
                        ...
                        (yp updatej-yp<...,(back y1),...,(back yp),...>))'),
    where @('lemma') is a theorem name
    and where @('updatej-yk<...,y1,...,yp,...>') is the actual argument
    of the @('j')-th recursive call of @('old')
    that corresponds to the @('yk') formal of @('old')
    whose representation is being transformed.")
  (if (endp rec-calls-with-tests)
      nil
    (let* ((tests-and-call (car rec-calls-with-tests))
           (rec-call (access tests-and-call tests-and-call :call))
           (rec-call-args (isodata-get-rec-call-args-transformed
                           rec-call old$ args$ wrld))
           (back-of-args (apply-unary-to-terms back$ args$))
           (rec-call-args-back
            (subcor-var-lst args$ back-of-args rec-call-args))
           (args-to-rec-calls-of-back-args
            (alist-to-doublets (pairlis$ args$ rec-call-args-back))))
      (cons
       `(:instance ,lemma :extra-bindings-ok ,@args-to-rec-calls-of-back-args)
       (isodata-gen-lemma-instances-rec-calls-back-args
        lemma (cdr rec-calls-with-tests)
        old$ args$ back$ wrld)))))

(define isodata-gen-lemma-instances-forth-rec-calls-back-args
  ((lemma symbolp "Lemma to generate instances of.")
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Result of @('(recursive-calls old)')
                          initially,
                          then suffix of it in the recursive calls
                          of this function.")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (wrld plist-worldp))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate the lemma instances used in generated proof hints,
          where @('y1'), ..., @('yp') are instantiated to
          @('(forth updatej-y1<...,(back y1),...,(back yp),...>)'),
          ...,
          @('(forth updatej-yp<...,(back y1),...,(back yp),...>)'),
          for each recursive call of @('old')."
  :long
  (xdoc::topstring-p
   "The transformation generates proof hints
    that use lemma instances of the form
    @('(:instance lemma
                  (y1 (forth updatej-y1<...,(back y1),...,(back yp),...>))
                  ...
                  (yp (forth updatej-yp<...,(back y1),...,(back yp),...>)))'),
    where @('lemma') is a theorem name
    and where @('updatej-yk<...,y1,...,yp,...>') is the actual argument
    of the @('j')-th recursive call of @('old')
    that corresponds to the @('yk') formal of @('old')
    whose representation is being transformed.")
  (if (endp rec-calls-with-tests)
      nil
    (let* ((tests-and-call (car rec-calls-with-tests))
           (rec-call (access tests-and-call tests-and-call :call))
           (rec-call-args (isodata-get-rec-call-args-transformed
                           rec-call old$ args$ wrld))
           (back-of-args (apply-unary-to-terms back$ args$))
           (rec-call-back-args
            (subcor-var-lst args$ back-of-args rec-call-args))
           (forth-rec-call-back-args
            (apply-unary-to-terms forth$ rec-call-back-args))
           (args-to-forth-rec-calls-of-back-args
            (alist-to-doublets (pairlis$ args$ forth-rec-call-back-args))))
      (cons
       `(:instance ,lemma
         :extra-bindings-ok
         ,@args-to-forth-rec-calls-of-back-args)
       (isodata-gen-lemma-instances-forth-rec-calls-back-args
        lemma (cdr rec-calls-with-tests)
        old$ args$ forth$ back$ wrld)))))

(define isodata-gen-new-fn-guard ((old$ symbolp)
                                  (args$ symbol-listp)
                                  (newp$ pseudo-termfnp)
                                  (back$ pseudo-termfnp)
                                  (predicate$ booleanp)
                                  (wrld plist-worldp))
  :returns (new-guard "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the guard of the new function."
  (b* ((newp-of-args (apply-unary-to-terms newp$ args$)))
    (if predicate$
        `(and ,@newp-of-args)
      (b* ((old-guard (guard old$ nil wrld))
           (back-of-args (apply-unary-to-terms back$ args$))
           (old-guard-with-back-of-args
            (subcor-var args$ back-of-args old-guard)))
        `(and ,@newp-of-args
              ,old-guard-with-back-of-args)))))

(define isodata-gen-new-fn-body-pred ((old$ symbolp)
                                      (args$ symbol-listp)
                                      (newp$ pseudo-termfnp)
                                      (forth$ pseudo-termfnp)
                                      (back$ pseudo-termfnp)
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
  (b* ((old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls-in-term
         old-body old$ args$ forth$ new-name$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args
        (subcor-var args$ back-of-args old-body-with-new-rec-calls))
       (newp-of-args (apply-unary-to-terms newp$ args$)))
    `(and ,@newp-of-args
          ,old-body-with-back-of-args)))

(define isodata-gen-new-fn-body-nonpred-nonrec ((old$ symbolp)
                                                (args$ symbol-listp)
                                                (back$ pseudo-termfnp)
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
  (b* ((old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args
        (subcor-var args$ back-of-args old-body)))
    old-body-with-back-of-args))

(define isodata-gen-new-fn-body-nonpred-rec ((old$ symbolp)
                                             (args$ symbol-listp)
                                             (newp$ pseudo-termfnp)
                                             (forth$ pseudo-termfnp)
                                             (back$ pseudo-termfnp)
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
  (b* ((old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (body old$ nil wrld)))
       (old-body-with-new-rec-calls
        (isodata-xform-rec-calls-in-term
         old-body old$ args$ forth$ new-name$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-body-with-back-of-args
        (subcor-var args$ back-of-args old-body-with-new-rec-calls))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (else-term (b* ((n (number-of-results old$ wrld)))
                    (if (> n 1)
                        (cons 'mv (repeat n nil))
                      nil))))
    `(if ,(conjoin newp-of-args)
         ,old-body-with-back-of-args
       ,else-term)))

(define isodata-gen-new-fn-body ((old$ symbolp)
                                 (args$ symbol-listp)
                                 (newp$ pseudo-termfnp)
                                 (forth$ pseudo-termfnp)
                                 (back$ pseudo-termfnp)
                                 (predicate$ booleanp)
                                 (new-name$ symbolp)
                                 (wrld plist-worldp))
  :returns (new-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the body of the new function."
  (if predicate$
      (isodata-gen-new-fn-body-pred
       old$ args$ newp$ forth$ back$ new-name$ wrld)
    (if (recursivep old$ nil wrld)
        (isodata-gen-new-fn-body-nonpred-rec
         old$ args$ newp$ forth$ back$ new-name$ wrld)
      (isodata-gen-new-fn-body-nonpred-nonrec old$ args$ back$ wrld))))

(define isodata-gen-new-fn-measure ((old$ symbolp)
                                    (args$ symbol-listp)
                                    (back$ pseudo-termfnp)
                                    (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the measure of the function, if recursive."
  (b* ((old-measure (measure old$ wrld))
       (back-of-args (apply-unary-to-terms back$ args$)))
    (subcor-var args$ back-of-args old-measure)))

(define isodata-gen-new-fn-termination-hints
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (back-image symbolp)
   (back-of-forth symbolp)
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
  (b* ((a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-rec-calls (cdr (assoc-eq :oldp-of-rec-calls
                                 app-cond-thm-names)))
       (instance-termination-thm-old
        (isodata-gen-lemma-instance-back/forth-args `(:termination-theorem ,old$)
                                                    args$
                                                    back$))
       (instances-back-image
        (isodata-gen-lemma-instances-of-var back-image
                                            b
                                            args$))
       (instance-oldp-of-rec-calls
        (isodata-gen-lemma-instance-back/forth-args oldp-of-rec-calls
                                                    args$
                                                    back$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-rec-calls back-of-forth
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld)))
    `(("Goal"
       :in-theory nil
       :use (,instance-termination-thm-old
             ,@instances-back-image
             ,instance-oldp-of-rec-calls
             ,@instances-back-of-forth)))))

(define isodata-gen-new-fn
  ((old$ symbolp)
   (args$ symbol-listp)
   (newp$ pseudo-termfnp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (predicate$ booleanp)
   (new-name$ symbolp)
   (new-enable$ booleanp)
   (non-executable$ booleanp)
   (normalize$ booleanp)
   (verify-guards$ booleanp)
   (untranslate$ untranslate-specifier-p)
   (app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
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
              old$ args$ newp$ forth$ back$ predicate$ new-name$ wrld))
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
       (guard (isodata-gen-new-fn-guard old$ args$ newp$ back$ predicate$ wrld))
       (guard (conjoin (flatten-ands-in-lit guard)))
       (guard (untranslate guard nil wrld))
       (recursive (recursivep old$ nil wrld))
       (wfrel? (if recursive
                   (well-founded-relation old$ wrld)
                 nil))
       (measure? (if recursive
                     (isodata-gen-new-fn-measure old$ args$ back$ wrld)
                   nil))
       (termination-hints? (if recursive
                               (isodata-gen-new-fn-termination-hints
                                app-cond-thm-names
                                old$ args$ forth$ back$
                                back-image back-of-forth
                                wrld)
                             nil))
       (local-event
        `(local
          (,macro ,new-name$ (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  ,@(and (not normalize$)
                                         (list :normalize nil))
                                  :guard ,guard
                                  :verify-guards nil))
                  ,body)))
       (exported-event
        `(,macro ,new-name$ (,@formals)
                 (declare (xargs ,@(and recursive
                                        (list :well-founded-relation wfrel?
                                              :measure measure?
                                              :ruler-extenders :all))
                                 ,@(and (not normalize$)
                                        (list :normalize nil))
                                 :guard ,guard
                                 :verify-guards ,verify-guards$))
                 ,body)))
    (mv local-event exported-event)))

(define isodata-gen-new-to-old-thm-formula ((old$ symbolp)
                                            (args$ symbol-listp)
                                            (newp$ pseudo-termfnp)
                                            (back$ pseudo-termfnp)
                                            (predicate$ booleanp)
                                            (new-name$ symbolp)
                                            (wrld plist-worldp))
  :returns (new-to-old-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that expresses the new function in terms of the old function."
  (b* ((formals (formals old$ wrld))
       (newp-of-args (apply-unary-to-terms newp$ args$))
       (back-of-args (apply-unary-to-terms back$ args$))
       (old-call (subcor-var args$ back-of-args `(,old$ ,@formals))))
    (if (or predicate$
            (recursivep old$ nil wrld))
        (implicate (conjoin newp-of-args)
                   `(equal (,new-name$ ,@formals)
                           ,old-call))
      `(equal (,new-name$ ,@formals)
              ,old-call))))

(define isodata-gen-new-to-old-thm-hints-nonrec
  ((old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function."))
  :returns (hints true-listp)
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are not recursive."
  `(("Goal"
     :in-theory '(,old-fn-unnorm-name ,new-fn-unnorm-name))))

(define isodata-gen-new-to-old-thm-hints-rec
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function.")
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function,
          when the functions are recursive."
  (b* ((a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-rec-calls (cdr (assoc-eq :oldp-of-rec-calls
                                 app-cond-thm-names)))
       (instance-oldp-of-rec-calls
        (isodata-gen-lemma-instance-back/forth-args oldp-of-rec-calls
                                                    args$
                                                    back$))
       (instances-back-image
        (isodata-gen-lemma-instances-of-var back-image
                                            b
                                            args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-rec-calls forth-image
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-rec-calls back-of-forth
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld)))
    `(("Goal"
       :in-theory '(,old-fn-unnorm-name
                    ,new-fn-unnorm-name
                    (:induction ,new-name$))
       :induct (,new-name$ ,@(formals old$ wrld)))
      '(:use (,instance-oldp-of-rec-calls
              ,@instances-back-image
              ,@instances-forth-image
              ,@instances-back-of-forth)))))

(define isodata-gen-new-to-old-thm-hints
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (new-name$ symbolp)
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function.")
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that expresses the new function in terms of the old function."
  (if (recursivep old$ nil wrld)
      (isodata-gen-new-to-old-thm-hints-rec app-cond-thm-names
                                            old$
                                            args$
                                            forth$
                                            back$
                                            forth-image
                                            back-image
                                            back-of-forth
                                            new-name$
                                            old-fn-unnorm-name
                                            new-fn-unnorm-name
                                            wrld)
    (isodata-gen-new-to-old-thm-hints-nonrec old-fn-unnorm-name
                                             new-fn-unnorm-name)))

(define isodata-new-to-old-thm
  ((old$ symbolp)
   (args$ symbol-listp)
   (newp$ pseudo-termfnp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (predicate$ booleanp)
   (new-name$ symbolp)
   (names-to-avoid symbol-listp)
   (app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function.")
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
  (b* ((name (fresh-name-in-world-with-$s 'new-to-old names-to-avoid wrld))
       (formula (isodata-gen-new-to-old-thm-formula old$
                                                    args$
                                                    newp$
                                                    back$
                                                    predicate$
                                                    new-name$
                                                    wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-new-to-old-thm-hints app-cond-thm-names
                                                old$
                                                args$
                                                forth$
                                                back$
                                                forth-image
                                                back-image
                                                back-of-forth
                                                new-name$
                                                old-fn-unnorm-name
                                                new-fn-unnorm-name
                                                wrld))
       (event `(local
                (defthmd ,name
                  ,formula
                  :hints ,hints))))
    (mv event name)))

(define isodata-gen-old-to-new-thm-formula ((old$ symbolp)
                                            (args$ symbol-listp)
                                            (oldp$ pseudo-termfnp)
                                            (forth$ pseudo-termfnp)
                                            (predicate$ booleanp)
                                            (new-name$ symbolp)
                                            (wrld plist-worldp))
  :returns (old-to-new-formula "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the formula of the theorem
          that relates the old and new function."
  (b* ((formals (formals old$ wrld))
       (oldp-of-args (apply-unary-to-terms oldp$ args$))
       (forth-of-args (apply-unary-to-terms forth$ args$))
       (new-call
        (subcor-var args$ forth-of-args `(,new-name$ ,@formals))))
    (if predicate$
        (implicate (conjoin oldp-of-args)
                   `(equal (,old$ ,@formals)
                           ,new-call))
      (implicate (conjoin oldp-of-args)
                 `(equal (,old$ ,@formals)
                         ,new-call)))))

(define isodata-gen-old-to-new-thm-hints
  ((args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (forth-image symbolp)
   (back-of-forth symbolp)
   (new-to-old symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to prove the theorem
          that relates the old and new function."
  (b* ((a (isodata-gen-var-a forth$ wrld))
       (instances-forth-image
        (isodata-gen-lemma-instances-of-var forth-image
                                            a
                                            args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-of-var back-of-forth
                                            a
                                            args$))
       (instance-new-to-old
        (isodata-gen-lemma-instance-back/forth-args new-to-old
                                                    args$
                                                    forth$)))
    `(("Goal"
       :in-theory nil
       :use (,@instances-forth-image
             ,@instances-back-of-forth
             ,instance-new-to-old)))))

(define isodata-gen-old-to-new-thm
  ((old$ symbolp)
   (args$ symbol-listp)
   (oldp$ pseudo-termfnp)
   (forth$ pseudo-termfnp)
   (forth-image symbolp)
   (back-of-forth symbolp)
   (predicate$ booleanp)
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
                 old$ args$ oldp$ forth$ predicate$ new-name$ wrld))
       (formula (untranslate formula t wrld))
       (hints (isodata-gen-old-to-new-thm-hints args$
                                                forth$
                                                forth-image
                                                back-of-forth
                                                new-to-old
                                                wrld))
       (local-event `(local
                      (,macro ,thm-name$
                              ,formula
                              :hints ,hints)))
       (exported-event `(,macro ,thm-name$
                                ,formula)))
    (mv local-event exported-event)))

(define isodata-gen-new-fn-verify-guards-hints-pred-nonrec
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (back$ pseudo-termfnp)
   (back-image symbolp)
   (newp-guard symbolp)
   (back-guard symbolp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when non-recursive and when @(':predicate') is @('t')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((b (isodata-gen-var-b back$ wrld))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-back/forth-args `(:guard-theorem ,old$)
                                                    args$
                                                    back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-of-var newp-guard
                                            b
                                            args$))
       (instances-back-guard
        (isodata-gen-lemma-instances-of-var back-guard
                                            b
                                            args$))
       (instances-back-image
        (isodata-gen-lemma-instances-of-var back-image
                                            b
                                            args$))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-back/forth-args old-guard-pred
                                                    args$
                                                    back$)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard
             ,instance-old-guard-pred
             ,@instances-back-image)))))

(define isodata-gen-new-fn-verify-guards-hints-pred-rec
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
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
  (b* ((a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-rec-calls (cdr (assoc-eq :oldp-of-rec-calls
                                 app-cond-thm-names)))
       (old-guard-pred (cdr (assoc-eq :old-guard-pred
                              app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-back/forth-args `(:guard-theorem ,old$)
                                                    args$
                                                    back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-of-var newp-guard
                                            b
                                            args$))
       (instances-forth-guard
        (isodata-gen-lemma-instances-rec-calls forth-guard
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instances-back-guard
        (isodata-gen-lemma-instances-of-var back-guard
                                            b
                                            args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-rec-calls forth-image
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-of-var back-image
                                            b
                                            args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-rec-calls back-of-forth
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instance-old-guard-pred
        (isodata-gen-lemma-instance-back/forth-args old-guard-pred
                                                    args$
                                                    back$))
       (instance-oldp-of-rec-calls
        (isodata-gen-lemma-instance-back/forth-args oldp-of-rec-calls
                                                    args$
                                                    back$))
       (instances-new-to-old
        (isodata-gen-lemma-instances-forth-rec-calls-back-args
         new-to-old
         (recursive-calls old$ wrld)
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
             ,instance-oldp-of-rec-calls
             ,@instances-new-to-old)))))

(define isodata-gen-new-fn-verify-guards-hints-pred
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
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
                                                       forth$
                                                       back$
                                                       forth-image
                                                       back-image
                                                       back-of-forth
                                                       newp-guard
                                                       forth-guard
                                                       back-guard
                                                       new-to-old
                                                       wrld)
    (isodata-gen-new-fn-verify-guards-hints-pred-nonrec app-cond-thm-names
                                                        old$
                                                        args$
                                                        back$
                                                        back-image
                                                        newp-guard
                                                        back-guard
                                                        wrld)))

(define isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec
  ((old$ symbolp)
   (args$ symbol-listp)
   (back$ pseudo-termfnp)
   (newp-guard symbolp)
   (back-guard symbolp)
   (wrld plist-worldp))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints to verify the guards of the new function,
          when non-recursive and when @(':predicate') is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes."))
  (b* ((b (isodata-gen-var-b back$ wrld))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-back/forth-args `(:guard-theorem ,old$)
                                                    args$
                                                    back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-of-var newp-guard
                                            b
                                            args$))
       (instances-back-guard
        (isodata-gen-lemma-instances-of-var back-guard
                                            b
                                            args$)))
    `(("Goal"
       :in-theory nil
       :use (,instance-guard-thm-old
             ,@instances-newp-guard
             ,@instances-back-guard)))))

(define isodata-gen-new-fn-verify-guards-hints-nonpred-rec
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when recursive and when @(':predicate') is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the design notes,
     taking into account that there may be multiple recursive calls,
     while the design notes only assume one."))
  (b* ((a (isodata-gen-var-a forth$ wrld))
       (b (isodata-gen-var-b back$ wrld))
       (oldp-of-rec-calls (cdr (assoc-eq :oldp-of-rec-calls
                                 app-cond-thm-names)))
       (instance-guard-thm-old
        (isodata-gen-lemma-instance-back/forth-args `(:guard-theorem ,old$)
                                                    args$
                                                    back$))
       (instances-newp-guard
        (isodata-gen-lemma-instances-of-var newp-guard
                                            b
                                            args$))
       (instances-forth-guard
        (isodata-gen-lemma-instances-rec-calls forth-guard
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instances-back-guard
        (isodata-gen-lemma-instances-of-var back-guard
                                            b
                                            args$))
       (instances-forth-image
        (isodata-gen-lemma-instances-rec-calls forth-image
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instances-back-image
        (isodata-gen-lemma-instances-of-var back-image
                                            b
                                            args$))
       (instances-back-of-forth
        (isodata-gen-lemma-instances-rec-calls back-of-forth
                                               a
                                               (recursive-calls old$ wrld)
                                               old$
                                               args$
                                               back$
                                               wrld))
       (instance-oldp-of-rec-calls
        (isodata-gen-lemma-instance-back/forth-args oldp-of-rec-calls
                                                    args$
                                                    back$))
       (instances-old-to-new
        (isodata-gen-lemma-instances-rec-calls-back-args
         thm-name$
         (recursive-calls old$ wrld)
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
             ,instance-oldp-of-rec-calls
             ,@instances-old-to-new)))))

(define isodata-gen-new-fn-verify-guards-hints-nonpred
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function,
          when @(':predicate') is @('nil')."
  (if (recursivep old$ nil wrld)
      (isodata-gen-new-fn-verify-guards-hints-nonpred-rec app-cond-thm-names
                                                          old$
                                                          args$
                                                          forth$
                                                          back$
                                                          forth-image
                                                          back-image
                                                          back-of-forth
                                                          newp-guard
                                                          forth-guard
                                                          back-guard
                                                          thm-name$
                                                          wrld)
    (isodata-gen-new-fn-verify-guards-hints-nonpred-nonrec old$
                                                           args$
                                                           back$
                                                           newp-guard
                                                           back-guard
                                                           wrld)))

(define isodata-gen-new-fn-verify-guards-hints
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
   (predicate$ booleanp)
   (new-to-old symbolp)
   (thm-name$ symbolp)
   (wrld plist-worldp))
  :returns (hints "A @(tsee true-listp).")
  :mode :program
  :short "Generate the hints to verify the guards of the new function."
  (if predicate$
      (isodata-gen-new-fn-verify-guards-hints-pred app-cond-thm-names
                                                   old$
                                                   args$
                                                   forth$
                                                   back$
                                                   forth-image
                                                   back-image
                                                   back-of-forth
                                                   newp-guard
                                                   forth-guard
                                                   back-guard
                                                   new-to-old
                                                   wrld)
    (isodata-gen-new-fn-verify-guards-hints-nonpred app-cond-thm-names
                                                    old$
                                                    args$
                                                    forth$
                                                    back$
                                                    forth-image
                                                    back-image
                                                    back-of-forth
                                                    newp-guard
                                                    forth-guard
                                                    back-guard
                                                    thm-name$
                                                    wrld)))

(define isodata-gen-new-fn-verify-guards
  ((app-cond-thm-names symbol-symbol-alistp
                       "Result of @(tsee isodata-gen-app-conds).")
   (old$ symbolp)
   (args$ symbol-listp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
   (predicate$ booleanp)
   (new-name$ symbolp)
   (new-to-old symbolp)
   (thm-name$ symbolp)
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
                                                      forth$
                                                      back$
                                                      forth-image
                                                      back-image
                                                      back-of-forth
                                                      newp-guard
                                                      forth-guard
                                                      back-guard
                                                      predicate$
                                                      new-to-old
                                                      thm-name$
                                                      wrld))
       (event `(local (verify-guards ,new-name$ :hints ,hints))))
    event))

(define isodata-gen-everything
  ((old$ symbolp)
   (args$ symbol-listp)
   (iso$ symbolp)
   (oldp$ pseudo-termfnp)
   (newp$ pseudo-termfnp)
   (forth$ pseudo-termfnp)
   (back$ pseudo-termfnp)
   (forth-image symbolp)
   (back-image symbolp)
   (back-of-forth symbolp)
   (forth-of-back symbolp)
   (oldp-guard symbolp)
   (newp-guard symbolp)
   (forth-guard symbolp)
   (back-guard symbolp)
   (forth-injective symbolp)
   (back-injective symbolp)
   (namedp booleanp)
   iso-hints
   (predicate$ booleanp)
   (new-name$ symbolp)
   (new-enable$ booleanp)
   (thm-name$ symbolp)
   (thm-enable$ booleanp)
   (non-executable$ booleanp)
   (normalize$ booleanp)
   (verify-guards$ booleanp)
   (untranslate$ untranslate-specifier-p)
   (hints$ symbol-truelist-alistp)
   (print$ evmac-input-print-p)
   (show-only$ booleanp)
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
       (defiso-event? (and (not namedp)
                           (list (isodata-gen-defiso iso$
                                                     oldp$
                                                     newp$
                                                     forth$
                                                     back$
                                                     forth-image
                                                     back-image
                                                     back-of-forth
                                                     forth-of-back
                                                     oldp-guard
                                                     newp-guard
                                                     forth-guard
                                                     back-guard
                                                     forth-injective
                                                     back-injective
                                                     verify-guards$
                                                     print$
                                                     iso-hints))))
       ((mv app-cond-thm-events
            app-cond-thm-names)
        (isodata-gen-app-conds app-conds
                               old$
                               args$
                               oldp$
                               hints$
                               print$
                               names-to-avoid
                               ctx
                               state))
       (names-to-avoid (append names-to-avoid
                               (strip-cdrs app-cond-thm-names)))
       ((mv old-fn-unnorm-event
            old-fn-unnorm-name)
        (install-not-norm-event old$ t names-to-avoid wrld))
       (names-to-avoid (cons old-fn-unnorm-name names-to-avoid))
       ((mv new-fn-local-event
            new-fn-exported-event)
        (isodata-gen-new-fn old$
                            args$
                            newp$
                            forth$
                            back$
                            back-image
                            back-of-forth
                            predicate$
                            new-name$
                            new-enable$
                            non-executable$
                            normalize$
                            verify-guards$
                            untranslate$
                            app-cond-thm-names
                            wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name)
        (install-not-norm-event new-name$ t names-to-avoid wrld))
       ((mv new-to-old-thm-event
            new-to-old)
        (isodata-new-to-old-thm old$
                                args$
                                newp$
                                forth$
                                back$
                                forth-image
                                back-image
                                back-of-forth
                                predicate$
                                new-name$
                                names-to-avoid
                                app-cond-thm-names
                                old-fn-unnorm-name
                                new-fn-unnorm-name
                                wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event)
        (isodata-gen-old-to-new-thm old$
                                    args$
                                    oldp$
                                    forth$
                                    forth-image
                                    back-of-forth
                                    predicate$
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
                                           forth$
                                           back$
                                           forth-image
                                           back-image
                                           back-of-forth
                                           newp-guard
                                           forth-guard
                                           back-guard
                                           predicate$
                                           new-name$
                                           new-to-old
                                           thm-name$
                                           wrld))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@defiso-event?
                             ,@app-cond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,old-fn-unnorm-event
                             ,new-fn-local-event
                             ,new-fn-unnorm-event
                             ,new-to-old-thm-event
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
                    args-iso
                    predicate
                    new-name
                    new-enable
                    thm-name
                    thm-enable
                    non-executable
                    normalize
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
                  iso$
                  oldp$
                  newp$
                  forth$
                  back$
                  forth-image
                  back-image
                  back-of-forth
                  forth-of-back
                  oldp-guard
                  newp-guard
                  forth-guard
                  back-guard
                  forth-injective
                  back-injective
                  namedp
                  iso-hints
                  new-name$
                  new-enable$
                  thm-name$
                  non-executable$
                  verify-guards$
                  hints$
                  app-cond-keywords
                  names-to-avoid))
        (isodata-process-inputs old
                                args-iso
                                predicate
                                new-name
                                new-enable
                                thm-name
                                thm-enable
                                non-executable
                                normalize
                                verify-guards
                                untranslate
                                hints
                                print
                                show-only
                                ctx
                                state))
       (event (isodata-gen-everything old$
                                      args$
                                      iso$
                                      oldp$
                                      newp$
                                      forth$
                                      back$
                                      forth-image
                                      back-image
                                      back-of-forth
                                      forth-of-back
                                      oldp-guard
                                      newp-guard
                                      forth-guard
                                      back-guard
                                      forth-injective
                                      back-injective
                                      namedp
                                      iso-hints
                                      predicate
                                      new-name$
                                      new-enable$
                                      thm-name$
                                      thm-enable
                                      non-executable$
                                      normalize
                                      verify-guards$
                                      untranslate
                                      hints$
                                      print
                                      show-only
                                      names-to-avoid
                                      app-cond-keywords
                                      call
                                      ctx
                                      state)))
    (value event)))

(defsection isodata-macro-definition
  :parents (isodata-implementation)
  :short "Implementation of the isomorphic data transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee isodata-fn).")
   (xdoc::@def "isodata"))
  (defmacro isodata (&whole
                     call
                     ;; mandatory inputs:
                     old
                     args-iso
                     ;; optional inputs:
                     &key
                     (predicate 'nil)
                     (new-name ':auto)
                     (new-enable ':auto)
                     (thm-name ':auto)
                     (thm-enable 't)
                     (non-executable ':auto)
                     (normalize 't)
                     (verify-guards ':auto)
                     (untranslate ':nice)
                     (hints 'nil)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (isodata-fn ',old
                                   ',args-iso
                                   ',predicate
                                   ',new-name
                                   ',new-enable
                                   ',thm-name
                                   ',thm-enable
                                   ',non-executable
                                   ',normalize
                                   ',verify-guards
                                   ',untranslate
                                   ',hints
                                   ',print
                                   ',show-only
                                   ',call
                                   (cons 'isodata ',old)
                                   state)
                       :suppress-errors ,(not print))))
