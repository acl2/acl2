; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "evmac-input-hints-p")
(include-book "evmac-input-print-p")

(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macro-applicability-conditions
  :parents (event-macros)
  :short "Applicability conditions of event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "In general, the inputs of an event macro
     must satisfy certain (event-macro-specific) conditions
     in order for the call of the event macro to succeed.
     Some of these conditions are computable,
     so the implementation of the event macro can reliably check them.
     But other conditions amount to theorems to be proved,
     so the implementation of the event macro
     must generally resort to the ACL2 theorem proving engine
     to check whether these conditions hold or not.
     We call the latter `applicability conditions':
     they are (proof) conditions that must be satisfied
     in order for the event macro to be applied successfully to its inputs.
     Even though the non-proof conditions are also necessary
     for the event macro to be applied successfully to its inputs,
     we reserve that terminology for the proof conditions,
     since they are the ones that require more special handling.")
   (xdoc::p
    "Often an event macro generates theorems
     that can be systematically proved
     from the event macro's applicability conditions.
     Prime examples are APT transformations like @(tsee apt::tailrec),
     which generates correctness and guard proofs
     from its applicability conditions.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-applicability-condition-utilities
  :parents (event-macro-applicability-conditions)
  :short (xdoc::topstring
          "Utilities for "
          (xdoc::seetopic "event-macro-applicability-conditions"
                          "applicability conditions")
          ".")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate evmac-appcond
  :short "Recognize applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We represent an applicability condition as an aggregate.")
   (xdoc::p
    "The first field is a keyword that names the applicabiilty condition.
     This keyword should be the one shown
     in the user documentation of the event macro,
     and in progress or error messages on the screen when the event macro runs.
     The keyword may be one of a fixed finite set of possibilities,
     or could be calculated dynamically (e.g. to include a numeric index),
     based on the specifics of the event macro.")
   (xdoc::p
    "The second field is the formula (a term) that must be proved
     for the applicability condition to be satisfied.")
   (xdoc::p
    "More fields might be added in the future."))
  ((name keywordp)
   (formula pseudo-termp))
  :pred evmac-appcondp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist evmac-appcond-listp (x)
  (evmac-appcondp x)
  :short "Recognize true lists of applicabilty conditions."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection make-evmac-appcond?
  :short "Conditionally construct an applicability condition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Event macros sometimes have applicability conditions
     that are present (i.e. that must be proved)
     only under certain conditions on the inputs.
     An example is the applicability conditions related to guards
     in " (xdoc::seetopic "apt::apt" "APT") " transformations,
     which are present only if guards must be verified.")
   (xdoc::p
    "This function provides a convenient way for event macros
     to generate either @('nil')
     or a singleton list of an applicability condition
     with given @(':name') and @(':formula'),
     based on whether the @(':when') input is @('nil') or not.
     We treat the latter input as a boolean, but do not require it to be,
     for greater flexibility (e.g. so that @(tsee member) can be used);
     its default is @('t'), i.e. generate the applicability condition
     unless an explicit condition (which may hold or not) is given.")
   (xdoc::p
    "An event macro may generate all its applicability conditions
     by @(tsee append)ing calls of this function.")
   (xdoc::p
    "Note that this macro expands into a non-strict @(tsee and) form,
     so that the name and formula arguments are not evaluated
     if the condition evaluates to @('nil').
     This is important if the evaluation of the name and formula
     (most likely the formula, as the name is often just a keyword constant)
     only makes sense (in particular, does not cause an error)
     under the condition.")
   (xdoc::@def "make-evmac-appcond?"))

  (defmacro make-evmac-appcond? (name formula &key (when 't))
    `(and ,when
          (list (make-evmac-appcond :name ,name :formula ,formula)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-appcond-theorem ((appcond evmac-appcondp)
                               (hints evmac-input-hints-p)
                               (names-to-avoid symbol-listp)
                               (print evmac-input-print-p)
                               ctx
                               state)
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (thm-name "A @(tsee symbolp).")
               (new-hints "An @(tsee evmac-input-hints-p).")
               (new-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a theorem event for an applicability condition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a name for the theorem that is not in the world
     and that is distinct from the given list of names to avoid;
     the latter are names not yet in the world,
     but are names of other events
     that will be added to the world together with this theorem,
     and that therefore must be all distinct.
     We return an updated list of names to avoid that includes the new name,
     so that future calls of this function, or of other event-generating code,
     can use the updated list to avoid conflicts with this new name.
     The new theorem name is also returned as a result as a convenience
     (it could be extracted from the returned event instead);
     the event macro may reference this name in generated proofs
     (see @(tsee evmac-appcond-theorem-list) for more discussion on this).
     The theorem name is the same as
     the keyword that names the applicability condition,
     if fresh, otherwise @('$') characters are appended to it until it is fresh.
     The theorem name is in the @('\"ACL2\"') package,
     which seems like a good general choice;
     the event macro, or the application where the event macro is used,
     may be in an arbitrary package.")
   (xdoc::p
    "We untranslate the formula so that it is more readable
     if printed on the screen.
     The use of @(tsee untranslate) forces this function and its callers
     into program mode.
     An alternative could be to use a more limited, logic-mode untranslation.")
   (xdoc::p
    "If the event macro's hints are an alist from keywords to true lists,
     we extract the ones associated to the applicability conditions
     (if any, otherwise we get @('nil')) and use those to prove the theorem;
     we also remove the pair from the alist, and return the updated alist.
     By threading the hints alist through calls of this functions,
     one for each applicability condition,
     at the end the event macro can detect if there were unused hints
     (e.g. for applicability conditions that were not actually present),
     and issue a warning or error in that case
     (see @(tsee evmac-ensure-no-extra-hints)).
     If the event macro's hints are not an alist from keywords to true lists,
     we use those in their entirety to prove the theorem,
     and we return them unchanged.")
   (xdoc::p
    "The theorem has no rule classes,
     because it is meant to be referenced in @(':use') hints
     in proofs generated by the event macro.
     Not having rule classes avoids any restrictions on the formula,
     such as having a conclusion @('(equal var ...)') for a rewrite rule.")
   (xdoc::p
    "The theorem is wrapped into @(tsee try-event)
     in order to provide a terser error message if the proof fails.
     This choice may be revisited at some point.")
   (xdoc::p
    "This function also takes a print specifier as input,
     meant to be one of the inputs of the event macro.
     This is used to determine whether
     events that show progress messages should be generated or not.
     Since this is a binary choice,
     the input of this function could be a boolean flag
     instead of a print specifier.
     However, having a print specifier makes things more modular
     (e.g. if print specifiers are extended with more options in the future).
     If an event macro does not have a print specifier input (perhaps yet),
     the caller of this function can still set one adequate to
     whether progress messages must be shown or not.")
   (xdoc::p
    "The returned event, which consists of the theorem
     and the optional show-progress events,
     is local (to the @(tsee encapsulate) that the event macro expands to).
     This is why the exact name of the theorem is not too important,
     so long as it is valid and does not clash with others.
     If an event macro should generate
     (some of) its applicability conditions as persistent events,
     the best course of action is to still use this function
     to generate local theorems with no rule classes,
     and then do another pass over such applicability conditions
     to generate non-local theorems
     with the same formulas,
     without hints (thus keeping the history ``clean'')
     and with the desired names and rule classes.
     These non-local theorems can be easily proved via @(':by') hints:
     to avoid their appearance in the history,
     the theorems with the desired names can be introduced twice,
     once locally with the @(':by') hints,
     and once non-locally and redundantly without hints.
     Perhaps there should be a utility to do this,
     if the task becomes common among event macros.")
   (xdoc::p
    "So this function generates a little more than just a theorem event,
     because of the surrounding things generated.
     However, those surrounding things are auxiliary:
     it is still, mainly, a theorem event."))
  (b* ((wrld (w state))
       ((evmac-appcond appcond) appcond)
       (thm-name (fresh-logical-name-with-$s-suffix (intern-in-package-of-symbol
                                                     (symbol-name appcond.name)
                                                     (pkg-witness "ACL2"))
                                                    nil
                                                    names-to-avoid
                                                    wrld))
       (new-names-to-avoid (cons thm-name names-to-avoid))
       (thm-formula (untranslate appcond.formula t wrld))
       ((mv thm-hints new-hints) (if (keyword-truelist-alistp hints)
                                     (mv (cdr (assoc-eq appcond.name hints))
                                         (remove-assoc-eq appcond.name hints))
                                   (mv hints hints)))
       (thm-event `(defthm ,thm-name
                     ,thm-formula
                     :rule-classes nil
                     ,@(and thm-hints (list :hints thm-hints))))
       (error-msg (msg
                   "The proof of the ~x0 applicability condition fails:~%~x1~|"
                   appcond.name thm-formula))
       (try-thm-event (try-event thm-event ctx t nil error-msg))
       (show-progress-p (member-eq print '(:info :all)))
       (progress-start? (and show-progress-p
                             `((cw-event
                                "~%Attempting to prove the ~x0 ~
                                 applicability condition:~%~x1~|"
                                ',appcond.name ',thm-formula))))
       (progress-end? (and show-progress-p
                           `((cw-event "Done.~%"))))
       (event `(local (progn ,@progress-start?
                             ,try-thm-event
                             ,@progress-end?))))
    (mv event thm-name new-hints new-names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-appcond-theorem-list ((appconds evmac-appcond-listp)
                                    (hints evmac-input-hints-p)
                                    (names-to-avoid symbol-listp)
                                    (print evmac-input-print-p)
                                    ctx
                                    state)
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (thm-names "A @(tsee keyword-symbol-alistp).")
               (new-hints "An @(tsee evmac-input-hints-p).")
               (new-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Lift @(tsee evmac-appcond-theorem)
          to lists of applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee evmac-appcond-theorem)
     on each applicability condition in turn,
     returning the corresponding list of theorem events.
     We thread the hints and the list of names to avoid through.
     If the resulting hints are a non-empty alist
     from keywords to true lists,
     it means that there were keywords in the hints' keys
     not matching any of the applicability conditions.
     Perhaps those keywords refer to applicability conditions
     that may be present but were not actually present this time.
     Callers of this function can decide how to handle this situation,
     e.g. by issuing a warning or error
     (see @(tsee evmac-ensure-no-extra-hints)).")
   (xdoc::p
    "Since there may be multiple applicability conditions,
     the generated names of the theorems are returned in alist form.
     The theorem names are the values,
     while the keys are the keywords that name the applicability conditions.
     This makes it more convenient to look up the theorem names,
     particularly in order to generate proof hints
     that reference applicability conditions:
     those hints must reference not applicability condition keywords,
     but the corresponding theorems.
     Given the possible addition of @('$') characters
     to ensure the freshness of the theorem names,
     the names of the theorems cannot be guaranteed or easily predicted,
     and so it is best to have them be returned, in alist form,
     by this function."))
  (b* (((when (endp appconds)) (mv nil nil hints names-to-avoid))
       (appcond (car appconds))
       ((mv event thm-name hints names-to-avoid)
        (evmac-appcond-theorem appcond hints names-to-avoid print ctx state))
       ((mv events thm-names hints names-to-avoid)
        (evmac-appcond-theorem-list
         (cdr appconds) hints names-to-avoid print ctx state)))
    (mv (cons event events)
        (acons (evmac-appcond->name appcond) thm-name thm-names)
        hints
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-ensure-no-extra-hints ((remaining-hints evmac-input-hints-p)
                                     ctx
                                     state)
  :returns (mv erp (nothing null) state)
  :short "Ensure that there are no extra hints for applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is meant to be called on
     the hints result of @(tsee evmac-appcond-theorem-list).
     That function removes the specific hints for applicability conditions
     as it turns the applicability conditions into theorem form.
     Thus, if there are remaining hints at the end,
     it means that the user has specified hints
     for applicability conditions that did not have to hold
     in that particular call of the event macro.
     If that is the case, the event macro may cause an error,
     and can use this function to do so consistently.")
   (xdoc::p
    "Note that here we cause an error only if
     the hints are a non-empty alist from keywords to true lists.
     It would be wrong to just check for @(tsee consp),
     because if the hints originally entered by the user
     are not a keyword-value list,
     then @(tsee evmac-appcond-theorem-list)
     uses the same hints on all the applicability conditions,
     and never changes them."))
  (if (and (keyword-truelist-alistp remaining-hints)
           (consp remaining-hints))
      (er-soft+ ctx t nil
                "The :HINTS input includes the keywords ~x0, ~
                 which do not correspond to applicability conditions ~
                 that must hold in this call. ~
                 Double-check the names (keywords) ~
                 of the applicability conditions, ~
                 as well as the conditions under which ~
                 each applicability condition must hold."
                (strip-cars remaining-hints))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-appcond-theorems-no-extra-hints ((appconds evmac-appcond-listp)
                                               (hints evmac-input-hints-p)
                                               (names-to-avoid symbol-listp)
                                               (print evmac-input-print-p)
                                               ctx
                                               state)
  :returns (mv erp
               (result "A tuple
                        @('(events thm-names new-named-to-avoid)')
                        satisfying
                        @('(typed-tupledp pseudo-event-form-listp
                                          keyword-symbol-alistp
                                          symbol-listp
                                          result)').")
               state)
  :mode :program
  :short "Combine @(tsee evmac-appcond-theorem-list)
          and @(tsee evmac-ensure-no-extra-hints)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function automates the coding pattern in which
     first one calls @(tsee evmac-appcond-theorem-list)
     and then @(tsee evmac-ensure-no-extra-hints) on the remaining hints.
     This combining function returns no hints result."))
  (b* (((mv events thm-names remaining-hints new-names-to-avoid)
        (evmac-appcond-theorem-list
         appconds hints names-to-avoid print ctx state))
       ((er &) (evmac-ensure-no-extra-hints remaining-hints ctx state)))
    (value (list events thm-names new-names-to-avoid))))
