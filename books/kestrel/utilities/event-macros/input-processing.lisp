; Event Macros -- Input Processing
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-input-processors
  :parents (event-macros)
  :short "Utilities to process inputs
          that are common to multiple event macros."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-hints (hints (app-conds keyword-listp) ctx state)
  :returns (mv erp (hints$ symbol-alistp) state)
  :short "Process the @(':hints') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for event macros that have a @(':hints') input
     for user-supplied hints to prove applicability conditions.")
   (xdoc::p
    "The @(':hints') input must be a
     <see topic='@(url acl2::keyword-value-listp)'>keyword-value list</see>
     @('(appcond1 hints1 ... appcondp hintsp)'),
     where each @('appcondk') is a keyword
     that identifies one an applicability conditions
     and each @('hintsk') consists of hints that may appear
     just after @(':hints') in a @(tsee defthm).
     The allowed @('appcondk') keywords are passed
     as the @('app-conds') argument of this function;
     in general they may be a subset of
     all the possible applicability conditions of an event macro,
     based on certain conditions determined by other inputs of the macro.
     The @('appcond1'), ..., @('appcondp') keywords must be all distinct.
     Here we do not check @('hints1'), ..., @('hintsp'):
     they are implicitly checked
     when attempting to prove the applicability conditions.")
   (xdoc::p
    "If all the validation checks pass,
     we return the information in the @(':hints') input in alist form:
     the keys are the @('appcondk') keywords,
     and the values are the @('hintsk') hints."))
  (b* (((er &) (ensure-keyword-value-list$ hints "The :HINTS input" t nil))
       (alist (keyword-value-list-to-alist hints))
       (keys (strip-cars alist))
       (description
        (msg "The list of keywords ~x0 ~
              that identify applicability conditions ~
              in the :HINTS input" keys))
       ((er &) (ensure-list-no-duplicates$ keys description t nil))
       ((er &) (ensure-list-subset$ keys app-conds description t nil)))
    (value alist))
  ;; for guard verification and return type proofs:
  :prepwork ((local (in-theory (enable ensure-keyword-value-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum evmac-input-print-p (nil :error :result :info :all)
  :short "Recognize a valid @(':print') input of an event macro."
  :long
  "<p>
   These are ordered printing levels
   </p>
   @({
   nil < :error < :result < :info < :all
   })
   <p>
   where the amount of printed material increases monotonically.
   </p>
   <p>
   When @(':print') is @('nil'),
   nothing is printed (not even errors).
   </p>
   <p>
   When @(':print') is @(':error'),
   only errors (if any) are printed.
   </p>
   <p>
   When @(':print') is @(':result'),
   besides errors (if any),
   also the generated events described in
   the event macro's reference documentation
   are printed,
   i.e. the resulting events.
   </p>
   <p>
   When @(':print') is @(':info'),
   besides errors (if any)
   and the resulting events,
   also some additional information, specific to the event macro,
   is printed.
   </p>
   <p>
   When @(':print') is @(':all'),
   besides errors (if any),
   the resulting events,
   and the additional information,
   also all the ACL2 output in response to the submitted events
   (the resulting ones and some ancillary ones).
   </p>")

(define evmac-process-input-print (print ctx state)
  :returns (mv erp (print$ evmac-input-print-p) state)
  :short "Process the @(':print') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for event macros that have a @(':print') input
     to specify what is printed on the screen when the even macro is run.")
   (xdoc::p
    "If the @(':print') input, is valid,
     it is returned unchanged.
     This facilitates guard/type proofs involving this function,
     by obviating the need to enable this function in such proofs
     to establish that, if the @(':print') input passes validation,
     then it satisfies @(tsee evmac-input-print-p)."))
  (if (evmac-input-print-p print)
      (value print)
    (er-soft+ ctx t nil
              "The :PRINT input must be ~
               NIL, :ERROR, :RESULT, :INFO, or :ALL; ~
               but it is ~x0 instead."
              print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-show-only (show-only ctx state)
  :returns (mv erp (show-only$ booleanp) state)
  :short "Process the @(':show-only') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for event macros that have a @(':show-only') input
     to specify whether the event expansion should be
     submitted to ACL2 or just shown on the screen.")
   (xdoc::p
    "If the @(':show-only') input, is valid,
     it is returned unchanged.
     This facilitates guard/type proofs involving this function,
     by obviating the need to enable this function in such proofs
     to establish that, if the @(':show-only') input passes validation,
     then it satisfies @(tsee booleanp)."))
  (if (booleanp show-only)
      (value show-only)
    (er-soft+ ctx t nil
              "The :SHOW-ONLY input must be T or NIL; ~
               but it is ~x0 instead."
              show-only)))
