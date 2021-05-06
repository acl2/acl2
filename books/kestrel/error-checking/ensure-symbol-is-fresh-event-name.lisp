; Error Checking Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/fresh-namep" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ensure-symbol-is-fresh-event-name
  ((sym symbolp "Symbol to check.")
   (description msgp "Description of @('sym'), for the error messages.")
   (type (member-eq type
                    '(function macro const stobj constrained-function nil)))
   (other-event-names-to-avoid symbol-listp)
   (error-erp (not (null error-erp)) "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@('nil') or @('error-erp').")
               (updated-event-names-to-avoid "A @(tsee symbol-listp).")
               state)
  :mode :program
  :parents (error-checking)
  :short "Cause an error if a symbol
          cannot be used as the name of a new event of a certain type,
          also given that certain symbols will be used as event names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The typical use of this error checker is in code that generates events.
     The name of each event must be fresh,
     i.e. not already in use in the ACL2 world:
     we check this via @(tsee fresh-namep-msg-weak);
     the type of event here is the same as in that utility.
     Furthermore, when multiple events are generated,
     we must ensure that the names (which are not yet in the world)
     are all distinct from each other:
     the symbol list parameter of this error checker
     contains names of other events that are being generated;
     we check that the symbol is distinct form of them."))
  (b* ((msg/nil (fresh-namep-msg-weak sym type (w state)))
       ((when msg/nil)
        (er-soft+ ctx error-erp error-val
                  "~@0 is already in use.  ~@1" description msg/nil))
       ((when (member-eq sym other-event-names-to-avoid))
        (er-soft+ ctx error-erp error-val
                  "~@0 must be distinct from the names ~&1 ~
                   of events that are also being generated, ~
                   but it is not."
                  description other-event-names-to-avoid)))
    (value (cons sym other-event-names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ ensure-symbol-is-fresh-event-name$ (sym
                                               description
                                               type
                                               other-event-names-to-avoid
                                               error-erp
                                               error-val)
  :parents (ensure-symbol-is-fresh-event-name)
  :short "Call @(tsee ensure-symbol-is-fresh-event-name)
          with @('ctx') and @('state') as the last two arguments."
  `(ensure-symbol-is-fresh-event-name ,sym
                                      ,description
                                      ,type
                                      ,other-event-names-to-avoid
                                      ,error-erp
                                      ,error-val
                                      ctx
                                      state))
