; Error Checking Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/check-user-term" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ensure-value-is-untranslated-term
  ((x "Value to check.")
   (description msgp "Description of @('x'), for the error messages.")
   (error-erp (not (null error-erp)) "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@('nil') or @('error-erp').")
               (val "A tuple @('(term stobjs-out)') consisting of
                     a @(tsee pseudo-termp) and
                     a @(tsee symbol-listp)
                     if @('erp') is @('nil');
                     otherwise @('error-val').")
               state)
  :mode :program
  :parents (error-checking)
  :short "Cause an error if a value is not a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful,
     return the " (xdoc::seetopic "term" "translation") " of @('x')
     and the @(tsee stobjs-out) list returned by @(tsee check-user-term).")
   (xdoc::p
    "If @(tsee check-user-term) fails,
     the error message it returns is incorporated into a larger error message.
     Since the message returned by @(tsee check-user-term) starts with the term,
     it can be incorporated into the larger message
     without capitalization concerns."))
  (b* (((mv term/msg stobjs-out) (check-user-term x (w state))))
    (if (msgp term/msg)
        (er-soft+ ctx error-erp error-val
                  "~@0 must be an untranslated term.  ~@1"
                  description term/msg)
      (value (list term/msg stobjs-out)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ ensure-value-is-untranslated-term$ (x
                                               description
                                               error-erp
                                               error-val)
  :parents (ensure-value-is-untranslated-term)
  :short "Call @(tsee ensure-value-is-untranslated-term)
          with @('ctx') and @('state') as the last two arguments."
  `(ensure-value-is-untranslated-term ,x
                                      ,description
                                      ,error-erp
                                      ,error-val
                                      ctx
                                      state))
