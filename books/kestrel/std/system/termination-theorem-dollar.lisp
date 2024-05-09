; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define termination-theorem$ ((fn symbolp) state)
  :guard (and (function-symbolp fn (w state))
              (logicp fn (w state)))
  :returns (term? (or (and (consp term?)
                           (equal (car term?) :failed)
                           (msgp (cdr term?)))
                      (symbolp term?)
                      (and (consp term?)
                           (not (equal (car term?) :failed))
                           (pseudo-termp term?))))
  :parents (std/system/function-queries)
  :short "A logic-mode guard-verified version of
          the built-in @('termination-theorem')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee magic-ev-fncall) to call @('termination-theorem'),
     and check that the result is either a term
     or a pair @('(:failed . msg)') where @('msg') is an error message.
     We check the returned value, so that we can have a return type theorem.
     Hard errors happening in @('termination-theorem') are not suppressed,
     i.e. cause @('termination-theorem$') to stop with those hard errors.
     If @(tsee magic-ev-fncall) fails,
     or if the result is not a symbol,
     we also stop with hard errors.")
   (xdoc::p
    "Compared to @('termination-theorem'),
     this utility requires a @(see state) argument.
     It may also be slightly less efficient
     due the @(tsee magic-ev-fncall) overhead.
     However, it can be used in logic-mode guard-verified code
     that follows a statically typed discipline."))
  (b* (((mv erp term?) (magic-ev-fncall 'termination-theorem
                                        (list fn (w state))
                                        state
                                        nil
                                        t))
       ((when erp)
        (raise "Internal error: ~@0" term?)
        (cons :failed ""))
       ((unless (and (consp term?)
                     (or (and (equal (car term?) :failed)
                              (msgp (cdr term?)))
                         (and (not (equal (car term?) :failed))
                              (pseudo-termp term?)))))
        (raise "Internal error: ~x0 is malformed." term?)
        (cons :failed "")))
    term?)
  ///

  (more-returns
   (term? consp :rule-classes :type-prescription))

  (defret msgp-of-termination-theorem-when-failed
    (implies (equal (car term?) :failed)
             (msgp (cdr term?)))
    :hints (("Goal"
             :in-theory (disable termination-theorem$)
             :use return-type-of-termination-theorem$)))

  (defret msgp-of-termination-theorem-when-not-failed
    (implies (not (equal (car term?) :failed))
             (pseudo-termp term?))
    :hints (("Goal"
             :in-theory (disable termination-theorem$)
             :use return-type-of-termination-theorem$))))
