; Standard System Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-theorem-no-simplify")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-no-simplify$ ((fn symbolp)
                                    guard-debug
                                    safe-mode
                                    gc-off
                                    state)
  :returns (term pseudo-termp)
  :parents (std/system/function-queries)
  :short "A logic-mode guard-verified version of
          @(tsee guard-theorem-no-simplify)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has a stronger guard than @(tsee guard-theorem-no-simplify)
     and always returns a pseudo-term (if it does not cause an error).
     We use @(tsee magic-ev-fncall) to call @(tsee guard-theorem-no-simplify),
     and check that the result is a pseudo-term.
     Hard errors happening in @(tsee guard-theorem) are not suppressed,
     i.e. cause @('guard-theorem$') to stop with those hard errors.
     If @(tsee magic-ev-fncall) fails,
     or if the result is not a pseudo-term,
     we also stop with hard errors.")
   (xdoc::p
    "Compared to @(tsee guard-theorem-no-simplify),
     this utility requires a @(see state) argument.
     It may also be slightly less efficient
     due the @(tsee magic-ev-fncall) overhead.
     However, it can be used in logic-mode guard-verified code
     that follows a statically typed discipline."))
  (b* (((mv erp term) (magic-ev-fncall 'guard-theorem-no-simplify
                                       (list fn
                                             guard-debug
                                             (w state)
                                             safe-mode
                                             gc-off)
                                       state
                                       nil
                                       t))
       ((when erp) (raise "Internal error: ~@0" term))
       ((unless (pseudo-termp term))
        (raise "Internal error: ~x0 is not a pseudo-term." term)))
    term))
