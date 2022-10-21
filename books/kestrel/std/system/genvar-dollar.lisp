; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/defs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define genvar$ ((pkg-witness symbolp)
                 (prefix stringp)
                 (n maybe-natp)
                 (avoid-lst symbol-listp)
                 state)
  :returns (var symbolp)
  :parents (std/system)
  :short "A logic-mode guard-verified version of @(tsee genvar)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has a stronger guard than @(tsee genvar)
     and always returns a symbol (if it does not cause an error).
     We use @(tsee magic-ev-fncall) to call @(tsee genvar),
     and check that the result is a symbol.
     Hard errors happening in @(tsee genvar) are not suppressed,
     i.e. cause @('genvar$') to stop with those hard errors.
     If @(tsee magic-ev-fncall) fails,
     or if the result is not a symbol,
     we also stop with hard errors.")
   (xdoc::p
    "Compared to @(tsee genvar), this utility requires a @(see state) argument.
     It may also be slightly less efficient
     due the @(tsee magic-ev-fncall) overhead.
     However, it can be used in logic-mode guard-verified code
     that follows a statically typed discipline."))
  (b* (((mv erp var) (magic-ev-fncall 'genvar
                                      (list pkg-witness prefix n avoid-lst)
                                      state
                                      nil
                                      t))
       ((when erp) (raise "Internal error: ~@0" var))
       ((unless (symbolp var))
        (raise "Internal error: ~x0 is not a symbol." var)))
    var))
