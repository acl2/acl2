; Standard System Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-user-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-user-term$ (x state)
  :returns (mv (term/message (or (pseudo-termp term/message)
                                 (msgp term/message)))
               (stobjs-out symbol-listp)
               state)
  :parents (std/system/term-queries)
  :short "A logic-mode guard-verified version of @(tsee check-user-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This uses @(tsee in-logic-mode) on @(tsee check-user-term),
     and thus it takes the ACL2 state instead of just the ACL2 world,
     and it also returns the ACL2 state."))
  (b* ((wrld (w state))
       ((mv erp val state)
        (in-logic-mode (mv-list 2 (check-user-term x wrld)) state '(x wrld)))
       ((when erp)
        (raise "Internal error: call of CHECK-USER-TERM failed.")
        (mv nil nil state))
       ((unless (and (true-listp val)
                     (= (len val) 2)))
        (raise "Internal error: call of CHECK-USER-TERM returns ~x0." val)
        (mv nil nil state))
       ((list term/message stobjs-out) val)
       ((unless (or (pseudo-termp term/message)
                    (msgp term/message)))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." term/message)
        (mv nil nil state))
       ((unless (symbol-listp stobjs-out))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." stobjs-out)
        (mv nil nil state)))
    (mv term/message stobjs-out state)))
