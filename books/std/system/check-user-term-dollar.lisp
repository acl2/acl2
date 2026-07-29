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
               (stobjs-out symbol-listp))
  :parents (std/system/term-queries)
  :short "A logic-mode guard-verified version of @(tsee check-user-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This uses @(tsee magic-ev-fncall) on @(tsee check-user-term),
     and thus it takes the ACL2 state instead of just the ACL2 world.
     But this currently has a significant limitation:
     since @(tsee magic-ev-fncall) executes @(tsee check-user-term) in safe mode
     (see @(tsee magic-ev-fncall) for details),
     attempting to check (translate) mundane macros like @('+')
     results in an error."))
  (b* ((wrld (w state))
       ((mv erp val)
        (magic-ev-fncall 'check-user-term (list x wrld) state nil nil))
       ((when erp)
        (raise "Internal error: call of CHECK-USER-TERM failed.")
        (mv nil nil))
       ((unless (and (true-listp val)
                     (= (len val) 2)))
        (raise "Internal error: call of CHECK-USER-TERM returns ~x0." val)
        (mv nil nil))
       ((list term/message stobjs-out) val)
       ((unless (or (pseudo-termp term/message)
                    (msgp term/message)))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." term/message)
        (mv nil nil))
       ((unless (symbol-listp stobjs-out))
        (raise "Internal error: CHECK-USER-TERM returned ~x0." stobjs-out)
        (mv nil nil)))
    (mv term/message stobjs-out))
  :no-function nil)
