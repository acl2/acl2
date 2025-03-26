; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "simultaneous-induction")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ same-committees
  :parents (correctness)
  :short "Invariant that correct validators calculate the same committees:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see same-committees-def-and-implied)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection same-committees-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled same-committees-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate)
                  (all-system-committees-fault-tolerant-p systate events))
             (same-committees-p (events-next events systate)))))
