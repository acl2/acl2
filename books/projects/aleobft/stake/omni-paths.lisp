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

(defxdoc+ omni-paths
  :parents (correctness)
  :short "Invariant that the last committed anchor in a validator
          is also present and reachable from later certificates
          in any validator:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see omni-paths-def-and-implied)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection omni-paths-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled omni-paths-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate)
                  (all-system-committees-fault-tolerant-p systate events))
             (omni-paths-p (events-next events systate)))))
