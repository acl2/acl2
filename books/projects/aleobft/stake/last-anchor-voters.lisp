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

(defxdoc+ last-anchor-voters
  :parents (correctness)
  :short "Invariant that the last committed anchor
          has at least a certain number of successors:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see last-anchor-voters-def-and-init-and-next)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-voters-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled last-anchor-voters-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate)
                  (all-system-committees-fault-tolerant-p systate events))
             (last-anchor-voters-p (events-next events systate)))))
