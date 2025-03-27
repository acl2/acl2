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

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ previous-quorum
  :parents (correctness)
  :short "Invariant that each certificate in a DAG
          has references to previous certificates
          that form a non-zero quorum in the committee for the previous round,
          unless the round is 1,
          in which case there are no references to previous certificates:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see previous-quorum-def-and-init-and-next)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled previous-quorum-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate)
                  (all-system-committees-fault-tolerant-p systate events))
             (previous-quorum-p (events-next events systate)))))
