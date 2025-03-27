; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "reachability")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ certificate-in-author
  :parents (correctness)
  :short "Invariant that the certificate in every certificate message
          is in the state of the certificate author if correct."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no messages.
     When a certificate message is created by a correct validator,
     it is added to its DAG.
     Certificates are never removed from DAGs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-in-author-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (msg)
          (implies (and (set::in msg (get-network-state systate))
                        (message-case msg :certificate))
                   (b* ((cert (message-certificate->certificate msg))
                        (author (certificate->author cert)))
                     (implies (set::in author (correct-addresses systate))
                              (b* (((validator-state vstate)
                                    (get-validator-state author systate)))
                                (set::in cert vstate.dag))))))
  ///
  (fty::deffixequiv-sk certificate-in-author-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-in-author-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (certificate-in-author-p systate))
  :enable (certificate-in-author-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certificate-in-author-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled certificate-in-author-p-of-propose-next
    (implies (certificate-in-author-p systate)
             (certificate-in-author-p (propose-next prop dests systate)))
    :enable (certificate-in-author-p
             certificate-in-author-p-necc
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled certificate-in-author-p-of-endorse-next
    (implies (certificate-in-author-p systate)
             (certificate-in-author-p (endorse-next prop endor systate)))
    :enable (certificate-in-author-p
             certificate-in-author-p-necc
             get-network-state-of-endorse-next))

  (defruled certificate-in-author-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (certificate-in-author-p systate))
             (certificate-in-author-p (augment-next prop endor systate)))
    :enable (certificate-in-author-p
             certificate-in-author-p-necc
             get-network-state-of-augment-next))

  (defruled certificate-in-author-p-of-certify-next
    (implies (certificate-in-author-p systate)
             (certificate-in-author-p (certify-next cert dests systate)))
    :use (:instance certificate-in-author-p-necc
                    (msg (certificate-in-author-p-witness
                          (certify-next cert dests systate))))
    :enable (certificate-in-author-p
             validator-state->dag-of-certify-next
             get-network-state-of-certify-next
             in-of-make-certificate-messages))

  (defruled certificate-in-author-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (certificate-in-author-p systate))
             (certificate-in-author-p (accept-next val cert systate)))
    :use (:instance certificate-in-author-p-necc
                    (msg (certificate-in-author-p-witness
                          (accept-next val cert systate))))
    :enable (certificate-in-author-p
             validator-state->dag-of-accept-next
             get-network-state-of-accept-next))

  (defruled certificate-in-author-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (certificate-in-author-p systate))
             (certificate-in-author-p (advance-next val systate)))
    :enable (certificate-in-author-p
             certificate-in-author-p-necc))

  (defruled certificate-in-author-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (certificate-in-author-p systate))
             (certificate-in-author-p (commit-next val systate)))
    :enable (certificate-in-author-p
             certificate-in-author-p-necc))

  (defruled certificate-in-author-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (certificate-in-author-p systate))
             (certificate-in-author-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-in-author-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (certificate-in-author-p systate))
           (certificate-in-author-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-in-author-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (certificate-in-author-p systate))
  :enable (system-state-reachablep
           certificate-in-author-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (certificate-in-author-p from))
              (certificate-in-author-p systate))
     :use (:instance
           certificate-in-author-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
