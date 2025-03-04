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

(defxdoc+ certificate-to-other
  :parents (correctness)
  :short "Invariant that every certificate message from a correct validator
          is addressed to a different validator than the proposal author."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there is no (certificate or other kind of) message
     in the network.
     Certificate messages are only created when certificates are created.
     When a correct validator creates a certificate,
     it does not send the certificate messages to itself.
     Faulty validators may send certificate messages to themselves,
     but this invariant only concerns certificates from correct validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-to-other-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (cert dest)
          (implies (and (certificatep cert)
                        (addressp dest)
                        (set::in (message-certificate cert dest)
                                 (get-network-state systate))
                        (set::in (certificate->author cert)
                                 (correct-addresses systate)))
                   (not (equal (certificate->author cert) dest))))
  ///
  (fty::deffixequiv-sk certificate-to-other-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-to-other-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (certificate-to-other-p systate))
  :enable (certificate-to-other-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certificate-to-other-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reason why use the @(':expand') hint in some of the proofs,
     instead of just enabling @(tsee certificate-to-other-p),
     is that, if we do the latter,
     the @('certificate-to-other-p-necc') rule does not fire,
     because it cannot instantiate the free variable @('systate').
     With the @(':expand') hint,
     only the call of @(tsee certificate-to-other-p)
     in the conclusion of the theorems is expanded,
     leaving the call in the hypothesis unexpanded,
     so it can be used to provide an instantiation for
     the free variable @('systate') in @('certificate-to-other-p-necc').
     This is only the case for some of the theorems;
     others need a @(':use') hint for @('certificate-to-other-p-necc'),
     and so in that case we just enable @(tsee certificate-to-other-p)."))

  (defruled certificate-to-other-p-of-propose-next
    (implies (certificate-to-other-p systate)
             (certificate-to-other-p (propose-next cert dests systate)))
    :use (:instance certificate-to-other-p-necc
                    (cert (mv-nth 0 (certificate-to-other-p-witness
                                     (propose-next cert dests systate))))
                    (dest (mv-nth 1 (certificate-to-other-p-witness
                                     (propose-next cert dests systate)))))
    :enable (certificate-to-other-p
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled certificate-to-other-p-of-endorse-next
    (implies (certificate-to-other-p systate)
             (certificate-to-other-p (endorse-next cert endor systate)))
    :use (:instance certificate-to-other-p-necc
                    (cert (mv-nth 0 (certificate-to-other-p-witness
                                     (endorse-next cert endor systate))))
                    (dest (mv-nth 1 (certificate-to-other-p-witness
                                     (endorse-next cert endor systate)))))
    :enable (certificate-to-other-p
             get-network-state-of-endorse-next))

  (defruled certificate-to-other-p-of-augment-next
    (implies (and (augment-possiblep cert endor systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (augment-next cert endor systate)))
    :expand (certificate-to-other-p (augment-next cert endor systate))
    :enable (certificate-to-other-p-necc
             get-network-state-of-augment-next))

  (defruled certificate-to-other-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (certify-next cert dests systate)))
    :use (:instance certificate-to-other-p-necc
                    (cert (mv-nth 0 (certificate-to-other-p-witness
                                     (certify-next cert dests systate))))
                    (dest (mv-nth 1 (certificate-to-other-p-witness
                                     (certify-next cert dests systate)))))
    :enable (certificate-to-other-p
             get-network-state-of-certify-next
             in-of-make-certificate-messages
             certify-possiblep
             certificate->author))

  (defruled certificate-to-other-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (accept-next val cert systate)))
    :expand (certificate-to-other-p (accept-next val cert systate))
    :enable (certificate-to-other-p-necc
             get-network-state-of-accept-next))

  (defruled certificate-to-other-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (advance-next val systate)))
    :expand (certificate-to-other-p (advance-next val systate))
    :enable certificate-to-other-p-necc)

  (defruled certificate-to-other-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (commit-next val systate)))
    :expand (certificate-to-other-p (commit-next val systate))
    :enable certificate-to-other-p-necc)

  (defruled certificate-to-other-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (certificate-to-other-p systate))
             (certificate-to-other-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-to-other-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (certificate-to-other-p systate))
           (certificate-to-other-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-to-other-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (certificate-to-other-p systate))
  :enable (system-state-reachablep
           certificate-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (certificate-to-other-p from))
              (certificate-to-other-p systate))
     :use (:instance
           certificate-to-other-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
