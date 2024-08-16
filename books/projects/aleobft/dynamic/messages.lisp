; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ messages
  :parents (states events)
  :short "Messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model the network that connects the validators
     as eventually reliable with authenticated senders,
     as commonly assumes in the BFT literature.
     The only kind of network communication that is relevant to our model
     is the exchange of certificates among validators.
     Since we model the exchange of proposals and signatures
     at an abstract level here,
     there are no explicit batch headers, signatures, etc.
     exchanged in messages.
     Instead, validators may (nondeterministically) broadcast certificates,
     as formalized in the state transitions of the system.
     Those are not immediately delivered to the other validators,
     so we need to model the situation in which
     a certificate has been broadcast but not yet delivered,
     to at least some of the validators (others may have received it already).
     Thus, we model messages as consisting of certificates,
     augmented with destination addresses (one per message)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod message
  :short "Fixtype of messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a message as consisting of
     a certificate and a destination address.
     Note that the certificate includes the author's address,
     which is the sender's address.
     This fulfills the authentication assumption of network communication.")
   (xdoc::p
    "As formalized in the state transitions,
     when a validator broadcasts a certificate,
     messages with that certificate and different destinations
     are added to our model of the network.
     As separate events, messages are removed from the network
     and delivered to the destination validators, one at a time."))
  ((certificate certificate)
   (destination address))
  :pred messagep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset message-set
  :short "Fixtype of sets of messages."
  :elt-type message
  :elementp-of-nil nil
  :pred message-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-certificate-messages ((cert certificatep)
                                   (dests address-setp))
  :returns (msgs message-setp)
  :short "Create messages for a certificate with given destinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each given address,
     we create a message with the certificate
     and with the address as destination.")
   (xdoc::p
    "These are the messages broadcasted to the network
     when a certificate is created."))
  (cond ((set::emptyp dests) nil)
        (t (set::insert (make-message :certificate cert
                                      :destination (set::head dests))
                        (make-certificate-messages cert (set::tail dests)))))
  :verify-guards :after-returns
  ///

  (defruled in-of-make-certificate-messages
    (implies (address-setp dests)
             (equal (set::in msg
                             (make-certificate-messages cert dests))
                    (and (messagep msg)
                         (equal (message->certificate msg)
                                (certificate-fix cert))
                         (set::in (message->destination msg)
                                  dests))))
    :induct t))
