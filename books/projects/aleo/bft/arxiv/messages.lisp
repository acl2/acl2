; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

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
     as commonly assumed in the BFT literature.
     The only kind of network communication that is relevant to our model
     is the exchange of certificates among validators.
     Since we model the exchange of proposals and signatures
     at an abstract level here,
     there are no explicit proposals, signatures, etc.
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

;;;;;;;;;;;;;;;;;;;;

(define message-set->certificate-set ((msgs message-setp))
  :returns (certs certificate-setp)
  :short "Lift @(tsee message->certificate) to sets."
  (cond ((set::emptyp msgs) nil)
        (t (set::insert (message->certificate (set::head msgs))
                        (message-set->certificate-set (set::tail msgs)))))
  :verify-guards :after-returns

  ///

  (defruled message->certificate-in-message-set->certificate-set
    (implies (set::in msg msgs)
             (set::in (message->certificate msg)
                      (message-set->certificate-set msgs)))
    :induct t)

  (defruled message-set->certificate-set-of-insert
    (equal (message-set->certificate-set (set::insert msg msgs))
           (set::insert (message->certificate msg)
                        (message-set->certificate-set msgs)))
    :induct t
    :enable (set::in
             message->certificate-in-message-set->certificate-set))

  (defruled message-set->certificate-set-of-union
    (equal (message-set->certificate-set (set::union msgs1 msgs2))
           (set::union (message-set->certificate-set msgs1)
                       (message-set->certificate-set (set::sfix msgs2))))
    :induct t
    :enable (set::union
             message-set->certificate-set-of-insert))

  (defruled message-set->certificate-set-monotone
    (implies (set::subset msgs1 msgs2)
             (set::subset (message-set->certificate-set msgs1)
                          (message-set->certificate-set msgs2)))
    :induct t
    :enable (set::subset
             message->certificate-in-message-set->certificate-set))

  (defruled in-of-message-set->certificate-set-of-delete
    (implies (and (certificatep cert)
                  (message-setp msgs)
                  (set::in cert (message-set->certificate-set msgs))
                  (not (equal (message->certificate msg) cert)))
             (set::in cert (message-set->certificate-set
                            (set::delete msg msgs))))
    :induct t
    :enable (message-set->certificate-set-of-insert
             set::delete)))

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

  (fty::deffixequiv make-certificate-messages
    :args ((cert certificatep)))

  (defruled in-of-make-certificate-messages
    (implies (address-setp dests)
             (equal (set::in msg
                             (make-certificate-messages cert dests))
                    (and (messagep msg)
                         (equal (message->certificate msg)
                                (certificate-fix cert))
                         (set::in (message->destination msg)
                                  dests))))
    :induct t)

  (defruled message-set->certificate-set-of-make-certificate-messages
    (equal (message-set->certificate-set (make-certificate-messages cert dests))
           (if (set::emptyp dests)
               nil
             (set::insert (certificate-fix cert) nil)))
    :induct t
    :enable message-set->certificate-set-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-certs-with-dest ((dest addressp) (msgs message-setp))
  :returns (certs certificate-setp)
  :short "Extract, from a set of messages,
          the ones with a given destination,
          and return their certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used to obtain, from the network (which is a set of messages),
     the certificates addressed to a certain validator."))
  (b* (((when (set::emptyp msgs)) nil)
       (msg (set::head msgs)))
    (if (equal (message->destination msg) (address-fix dest))
        (set::insert (message->certificate msg)
                     (message-certs-with-dest dest (set::tail msgs)))
      (message-certs-with-dest dest (set::tail msgs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv message-certs-with-dest
    :args ((dest addressp)))

  (defrule message-certs-with-dest-of-empty-msgs
    (implies (set::emptyp msgs)
             (equal (message-certs-with-dest dest msgs)
                    nil)))

  (defruled in-of-message-certs-with-dest
    (implies (message-setp msgs)
             (equal (set::in cert
                             (message-certs-with-dest dest msgs))
                    (and (set::in (message cert dest) msgs)
                         (certificatep cert))))
    :induct t
    :enable set::in)

  (defruled message-certs-with-dest-of-insert
    (implies (and (messagep msg)
                  (message-setp msgs))
             (equal (message-certs-with-dest
                     dest (set::insert msg msgs))
                    (if (equal (message->destination msg) (address-fix dest))
                        (set::insert (message->certificate msg)
                                     (message-certs-with-dest dest msgs))
                      (message-certs-with-dest dest msgs))))
    :enable (in-of-message-certs-with-dest
             set::expensive-rules
             set::double-containment-no-backchain-limit)
    :disable message-certs-with-dest)

  (defruled message-certs-with-dest-of-union
    (implies (and (message-setp msgs1)
                  (message-setp msgs2))
             (equal (message-certs-with-dest
                     dest (set::union msgs1 msgs2))
                    (set::union
                     (message-certs-with-dest dest msgs1)
                     (message-certs-with-dest dest msgs2))))
    :enable (in-of-message-certs-with-dest
             set::expensive-rules
             set::double-containment-no-backchain-limit)
    :disable message-certs-with-dest)

  (defruled message-certs-with-dest-of-delete
    (implies (message-setp msgs)
             (equal (message-certs-with-dest dest (set::delete msg msgs))
                    (if (and (set::in msg msgs)
                             (equal (message->destination msg)
                                    (address-fix dest)))
                        (set::delete (message->certificate msg)
                                     (message-certs-with-dest dest msgs))
                      (message-certs-with-dest dest msgs))))
    :enable (in-of-message-certs-with-dest
             set::expensive-rules
             set::double-containment-no-backchain-limit)
    :disable message-certs-with-dest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled message-certs-with-dest-of-make-certificate-messages
  :parents (make-certificate-messages
            message-certs-with-dest)
  :short "Relation between message extraction and message creation."
  (implies (address-setp dests)
           (equal (message-certs-with-dest
                   dest (make-certificate-messages cert dests))
                  (if (set::in (address-fix dest) dests)
                      (set::insert (certificate-fix cert) nil)
                    nil)))
  :induct t
  :enable (message-certs-with-dest-of-insert
           make-certificate-messages))
