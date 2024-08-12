; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "certificates")

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

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
     in terms of a reliable broadcast mechanism
     as described in the BFT literature.
     The only kind of network communication that is relevant to our model
     is the exchange of certificates among validators.
     Since we model the exchange of proposals and signatures
     at an abstract level here,
     there are no explicit batch headers, signatures, etc.
     exchanged in messages.
     Instead, validators may (nondeterministically)
     reliably broadcast certificates,
     as formalized in the state transitions of the system.
     Those are not immediately delivered to the other validators,
     so we need to model the situation in which
     a certificate has been broadcast but not yet delivered
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
     i.e. the sender's address.
     As formalized in the state transitions,
     when a validator reliably broadcasts a certificate,
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
