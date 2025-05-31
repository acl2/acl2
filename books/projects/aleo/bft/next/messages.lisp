; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

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
     as consisting of authenticated point-to-point connections
     with unbounded delays,
     as commonly assumed in the BFT literature.
     We model messages that include information about both sender and receiver,
     and we model the network (in the system states)
     as the set of messages currently in transit,
     i.e. sent but not yet received.")
   (xdoc::p
    "There are three kinds of messages:
     proposals, endorsements, and certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum message
  :short "Fixtype of messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "A proposal message consists of a proposal and a destination address.
     When a validator creates a proposal,
     it broadcasts it to other validators,
     one message per validator,
     with the same proposal but different destination (i.e. receiver).
     In a proposal message, the sender is the author of the proposal.
     The latter assertion does not quite apply to
     the extra proposal messages to faulty validators not in the committee
     discussed in @(see transitions-propose):
     these extra messages are just a device to provide faulty validators
     with the ability to endorse proposals from the correct validators
     even when the faulty validators are not in the committee.")
   (xdoc::p
    "An endorsement message consists of a proposal and an endorser address.
     When a validator receives a valid proposal from another validator,
     it endorses it by sending an endorsement back to the proposal author.
     The endorser's address represents a signature of the endorser in our model.
     The endorser is the sender,
     while the receiver is the author of the proposal.
     In AleoBFT, endorsements only include
     cryptographically unique references to proposals,
     but in our model we use the whole proposal for modeling simplicity.")
   (xdoc::p
    "A certificate message consists of a certificate and a destination address.
     When a validator, after creating and broadcasting a proposal,
     receives enough endorsements,
     it creates and broadcasts a certificate.
     Thus a certificate message is similar to a proposal message,
     but with a certificate instead of a proposal.
     The sender of a certificate is the author of the proposal/certificate."))
  (:proposal ((proposal proposal)
              (destination address)))
  (:endorsement ((proposal proposal)
                 (endorser address)))
  (:certificate ((certificate certificate)
                 (destination address)))
  :pred messagep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset message-set
  :short "Fixtype of sets of messages."
  :elt-type message
  :elementp-of-nil nil
  :pred message-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-proposal-messages ((prop proposalp)
                                (dests address-setp))
  :returns (msgs message-setp)
  :short "Create messages for a proposal with given destinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each given address,
     we create a proposal message with the proposal
     and with the address as destination.")
   (xdoc::p
    "These are the messages broadcasted to the network
     when a proposal is created:
     see @(see transitions-propose)."))
  (cond ((set::emptyp (address-set-fix dests)) nil)
        (t (set::insert (make-message-proposal
                         :proposal prop
                         :destination (set::head dests))
                        (make-proposal-messages prop (set::tail dests)))))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret emptyp-of-make-proposal-messages
    (equal (set::emptyp msgs)
           (set::emptyp (address-set-fix dests)))
    :hints (("Goal" :induct t)))

  (defruled in-of-make-proposal-messages
    (equal (set::in msg (make-proposal-messages prop dests))
           (and (messagep msg)
                (message-case msg :proposal)
                (equal (message-proposal->proposal msg)
                       (proposal-fix prop))
                (set::in (message-proposal->destination msg)
                         (address-set-fix dests))))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-endorsement-messages ((prop proposalp)
                                   (endors address-setp))
  :returns (msgs message-setp)
  :short "Create messages for an endorsement from given endorsers."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each given address,
     we create an endorsement message with the proposal
     and with the address as endorser.")
   (xdoc::p
    "These are the messages consumed from the network
     when a faulty validator creates a certificate:
     see @(see transitions-certify)."))
  (cond ((set::emptyp (address-set-fix endors)) nil)
        (t (set::insert (make-message-endorsement
                         :proposal prop
                         :endorser (set::head endors))
                        (make-endorsement-messages prop (set::tail endors)))))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret emptyp-of-make-endorsement-messages
    (equal (set::emptyp msgs)
           (set::emptyp (address-set-fix endors)))
    :hints (("Goal" :induct t)))

  (defruled in-of-make-endorsement-messages
    (equal (set::in msg (make-endorsement-messages prop endors))
           (and (messagep msg)
                (message-case msg :endorsement)
                (equal (message-endorsement->proposal msg)
                       (proposal-fix prop))
                (set::in (message-endorsement->endorser msg)
                         (address-set-fix endors))))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     when a certificate is created:
     see @(see transitions-certify)."))
  (cond ((set::emptyp (address-set-fix dests)) nil)
        (t (set::insert (make-message-certificate
                         :certificate cert
                         :destination (set::head dests))
                        (make-certificate-messages cert (set::tail dests)))))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret emptyp-of-make-certificate-messages
    (equal (set::emptyp msgs)
           (set::emptyp (address-set-fix dests)))
    :hints (("Goal" :induct t)))

  (defruled in-of-make-certificate-messages
    (equal (set::in msg (make-certificate-messages cert dests))
           (and (messagep msg)
                (message-case msg :certificate)
                (equal (message-certificate->certificate msg)
                       (certificate-fix cert))
                (set::in (message-certificate->destination msg)
                         (address-set-fix dests))))
    :induct t))
