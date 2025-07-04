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

(include-book "validator-states")
(include-book "messages")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ system-states
  :parents (states)
  :short "States of the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "The committee of validators that run the protocol is dynamic:
     validators are bonded and unbonded via transactions;
     see @(see transactions).
     There is a genesis committees, i.e. an initial set of validators,
     and then the committee may change, potentially at every block.
     Validators who unbond simply leave,
     while validators that bond after genesis
     need to sync with the rest of the validators,
     in order to have enough internal state to run the protocol.")
   (xdoc::p
    "This dynamic aspect of AleoBFT is complex.
     Note also that each validator has its own notion of the current committee,
     based on their own view of the blockchain.
     If the blockchains are in sufficient agreement,
     which is the purpose of the protocol,
     then there is also suitable agreement on the current committee.")
   (xdoc::p
    "To avoid modeling the syncing process of newly bonded validators,
     we make a modeling assumption that,
     while unrealistic if taken literally,
     it seems actually quite adequate as a way to model successful syncing,
     at least at an abstract level.
     Our approach is to include, in the system state,
     all possible validators that may ever be part of any committee;
     this may be a very large set, but that causes no issue in a formal model.
     All these validators keep their internal states up to date,
     by receiving and processing messages from other validators.
     But only validators in the current committee generate messages.
     A validator knows whether it is in the current committee or not,
     based on its current blockchain.
     A faulty validator may violate that,
     and attempt to author certificates without being in the committee,
     but those are not accepted by correct validators,
     if they come from validators not in the committees.")
   (xdoc::p
    "The above explanation is just a sketch,
     which alludes to several complexities.
     We discuss how we model all of that
     in the definition of state transitions.")
   (xdoc::p
    "At a high level, the adequacy of this modeling choice can be argued thus.
     If a new validator bonds and syncs,
     after successful syncing it will have enough state
     to participate in the protocol.
     This is somewhat equivalent to the validator having always been present,
     receiving and processing messages to update its internal state,
     instead of doing all of that (or a sufficient part of it)
     at syncing time.")
   (xdoc::p
    "Eventually, we will want to model syncing more explicitly.
     However, we believe that the current model is already a good one,
     at least as a first cut at handling dynamic committees.")
   (xdoc::p
    "Besides the validators,
     we also model the state of the network that connects the validators,
     in terms of messages in transit,
     which have been sent but not received yet.")
   (xdoc::p
    "Along with a definition of the states of the system,
     we also introduce operations to handle system states
     in a slightly more abstract way:
     operations to retrieve validator addresses,
     operations to read and write validator states,
     and operations to read and write the network state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (set-induction-depth-limit 1)

  (fty::defomap address-validator-state-map
    :short "Fixtype of maps from addresses to validator states."
    :key-type address
    :val-type validator-state
    :pred address-validator-state-mapp

    ///

    (defrule address-setp-of-keys-when-address-validator-state-map
      (implies (address-validator-state-mapp map)
               (address-setp (omap::keys map)))
      :induct t
      :enable omap::keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod system-state
  :short "Fixtype of system states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixtype captures the state of the whole system of validators,
     i.e. the state of the whole protocol.
     It consists of the state of the validators and the state of the network.")
   (xdoc::p
    "The state of the validators is captured by
     a map from addresses to validator states.
     This map captures the state of all the correct validators in the system,
     which, as explained in @(see system-states),
     is a potentially large set of all the possible ones
     that could be in a committee at some point in time.
     The (unchanging) addresses are captured in the keys of the map,
     while the changeable states are the values of the map.
     The set of keys of this map does not change,
     because again these are all possible validators,
     not just a committee.")
   (xdoc::p
    "Since faulty validators may do almost arbitrary things
     (short of breaking cryptography,
     along with other well-defined and well-motivated restrictions),
     there is no need to actually model their internal states,
     or even to include them explicitly in the state.
     This is why the map is only for the correct validators in the system;
     the faulty ones are implicit, and not explicitly part of the state.
     In the definition of the system transitions,
     we model the behavior of faulty validators
     in terms of nondeterministic generation of
     messages for other (correct) validators:
     this modeling approach does not require the explicit presence,
     in the system state, of the faulty validators.
     It also does not matter which messages are received by faulty validators,
     who can behave arbitrarily regardless of what they receive or not.")
   (xdoc::p
    "A basic assumption in our model is that a validator is
     either always correct or not.
     If not, it is considered faulty,
     no matter how small its deviation from correct behavior.
     In practice, this corresponds to a validator
     either running a correct implementation of AleoBFT or not;
     it is a separate problem whether the implementation
     is correct with respect to the specification of AleoBFT.")
   (xdoc::p
    "The network is modeled as a set of messages in transit.")
   (xdoc::p
    "As explained in @(see system-states),
     the validators are all the possible ones,
     in the genesis committe as well as any future committee;
     more precisely, only the correct ones in all these committees,
     since the faulty ones are not explicitly represented.
     Note that the system state does not have any information
     about the current committee,
     because that is a notion that every validator computes on its own,
     based on their view of the blockchain.")
   (xdoc::p
    "The only shared state among validators is the network,
     which is shared in a very restricted way
     (as formalized by the state transitions),
     in terms of message sending and receiving.
     The rest of the system state is strictly partitioned among the validators,
     which communicate exclusively through network messages."))
  ((validators address-validator-state-map)
   (network message-set))
  :pred system-statep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define correct-addresses ((systate system-statep))
  :returns (addrs address-setp)
  :short "Set of the addresses of all the correct validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys in the map,
     which only includes correct validators,
     as explained in @(tsee system-state)."))
  (omap::keys (system-state->validators systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-validator-state ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (vstate validator-statep)
  :short "Retrieve the state of a correct validator from the system."
  (validator-state-fix
   (omap::lookup (address-fix val) (system-state->validators systate)))
  :guard-hints (("Goal" :in-theory (enable correct-addresses
                                           omap::in-of-keys-to-assoc)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-validator-state ((val addressp)
                                (vstate validator-statep)
                                (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (new-systate system-statep)
  :short "Update the state of a correct validator in the system."
  (b* ((valmap (system-state->validators systate))
       (new-valmap (omap::update (address-fix val)
                                 (validator-state-fix vstate)
                                 valmap)))
    (change-system-state systate :validators new-valmap))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-update-validator-state
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (set::in (address-fix val) (correct-addresses systate))
    :hints (("Goal" :in-theory (enable correct-addresses))))

  (defruled get-validator-state-of-update-validator-state
    (equal (get-validator-state val1
                                (update-validator-state val
                                                        vstate
                                                        systate))
           (if (equal (address-fix val) (address-fix val1))
               (validator-state-fix vstate)
             (get-validator-state val1 systate)))
    :enable (get-validator-state
             omap::lookup-of-update))

  (defrule get-validator-state-of-update-validator-state-same
    (equal (get-validator-state val
                                (update-validator-state val
                                                        vstate
                                                        systate))
           (validator-state-fix vstate))
    :enable (get-validator-state
             omap::lookup-of-update))

  (defrule get-validator-state-of-update-validator-state-diff
    (implies (not (equal (address-fix val) (address-fix val1)))
             (equal (get-validator-state val1
                                         (update-validator-state val
                                                                 vstate
                                                                 systate))
                    (get-validator-state val1 systate)))
    :enable (get-validator-state
             omap::lookup-of-update)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-network-state ((systate system-statep))
  :returns (network message-setp)
  :short "Retrieve the state of the network in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a thin layer, but it provides slightly more abstraction."))
  (system-state->network systate)
  :hooks (:fix)

  ///

  (defrule get-network-state-of-update-validator-state
    (equal (get-network-state (update-validator-state val vstate systate))
           (get-network-state systate))
    :enable update-validator-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-network-state ((network message-setp) (systate system-statep))
  :returns (new-systate system-statep)
  :short "Update the state of the network in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a thin layer, but it provides more abstraction."))
  (change-system-state systate :network network)
  :hooks (:fix)

  ///

  (defret correct-addresses-of-update-network-state
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hints (("Goal" :in-theory (enable correct-addresses))))

  (defrule get-network-state-of-update-network-state
    (equal (get-network-state (update-network-state network systate))
           (message-set-fix network))
    :enable get-network-state)

  (defrule get-validator-state-of-update-network-state
    (equal (get-validator-state val (update-network-state network systate))
           (get-validator-state val systate))
    :enable get-validator-state))
