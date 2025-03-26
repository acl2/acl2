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

(include-book "validator-states")
(include-book "messages")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

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
    "The system consists of a number of validators,
     some correct and some faulty.
     We model the correctness or faultiness of each validator,
     and the internal state of each validator.
     We also model the state of the network that connects the validators,
     in terms of messages in transit,
     which have been sent but not received yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (set-induction-depth-limit 1)
  (fty::defomap validators-state
    :short "Fixtype of states of a collection of validators."
    :long
    (xdoc::topstring
     (xdoc::p
      "This map captures the state of all the validators in the system,
       which in this model form a fixed committee.
       The (unchanging) addresses are captured in the keys of the map,
       while the changeable states are the values of the map.
       The set of keys of this map does not change,
       because the committee is fixed.")
     (xdoc::p
      "Since faulty validators may do almost arbitrary things
       (short of breaking cryptography,
       along with other well-defined and well-motivated restrictions),
       there is no need to actually model their internal states.
       So we use @('nil') to model (the state of) faulty validators in this map.
       We model the behavior of faulty validators
       in terms of nondeterministic generation of events.")
     (xdoc::p
      "A basic assumption in our model is that a validator is
       either always correct or not.
       If not, it is considered faulty,
       no matter how small its deviation from correct behavior.
       In practice, this corresponds to a validator
       either running snarkOS or not;
       whether snarkOS correctly implements AleoBFT is a separate problem."))
    :key-type address
    :val-type validator-state-option
    :pred validators-statep
    ///

    (defrule address-setp-of-keys-when-validators-statep
      (implies (validators-statep map)
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
     It consists of a map from validator addresses to optional validator states
     (see @(tsee validators-state)),
     and a set of messages that models the state of the network
     (see @(tsee message) for a rationale of this model of the network)."))
  ((validators validators-state)
   (network message-set))
  :pred system-statep)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption system-state-option
  system-state
  :short "Fixtype of optional system states."
  :long
  (xdoc::topstring
   (xdoc::p
    "System states are defined in @(tsee system-state)."))
  :pred system-state-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-addresses ((systate system-statep))
  :returns (addrs address-setp)
  :short "Set of the addresses of all the validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys in the map."))
  (omap::keys (system-state->validators systate))
  :hooks (:fix)
  ///

  (defruled all-addresses-fold
    (equal (omap::keys (system-state->validators systate))
           (all-addresses systate))
    :enable all-addresses)

  (theory-invariant (incompatible (:definition all-addresses)
                                  (:rewrite all-addresses-fold))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define correct-addresses ((systate system-statep))
  :returns (addrs address-setp)
  :short "Set of the addresses of all the correct validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys in the map
     with an associated non-@('nil') (i.e. correct) validator state."))
  (correct-addresses-loop (system-state->validators systate))
  :hooks (:fix)

  :prepwork
  ((define correct-addresses-loop ((vstates validators-statep))
     :returns (addrs address-setp)
     :parents nil
     (b* (((when (omap::emptyp vstates)) nil)
          ((mv addr vstate) (omap::head vstates)))
       (if vstate
           (set::insert (address-fix addr)
                        (correct-addresses-loop (omap::tail vstates)))
         (correct-addresses-loop (omap::tail vstates))))
     :verify-guards :after-returns
     ///

     (defruled correct-addresses-loop-subset-keys
       (implies (validators-statep vstates)
                (set::subset (correct-addresses-loop vstates)
                             (omap::keys vstates)))
       :induct t
       :enable set::expensive-rules)

     (defruled lookup-nonnil-of-correct-addresses-loop
       (implies (and (validators-statep vstates)
                     (set::in addr
                              (correct-addresses-loop vstates)))
                (omap::lookup addr vstates))
       :rule-classes (:rewrite :type-prescription)
       :induct t
       :enable (omap::lookup
                omap::assoc-of-tail-when-assoc-of-tail
                set::expensive-rules)
       :hints ('(:use ((:instance correct-addresses-loop-subset-keys
                                  (vstates (omap::tail vstates)))
                       (:instance omap::in-of-keys-to-assoc
                                  (key addr)
                                  (map (omap::tail vstates)))))))

     (defruled in-of-correct-addresses-loop
       (implies (validators-statep vstates)
                (iff (set::in addr (correct-addresses-loop vstates))
                     (and (omap::assoc addr vstates)
                          (cdr (omap::assoc addr vstates)))))
       :induct t
       :enable (omap::assoc
                set::expensive-rules)
       :hints ('(:use (:instance correct-addresses-loop-subset-keys
                                 (vstates (omap::tail vstates))))))

     (defruled correct-addresses-loop-of-update
       (implies (and (addressp val)
                     (validator-statep vstate)
                     (validators-statep vstates))
                (equal (correct-addresses-loop
                        (omap::update val vstate vstates))
                       (if vstate
                           (set::insert val
                                        (correct-addresses-loop
                                         vstates))
                         (set::delete val
                                      (correct-addresses-loop
                                       vstates)))))
       :enable (set::double-containment-no-backchain-limit
                set::pick-a-point-subset-strategy
                in-of-correct-addresses-loop))

     (defruled nil-not-in-correct-addresses-loop
       (not (set::in nil (correct-addresses-loop vstates)))
       :induct t)))

  ///

  (defruled correct-addresses-subset-all-addresses
    (set::subset (correct-addresses systate)
                 (all-addresses systate))
    :enable (all-addresses
             correct-addresses-loop-subset-keys))

  ;; Variant of the theorem just above with all-addresses expanded.
  ;; Useful when all-addresses is enabled in a proof.
  (defruled correct-addresses-subset-keys-validators
    (set::subset (correct-addresses systate)
                 (omap::keys (system-state->validators systate)))
    :use correct-addresses-subset-all-addresses
    :enable all-addresses)

  (defruled in-all-addresses-when-in-correct-addresses
    (implies (set::in val (correct-addresses systate))
             (set::in val (all-addresses systate)))
    :disable correct-addresses
    :enable (set::expensive-rules
             correct-addresses-subset-all-addresses))

  (defruled lookup-nonnil-of-correct-addresses
    (implies (set::in addr (correct-addresses systate))
             (omap::lookup addr (system-state->validators systate)))
    :rule-classes (:rewrite :type-prescription)
    :enable
    (correct-addresses
     lookup-nonnil-of-correct-addresses-loop))

  (defruled nonempty-all-addresses-when-correct-validator
    (implies (set::in val (correct-addresses systate))
             (not (set::emptyp (all-addresses systate))))
    :use correct-addresses-subset-all-addresses
    :disable correct-addresses-subset-all-addresses)

  (defruled not-nil-in-correct-addresses
    (not (set::in nil (correct-addresses systate)))
    :enable nil-not-in-correct-addresses-loop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define faulty-addresses ((systate system-statep))
  :returns (addrs address-setp)
  :short "Set of the addresses of all the faulty validator in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys in the map with an associated faulty validator state,
     or equivalently the difference between
     the set of all the validator addresses
     and the set of all the correct validator addresses."))
  (set::difference (all-addresses systate)
                   (correct-addresses systate))
  :hooks (:fix)
  ///

  (defruled faulty-addresses-subset-all-addresses
    (set::subset (faulty-addresses systate)
                 (all-addresses systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-validators ((systate system-statep))
  :returns (number natp)
  :short "Number of validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the total number of validators in the system,
     often denoted @($n$) in the BFT literature."))
  (set::cardinality (all-addresses systate))
  :hooks (:fix)
  ///

  (defruled number-validators-alt-def
    (equal (number-validators systate)
           (omap::size (system-state->validators systate)))
    :enable (all-addresses
             omap::size-to-cardinality-of-keys))

  (defruled number-validator-gt-0-when-nonempty-all-addresses
    (implies (not (set::emptyp (all-addresses systate)))
             (> (number-validators systate) 0))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-correct ((systate system-statep))
  :returns (number natp)
  :short "Number of correct validators in the system."
  (set::cardinality (correct-addresses systate))
  :hooks (:fix)
  ///

  (defret number-correct-upper-bound
    (<= number (number-validators systate))
    :rule-classes :linear
    :hints
    (("Goal"
      :in-theory (acl2::enable number-validators
                               correct-addresses-subset-all-addresses))))
  (in-theory (disable number-correct-upper-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-faulty ((systate system-statep))
  :returns (number natp
                   :hints (("Goal" :in-theory (enable natp))))
  :short "Number of faulty validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is sometimes denoted @($f$) in the literature,
     but the same symbol sometimes instead denotes
     the maximum tolerated number of faulty validators.
     See the discussion in @(tsee max-faulty-for-total)."))
  (set::cardinality (faulty-addresses systate))
  :hooks (:fix)
  ///

  (defruled number-faulty-alt-def
    (equal (number-faulty systate)
           (- (number-validators systate)
              (number-correct systate)))
    :enable (number-validators
             number-correct
             faulty-addresses
             correct-addresses-subset-all-addresses
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-validator-state ((val addressp) (systate system-statep))
  :guard (set::in val (all-addresses systate))
  :returns (vstate? validator-state-optionp)
  :short "Retrieve the state of a validator from the system."
  (validator-state-option-fix
   (omap::lookup val (system-state->validators systate)))
  :guard-hints (("Goal" :in-theory (enable all-addresses
                                           omap::assoc-to-in-of-keys)))
  ///

  (fty::deffixequiv get-validator-state
    :args ((systate system-statep)))

  (defret validator-statep-of-get-validator-state
    (validator-statep vstate?)
    :hyp (set::in val (correct-addresses systate))
    :hints (("Goal" :in-theory (enable lookup-nonnil-of-correct-addresses))))
  (in-theory (disable validator-statep-of-get-validator-state))

  (defruled in-correct-validator-addresess-when-get-validator-state
    (implies (get-validator-state val systate)
             (set::in val (correct-addresses systate)))
    :enable (correct-addresses
             in-of-correct-addresses-loop
             omap::lookup))

  (defruled get-validator-state-iff-in-correct-addresses
    (iff (get-validator-state val systate)
         (set::in val (correct-addresses systate)))
    :hints
    (("Goal"
      :in-theory
      (enable lookup-nonnil-of-correct-addresses
              in-correct-validator-addresess-when-get-validator-state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-validator-state ((val addressp)
                                (vstate validator-statep)
                                (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (new-systate system-statep)
  :short "Update the state of a correct validator in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this function, which only operates on correct validators,
     is not completely parallel with @(tsee get-validator-state),
     which may retrieve the @('nil') state of a faulty validator.
     But we prefer the shorter name to @('update-correct-validator-state')."))
  (b* ((vstates (system-state->validators systate))
       (new-vstates (omap::update val vstate vstates)))
    (change-system-state systate :validators new-vstates))
  ///

  (fty::deffixequiv update-validator-state
    :args ((systate system-statep)))

  (defret all-addresses-of-update-validator-state
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hyp (and (set::in val (all-addresses systate))
              (validator-statep vstate))
    :hints (("Goal" :in-theory (enable all-addresses))))

  (defret correct-addresses-of-update-validator-state
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (and (set::in val (correct-addresses systate))
              (validator-statep vstate))
    :hints (("Goal" :in-theory (enable correct-addresses
                                       correct-addresses-loop-of-update))))

  (defruled get-validator-state-of-update-validator-state
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-statep vstate))
             (equal (get-validator-state
                     val (update-validator-state val1 vstate systate))
                    (if (equal val val1)
                        vstate
                      (get-validator-state val systate))))
    :enable (get-validator-state
             omap::lookup))

  (defrule get-validator-state-of-update-validator-state-same
    (implies (and (set::in val (correct-addresses systate))
                  (validator-statep vstate))
             (equal (get-validator-state val
                                         (update-validator-state val
                                                                 vstate
                                                                 systate))
                    vstate))
    :enable (get-validator-state
             omap::lookup))

  (defrule get-validator-state-of-update-validator-state-diff
    (implies (and (set::in val1 (correct-addresses systate))
                  (not (equal val val1))
                  (validator-statep vstate))
             (equal (get-validator-state val
                                         (update-validator-state val1
                                                                 vstate
                                                                 systate))
                    (get-validator-state val systate)))
    :enable (get-validator-state
             omap::lookup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-network-state ((systate system-statep))
  :returns (network message-setp)
  :short "Retrieve the state of the network in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a thin layer,
     introduced mainly to match @(tsee update-network-state)."))
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
    "This is a relatively thin layer,
     but it creates a bit more abstraction."))
  (change-system-state systate :network network)
  :hooks (:fix)
  ///

  (defret all-addresses-of-update-network-state
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hints (("Goal" :in-theory (enable all-addresses))))

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
