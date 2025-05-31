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

(include-book "system-states")
(include-book "committees")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ initialization
  :parents (definition)
  :short "Initial states of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are multiple possible initial states of the system,
     corresponding to different choices of (the addresses of)
     the correct validators in the system,
     and of the genesis committee.
     Recall that faulty validators
     are not modeled explicitly in the system state,
     except for the presence, in some components of the system state,
     of some addresses of faulty validators
     (e.g. the authors of some certificates).")
   (xdoc::p
    "As explained in @(see committees),
     the genesis committee is modeled via a constrained nullary function,
     namely @(tsee genesis-committee).")
   (xdoc::p
    "We could have similarly introduced a constrained nullary function
     that returns the set of addresses of the correct validators,
     which are also arbitrary, but fixed during the execution of the protocol.
     Then we could have formalized "
    (xdoc::seetopic "system-states" "system states")
    " a little differently, using just
     a map from validator addresses to validator states,
     and constraining the keys of the map to be
     the set of correct validator addresses returned by the nullary function.
     But we prefer the current formulation, without the two nullary function,
     and with a system state containing
     an unconstrained map from addresses to validator states,
     because this is more natural for a future version of the model
     in which, instead of having a fixed collection of
     all possible (correct) validators,
     we actually have validators coming into and going out of existence,
     i.e. being added to and removed from the map in the system state.")
   (xdoc::p
    "There is a unique possible initial state
     of an individual (correct) validator,
     which we therefore formalize via a defined nullary function
     that returns that initial state.")
   (xdoc::p
    "We introduce a predicate that characterizes
     all the possible initial states of the system.")
   (xdoc::p
    "We also introduce a function that,
     given a sets of addresses for correct validators,
     constructs the initial system state with those validators.
     This is not necessary to define the labeled transition system,
     for which the predicate described in the previous paragraph suffices.
     However, this function may be useful to simulate the system:
     given the inputs to this functions and a list of events,
     we can calculate the initial state and the successive states
     that the system goes through by way of those events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-init ()
  :returns (vstate validator-statep)
  :short "Initial (correct) validator state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, each correct validator
     is in round 1,
     has empty DAG,
     has no record of endorsed certificates,
     has 0 as last committed round
     (meaning that no anchors have been committed yet,
     since 0 is not a valid round number),
     has an empty blockchain, and
     has no committed certificates."))
  (make-validator-state :round 1
                        :dag nil
                        :endorsed nil
                        :last 0
                        :blockchain nil
                        :committed nil)
  ///
  (in-theory (disable (:e validator-init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-validators-initp ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if all the validators in the system are in the initial state."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (equal (get-validator-state val systate)
                          (validator-init))))
  ///
  (fty::deffixequiv-sk system-validators-initp
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-initp ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a system state is an initial one."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every correct validator must be in the initial state,
     and the network must be empty (no messages have been sent yet).")
   (xdoc::p
    "Furthermore, the network is initially empty."))
  (and (system-validators-initp systate)
       (set::emptyp (get-network-state systate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-init ((correct-vals address-setp))
  :returns (systate system-statep)
  :short "Calculate an initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial state of the sytem is determined by
     the addresses of the correct validators.")
   (xdoc::p
    "We prove that every system state calculated by this function
     satisfies the predicate that characterized initial states."))
  (b* ((vstates (system-init-loop correct-vals nil)))
    (make-system-state :validators vstates
                       :network nil))
  :hooks (:fix)

  :prepwork

  ((define system-init-loop ((correct-vals address-setp)
                             (vstates validators-statep))
     :returns (new-vstates validators-statep :hyp (validators-statep vstates))
     (b* (((when (or (not (mbt (address-setp correct-vals)))
                     (set::emptyp correct-vals)))
           (validators-state-fix vstates))
          (vstates (omap::update (set::head correct-vals)
                                 (validator-init)
                                 vstates)))
       (system-init-loop (set::tail correct-vals) vstates))

     ///

     (fty::deffixequiv system-init-loop
       :args ((correct-vals address-setp)))

     (defruled in-of-keys-of-system-init-loop
       (implies (validators-statep vstates)
                (equal (set::in val
                                (omap::keys
                                 (system-init-loop correct-vals vstates)))
                       (or (set::in val (address-set-fix correct-vals))
                           (set::in val (omap::keys vstates)))))
       :induct t)

     (defruled keys-of-system-init-loop
       (implies (validators-statep vstates)
                (equal (omap::keys (system-init-loop correct-vals vstates))
                       (set::union (address-set-fix correct-vals)
                                   (omap::keys vstates))))
       :enable (in-of-keys-of-system-init-loop
                set::expensive-rules)
       :disable system-init-loop)

     (defruled lookup-of-system-init-loop
       (implies (validators-statep vstates)
                (equal (omap::lookup val
                                     (system-init-loop correct-vals vstates))
                       (if (set::in val (address-set-fix correct-vals))
                           (validator-init)
                         (omap::lookup val vstates))))
       :induct t
       :enable omap::lookup)))

  ///

  (defrule system-initp-of-system-init
    (system-initp (system-init correct-vals))
    :enable (system-initp
             system-validators-initp
             get-validator-state
             get-network-state
             correct-addresses
             keys-of-system-init-loop
             lookup-of-system-init-loop)))
