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

(include-book "system-states")
(include-book "committees")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)

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
     the correct and faulty validators in the system,
     and of the genesis committee.")
   (xdoc::p
    "As explained in @(see committees),
     the genesis committee is modeled via a constrained nullary function.")
   (xdoc::p
    "We could have similarly introduced two constrained nullary functions
     that return the set of addresses of the correct validators
     and the set of addresses of the faulty validators,
     which are also arbitrary, but fixed during the execution of the protocol.
     Then we could have formalized "
    (xdoc::seetopic "system-states" "system states")
    " a little differently, using just
     a map from validator addresses to validator states,
     and constraining the keys of the map to be
     the set of correct validator addresses returned by the nullary function.
     But we prefer the current formulation, without the two nullary functions,
     and with a system state containing
     a map from addresses to optional validator states,
     because this is more natural for a future version of the model
     in which, instead of having a fixed collection of all possible validators,
     we actually have validators coming into and going out of existence
     (i.e. being added to and removed from the map in the system state).")
   (xdoc::p
    "There is a unique possible initial state
     of an individual (correct) validator,
     which we therefore formalize via a defined nullary function
     that returns this initial state.")
   (xdoc::p
    "We introduce a predicate that characterizes
     all the possible initial states of the system.
     This predicate refers to the nullary function for the genesis committee,
     to ensure that the commitee is part of the validators.")
   (xdoc::p
    "We also introduce a function that,
     given two sets of disjoint addresses,
     one for correct validators and one for faulty ones,
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
     has empty DAG and buffer,
     has no record of endorsed certificates,
     has 0 as last committed round
     (meaning that no anchors have been committed yet,
     since 0 is not a valid round number),
     has an empty blockchain,
     has no committed certificates,
     and the timer is expired (i.e. not running)."))
  (make-validator-state :round 1
                        :dag nil
                        :buffer nil
                        :endorsed nil
                        :last 0
                        :blockchain nil
                        :committed nil
                        :timer (timer-expired))
  ///
  (in-theory (disable (:e validator-init))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-validators-initp ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if all the correct validators in the system
          are in the initial state."
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
     and the genesis committee must be a subset of all the validators.
     Note that a committee may include correct and faulty validators.")
   (xdoc::p
    "Furthermore, the network is initially empty."))
  (and (system-validators-initp systate)
       (set::subset (committee-members (genesis-committee))
                    (all-addresses systate))
       (set::emptyp (get-network-state systate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-init ((correct-vals address-setp)
                     (faulty-vals address-setp))
  :guard (and (set::emptyp (set::intersect correct-vals faulty-vals))
              (set::subset (committee-members (genesis-committee))
                           (set::union correct-vals faulty-vals)))
  :returns (systate system-statep)
  :short "Calculate an initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial state of the sytem is determined by
     the addresses of the correct validators
     and the addresses of the faulty validators.
     The guard requires
     the disjointness of the addresses of correct and faulty validators
     and the inclusion of the genesis committee addresses
     in the union of the addresses."))
  (b* ((vstates nil)
       (vstates (system-init-loop1 correct-vals vstates))
       (vstates (system-init-loop2 faulty-vals vstates)))
    (make-system-state :validators vstates
                       :network nil))
  :hooks (:fix)

  :prepwork

  ((define system-init-loop1 ((correct-vals address-setp)
                              (vstates validators-statep))
     :returns (new-vstates validators-statep
                           :hyp (validators-statep vstates))
     (b* (((when (or (not (mbt (address-setp correct-vals)))
                     (set::emptyp correct-vals)))
           (validators-state-fix vstates))
          (vstates (omap::update (set::head correct-vals)
                                 (validator-init)
                                 vstates)))
       (system-init-loop1 (set::tail correct-vals) vstates))

     ///

     (fty::deffixequiv system-init-loop1
       :args ((correct-vals address-setp)))

     (defruled in-of-keys-of-system-init-loop1
       (implies (validators-statep vstates)
                (equal (set::in val
                                (omap::keys
                                 (system-init-loop1 correct-vals vstates)))
                       (or (set::in val (address-set-fix correct-vals))
                           (set::in val (omap::keys vstates)))))
       :induct t)

     (defruled keys-of-system-init-loop1
       (implies (validators-statep vstates)
                (equal (omap::keys (system-init-loop1 correct-vals vstates))
                       (set::union (address-set-fix correct-vals)
                                   (omap::keys vstates))))
       :enable (in-of-keys-of-system-init-loop1
                set::expensive-rules)
       :disable system-init-loop1)

     (defruled correct-addresses-loop-of-system-init-loop1
       (implies (and (validators-statep vstates)
                     (not (set::intersectp (address-set-fix correct-vals)
                                           (omap::keys vstates))))
                (equal (correct-addresses-loop
                        (system-init-loop1 correct-vals vstates))
                       (set::union (address-set-fix correct-vals)
                                   (correct-addresses-loop vstates))))
       :induct t
       :enable (correct-addresses-loop-of-update
                set::expensive-rules)
       :hints ('(:use (:instance set::emptyp-of-intersect-of-subset-left
                                 (a (tail correct-vals))
                                 (b correct-vals)
                                 (c (omap::keys vstates))))))


     (defruled lookup-of-system-init-loop1
       (implies (validators-statep vstates)
                (equal (omap::lookup val
                                     (system-init-loop1 correct-vals vstates))
                       (if (set::in val (address-set-fix correct-vals))
                           (validator-init)
                         (omap::lookup val vstates))))
       :induct t
       :enable omap::lookup))

   (define system-init-loop2 ((faulty-vals address-setp)
                              (vstates validators-statep))
     :returns (new-vstates validators-statep
                           :hyp (validators-statep vstates))
     (b* (((when (or (not (mbt (address-setp faulty-vals)))
                     (set::emptyp faulty-vals)))
           (validators-state-fix vstates))
          (vstates (omap::update (set::head faulty-vals)
                                 nil
                                 vstates)))
       (system-init-loop2 (set::tail faulty-vals) vstates))

     ///

     (fty::deffixequiv system-init-loop2
       :args ((faulty-vals address-setp)))

     (defruled in-of-keys-of-system-init-loop2
       (implies (validators-statep vstates)
                (equal (set::in val
                                (omap::keys
                                 (system-init-loop2 faulty-vals vstates)))
                       (or (set::in val (address-set-fix faulty-vals))
                           (set::in val (omap::keys vstates)))))
       :induct t)

     (defruled keys-of-system-init-loop2
       (implies (validators-statep vstates)
                (equal (omap::keys (system-init-loop2 faulty-vals vstates))
                       (set::union (address-set-fix faulty-vals)
                                   (omap::keys vstates))))
       :enable (in-of-keys-of-system-init-loop2
                set::expensive-rules)
       :disable system-init-loop2)

     (defruled correct-addresses-loop-of-system-init-loop2
       (implies (and (validators-statep vstates)
                     (not (set::intersect (address-set-fix faulty-vals)
                                          (omap::keys vstates))))
                (equal (correct-addresses-loop
                        (system-init-loop2 faulty-vals vstates))
                       (correct-addresses-loop vstates)))
       :induct t
       :enable (correct-addresses-loop-of-update
                set::emptyp
                set::expensive-rules
                correct-addresses-loop-subset)
       :hints ('(:use ((:instance set::emptyp-of-intersect-of-subset-left
                                  (a (tail faulty-vals))
                                  (b faulty-vals)
                                  (c (omap::keys vstates)))
                       (:instance set::not-member-when-member-of-disjoint
                                  (a faulty-vals)
                                  (b (omap::keys vstates))
                                  (x (set::head faulty-vals)))))))

     (defruled lookup-of-system-init-loop2
       (implies (validators-statep vstates)
                (equal (omap::lookup val (system-init-loop2 faulty-vals vstates))
                       (if (set::in val (address-set-fix faulty-vals))
                           nil
                         (omap::lookup val vstates))))
       :induct t
       :enable omap::lookup)))

  ///

  (defrule system-initp-of-system-init
    (implies (and (address-setp correct-vals)
                  (address-setp faulty-vals)
                  (set::subset (committee-members (genesis-committee))
                               (set::union correct-vals faulty-vals))
                  (not (set::intersect correct-vals faulty-vals)))
             (system-initp (system-init correct-vals faulty-vals)))
    :enable (system-initp
             system-validators-initp
             get-validator-state
             get-network-state
             all-addresses
             correct-addresses
             keys-of-system-init-loop1
             keys-of-system-init-loop2
             correct-addresses-loop-of-system-init-loop1
             correct-addresses-loop-of-system-init-loop2
             lookup-of-system-init-loop1
             lookup-of-system-init-loop2
             set::not-member-when-member-of-disjoint
             set::expensive-rules)))
