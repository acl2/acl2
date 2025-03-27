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

(include-book "states")

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
    "There are multiple possible initial states of the system.
     We introduce operations to calculate the initial states
     (from suitable inputs),
     and predicates to characterize the possible initial states."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-init ((correct-vals address-setp)
                     (faulty-vals address-setp))
  :guard (set::emptyp (set::intersect correct-vals faulty-vals))
  :returns (systate system-statep)
  :short "Initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial state of the sytem depends on
     the addresses of the correct validators
     and the addresses of the faulty validators;
     in fact, it is completely determined by them.")
   (xdoc::p
    "The initial map associates
     the initial validator state to each correct validator address,
     and @('nil') to each faulty validator address.
     The initial network has no message."))
  (b* ((correct-map (system-init-loop1 correct-vals))
       (faulty-map (system-init-loop2 faulty-vals))
       (vstates (omap::update* correct-map faulty-map)))
    (make-system-state :validators vstates
                       :network nil))

  :prepwork

  ((define system-init-loop1 ((correct-vals address-setp))
     :returns (map validators-statep
                   :hyp (address-setp correct-vals))
     (cond ((set::emptyp correct-vals) nil)
           (t (omap::update (set::head correct-vals)
                            (validator-init)
                            (system-init-loop1 (set::tail correct-vals)))))
     :verify-guards :after-returns)

   (define system-init-loop2 ((faulty-vals address-setp))
     :returns (map validators-statep
                   :hyp (address-setp faulty-vals))
     (cond ((set::emptyp faulty-vals) nil)
           (t (omap::update (set::head faulty-vals)
                            nil
                            (system-init-loop2 (set::tail faulty-vals)))))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validators-state-initp ((vstates validators-statep))
  :returns (yes/no booleanp)
  :short "Check if the states of a collection of validators is initial."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each validator must be
     either the initial one for correct validators
     or @('nil') for faulty validators."))
  (b* (((when (omap::emptyp vstates)) t)
       (vstate (omap::head-val vstates))
       ((unless (or (not vstate)
                    (equal vstate (validator-init))))
        nil))
    (validators-state-initp (omap::tail vstates)))

  ///

  (defruled validator-init-when-validators-statep
    (implies (and (validators-state-initp vstates)
                  (omap::assoc val vstates)
                  (omap::lookup val vstates))
             (equal (omap::lookup val vstates)
                    (validator-init)))
    :induct t
    :enable omap::lookup))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-state-initp ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a system state is initial."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when every correct validator is in the initial state,
     and the network is empty."))
  (and (validators-state-initp (system-state->validators systate))
       (set::emptyp (system-state->network systate)))

  ///

  (defruled validator-init-when-system-initp
    (implies (and (system-state-initp systate)
                  (set::in val (correct-addresses systate)))
             (equal (get-validator-state val systate)
                    (validator-init)))
    :enable (get-validator-state
             correct-addresses
             in-of-correct-addresses-loop
             validator-init-when-validators-statep
             lookup-nonnil-of-correct-addresses)))
