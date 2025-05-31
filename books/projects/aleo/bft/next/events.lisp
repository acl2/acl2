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

(include-book "messages")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ events
  :parents (definition)
  :short "Events of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a fixtype for the events that can happen in the system,
     which move the system from state to state.")
   (xdoc::p
    "In the framework of labeled state transition systems,
     these events are the labels of the transitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum event
  :short "Fixtype of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The system changes its state (see @(tsee system-state))
     in response to the following events:")
   (xdoc::ol
    (xdoc::li
     "A validator creates a proposals
      and broadcasts it to some destinations.")
    (xdoc::li
     "A validator endorses a proposal received from another validator,
      and sends an endorsement (signature) back to the other validator.")
    (xdoc::li
     "A validator augments a proposal it has previously created
      with an endorsemenet received from another validator.")
    (xdoc::li
     "A validator certifies a proposal
      for which it has received enough endorsements,
      creating a certificate and sending it to some destinations.")
    (xdoc::li
     "A validator accepts a certificate received from another validator.")
    (xdoc::li
     "A validator advances its round.")
    (xdoc::li
     "A validator commits anchors."))
   (xdoc::p
    "The exact meaning of these different kinds of events is formalized
     as the transitions of the labeled state transition system.")
   (xdoc::p
    "Note that certificates (and proposals)
     are not necessarily broadcast to all the (correct) validators,
     but instead the events indicate the destination addresses.
     For the purpose of proving blockchain nonforking and other properties,
     there is in fact no need to require broadcasts to go to all validators;
     however, it is important for other kinds of properties,
     so we may revise the model accordingly,
     or perhaps create another version of the model for that."))
  (:propose ((proposal proposal)
             (destinations address-set)))
  (:endorse ((proposal proposal)
             (endorser address)))
  (:augment ((proposal proposal)
             (endorser address)))
  (:certify ((certificate certificate)
             (destinations address-set)))
  (:accept ((validator address)
            (certificate certificate)))
  (:advance ((validator address)))
  (:commit ((validator address)))
  :pred eventp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist event-list
  :short "Fixtype of lists of events."
  :elt-type event
  :true-listp t
  :elementp-of-nil nil
  :pred event-listp
  :prepwork ((local (in-theory (enable nfix)))))
