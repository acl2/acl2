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
  :order-subtopics (messages
                    t)
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
     "A validator creates a new certificate.
      Note that the certificate includes the author,
      i.e. it indicates the validator.
      This adds the certificate to the DAG of the validator,
      and broadcasts the certificate on the network.")
    (xdoc::li
     "A validator accepts a certificate,
      from a message in the network,
      which is removed from the network
      and added to the DAG of the validator.
      Note that the message indicates the validator,
      as the destination.")
    (xdoc::li
     "A validator advances its round.")
    (xdoc::li
     "A validator commits anchors.")))
  (:create ((certificate certificate)))
  (:accept ((message message)))
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
