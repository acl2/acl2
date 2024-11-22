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

(include-book "operations-blockchain")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-blockchain-additional
  :parents (operations-additional)
  :short "Additional operations on the blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation to calculate the whole blockchain
     from the DAG and the full sequence of committed anchors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define calculate-blockchain ((anchors certificate-listp)
                              (dag certificate-setp))
  :returns (blockchain block-listp)
  :short "Calculate the blockchain from the anchors and DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee extend-blockchain)
     starting with the empty blockchain and no committed certificates.
     We only returns the blockchain,
     discarding the committed certificate set."))
  (b* (((mv blockchain &) (extend-blockchain anchors dag nil nil)))
    blockchain)

  ///

  (defruled calculate-blockchain-of-nil
    (equal (calculate-blockchain nil dag)
           nil)
    :enable extend-blockchain-of-nil)

  (defret len-of-calculate-blockchain
    (equal (len blockchain)
           (len anchors))
    :hints (("Goal" :in-theory (enable fix
                                       len-of-extend-blockchain))))
  (in-theory (disable len-of-calculate-blockchain))

  (defruled nthcdr-of-calculate-blockchain
    (implies (<= n (len anchors))
             (equal (nthcdr n (calculate-blockchain anchors dag))
                    (calculate-blockchain (nthcdr n anchors) dag)))
    :enable nthcdr-of-extend-blockchain))
