; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "validator-states")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ author-round-pairs-in-validators
  :parents (correctness)
  :short "Author-round pairs in validator states."
  :long
  (xdoc::topstring
   (xdoc::p
    "An important notion for the correctness of the protocol
     is that of the author-round pairs in the state of a correct validator.
     These are the author-round pairs of the proposals
     (i) in (the certificates in) the DAG,
     (ii) in (the keys of) the pending proposal map, and
     (iii) in the set of endorsed proposals.
     Here we define this notion, which is then used elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-has-author+round-p ((author addressp)
                                      (round posp)
                                      (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a validator state includes a proposal
          with a given author or round
          in its DAG or pending proosal map or endorsed proposal set."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the DAG, it is equivalent to check whether
     there is a certificate with the given author and round,
     given that those are the same for the proposal in the certificate."))
  (b* (((validator-state vstate) vstate))
    (or (not (set::emptyp (certs-with-author+round
                           author round vstate.dag)))
        (not (set::emptyp (props-with-author+round
                           author round (omap::keys vstate.proposed))))
        (not (set::emptyp (props-with-author+round
                           author round vstate.endorsed)))))
  :hooks (:fix))
