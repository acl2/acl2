; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "baby-jubjub")
(include-book "base-points-for-pedersen-hash")
(include-book "pedersen-hash")
(include-book "prime-field-abbreviations")

(include-book "json-to-r1cs/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semaphore
  :parents (ethereum::ethereum)
  :short "Ethereum's Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "Semaphore is a zero-knowledge gadget for Ethereum,
     but it may have wider applicability.
     See the "
    (xdoc::ahref "https://github.com/appliedzkp/semaphore"
                 "Ethereum Semaphore repository")
    " for more information.")
   (xdoc::p
    "This library provides an ACL2 formalization of the Semaphore functionality,
    and formal proofs that the R1CS used to implement Semaphore are equivalent
    to the formalization.  The formalization is primarily based on the specification in the paper "
    (xdoc::ahref "https://github.com/appliedzkp/semaphore/blob/master/spec/Semaphore%20Spec.pdf"
                 "Community Proposal: Semaphore: Zero-Knowledge Signaling on Ethereum")
    ", referenced here as `[Sema-Spec]' for brevity.
    Sections are referenced by appending their designations separated by a colon,
    e.g.,
    `[Sema-Spec:5.3.2]' references Section 5.3.2."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semaphore-specification
  :parents (semaphore)
  :short "Formal specification of Ethereum's Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here are specifications of key components of Ethereum's Semaphore.
     We plan to formally specify the remaining components as well.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semaphore-proofs
  :parents (semaphore)
  :short "Formal proofs of Ethereum's Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here are formal proofs of key components of Ethereum's Semaphore.
     We plan to formally verify the remaining components as well.")))
