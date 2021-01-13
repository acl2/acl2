; Isar (Intelligible Semi-Automated Reasoning) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ISAR")

(include-book "defisar")
(include-book "defisar-doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc isar
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Isar-style proofs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Isar (Intelligent Semi-Automated Reasoning) is "
    (xdoc::ahref "https://isabelle.in.tum.de" "Isabelle")
    "'s structured proof language,
     designed to be not only machine-processable
     but also human-readable.
     It supports proofs that look similar to those found in textbooks,
     and accommodates the use of automated proof methods
     to carry out the individual proof steps,
     which may be smaller or larger as desired.
     See the Isabelle documentation for more information.")
   (xdoc::p
    "This ACL2 library aims at providing a similar capability for ACL2.
     It is just a small start in that direction for now.")
   (xdoc::p
    "This is not meant to replace ACL2's existing proof styles,
     but merely to provide an additional style
     that may be valuable in some circumstances.
     For example, when programmatically generating proofs
     that are always expected to work based on some handwritten general proofs,
     Isar proofs can be created that mimic the handwritten proofs closely.
     As another example, when the goal is not only to carry out a proof
     but also to explain how and why it works to human readers,
     Isar proofs may be especially appropriate.
     As a third example, when certain ACL2 proofs need user guidance
     (beyond enabling and/or disabling rules)
     to direct the prover through the right steps,
     Isar proofs may be preferable, in terms of readability and maintenability,
     to certain kinds of @(':use') hints that provide that guidance.")
   (xdoc::p
    "Different proof styles make different tradeoffs in terms of
     effort, readability, maintainability, robustness, etc.;
     and some of these qualities have multiple dimensions,
     e.g. a proof in a certain style may be more robust along a dimension
     while a proof in another style may be more robust in another dimension.
     It is also important to remark that the Isar style
     accommodates the use of ACL2's normal proof style (including @(':hints'))
     within a structured Isar proof.
     In fact, a one-step Isar proof is isomorphic to a traditional ACL2 proof.
     The Isar proof steps may be as small or as large as desired.
     An Isar proof with more detailed steps may also be incrementally changed
     to use less and less detailed steps,
     possibly to the point of being replaced with a traditional ACL2 proof,
     if the latter can be carried out automatically
     via sufficiently general rules.")
   (xdoc::p
    "This ACL2 library for Isar
     does not provide a new prover,
     does not change ACL2 itself,
     and does not introduce new axioms.
     It merely provides a language to generate regular ACL2 events
     that are checked and proved using ACL2's usual proof capabilities
     and that cannot generate unsoundness or logical inconsistencies.")
   (xdoc::p
    "The differences between the ACL2 and Isabelle logics
     may motivate certain differnces between Isabelle's Isar language
     and the language provided by this ACL2 library.
     However, the more similar the two languages can be made,
     the easier it is to leverage concepts
     and facilitate the use of both systems by more users.")
   (xdoc::p
    "The "
    (xdoc::seetopic "acl2::proof-builder" "ACL2 proof builder")
    " can also be used to decompose a proof into more controlled steps.
     However, the proof builder commands
     are more similar to tactics that operate on the proof goals,
     where the intermediate proof states are not visible in the proof script,
     with the result that a human reader cannot, in general,
     readily undestand the proof just by looking at the proof script,
     without running it.
     In contrast, Isar is designed to make those proof states visible,
     and to let a human reader understand the proof
     without actually running it.
     This is explained in more detail in the Isar documentation,
     in particular where it is contrasted to Isabelle's tactics.")))
