; Aleo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "bft/top")
(include-book "leo/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleo
  :parents (acl2::projects)
  :short "An ACL2 library about the Aleo blockchain and ecosystem."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::ahref "https://www.aleo.org" "Aleo")
    " supports private applications via zero-knowledge proofs.")
   (xdoc::p
    "This ACL2 library contains a growing collection of
     formalizations, proofs, and tools
     for the Aleo blockchain and ecosystem.")
   (xdoc::p
    "This ACL2 library is being developed by "
    (xdoc::ahref "https://provable.com" "Provable")
    ".")
   (xdoc::p
    "Currently this library contains two sub-libraries:")
   (xdoc::ul
    (xdoc::li
     "A sub-library about AleoBFT,
      the consensus protocol of the Aleo blockchain.")
    (xdoc::li
     "A sub-library about Leo,
      a programming language for zero-knowledge applications
      to be deployed on the Aleo blockchain.")))
  :order-subtopics (aleobft::aleobft
                    leo::leo))
