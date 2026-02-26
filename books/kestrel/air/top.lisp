; AIR Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR")

(include-book "model-0/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ air
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for AIR."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIR (Algebraic Intermediate Representation)
     is a general framework for expressing computation
     as polynomial constraints over execution traces,
     used in zero-knowledge proofs.
     Any computation that can be represented
     as a sequence of states with valid transitions
     can be encoded as an AIR.
     There are various online resources on AIR, such as:")
   (xdoc::ul
    (xdoc::li
     "``Scalable, transparent, and post-quantum secure computational integrity''
      by Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, and Michael Riabzev ("
     (xdoc::ahref "https://eprint.iacr.org/2018/046"
                  "Cryptology ePrint Archive Paper 2018/046")
     ").")
    (xdoc::li
     "``ethSTARK Documentation''
      by Eli Ben-Sasson ("
     (xdoc::ahref "https://eprint.iacr.org/2021/582"
                  "Cryptology ePrint Archive Paper 2021/582")
     ").")
    (xdoc::li
     "The "
     (xdoc::ahref "https://docs.zkm.io/design/arithmetization.html"
                  "Arithmetization Section")
     " of the ZKM documentation."))
   (xdoc::p
    "This library contains a very simple but illustrative development
     showing how computations in a simple machine-like language
     are represented as AIR constraints,
     with formal proofs of correctness.
     This is not a comprehensive library on AIR yet,
     but it is an exploratory start towards it."))
  :order-subtopics t
  :default-parent t)
