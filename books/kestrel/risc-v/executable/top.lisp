; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "decoding-executable")
(include-book "decoding-left-inverse")
(include-book "decoding-right-inverse")
(include-book "decoding-correct")
(include-book "execution-executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ executable
  :parents (riscv)
  :short "Executable refinement of the RISC-V @(see specification)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see specification) is aimed at clarity,
     and not at efficient execution.
     In fact, since decoding is specified as inverse of encoding,
     the specification is not fully executable.
     Here we provide an executable refinement of the specification.
     In particular, we define an executable decoding function @(tsee decodex)
     and we prove it equivalent to the declaratively defined @(tsee decode).")
   (xdoc::p
    "In the future,
     we may investigate synthesizing the executable decoder using "
    (xdoc::seetopic "apt::apt" "APT")
    ".")
   (xdoc::p
    "We use @(tsee apt::simplify) to obtain
     executable versions of @(tsee step) and @(tsee stepn),
     which call @(tsee decodex) instead of @(tsee decode).")
   (xdoc::p
    "The semnantic functions do not depend on decoding
     and thus do not need to be refined to be fully executable."))
  :order-subtopics (decoding-executable
                    decoding-left-inverse
                    decoding-right-inverse
                    decoding-correct
                    execution-executable))
