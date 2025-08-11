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

(include-book "decoding-left-inverse")
(include-book "decoding-right-inverse")

(include-book "../specification/decoding")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decoding-correct
  :parents (executable)
  :short "Correctness of the executable decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the inversion theorems proved in
     @(see decoding-left-inverse) and @(see decoding-right-inverse)
     to show that the declarative definition of the decoder
     is equivalent to the executable definition of the decoder.")
   (xdoc::p
    "See @(see encoding-decoding-illustration)
     for an illustration of encoding and decoding."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled decode-is-decodex
  :short "Equivalence of declarative and executable decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the encoding @('enc') is valid,
     it is equal to @('(encode (encoding-valid-witness enc feat) feat)')
     by the definition of @(tsee encoding-validp).
     If we substitute that into @('(decodex enc feat)')
     and use @(tsee decodex-of-encode),
     that simplifies to @('(encoding-valid-witness enc feat)'),
     which is the same as @('(decode enc feat)')
     by definition of the latter.")
   (xdoc::p
    "If instead the encoding @('enc') is invalid,
     by definition @('(decode enc feat)') is @('nil').
     If @('(decodex enc feat)') were not @('nil'),
     it would be a witness for @(tsee encoding-validp),
     using @(tsee encode-of-decodex) to show that
     the encoding of the witness is @('enc'),
     but we had assumed that the encoding was not valid.
     Thus also @('(decodex enc feat)') must be @('nil'),
     the same as @('(decode enc feat)')."))
  (equal (decode enc feat)
         (decodex enc feat))
  :use (decode-is-decodex-when-encoding-validp
        decode-is-decodex-when-not-encoding-validp)

  :prep-lemmas

  ((defruled decode-is-decodex-when-encoding-validp
     (implies (encoding-validp enc feat)
              (equal (decode enc feat)
                     (decodex enc feat)))
     :use (:instance lemma (enc (ubyte32-fix enc)) (feat (feat-fix feat)))
     :prep-lemmas
     ((defruled lemma
        (implies (and (encoding-validp enc feat)
                      (ubyte32p enc)
                      (featp feat))
                 (equal (decode enc feat)
                        (decodex enc feat)))
        :use (:instance decodex-of-encode
                        (instr (encoding-valid-witness enc feat)))
        :enable (encoding-validp
                 decode))))

   (defruled decode-is-decodex-when-not-encoding-validp
     (implies (not (encoding-validp enc feat))
              (equal (decode enc feat)
                     (decodex enc feat)))
     :enable (decode
              encode-of-decodex)
     :use (:instance encoding-validp-suff (instr (decodex enc feat))))))
