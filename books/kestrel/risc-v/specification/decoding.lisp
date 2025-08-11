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

(include-book "encoding")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decoding
  :parents (specification)
  :short "Decoding of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instructions are encoded as specified in [ISA] and [ISAP],
     and as formalized in @(see encoding).
     We declaratively define a decoder as non-executable inverse of the encoder;
     see @(see decoding-executable) for an equivalent executable decoder.")
   (xdoc::p
    "See @(see encoding-decoding-illustration)
     for an illustration of encoding and decoding."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode ((enc ubyte32p) (feat featp))
  :returns (instr? instr-optionp)
  :short "Declarative definition of instruction decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is some valid instruction whose encoding is @('enc'),
     we return one such instruction.
     We use the witness function of @(tsee encoding-validp) for that.")
   (xdoc::p
    "Since @(tsee encode) is injective (as proved elsewhere),
     there is in fact at most one such instruction.
     However, this uniqueness is unnecessary for defining the decoder here.")
   (xdoc::p
    "The encoder is left inverse of the decoder over valid encodings.
     This follows from the same property of the witness function
     of @(tsee encoding-validp), which is proved there."))
  (if (encoding-validp enc feat)
      (encoding-valid-witness (ubyte32-fix enc) (feat-fix feat))
    nil)

  ///

  (fty::deffixequiv decode
    :args ((enc ubyte32p) (feat featp)))

  (defret instrp-of-decode
    (instrp instr?)
    :hyp (encoding-validp enc feat))

  (defret instr-validp-of-decode
    (instr-validp instr? feat)
    :hyp (encoding-validp enc feat)
    :hints (("Goal"
             :use (:instance instr-validp-of-encoding-valid-witness
                             (enc (ubyte32-fix enc))
                             (feat (feat-fix feat)))
             :in-theory (disable instr-validp-of-encoding-valid-witness))))

  (defruled encode-of-decode
    (implies (encoding-validp enc feat)
             (equal (encode (decode enc feat) feat)
                    (ubyte32-fix enc)))
    :use (:instance lemma (enc (ubyte32-fix enc)) (feat (feat-fix feat)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (ubyte32p enc)
                     (featp feat)
                     (encoding-validp enc feat))
                (equal (encode (decode enc feat) feat)
                       enc)))))

  (defruled decode-iff-encoding-validp
    (iff (decode enc feat)
         (encoding-validp enc feat))
    :use (:instance instrp-of-encoding-valid-witness
                    (enc (ubyte32-fix enc))
                    (feat (feat-fix feat)))
    :disable instrp-of-encoding-valid-witness))
