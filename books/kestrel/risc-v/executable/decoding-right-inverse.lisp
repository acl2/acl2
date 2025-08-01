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

(include-book "../specification/encoding")

(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "../library-extensions/logops-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decoding-right-inverse
  :parents (executable)
  :short "Encoding applied to the executable decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the executable decoding is right inverse of encoding
     (i.e. that encoding is left inverse of the executable decoding)
     over valid encodings, i.e. over encodings of valid instructions:
     if decoding yields an instruction
     (which we know to be valid as proved in @(tsee decodex)),
     then applying the encoding to the instruction yields the original encoding.
     As a consequence, decoding is injective over valid encodings:
     if two different encodings were decoded in the same way,
     the encoder would have to restore both from the same instruction,
     which is impossible since encoding is a function.")
   (xdoc::p
    "See @(see encoding-decoding-illustration)
     for an illustration of encoding and decoding."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled encode-of-decodex
  :short "Encoding the decoding of a valid encoding
          yields the original encoding."
  (b* ((instr? (decodex enc feat)))
    (implies instr?
             (equal (encode instr? feat)
                    (ubyte32-fix enc))))
  :enable (decodex
           get-opcode
           get-rd
           get-rs1
           get-rs2
           get-funct3
           get-funct7
           get-imm-itype
           get-imm-stype
           get-imm-btype
           get-imm-utype
           get-imm-jtype
           get-fields-rtype
           get-fields-itype
           get-fields-stype
           get-fields-utype
           get-fields-btype
           get-fields-jtype
           encode
           ubyte32-fix
           ubyte20-fix
           ubyte12-fix
           ubyte6-fix
           ubyte5-fix
           ubyte20p
           ubyte12p
           ubyte6p
           ubyte5p
           encode-load-funct
           encode-store-funct)
  :disable ((:e tau-system) ; for speed
            bitops::logapp-of-i-0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled decodex-injective
  :short "Injectivity of decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Different valid encodings are decoded differently.
     This is a direct consequence of @(tsee encode-of-decodex):
     if two different instructions were decoded in the same way,
     the encoder would be unable to restore both at the same time."))
  (b* ((instr1? (decodex enc1 feat))
       (instr2? (decodex enc2 feat)))
    (implies (and instr1?
                  instr2?)
             (equal (equal instr1? instr2?)
                    (equal (ubyte32-fix enc1)
                           (ubyte32-fix enc2)))))
  :use ((:instance encode-of-decodex (enc enc1))
        (:instance encode-of-decodex (enc enc2))))
