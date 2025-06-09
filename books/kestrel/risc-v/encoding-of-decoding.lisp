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
(include-book "decoding")

(include-book "library-extensions")

(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ encoding-of-decoding
  :parents (encoding decoding)
  :short "Encoding applied to decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that encoding is left inverse of decoding
     over valid encodings, i.e. over encodings of valid instructions:
     if decoding yields an instruction
     (which we know to be valid as proved in @(tsee decode)),
     then applying the encoding to the instruction yields the original encoding.
     As a consequence, decoding is injective over valid encodings:
     if two different encodings were decoded in the same way,
     the encoder would have to restore both from the same instruction,
     which is impossible since encoding is a function."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled encode-of-decode
  :short "Encoding the decoding of a valid encoding
          yields the original encoding."
  (b* ((instr? (decode enc feat)))
    (implies instr?
             (equal (encode instr? feat)
                    (ubyte32-fix enc))))
  :enable (decode
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

(defruled decode-injective
  :short "Injectivity of decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Different valid encodings are decoded differently.
     This is a direct consequence of @(tsee encode-of-decode):
     if two different instructions were decoded in the same way,
     the encoder would be unable to restore both at the same time."))
  (b* ((instr1? (decode enc1 feat))
       (instr2? (decode enc2 feat)))
    (implies (and instr1?
                  instr2?)
             (equal (equal instr1? instr2?)
                    (equal (ubyte32-fix enc1)
                           (ubyte32-fix enc2)))))
  :use ((:instance encode-of-decode (enc enc1))
        (:instance encode-of-decode (enc enc2))))
