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

(include-book "decoding-of-encoding")
(include-book "encoding-of-decoding")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decoding-as-inverse
  :parents (decoding)
  :short "Declarative definition of decoding as inverse of encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a declarative (non-executable) definition
     of decoding as the inverse of encoding.
     We use the inversion theorems proved in
     @(see decoding-of-encoding) and @(see encoding-of-decoding)
     to show that this is equivalent to the executable definition."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk encoding-validp ((enc ubyte32p) (feat featp))
  :returns (yes/no booleanp)
  :short "Check if a 32-bit word is a valid instruction encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when there exists an instruction,
     valid for the given features,
     whose encoding is @('enc').
     This is a declarative definition."))
  (exists (instr)
          (and (instrp instr)
               (instr-validp instr feat)
               (equal (encode instr feat)
                      (ubyte32-fix enc))))
  :skolem-name encoding-valid-witness

  ///

  (fty::deffixequiv-sk encoding-validp
    :args ((enc ubyte32p) (feat featp)))

  (defrule instrp-of-encoding-valid-witness
    (implies (encoding-validp enc feat)
             (instrp (encoding-valid-witness enc feat))))

  (defrule instr-validp-of-encoding-valid-witness
    (implies (encoding-validp enc feat)
             (instr-validp (encoding-valid-witness enc feat) feat)))

  (defrule encode-of-encoding-valid-witness
    (implies (encoding-validp enc feat)
             (equal (encode (encoding-valid-witness enc feat) feat)
                    (ubyte32-fix enc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decodei ((enc ubyte32p) (feat featp))
  :returns (instr? instr-optionp)
  :short "Declarative definition of instruction decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is some valid instruction whose encoding is @('enc'),
     we return one such instruction.
     We use the witness function of @(tsee encoding-validp) for that.")
   (xdoc::p
    "Since @(tsee encode) is injective,
     there is in fact at most one such instruction."))
  (if (encoding-validp enc feat)
      (encoding-valid-witness (ubyte32-fix enc) (feat-fix feat))
    nil)
  :hooks (:fix)

  ///

  (defruled encode-of-decodei
    (implies (encoding-validp enc feat)
             (equal (encode (decodei enc feat) feat)
                    (ubyte32-fix enc)))
    :use (:instance lemma (enc (ubyte32-fix enc)) (feat (feat-fix feat)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (ubyte32p enc)
                     (featp feat)
                     (encoding-validp enc feat))
                (equal (encode (decodei enc feat) feat)
                       enc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled decodei-is-decodex
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
     which is the same as @('(decodei enc feat)')
     by definition of the latter.")
   (xdoc::p
    "If instead the encoding @('enc') is invalid,
     by definition @('(decodei enc feat)') is @('nil').
     If @('(decodex enc feat)') were not @('nil'),
     it would be a witness for @(tsee encoding-validp),
     using @(tsee encode-of-decodex) to show that
     the encoding of the witness is @('enc'),
     but we had assumed that the encoding was not valid.
     Thus also @('(decodex enc feat)') must be @('nil'),
     the same as @('(decodei enc feat)')."))
  (equal (decodei enc feat)
         (decodex enc feat))
  :use (decodei-is-decodex-when-encoding-validp
        decodei-is-decodex-when-not-encoding-validp)

  :prep-lemmas

  ((defruled decodei-is-decodex-when-encoding-validp
     (implies (encoding-validp enc feat)
              (equal (decodei enc feat)
                     (decodex enc feat)))
     :use (:instance lemma (enc (ubyte32-fix enc)) (feat (feat-fix feat)))
     :prep-lemmas
     ((defruled lemma
        (implies (and (encoding-validp enc feat)
                      (ubyte32p enc)
                      (featp feat))
                 (equal (decodei enc feat)
                        (decodex enc feat)))
        :use (:instance decodex-of-encode
                        (instr (encoding-valid-witness enc feat)))
        :enable (encoding-validp
                 decodei))))

   (defruled decodei-is-decodex-when-not-encoding-validp
     (implies (not (encoding-validp enc feat))
              (equal (decodei enc feat)
                     (decodex enc feat)))
     :enable (decodei
              encode-of-decodex)
     :use (:instance encoding-validp-suff (instr (decodex enc feat))))))
