; Some changes to the open-source x86 model
;
; Copyright (C) 2022-2025 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

;; See also alt-defs.lisp

(include-book "rflags-spec-sub")
(include-book "projects/x86isa/machine/instructions/sub-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/add-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/shifts-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/and-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/or-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/xor-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/signextend" :dir :system) ; brings in ttags
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvashr" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/sbvlt-def" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
;(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ;reduce, for loghead-becomes-bvchop
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/rules3" :dir :system)) ;for logext-of-bvsx
(local (include-book "kestrel/bv/bvsx-rules" :dir :system)) ;needed?

(in-theory (disable ZF-SPEC-THM)) ;bad?

(local (in-theory (disable ACL2::LOGTAIL-OF-ONE-MORE ACL2::LOGTAIL-OF-ONE-LESS ; bad, matches a constant
                           )))

(local (in-theory (enable acl2::slice-becomes-getbit
                          ;logapp ;todo looped
                          )))

(local
 (defthm not-equal-when-<-cheap
   (implies (< y x)
            (not (equal x y)))
   :rule-classes ((:rewrite :backchain-limit-lst (0)))))

;move
(local
 (defthm not-equal-of-bvchop-and-bvchop-when-not-equal-of-bvchop-and-bvchop
   (implies (and (not (equal (acl2::bvchop freesize dst) (acl2::bvchop freesize src)))
                 (<= freesize size)
                 (natp freesize)
                 (natp size))
            (not (equal (acl2::bvchop size dst) (acl2::bvchop size src))))))

;move
(local
 (defthm not-equal-of-bvchop-and-bvchop-when-<-of-bvchop-and-bvchop
  (implies (and (< (acl2::bvchop freesize dst) (acl2::bvchop freesize src))
                (<= freesize size)
                (natp freesize)
                (natp size))
           (not (equal (acl2::bvchop size dst) (acl2::bvchop size src))))))

;move
(local
 (defthm not-equal-of-bvchop-and-bvchop-when-<-of-bvchop-and-bvchop-alt
   (implies (and (< (acl2::bvchop freesize src) (acl2::bvchop freesize dst))
                 (<= freesize size)
                 (natp freesize)
                 (natp size))
            (not (equal (acl2::bvchop size dst) (acl2::bvchop size src))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm x::cf-spec8-becomes-getbit
  (implies (unsigned-byte-p 9 x)
           (equal (cf-spec8 x)
                  (acl2::getbit 8 x)))
  :hints (("Goal" :in-theory (enable cf-spec8))))

(defthm x::cf-spec16-becomes-getbit
  (implies (unsigned-byte-p 17 x)
           (equal (cf-spec16 x)
                  (acl2::getbit 16 x)))
  :hints (("Goal" :in-theory (enable cf-spec16))))

(defthm x::cf-spec32-becomes-getbit
  (implies (unsigned-byte-p 33 x)
           (equal (cf-spec32 x)
                  (acl2::getbit 32 x)))
  :hints (("Goal" :in-theory (enable cf-spec32))))

;; todo: just put the result of this into the alt-def?
;see cf-spec64-becomes-getbit
(defthm x::cf-spec64-becomes-getbit
  (implies (unsigned-byte-p 65 x) ; example; sum of two u64s
           (equal (cf-spec64 x)
                  (acl2::getbit 64 x)))
  :hints (("Goal" :in-theory (enable cf-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A wrapper indicating that the CF functions should be opened when they are an
;; argument of this function.  We want to open the cf-spec functions when they
;; are used for something other than a conditional jump (see conditions.lisp).
;; For example, we want to open the cf-spec functions when they are added to
;; something, such as by ADC.

;; could generalize to mean "open the argument function"
(defund x::open-carry (x) x)

(acl2::def-constant-opener x::open-carry)

(defthm x::open-carry-of-cf-spec8
  (implies (unsigned-byte-p 9 x)
           (equal (x::open-carry (cf-spec8 x))
                  (acl2::getbit 8 x)))
  :hints (("Goal" :in-theory (enable cf-spec8 x::open-carry))))

(defthm x::open-carry-of-cf-spec16
  (implies (unsigned-byte-p 17 x)
           (equal (x::open-carry (cf-spec16 x))
                  (acl2::getbit 16 x)))
  :hints (("Goal" :in-theory (enable cf-spec16 x::open-carry))))

(defthm x::open-carry-of-cf-spec32
  (implies (unsigned-byte-p 33 x)
           (equal (x::open-carry (cf-spec32 x))
                  (acl2::getbit 32 x)))
  :hints (("Goal" :in-theory (enable cf-spec32 x::open-carry))))

;; todo: just put the result of this into the alt-def?
;see cf-spec64-becomes-getbit
(defthm x::open-carry-of-cf-spec64
  (implies (unsigned-byte-p 65 x) ; example; sum of two u64s
           (equal (x::open-carry (cf-spec64 x))
                  (acl2::getbit 64 x)))
  :hints (("Goal" :in-theory (enable cf-spec64 x::open-carry))))

;; Only for Axe
(defthmd x::integerp-of-open-carry
  (equal (integerp (x::open-carry x))
         (integerp x))
  :hints (("Goal" :in-theory (enable x::open-carry))))

(defthmd open-carry-of-rflagsbits->cf
  (equal (x::open-carry (rflagsbits->cf input-rflags))
         (acl2::getbit 0 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->cf x::open-carry rflagsbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These put in some equivalent :logic expressions for the flags (search for "note this" below).

;; We also change the output-rflags to use the :exec version, which calls
;; things like !rflagsbits->cf, instead of the :logic version, because the
;; change-rflagsbits in the :logic version expands to something large and
;; unwieldly.

;; Note that these sub-spec functions are also used to implement comparisons.

;; TODO: The :exec parts are not needed (here and elsewhere):

(local (in-theory (disable (:e tau-system))))

(defthm GPR-SUB-SPEC-1-alt-def
  (equal (GPR-SUB-SPEC-1 dst src input-rflags)
         ;; proposed new body for GPR-SUB-SPEC-1:
         (b*
             ((dst (mbe :logic (n-size 8 dst)
                        :exec dst))
              (src (mbe :logic (n-size 8 src)
                        :exec src))
              (input-rflags
                (mbe :logic (n32 input-rflags)
                     :exec input-rflags))
              (signed-raw-result
                (the (signed-byte 9)
                  (- (the (signed-byte 8)
                       (n08-to-i08 dst))
                     (the (signed-byte 8)
                       (n08-to-i08 src)))))
              (result
                (the (unsigned-byte 8)
                  (n-size 8 signed-raw-result)))
              (cf (mbe :exec (the (unsigned-byte 1)
                               (bool->bit (< dst src)))
                       ;; note this:
                       :logic (sub-cf-spec8 dst src)))
              (pf (mbe :exec (the (unsigned-byte 1)
                               (pf-spec8 result))
                       ;; note this:
                       :logic (sub-pf-spec8 dst src)))
              (af (the (unsigned-byte 1)
                    (sub-af-spec8 dst src)))
              (zf (mbe :exec (the (unsigned-byte 1)
                               (zf-spec result))
                       ;; note this:
                       :logic (sub-zf-spec8 dst src)))
              (sf (mbe :exec (the (unsigned-byte 1)
                               (sf-spec8 result))
                       ;; note this:
                       :logic (sub-sf-spec8 dst src)))
              (of (mbe :exec (the (unsigned-byte 1)
                               (of-spec8 signed-raw-result))
                       ;; note this:
                       :logic (sub-of-spec8 dst src)))
              (output-rflags
                (!rflagsbits->cf
                      cf
                      (!rflagsbits->pf
                        pf
                        (!rflagsbits->af
                          af
                          (!rflagsbits->zf
                            zf
                            (!rflagsbits->sf
                              sf
                              (!rflagsbits->of
                                of input-rflags)))))))
              ;; (output-rflags
              ;;   (mbe :logic (n32 output-rflags)
              ;;        :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags
               undefined-flags)))
  :hints (("Goal" :in-theory (enable* GPR-SUB-SPEC-1
                                      sub-cf-spec8
                                      sub-pf-spec8
                                      sub-zf-spec8
                                      sub-sf-spec8
                                      sub-of-spec8
                                      ZF-SPEC
                                      acl2::bvchop-of-sum-cases
                                      rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that this is also used to implement comparisons
(defthm GPR-SUB-SPEC-2-alt-def
  (equal (GPR-SUB-SPEC-2 dst src input-rflags)
         ;; proposed new body for GPR-SUB-SPEC-2:
         (b*
             ((dst (mbe :logic (n-size 16 dst)
                                :exec dst))
              (src (mbe :logic (n-size 16 src)
                                :exec src))
              (input-rflags
               (mbe :logic (n32 input-rflags)
                    :exec input-rflags))
              (signed-raw-result
               (the (signed-byte 17)
                    (- (the (signed-byte 16)
                            (n16-to-i16 dst))
                       (the (signed-byte 16)
                            (n16-to-i16 src)))))
              (result
               (the (unsigned-byte 16)
                    (n-size 16 signed-raw-result)))
              (cf (mbe :exec (the (unsigned-byte 1)
                                          (bool->bit (< dst src)))
                               :logic (sub-cf-spec16 DST SRC)))
              (pf (mbe :exec (the (unsigned-byte 1)
                                  (pf-spec16 result))
                       :logic (sub-pf-spec16 dst src)))
              (af (the (unsigned-byte 1)
                            (sub-af-spec16 dst src)))
              (zf
               (mbe :exec (the (unsigned-byte 1)
                                (zf-spec result))
                    :logic (sub-zf-spec16 dst src)))
              (sf (mbe :exec (the (unsigned-byte 1)
                                          (sf-spec16 result))
                               :logic (sub-sf-spec16 dst src)))
              (of (mbe :exec
               (the (unsigned-byte 1)
                    (of-spec16 signed-raw-result))
               :logic (sub-of-spec16 dst src)))
              (output-rflags
               (!rflagsbits->cf
                  cf
                  (!rflagsbits->pf
                   pf
                   (!rflagsbits->af
                    af
                    (!rflagsbits->zf
                     zf
                     (!rflagsbits->sf
                      sf
                      (!rflagsbits->of
                       of input-rflags)))))))
              ;; (output-rflags
              ;;  (mbe :logic (n32 output-rflags)
              ;;       :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags
               undefined-flags)))
  :hints (("Goal" :in-theory (enable* GPR-SUB-SPEC-2
                                     sub-cf-spec16
                                     sub-pf-spec16
                                     sub-zf-spec16
                                     sub-sf-spec16
                                     sub-of-spec16
                                     ZF-SPEC
                                     acl2::bvchop-of-sum-cases
                                     rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that this is also used to implement comparisons
;; the difference is in the flags?
(defthm GPR-SUB-SPEC-4-alt-def
  (equal (GPR-SUB-SPEC-4 dst src input-rflags)
         ;; proposed new body for GPR-SUB-SPEC-4:
         (B* ((DST (MBE :LOGIC (N-SIZE 32 DST)
                        :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 32 SRC)
                        :EXEC SRC))
              (INPUT-RFLAGS
               (MBE :LOGIC (N32 INPUT-RFLAGS)
                    :EXEC INPUT-RFLAGS))
              (SIGNED-RAW-RESULT
               (THE (SIGNED-BYTE 33)
                    (- (THE (SIGNED-BYTE 32)
                            (N32-TO-I32 DST))
                       (THE (SIGNED-BYTE 32)
                            (N32-TO-I32 SRC)))))
              (RESULT
               (THE (UNSIGNED-BYTE 32)
                    (N-SIZE 32 SIGNED-RAW-RESULT)))
              (CF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (BOOL->BIT (< DST SRC)))
                       :logic (sub-cf-spec32 DST SRC)))
              (PF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (PF-SPEC32 RESULT))
                       :logic (sub-pf-spec32 dst src)))
              (AF (THE (UNSIGNED-BYTE 1)
                       (SUB-AF-SPEC32 DST SRC)))
              (ZF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (ZF-SPEC RESULT))
                       :logic (sub-zf-spec32 dst src)))
              (SF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (SF-SPEC32 RESULT))
                       :logic (sub-sf-spec32 dst src)))
              (OF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (OF-SPEC32 SIGNED-RAW-RESULT))
                       :logic (sub-of-spec32 dst src)))
              (OUTPUT-RFLAGS
               (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->AF
                    AF
                    (!RFLAGSBITS->ZF
                     ZF
                     (!RFLAGSBITS->SF
                      SF
                      (!RFLAGSBITS->OF
                       OF INPUT-RFLAGS)))))))
              ;; (OUTPUT-RFLAGS
              ;;  (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;       :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS 0))
           (MV RESULT OUTPUT-RFLAGS
               UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* GPR-SUB-SPEC-4
                                      sub-cf-spec32
                                      sub-pf-spec32
                                      sub-zf-spec32
                                      sub-sf-spec32
                                      sub-of-spec32
                                      ZF-SPEC
                                     acl2::bvchop-of-sum-cases
                                     rflag-RoWs-enables))))

;; for rewriting
(defthmd GPR-SUB-SPEC-4-alt-def-better
  (equal (gpr-sub-spec-4 dst src input-rflags)
         (let ((dst (acl2::bvchop 32 dst)) ; drop?
               (src (acl2::bvchop 32 src)) ; drop?
               )
           (MV (acl2::bvchop 32 (- dst src)) ;; (acl2::bvminus 32 dst src) ; todo: put back but this a normal form change
               (!RFLAGSBITS->CF
                (sub-cf-spec32 dst src)
                (!RFLAGSBITS->PF
                 (sub-pf-spec32 dst src)
                 (!RFLAGSBITS->AF
                  (sub-af-spec32 dst src)
                  (!RFLAGSBITS->ZF
                   (sub-zf-spec32 dst src)
                   (!RFLAGSBITS->SF
                    (sub-sf-spec32 dst src)
                    (!RFLAGSBITS->OF
                     (sub-of-spec32 dst src)
                     (acl2::bvchop 32 input-rflags) ; drop the bvchop?
                     ))))))
               0)))
  :hints (("Goal" :in-theory (enable* GPR-SUB-SPEC-4
                                      sub-cf-spec32
                                      sub-pf-spec32
                                      ZF-SPEC
                                      acl2::bvchop-of-sum-cases
                                      acl2::bvminus
                                      rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm GPR-SUB-SPEC-8-alt-def
  (equal (GPR-SUB-SPEC-8 dst src input-rflags)
         ;; proposed new body:
         (B* ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 64 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              (SIGNED-RAW-RESULT
               (THE (SIGNED-BYTE 65)
                    (- (THE (SIGNED-BYTE 64) (N64-TO-I64 DST))
                       (THE (SIGNED-BYTE 64)
                            (N64-TO-I64 SRC)))))
              (RESULT (THE (UNSIGNED-BYTE 64)
                           (N-SIZE 64 SIGNED-RAW-RESULT)))
              (CF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (BOOL->BIT (< DST SRC)))
                       :logic (sub-cf-spec64 DST SRC)))
              (PF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (PF-SPEC64 RESULT))
                       :logic (sub-pf-spec64 dst src)))
              (AF (THE (UNSIGNED-BYTE 1)
                       (SUB-AF-SPEC64 DST SRC)))
              (ZF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (ZF-SPEC RESULT))
                       :logic (sub-zf-spec64 dst src)))
              (SF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (SF-SPEC64 RESULT))
                       :logic (sub-sf-spec64 dst src)))
              (OF (mbe :exec (THE (UNSIGNED-BYTE 1)
                                  (OF-SPEC64 SIGNED-RAW-RESULT))
                       :logic (sub-of-spec64 dst src)))
              (OUTPUT-RFLAGS
               (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->AF
                    AF
                    (!RFLAGSBITS->ZF
                     ZF
                     (!RFLAGSBITS->SF
                      SF
                      (!RFLAGSBITS->OF OF INPUT-RFLAGS)))))))
              ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;                     :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS 0))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* GPR-SUB-SPEC-8
                                     sub-cf-spec64
                                     sub-pf-spec64
                                     sub-zf-spec64
                                     sub-sf-spec64
                                     sub-of-spec64
                                     sf-spec64
                                     ZF-SPEC
                                     ;; ACL2::GETBIT-OF-+ ; rename
                                     ACL2::getbit-of-+
                                     acl2::bvchop-of-sum-cases
                                     ACL2::BVPLUS
                                     ACL2::LOGEXT-CASES
                                     rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The put in bvshl and also improve the handling of rflags. Anything else?

(defthm SAL/SHL-SPEC-8-alt-def
  (equal (sal/shl-spec-8 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst)
                        :exec dst))
              (src (mbe :logic (n-size 6 src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

;                   (raw-result (ash dst src))
;                   (result (the (unsigned-byte 8) (n-size 8 raw-result)))
              (result (acl2::bvshl 8 dst src))

              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32) undefined-flags))

               (case src
                 (0
                  ;; No flags affected.
                  (mv input-rflags 0))

                 (1
                  ;; All flags, but AF, are changed accordingly. AF is
                  ;; undefined.
                  (b* ((cf
                        ;; CF contains the last bit shifted out of the operand.
                        (mbe
                         :logic (part-select
                                 dst
                                 :low 7 ;8-1 ;; (- 8 src)
                                 :width 1)
                         :exec
                         (the (unsigned-byte 1)
                              (logand 1
                                      (the (unsigned-byte 8)
                                           (ash (the (unsigned-byte 8) dst)
                                                7 ;,neg-size-1
                                                ))))))
                       (pf (general-pf-spec 8 result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec 8 result))
                       (of
                        ;; OF is set when the top two bits of the original
                        ;; operand are the same.
                        (b-xor cf
                               (mbe :logic (logbit 7 ;8-1
                                                   result)
                                    :exec (the (unsigned-byte 1)
                                               (logand 1
                                                       (the (unsigned-byte 1)
                                                            (ash (the (unsigned-byte 8)
                                                                      result)
                                                                 7 ;,neg-size-1
                                                                 )))))))

                       (output-rflags (!rflagsBits->cf
                                        cf
                                        (!rflagsBits->pf
                                          pf
                                          (!rflagsBits->zf
                                            zf
                                            (!rflagsBits->sf
                                              sf
                                              (!rflagsBits->of
                                                of
                                                input-rflags))))))

                       (undefined-flags (!rflagsBits->af 1 0)))

                    (mv output-rflags undefined-flags)))

                 (otherwise
                  (if (<= 8 src)
                      ;; CF is undefined for SHL and SHR where the src
                      ;; is >= the width of the destination operand. OF and
                      ;; AF are also undefined.  Other flags are affected as
                      ;; usual.
                      (b* (;; CF is undefined.
                           (pf (general-pf-spec 8 result))
                           ;; AF is undefined.
                           (zf (zf-spec result))
                           (sf (general-sf-spec 8 result))
                           ;; OF is undefined.

                           (output-rflags (!rflagsBits->pf
                                            pf
                                            (!rflagsBits->zf
                                              zf
                                              (!rflagsBits->sf
                                                sf
                                                input-rflags))))

                           (undefined-flags (!rflagsBits->cf
                                              1
                                              (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                  1 0)))))
                        (mv output-rflags undefined-flags))

                    ;; OF and AF are undefined. Other flags are affected as
                    ;; usual.
                    (b* ((cf
                          ;; CF contains the last bit shifted out
                          ;; of the operand.
                          (part-select dst :low (- 8 src) :width 1))
                         (pf (general-pf-spec 8 result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec 8 result))
                         ;; OF is undefined.

                         (output-rflags (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))

                         (undefined-flags (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0))))
                      (mv output-rflags undefined-flags))))))

              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d* (ACL2::BVSHL
                                   sal/shl-spec-8
                                   SF-SPEC8
                                   PF-SPEC8
                                   ash
                                   acl2::bvcat
                                   rflag-RoWs-enables)
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-16-alt-def
  (equal (sal/shl-spec-16 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst)
                        :exec dst))
              (src (mbe :logic (n-size 6 src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

;                   (raw-result (ash dst src))
;                   (result (the (unsigned-byte 16) (n-size 16 raw-result)))
              (result (acl2::bvshl 16 dst src))

              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32) undefined-flags))

               (case src
                 (0
                  ;; No flags affected.
                  (mv input-rflags 0))

                 (1
                  ;; All flags, but AF, are changed accordingly. AF is
                  ;; undefined.
                  (b* ((cf
                        ;; CF contains the last bit shifted out of the operand.
                        (mbe
                         :logic (part-select
                                 dst
                                 :low 15 ;16-1 ;; (- 16 src)
                                 :width 1)
                         :exec
                         (the (unsigned-byte 1)
                              (logand 1
                                      (the (unsigned-byte 16)
                                           (ash (the (unsigned-byte 16) dst)
                                                15 ;,neg-size-1
                                                ))))))
                       (pf (general-pf-spec 16 result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec 16 result))
                       (of
                        ;; OF is set when the top two bits of the original
                        ;; operand are the same.
                        (b-xor cf
                               (mbe :logic (logbit 15 ;16-1
                                                   result)
                                    :exec (the (unsigned-byte 1)
                                               (logand 1
                                                       (the (unsigned-byte 1)
                                                            (ash (the (unsigned-byte 16)
                                                                      result)
                                                                 15 ;,neg-size-1
                                                                 )))))))

                       (output-rflags (!rflagsBits->cf
                                                 cf
                                                 (!rflagsBits->pf
                                                  pf
                                                  (!rflagsBits->zf
                                                   zf
                                                   (!rflagsBits->sf
                                                    sf
                                                    (!rflagsBits->of
                                                     of
                                                     input-rflags))))))

                       (undefined-flags (!rflagsBits->af 1 0)))

                    (mv output-rflags undefined-flags)))

                 (otherwise
                  (if (<= 16 src)
                      ;; CF is undefined for SHL and SHR where the src
                      ;; is >= the width of the destination operand. OF and
                      ;; AF are also undefined.  Other flags are affected as
                      ;; usual.
                      (b* (;; CF is undefined.
                           (pf (general-pf-spec 16 result))
                           ;; AF is undefined.
                           (zf (zf-spec result))
                           (sf (general-sf-spec 16 result))
                           ;; OF is undefined.

                           (output-rflags (!rflagsBits->pf
                                                     pf
                                                     (!rflagsBits->zf
                                                      zf
                                                      (!rflagsBits->sf
                                                       sf
                                                       input-rflags))))

                           (undefined-flags (!rflagsBits->cf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   (!rflagsBits->of
                                                    1 0)))))
                        (mv output-rflags undefined-flags))

                    ;; OF and AF are undefined. Other flags are affected as
                    ;; usual.
                    (b* ((cf
                          ;; CF contains the last bit shifted out
                          ;; of the operand.
                          (part-select dst :low (- 16 src) :width 1))
                         (pf (general-pf-spec 16 result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec 16 result))
                         ;; OF is undefined.

                         (output-rflags (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))

                         (undefined-flags (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0))))
                      (mv output-rflags undefined-flags))))))

              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d* (ACL2::BVSHL
                                   sal/shl-spec-16
                                   SF-SPEC16
                                   PF-SPEC16
                                   ash
                                   acl2::bvcat
                                   rflag-RoWs-enables
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-32-alt-def
  (equal (sal/shl-spec-32 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 32 dst)
                        :exec dst))
              (src (mbe :logic (n-size 6 src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

;                   (raw-result (ash dst src))
;                   (result (the (unsigned-byte 32) (n-size 32 raw-result)))
              (result (acl2::bvshl 32 dst src))

              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32) undefined-flags))

               (case src
                 (0
                  ;; No flags affected.
                  (mv input-rflags 0))

                 (1
                  ;; All flags, but AF, are changed accordingly. AF is
                  ;; undefined.
                  (b* ((cf
                        ;; CF contains the last bit shifted out of the operand.
                        (mbe
                         :logic (part-select
                                 dst
                                 :low 31 ;32-1 ;; (- 32 src)
                                 :width 1)
                         :exec
                         (the (unsigned-byte 1)
                              (logand 1
                                      (the (unsigned-byte 32)
                                           (ash (the (unsigned-byte 32) dst)
                                                31 ;,neg-size-1
                                                ))))))
                       (pf (general-pf-spec 32 result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec 32 result))
                       (of
                        ;; OF is set when the top two bits of the original
                        ;; operand are the same.
                        (b-xor cf
                               (mbe :logic (logbit 31 ;32-1
                                                   result)
                                    :exec (the (unsigned-byte 1)
                                               (logand 1
                                                       (the (unsigned-byte 1)
                                                            (ash (the (unsigned-byte 32)
                                                                      result)
                                                                 31 ;,neg-size-1
                                                                 )))))))

                       (output-rflags (!rflagsBits->cf
                                        cf
                                        (!rflagsBits->pf
                                          pf
                                          (!rflagsBits->zf
                                            zf
                                            (!rflagsBits->sf
                                              sf
                                              (!rflagsBits->of
                                                of
                                                input-rflags))))))

                       (undefined-flags (!rflagsBits->af 1 0)))

                    (mv output-rflags undefined-flags)))

                 (otherwise
                  (if (<= 32 src)
                      ;; CF is undefined for SHL and SHR where the src
                      ;; is >= the width of the destination operand. OF and
                      ;; AF are also undefined.  Other flags are affected as
                      ;; usual.
                      (b* (;; CF is undefined.
                           (pf (general-pf-spec 32 result))
                           ;; AF is undefined.
                           (zf (zf-spec result))
                           (sf (general-sf-spec 32 result))
                           ;; OF is undefined.

                           (output-rflags (!rflagsBits->pf
                                                     pf
                                                     (!rflagsBits->zf
                                                      zf
                                                      (!rflagsBits->sf
                                                       sf
                                                       input-rflags))))

                           (undefined-flags (!rflagsBits->cf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   (!rflagsBits->of
                                                    1 0)))))
                        (mv output-rflags undefined-flags))

                    ;; OF and AF are undefined. Other flags are affected as
                    ;; usual.
                    (b* ((cf
                          ;; CF contains the last bit shifted out
                          ;; of the operand.
                          (part-select dst :low (- 32 src) :width 1))
                         (pf (general-pf-spec 32 result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec 32 result))
                         ;; OF is undefined.

                         (output-rflags (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))

                         (undefined-flags (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0))))
                      (mv output-rflags undefined-flags))))))

              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d* (ACL2::BVSHL
                                   sal/shl-spec-32
                                   SF-SPEC32
                                   PF-SPEC32
                                   ash
                                   acl2::bvcat
                                   rflag-RoWs-enables
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-64-alt-def
  (equal (sal/shl-spec-64 dst src input-rflags)
         (B*
                 ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
                  (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
                  (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                     :EXEC INPUT-RFLAGS))
                  ;; (RAW-RESULT (ASH DST SRC))
                  ;; (RESULT (THE (UNSIGNED-BYTE 64)
                  ;;              (N-SIZE 64 RAW-RESULT)))
                  (result (acl2::bvshl 64 dst src))
                  ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
                       (THE (UNSIGNED-BYTE 32)
                            UNDEFINED-FLAGS))
                   (CASE
                    SRC (0 (MV INPUT-RFLAGS 0))
                    (1
                     (B*
                      ((CF
                        (MBE
                          :LOGIC (PART-SELECT DST :LOW 63 :WIDTH 1)
                          :EXEC
                          (THE (UNSIGNED-BYTE 1)
                               (LOGAND 1
                                       (THE (UNSIGNED-BYTE 64)
                                            (ASH (THE (UNSIGNED-BYTE 64) DST)
                                                 -63))))))
                       (PF (GENERAL-PF-SPEC 64 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 64 RESULT))
                       (OF
                        (B-XOR
                         CF
                         (MBE
                          :LOGIC (LOGBIT 63 RESULT)
                          :EXEC
                          (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND 1
                                    (THE (UNSIGNED-BYTE 1)
                                         (ASH (THE (UNSIGNED-BYTE 64) RESULT)
                                              -63)))))))
                       (OUTPUT-RFLAGS
                        (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
                       (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
                      (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                    (OTHERWISE
                     (IF
                      (<= 64 SRC)
                      (B*
                       ((PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->CF
                                1
                                (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                      (B*
                       ((CF (PART-SELECT DST
                                         :LOW (- 64 SRC)
                                         :WIDTH 1))
                        (PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                  ;;                     :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (e/d* (ACL2::BVSHL
                                   sal/shl-spec-64
                                   SF-SPEC64
                                   PF-SPEC64
                                   ash
                                   acl2::bvcat
                                   rflag-RoWs-enables
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These put in bvshr and change the handling of rflags.  Anything else?

(defthm SHR-SPEC-8-alt-def
  (equal (SHR-SPEC-8 dst src input-rflags)
         (B*
                 ((DST (MBE :LOGIC (N-SIZE 8 DST) :EXEC DST))
                  (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
                  (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                     :EXEC INPUT-RFLAGS))
                  ;; (NEG-SRC (THE (SIGNED-BYTE 9) (- SRC)))
                  ;; (RAW-RESULT (THE (UNSIGNED-BYTE 8)
                  ;;                  (ASH (THE (UNSIGNED-BYTE 8) DST)
                  ;;                       (THE (SIGNED-BYTE 9) NEG-SRC))))
                  ;; (RESULT (THE (UNSIGNED-BYTE 8)
                  ;;              (N-SIZE 8 RAW-RESULT)))
                  (result (acl2::bvshr 8 dst src))
                  ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
                       (THE (UNSIGNED-BYTE 32)
                            UNDEFINED-FLAGS))
                   (CASE
                    SRC (0 (MV INPUT-RFLAGS 0))
                    (1
                     (B*
                      ((CF
                        (MBE
                         :LOGIC (PART-SELECT DST :LOW 0 :WIDTH 1)
                         :EXEC (THE (UNSIGNED-BYTE 1)
                                    (LOGAND 1 (THE (UNSIGNED-BYTE 8) DST)))))
                       (PF (GENERAL-PF-SPEC 8 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 8 RESULT))
                       (OF
                        (MBE
                           :LOGIC (PART-SELECT DST :LOW 7 :WIDTH 1)
                           :EXEC (THE (UNSIGNED-BYTE 1)
                                      (ASH (THE (UNSIGNED-BYTE 8) DST) -7))))
                       (OUTPUT-RFLAGS
                        (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
                       (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
                                             (!RFLAGSBITS->AF 1 0))))
                      (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                    (OTHERWISE
                     (IF
                      (<= 8 SRC)
                      (B*
                       ((PF (GENERAL-PF-SPEC 8 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 8 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->CF
                               1
                               (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                      (B*
                       ((CF
                         (MBE
                          :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT (THE (SIGNED-BYTE 8)
                                       (- 1 (THE (UNSIGNED-BYTE 8) SRC)))))
                           (THE
                             (UNSIGNED-BYTE 1)
                             (LOGAND
                                  1
                                  (THE (UNSIGNED-BYTE 8)
                                       (ASH (THE (UNSIGNED-BYTE 8) DST)
                                            (THE (SIGNED-BYTE 8) SHFT))))))))
                        (PF (GENERAL-PF-SPEC 8 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 8 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                  ;;                     :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* SHR-SPEC-8
                                     ACL2::BVSHR
                                     acl2::slice
                                     rflag-RoWs-enables))))

(defthm SHR-SPEC-16-alt-def
  (equal (SHR-SPEC-16 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 16 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;; (NEG-SRC (THE (SIGNED-BYTE 17) (- SRC)))
              ;; (RAW-RESULT (THE (UNSIGNED-BYTE 16)
              ;;                  (ASH (THE (UNSIGNED-BYTE 16) DST)
              ;;                       (THE (SIGNED-BYTE 17) NEG-SRC))))
              ;; (RESULT (THE (UNSIGNED-BYTE 16)
              ;;              (N-SIZE 16 RAW-RESULT)))
              (result (acl2::bvshr 16 dst src))
              ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
                   (THE (UNSIGNED-BYTE 32)
                        UNDEFINED-FLAGS))
               (CASE
                 SRC (0 (MV INPUT-RFLAGS 0))
                 (1
                  (B*
                      ((CF
                        (MBE :LOGIC (PART-SELECT DST :LOW 0 :WIDTH 1)
                             :EXEC
                             (THE (UNSIGNED-BYTE 1)
                                  (LOGAND 1 (THE (UNSIGNED-BYTE 16) DST)))))
                       (PF (GENERAL-PF-SPEC 16 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 16 RESULT))
                       (OF (MBE :LOGIC (PART-SELECT DST :LOW 15 :WIDTH 1)
                                :EXEC (THE (UNSIGNED-BYTE 1)
                                           (ASH (THE (UNSIGNED-BYTE 16) DST)
                                                -15))))
                       (OUTPUT-RFLAGS
                        (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
                       (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
                                             (!RFLAGSBITS->AF 1 0))))
                    (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                 (OTHERWISE
                  (IF
                   (<= 16 SRC)
                   (B*
                       ((PF (GENERAL-PF-SPEC 16 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 16 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                   (B*
                       ((CF
                         (MBE
                          :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT (THE (SIGNED-BYTE 16)
                                       (- 1 (THE (UNSIGNED-BYTE 16) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                             1
                             (THE (UNSIGNED-BYTE 16)
                                  (ASH (THE (UNSIGNED-BYTE 16) DST)
                                       (THE (SIGNED-BYTE 16) SHFT))))))))
                        (PF (GENERAL-PF-SPEC 16 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 16 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;                     :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* SHR-SPEC-16
                                     ACL2::BVSHR
                                     acl2::slice
                                     rflag-RoWs-enables))))

(defthm SHR-SPEC-32-alt-def
  (equal (SHR-SPEC-32 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 32 DST)
                                :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC)
                                :EXEC SRC))
              (INPUT-RFLAGS
               (MBE :LOGIC (N32 INPUT-RFLAGS)
                    :EXEC INPUT-RFLAGS))
              ;;(NEG-SRC (THE (SIGNED-BYTE 33) (- SRC)))
              ;; (RAW-RESULT
              ;;  (THE (UNSIGNED-BYTE 32)
              ;;       (ASH (THE (UNSIGNED-BYTE 32) DST)
              ;;            (THE (SIGNED-BYTE 33)
              ;;                 NEG-SRC))))
              ;; (RESULT
              ;;  (THE (UNSIGNED-BYTE 32)
              ;;       (N-SIZE 32 RAW-RESULT)))
              (result (acl2::bvshr 32 dst src))
              ((MV (THE (UNSIGNED-BYTE 32)
                        OUTPUT-RFLAGS)
                   (THE (UNSIGNED-BYTE 32)
                        UNDEFINED-FLAGS))
               (CASE
                 SRC
                 (0 (MV INPUT-RFLAGS 0))
                 (1
                  (B*
                      ((CF
                        (MBE
                         :LOGIC (ACL2::PART-SELECT DST
                                                   :LOW 0
                                                   :WIDTH 1)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 1)
                          (LOGAND 1
                                  (THE (UNSIGNED-BYTE 32) DST)))))
                       (PF (GENERAL-PF-SPEC 32 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF
                        (GENERAL-SF-SPEC 32 RESULT))
                       (OF
                        (MBE
                         :LOGIC (ACL2::PART-SELECT DST
                                                   :LOW 31
                                                   :WIDTH 1)
                         :EXEC (THE (UNSIGNED-BYTE 1)
                                    (ASH (THE (UNSIGNED-BYTE 32) DST)
                                         -31))))
                       (OUTPUT-RFLAGS
                        (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF
                               OF INPUT-RFLAGS))))))
                       (UNDEFINED-FLAGS
                        (THE (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->AF 1 0))))
                    (MV OUTPUT-RFLAGS
                        UNDEFINED-FLAGS)))
                 (OTHERWISE
                  (IF
                   (<= 32 SRC)
                   (B*
                       ((PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF
                         (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF INPUT-RFLAGS))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF
                             1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS
                         UNDEFINED-FLAGS))
                   (B*
                       ((CF
                         (MBE
                          :LOGIC (ACL2::PART-SELECT DST
                                                    :LOW (1- SRC)
                                                    :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT
                             (THE (SIGNED-BYTE 32)
                                  (- 1
                                     (THE (UNSIGNED-BYTE 32) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                             1
                             (THE (UNSIGNED-BYTE 32)
                                  (ASH (THE (UNSIGNED-BYTE 32) DST)
                                       (THE (SIGNED-BYTE 32)
                                            SHFT))))))))
                        (PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF
                         (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF
                               SF INPUT-RFLAGS)))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->AF
                                     1 (!RFLAGSBITS->OF 1 0))))
                     (MV OUTPUT-RFLAGS
                         UNDEFINED-FLAGS))))))
              ;; (OUTPUT-RFLAGS
              ;;  (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;       :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS
               (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS
               UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* SHR-SPEC-32
                                     ACL2::BVSHR
                                     acl2::slice
                                     rflag-RoWs-enables))))

(defthm SHR-SPEC-64-alt-def
  (equal (SHR-SPEC-64 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;; (NEG-SRC (THE (SIGNED-BYTE 65) (- SRC)))
              ;; (RAW-RESULT (THE (UNSIGNED-BYTE 64)
              ;;                  (ASH (THE (UNSIGNED-BYTE 64) DST)
              ;;                       (THE (SIGNED-BYTE 65) NEG-SRC))))
              ;; (RESULT (THE (UNSIGNED-BYTE 64)
              ;;              (N-SIZE 64 RAW-RESULT)))
              (result (acl2::bvshr 64 dst src))
              ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
                   (THE (UNSIGNED-BYTE 32)
                        UNDEFINED-FLAGS))
               (CASE
                 SRC (0 (MV INPUT-RFLAGS 0))
                 (1
                  (B*
                      ((CF
                        (MBE :LOGIC (PART-SELECT DST :LOW 0 :WIDTH 1)
                             :EXEC
                             (THE (UNSIGNED-BYTE 1)
                                  (LOGAND 1 (THE (UNSIGNED-BYTE 64) DST)))))
                       (PF (GENERAL-PF-SPEC 64 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 64 RESULT))
                       (OF (MBE :LOGIC (PART-SELECT DST :LOW 63 :WIDTH 1)
                                :EXEC (THE (UNSIGNED-BYTE 1)
                                           (ASH (THE (UNSIGNED-BYTE 64) DST)
                                                -63))))
                       (OUTPUT-RFLAGS
                        (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
                       (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
                                             (!RFLAGSBITS->AF 1 0))))
                    (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                 (OTHERWISE
                  (IF
                   (<= 64 SRC)
                   (B*
                       ((PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                   (B*
                       ((CF
                         (MBE
                          :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT (THE (SIGNED-BYTE 64)
                                       (- 1 (THE (UNSIGNED-BYTE 64) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                             1
                             (THE (UNSIGNED-BYTE 64)
                                  (ASH (THE (UNSIGNED-BYTE 64) DST)
                                       (THE (SIGNED-BYTE 64) SHFT))))))))
                        (PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))
                        (UNDEFINED-FLAGS
                         (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;                     :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* SHR-SPEC-64
                                     ACL2::BVSHR
                                     acl2::slice
                                     rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These use bvor for the result and also change the handling of rflagsbits

(defthm GPR-OR-SPEC-1-alt-def
  (equal (GPR-OR-SPEC-1 dst src input-rflags)
         (b*
             ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 8 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ;; ((the (unsigned-byte 8) result)
              ;;  (mbe :logic (part-select (logior dst src)
              ;;                           :low 0
              ;;                           :width 8)
              ;;       :exec (logior dst src)))
              (result (acl2::bvor 8 dst src)) ; note this
              (cf 0)
              (pf (the (unsigned-byte 1)
                       (pf-spec8 result)))
              (zf (the (unsigned-byte 1)
                       (zf-spec result)))
              (sf (the (unsigned-byte 1)
                       (sf-spec8 result)))
              (of 0)
              (output-rflags
               (!rflagsbits->cf
                  cf
                  (!rflagsbits->pf
                   pf
                   (!rflagsbits->zf
                    zf
                    (!rflagsbits->sf
                     sf
                     (!rflagsbits->of of input-rflags))))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* GPR-OR-SPEC-1
                                     ACL2::BVOR
                                     rflag-RoWs-enables))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-2-alt-def
  (equal (GPR-OR-SPEC-2 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 16 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 16 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;; ((THE (UNSIGNED-BYTE 16) RESULT)
              ;;  (MBE :LOGIC (PART-SELECT (LOGIOR DST SRC)
              ;;                           :LOW 0
              ;;                           :WIDTH 16)
              ;;       :EXEC (LOGIOR DST SRC)))
              (result (acl2::bvor 16 dst src))
              (CF 0)
              (PF (THE (UNSIGNED-BYTE 1)
                       (PF-SPEC16 RESULT)))
              (ZF (THE (UNSIGNED-BYTE 1)
                       (ZF-SPEC RESULT)))
              (SF (THE (UNSIGNED-BYTE 1)
                       (SF-SPEC16 RESULT)))
              (OF 0)
              (OUTPUT-RFLAGS
               (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->ZF
                    ZF
                    (!RFLAGSBITS->SF
                     SF
                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
              ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;                     :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
         )
  :hints (("Goal" :in-theory (enable* GPR-OR-SPEC-2
                                      ACL2::BVOR
                                      rflag-RoWs-enables))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-4-alt-def
  (equal (GPR-OR-SPEC-4 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 32 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 32 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;; ((THE (UNSIGNED-BYTE 32) RESULT)
              ;;  (MBE :LOGIC (PART-SELECT (LOGIOR DST SRC)
              ;;                           :LOW 0
              ;;                           :WIDTH 32)
              ;;       :EXEC (LOGIOR DST SRC)))
              (result (acl2::bvor 32 dst src))
              (CF 0)
              (PF (THE (UNSIGNED-BYTE 1)
                       (PF-SPEC32 RESULT)))
              (ZF (THE (UNSIGNED-BYTE 1)
                       (ZF-SPEC RESULT)))
              (SF (THE (UNSIGNED-BYTE 1)
                       (SF-SPEC32 RESULT)))
              (OF 0)
              (OUTPUT-RFLAGS
               (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->ZF
                    ZF
                    (!RFLAGSBITS->SF
                     SF
                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
              ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
              ;;                     :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable* GPR-OR-SPEC-4
                                      ACL2::BVOR
                                      rflag-RoWs-enables))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-8-alt-def
  (equal (GPR-OR-SPEC-8 dst src input-rflags)
         (B*
                 ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
                  (SRC (MBE :LOGIC (N-SIZE 64 SRC) :EXEC SRC))
                  (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                     :EXEC INPUT-RFLAGS))
                  ;; ((THE (UNSIGNED-BYTE 64) RESULT)
                  ;;  (MBE :LOGIC (PART-SELECT (LOGIOR DST SRC)
                  ;;                           :LOW 0
                  ;;                           :WIDTH 64)
                  ;;       :EXEC (LOGIOR DST SRC)))
                  (result (acl2::bvor 64 dst src))
                  (CF 0)
                  (PF (THE (UNSIGNED-BYTE 1)
                           (PF-SPEC64 RESULT)))
                  (ZF (THE (UNSIGNED-BYTE 1)
                           (ZF-SPEC RESULT)))
                  (SF (THE (UNSIGNED-BYTE 1)
                           (SF-SPEC64 RESULT)))
                  (OF 0)
                  (OUTPUT-RFLAGS
                   (!RFLAGSBITS->CF
                      CF
                      (!RFLAGSBITS->PF
                           PF
                           (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))
                  ;; (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                  ;;                     :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
         )
  :hints (("Goal" :in-theory (enable* GPR-OR-SPEC-8
                                      ACL2::BVOR
                                      rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;move and gen
;; (defthm bvchop-of-logext-when-<
;;   (equal (ACL2::BVCHOP 8 (LOGEXT 7 x))
;;          (acl2::bvcat 1 (acl2::getbit 6 x) 7 x)))

;todo: rule for (ACL2::BVCHOP 8 (LOGEXT 7 x)) when top bit is 1

;; Changes from the original:
;; 1. Improve how RESULT is calculated.
;; 2. Improve flag computation by preferring the :exec part (!rflagsbits-XXX) to the logic part (change-rflagsbits), since the translation of change-rflagsbits is unwieldy.
;; 3. Get rid of unnecessary calls of THE (not needed for logical reasoning).
;; 3. Get rid of unnecessary calls of n32.
;; todo: these have gross case splits for shift amounts that are too large
(defthm SaR-SPEC-8-alt-def
  (equal (SaR-SPEC-8 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 6 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ;; (neg-src (the (signed-byte 9) (- src)))
              ;; (raw-result-not-sign-extended (the (unsigned-byte 8)
              ;;                                    (ash (the (unsigned-byte 8) dst)
              ;;                                         (the (signed-byte 9) neg-src))))
              ;; (raw-result (if (eql (mbe :logic (logbit 7 dst)
              ;;                           :exec (the (unsigned-byte 1)
              ;;                                      (ash (the (unsigned-byte 8) dst) -7)))
              ;;                      1)
              ;;                 (loghead 8
              ;;                          (ash (mbe :logic (logext 8 dst)
              ;;                                    :exec (fast-logext 8 dst))
              ;;                               neg-src))
              ;;               raw-result-not-sign-extended))
              ;; (result (mbe :logic (n-size 8 raw-result)
              ;;              :exec raw-result))
              (result (if (< (ACL2::BVCHOP 6 SRC) 8)
                          (acl2::bvashr 8 dst src)
                        (ACL2::REPEATBIT 8 (ACL2::GETBIT 7 DST))))
              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32)
                     undefined-flags))
               (case src
                 (0 (mv input-rflags 0))
                 (1 (b* ((cf (mbe :logic (part-select dst :low 0 :width 1)
                                  :exec (the (unsigned-byte 1)
                                          (logand 1 (the (unsigned-byte 8) dst)))))
                         (pf (general-pf-spec 8 result))
                         (zf (zf-spec result))
                         (sf (general-sf-spec 8 result))
                         (of 0)
                         (output-rflags (!rflagsbits->cf cf
                                                         (!rflagsbits->pf pf
                                                                          (!rflagsbits->zf zf
                                                                                           (!rflagsbits->sf sf
                                                                                                            (!rflagsbits->of of input-rflags))))))
                         (undefined-flags (the (unsigned-byte 32)
                                            (!rflagsbits->af 1 0))))
                      (mv output-rflags undefined-flags)))
                 (otherwise (b* ((cf (if (<= 8 src)
                                         (mbe :logic (part-select dst :low 7 :width 1)
                                              :exec
                                              (let* ((shft (the (signed-byte 8) -7)))
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte 8) dst)
                                                       (the (signed-byte 8) shft)))))
                                       (mbe :logic
                                            (part-select dst :low (1- src) :width 1)
                                            :exec
                                            (let* ((shft (the (signed-byte 8)
                                                           (- 1 (the (unsigned-byte 8) src)))))
                                              (the (unsigned-byte 1)
                                                (logand 1
                                                        (the (unsigned-byte 8)
                                                          (ash (the (unsigned-byte 8) dst)
                                                               (the (signed-byte 8) shft)))))))))
                                 (pf (general-pf-spec 8 result))
                                 (zf (zf-spec result))
                                 (sf (general-sf-spec 8 result))
                                 (output-rflags (!rflagsbits->cf cf
                                                                 (!rflagsbits->pf pf
                                                                                  (!rflagsbits->zf zf
                                                                                                   (!rflagsbits->sf sf input-rflags)))))
                                 (undefined-flags (!rflagsbits->af 1 (!rflagsbits->of 1 0))))
                              (mv output-rflags undefined-flags)))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              ;; (undefined-flags (mbe :logic (n32 undefined-flags)
              ;;                       :exec undefined-flags))
              )
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d* (SaR-SPEC-8
                                    ACL2::BVaSHR
                                    ACL2::BVSX-REWRITE ;acl2::bvsx loops with ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE
                                    ACL2::BVSHR
                                    acl2::bvcat
;ACL2::LOGTAIL-OF-BVCHOP-BECOMES-SLICE
;ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                    acl2::slice ; loops with ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE
;acl2::logext-cases ;bad
                                    ACL2::BVCHOP-OF-LOGTAIL
;RFLAGSBITS
                                    zf-spec
;PF-SPEC8

;logapp ; slow
                                    logext
                                    rflag-RoWs-enables)
                                   (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

;; See comment on SaR-SPEC-8-alt-def.
(defthm SaR-SPEC-16-alt-def
  (equal (SaR-SPEC-16 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst) :exec dst))
              (src (mbe :logic (n-size 6 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ;; (neg-src (the (signed-byte 17) (- src)))
              ;; (raw-result-not-sign-extended (the (unsigned-byte 16)
              ;;                                 (ash (the (unsigned-byte 16) dst)
              ;;                                      (the (signed-byte 17) neg-src))))
              ;; (raw-result (if (eql (mbe :logic (logbit 15 dst)
              ;;                           :exec (the (unsigned-byte 1)
              ;;                                   (ash (the (unsigned-byte 16) dst) -15)))
              ;;                      1)
              ;;                 (loghead 16
              ;;                          (ash (mbe :logic (logext 16 dst)
              ;;                                    :exec (fast-logext 16 dst))
              ;;                               neg-src))
              ;;               raw-result-not-sign-extended))
              ;; (result (mbe :logic (n-size 16 raw-result)
              ;;              :exec raw-result))
              (result (if (< (ACL2::BVCHOP 6 SRC) 16)
                              (acl2::bvashr 16 dst src)
                        (ACL2::REPEATBIT 16 (ACL2::GETBIT 15 DST))))
              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32)
                     undefined-flags))
               (case src
                 (0 (mv input-rflags 0))
                 (1 (b* ((cf (mbe :logic (part-select dst :low 0 :width 1)
                                  :exec (the (unsigned-byte 1)
                                          (logand 1 (the (unsigned-byte 16) dst)))))
                         (pf (general-pf-spec 16 result))
                         (zf (zf-spec result))
                         (sf (general-sf-spec 16 result))
                         (of 0)
                         (output-rflags (!rflagsbits->cf cf
                                                                      (!rflagsbits->pf pf
                                                                                       (!rflagsbits->zf zf
                                                                                                        (!rflagsbits->sf sf
                                                                                                                         (!rflagsbits->of of input-rflags))))))
                         (undefined-flags (the (unsigned-byte 32)
                                            (!rflagsbits->af 1 0))))
                      (mv output-rflags undefined-flags)))
                 (otherwise (b* ((cf (if (<= 16 src)
                                         (mbe :logic
                                              (part-select dst :low 15 :width 1)
                                              :exec
                                              (let* ((shft (the (signed-byte 16) -15)))
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte 16) dst)
                                                       (the (signed-byte 16) shft)))))
                                       (mbe :logic
                                            (part-select dst :low (1- src) :width 1)
                                            :exec
                                            (let* ((shft (the (signed-byte 16)
                                                           (- 1 (the (unsigned-byte 16) src)))))
                                              (the (unsigned-byte 1)
                                                (logand 1
                                                        (the (unsigned-byte 16)
                                                          (ash (the (unsigned-byte 16) dst)
                                                               (the (signed-byte 16) shft)))))))))
                                 (pf (general-pf-spec 16 result))
                                 (zf (zf-spec result))
                                 (sf (general-sf-spec 16 result))
                                 (output-rflags (!rflagsbits->cf cf
                                                                              (!rflagsbits->pf pf
                                                                                               (!rflagsbits->zf zf
                                                                                                                (!rflagsbits->sf sf input-rflags)))))
                                 (undefined-flags (!rflagsbits->af 1 (!rflagsbits->of 1 0))))
                              (mv output-rflags undefined-flags)))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              ;; (undefined-flags (mbe :logic (n32 undefined-flags)
              ;;                       :exec undefined-flags))
              )
           (mv result output-rflags undefined-flags))


         )
  :hints (("Goal" :in-theory (e/d* (SaR-SPEC-16
                                   ACL2::BVaSHR
                                   ACL2::BVSX-REWRITE
                                   ACL2::BVSHR
                                   acl2::bvcat
                                   acl2::slice
                                   ACL2::BVCHOP-OF-LOGTAIL
                                   ;;RFLAGSBITS
                                   zf-spec
                                   logext
                                   rflag-RoWs-enables)
                                  (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

;; See comment on SaR-SPEC-8-alt-def.
(defthm SaR-SPEC-32-alt-def
  (equal (SaR-SPEC-32 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 32 dst) :exec dst))
              (src (mbe :logic (n-size 6 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ;; (neg-src (the (signed-byte 33) (- src)))
              ;; (raw-result-not-sign-extended (the (unsigned-byte 32)
              ;;                                    (ash (the (unsigned-byte 32) dst)
              ;;                                         (the (signed-byte 33) neg-src))))
              ;; (raw-result (if (eql (mbe :logic (logbit 31 dst)
              ;;                           :exec (the (unsigned-byte 1)
              ;;                                      (ash (the (unsigned-byte 32) dst) -31)))
              ;;                      1)
              ;;                 (loghead 32
              ;;                          (ash (mbe :logic (logext 32 dst)
              ;;                                    :exec (fast-logext 32 dst))
              ;;                               neg-src))
              ;;               raw-result-not-sign-extended))
              ;; (result (mbe :logic (n-size 32 raw-result)
              ;;              :exec raw-result))
              (result (if (< (ACL2::BVCHOP 6 SRC) 32)
                          (acl2::bvashr 32 dst src)
                        (ACL2::REPEATBIT 32 (ACL2::GETBIT 31 DST))))
              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32)
                     undefined-flags))
               (case src
                 (0 (mv input-rflags 0))
                 (1 (b* ((cf (mbe :logic (part-select dst :low 0 :width 1)
                                  :exec (the (unsigned-byte 1)
                                          (logand 1 (the (unsigned-byte 32) dst)))))
                         (pf (general-pf-spec 32 result))
                         (zf (zf-spec result))
                         (sf (general-sf-spec 32 result))
                         (of 0)
                         (output-rflags (!rflagsbits->cf cf
                                                         (!rflagsbits->pf pf
                                                                          (!rflagsbits->zf zf
                                                                                           (!rflagsbits->sf sf
                                                                                                            (!rflagsbits->of of input-rflags))))))
                         (undefined-flags (the (unsigned-byte 32)
                                            (!rflagsbits->af 1 0))))
                      (mv output-rflags undefined-flags)))
                 (otherwise (b* ((cf (if (<= 32 src)
                                         (mbe :logic
                                              (part-select dst :low 31 :width 1)
                                              :exec
                                              (let* ((shft (the (signed-byte 32) -31)))
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte 32) dst)
                                                       (the (signed-byte 32) shft)))))
                                       (mbe :logic
                                            (part-select dst :low (1- src) :width 1)
                                            :exec
                                            (let* ((shft (the (signed-byte 32)
                                                           (- 1 (the (unsigned-byte 32) src)))))
                                              (the (unsigned-byte 1)
                                                (logand 1
                                                        (the (unsigned-byte 32)
                                                          (ash (the (unsigned-byte 32) dst)
                                                               (the (signed-byte 32) shft)))))))))
                                 (pf (general-pf-spec 32 result))
                                 (zf (zf-spec result))
                                 (sf (general-sf-spec 32 result))
                                 (output-rflags (!rflagsbits->cf cf
                                                                 (!rflagsbits->pf pf
                                                                                  (!rflagsbits->zf zf
                                                                                                   (!rflagsbits->sf sf input-rflags)))))
                                 (undefined-flags (!rflagsbits->af 1 (!rflagsbits->of 1 0))))
                              (mv output-rflags undefined-flags)))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              ;; (undefined-flags (mbe :logic (n32 undefined-flags)
              ;;                       :exec undefined-flags))
              )
           (mv result output-rflags undefined-flags))

         )
  :hints (("Goal" :in-theory (e/d* (SaR-SPEC-32
                                    ACL2::BVaSHR
                                    ACL2::BVSX-REWRITE
                                    ACL2::BVSHR
                                    acl2::bvcat
                                    acl2::slice
                                    ACL2::BVCHOP-OF-LOGTAIL
                                    ;;RFLAGSBITS
                                    zf-spec
                                    logext
                                    rflag-RoWs-enables)
                                   (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

;; See comment on SaR-SPEC-8-alt-def.
(defthm SaR-SPEC-64-alt-def
  (equal (SaR-SPEC-64 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 64 dst) :exec dst))
              (src (mbe :logic (n-size 6 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ;; (neg-src (the (signed-byte 65) (- src)))
              ;; (raw-result-not-sign-extended (the (unsigned-byte 64)
              ;;                                 (ash (the (unsigned-byte 64) dst)
              ;;                                      (the (signed-byte 65) neg-src))))
              ;; (raw-result (if (eql (mbe :logic (logbit 63 dst)
              ;;                           :exec (the (unsigned-byte 1)
              ;;                                   (ash (the (unsigned-byte 64) dst) -63)))
              ;;                      1)
              ;;                 (loghead 64
              ;;                          (ash (mbe :logic (logext 64 dst)
              ;;                                    :exec (fast-logext 64 dst))
              ;;                               neg-src))
              ;;               raw-result-not-sign-extended))
              ;; (result (mbe :logic (n-size 64 raw-result)
              ;;              :exec raw-result))
              (result (if (< (ACL2::BVCHOP 6 SRC) 64)
                          (acl2::bvashr 64 dst src)
                        (ACL2::REPEATBIT 64 (ACL2::GETBIT 63 DST))))
              ((mv (the (unsigned-byte 32) output-rflags)
                   (the (unsigned-byte 32)
                     undefined-flags))
               (case src
                 (0 (mv input-rflags 0))
                 (1 (b* ((cf (mbe :logic (part-select dst :low 0 :width 1)
                                  :exec (the (unsigned-byte 1)
                                          (logand 1 (the (unsigned-byte 64) dst)))))
                         (pf (general-pf-spec 64 result))
                         (zf (zf-spec result))
                         (sf (general-sf-spec 64 result))
                         (of 0)
                         (output-rflags (!rflagsbits->cf cf
                                                                      (!rflagsbits->pf pf
                                                                                       (!rflagsbits->zf zf
                                                                                                        (!rflagsbits->sf sf
                                                                                                                         (!rflagsbits->of of input-rflags))))))
                         (undefined-flags (the (unsigned-byte 32)
                                            (!rflagsbits->af 1 0))))
                      (mv output-rflags undefined-flags)))
                 (otherwise (b* ((cf (if (<= 64 src)
                                         (mbe :logic
                                              (part-select dst :low 63 :width 1)
                                              :exec
                                              (let* ((shft (the (signed-byte 64) -63)))
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte 64) dst)
                                                       (the (signed-byte 64) shft)))))
                                       (mbe :logic
                                            (part-select dst :low (1- src) :width 1)
                                            :exec
                                            (let* ((shft (the (signed-byte 64)
                                                           (- 1 (the (unsigned-byte 64) src)))))
                                              (the (unsigned-byte 1)
                                                (logand 1
                                                        (the (unsigned-byte 64)
                                                          (ash (the (unsigned-byte 64) dst)
                                                               (the (signed-byte 64) shft)))))))))
                                 (pf (general-pf-spec 64 result))
                                 (zf (zf-spec result))
                                 (sf (general-sf-spec 64 result))
                                 (output-rflags (!rflagsbits->cf cf
                                                                              (!rflagsbits->pf pf
                                                                                               (!rflagsbits->zf zf
                                                                                                                (!rflagsbits->sf sf input-rflags)))))
                                 (undefined-flags (!rflagsbits->af 1 (!rflagsbits->of 1 0))))
                              (mv output-rflags undefined-flags)))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              ;; (undefined-flags (mbe :logic (n32 undefined-flags)
              ;;                       :exec undefined-flags))
              )
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d* (SaR-SPEC-64
                                    ACL2::BVaSHR
                                    ACL2::BVSX-REWRITE
                                    ACL2::BVSHR
;acl2::bvcat
                                    acl2::slice
                                    ACL2::BVCHOP-OF-LOGTAIL
                                    ;;RFLAGSBITS
                                    zf-spec
                                    logext
;ACL2::LOGAPP-BECOMES-BVCAT-WHEN-BV
                                    rflag-RoWs-enables
                                    )
                                   (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))


;; the normal definition splits with an if!
;; well, this one has an if too, but it's perhaps less bad since the shift amount will often be constant
;;maybe improve bvashr
;; (defthm SAR-SPEC-32-nice
;;   (equal (SAR-SPEC-32 DST SRC INPUT-RFLAGS)
;;          (B* ((DST (MBE :LOGIC (N-SIZE 32 DST)
;;                         :EXEC DST))
;;               (SRC (MBE :LOGIC (N-SIZE 6 SRC)
;;                         :EXEC SRC))
;;               (INPUT-RFLAGS
;;                (MBE :LOGIC (N32 INPUT-RFLAGS)
;;                     :EXEC INPUT-RFLAGS))
;;               (RESULT
;;                (if (<= 32 (ACL2::BVCHOP 6 SRC))
;;                    (if (EQUAL 1 (ACL2::GETBIT 31 DST))
;;                        (+ -1 (expt 2 32))
;;                      0)
;;                  (acl2::bvashr 32 dst SRC)))
;;               ((MV (THE (UNSIGNED-BYTE 32)
;;                         OUTPUT-RFLAGS)
;;                    (THE (UNSIGNED-BYTE 32)
;;                         UNDEFINED-FLAGS))
;;                (CASE
;;                  SRC
;;                  (0 (MV INPUT-RFLAGS 0))
;;                  (1
;;                   (B*
;;                       ((CF
;;                         (MBE
;;                          :LOGIC (ACL2::PART-SELECT DST
;;                                                    :LOW 0
;;                                                    :WIDTH 1)
;;                          :EXEC
;;                          (THE
;;                           (UNSIGNED-BYTE 1)
;;                           (LOGAND 1
;;                                   (THE (UNSIGNED-BYTE 32) DST)))))
;;                        (PF (GENERAL-PF-SPEC 32 RESULT))
;;                        (ZF (ZF-SPEC RESULT))
;;                        (SF
;;                         (GENERAL-SF-SPEC 32 RESULT))
;;                        (OF 0)
;;                        (OUTPUT-RFLAGS
;;                         (MBE
;;                          :LOGIC
;;                          (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                             :CF CF
;;                                             :PF PF
;;                                             :ZF ZF
;;                                             :SF SF
;;                                             :OF OF)
;;                          :EXEC
;;                          (THE
;;                           (UNSIGNED-BYTE 32)
;;                           (!RFLAGSBITS->CF
;;                            CF
;;                            (!RFLAGSBITS->PF
;;                             PF
;;                             (!RFLAGSBITS->ZF
;;                              ZF
;;                              (!RFLAGSBITS->SF
;;                               SF
;;                               (!RFLAGSBITS->OF
;;                                OF INPUT-RFLAGS))))))))
;;                        (UNDEFINED-FLAGS
;;                         (THE (UNSIGNED-BYTE 32)
;;                              (!RFLAGSBITS->AF 1 0))))
;;                     (MV OUTPUT-RFLAGS
;;                         UNDEFINED-FLAGS)))
;;                  (OTHERWISE
;;                   (IF
;;                    (<= 32 SRC)
;;                    (B*
;;                        ((PF (GENERAL-PF-SPEC 32 RESULT))
;;                         (ZF (ZF-SPEC RESULT))
;;                         (SF
;;                          (GENERAL-SF-SPEC 32 RESULT))
;;                         (OUTPUT-RFLAGS
;;                          (MBE
;;                           :LOGIC
;;                           (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                              :PF PF
;;                                              :ZF ZF
;;                                              :SF SF)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->PF
;;                             PF
;;                             (!RFLAGSBITS->ZF
;;                              ZF
;;                              (!RFLAGSBITS->SF
;;                               SF INPUT-RFLAGS))))))
;;                         (UNDEFINED-FLAGS
;;                          (MBE
;;                           :LOGIC (CHANGE-RFLAGSBITS 0
;;                                                     :CF 1
;;                                                     :AF 1
;;                                                     :OF 1)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->CF
;;                             1
;;                             (!RFLAGSBITS->AF
;;                              1 (!RFLAGSBITS->OF 1 0)))))))
;;                      (MV OUTPUT-RFLAGS
;;                          UNDEFINED-FLAGS))
;;                    (B*
;;                        ((CF
;;                          (MBE
;;                           :LOGIC (ACL2::PART-SELECT DST
;;                                                     :LOW (1- SRC)
;;                                                     :WIDTH 1)
;;                           :EXEC
;;                           (LET*
;;                            ((SHFT
;;                              (THE
;;                               (SIGNED-BYTE 32)
;;                               (- 1
;;                                  (THE (UNSIGNED-BYTE 32) SRC)))))
;;                            (THE
;;                             (UNSIGNED-BYTE 1)
;;                             (LOGAND
;;                              1
;;                              (THE (UNSIGNED-BYTE 32)
;;                                   (ASH (THE (UNSIGNED-BYTE 32) DST)
;;                                        (THE (SIGNED-BYTE 32)
;;                                             SHFT))))))))
;;                         (PF (GENERAL-PF-SPEC 32 RESULT))
;;                         (ZF (ZF-SPEC RESULT))
;;                         (SF
;;                          (GENERAL-SF-SPEC 32 RESULT))
;;                         (OUTPUT-RFLAGS
;;                          (MBE
;;                           :LOGIC
;;                           (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                              :CF CF
;;                                              :PF PF
;;                                              :ZF ZF
;;                                              :SF SF)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->CF
;;                             CF
;;                             (!RFLAGSBITS->PF
;;                              PF
;;                              (!RFLAGSBITS->ZF
;;                               ZF
;;                               (!RFLAGSBITS->SF
;;                                SF INPUT-RFLAGS)))))))
;;                         (UNDEFINED-FLAGS
;;                          (MBE :LOGIC (CHANGE-RFLAGSBITS 0
;;                                                         :AF 1
;;                                                         :OF 1)
;;                               :EXEC (!RFLAGSBITS->AF
;;                                      1 (!RFLAGSBITS->OF 1 0)))))
;;                      (MV OUTPUT-RFLAGS
;;                          UNDEFINED-FLAGS))))))
;;               (OUTPUT-RFLAGS
;;                (MBE :LOGIC (N32 OUTPUT-RFLAGS)
;;                     :EXEC OUTPUT-RFLAGS))
;;               (UNDEFINED-FLAGS
;;                (MBE :LOGIC (N32 UNDEFINED-FLAGS)
;;                     :EXEC UNDEFINED-FLAGS)))
;;            (MV RESULT OUTPUT-RFLAGS
;;                UNDEFINED-FLAGS)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (acl2::bvashr
;;                                    ;;acl2::bvsx
;;                                    SAR-SPEC-32 ACL2::BVSHR
;;                                    ;;ACL2::LOGEXT-CASES
;;                                    acl2::bvchop-of-logtail-becomes-slice
;;                                    acl2::<-of-bvchop-and-2
;;                                    acl2::slice-alt-def
;;                                    )
;;                                   ( ;ACL2::BVCAT-EQUAL-REWRITE ACL2::BVCAT-EQUAL-REWRITE-ALT
;;                                    acl2::BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE
;;                                    )))))
;; (DEFthm SAR-SPEC-64-nice
;;   (equal (SAR-SPEC-64 DST SRC INPUT-RFLAGS)
;;          (B*
;;              ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
;;               (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
;;               (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
;;                                  :EXEC INPUT-RFLAGS))
;;               (RESULT
;;                (if (<= 64 (ACL2::BVCHOP 7 SRC))
;;                    (if (EQUAL 1 (ACL2::GETBIT 63 DST))
;;                        (+ -1 (expt 2 64))
;;                      0)
;;                  (acl2::bvashr 64 dst SRC)))
;;               ((MV (THE (UNSIGNED-BYTE 32) OUTPUT-RFLAGS)
;;                    (THE (UNSIGNED-BYTE 32)
;;                         UNDEFINED-FLAGS))
;;                (CASE
;;                  SRC (0 (MV INPUT-RFLAGS 0))
;;                  (1
;;                   (B*
;;                       ((CF
;;                         (MBE :LOGIC (PART-SELECT DST :LOW 0 :WIDTH 1)
;;                              :EXEC
;;                              (THE (UNSIGNED-BYTE 1)
;;                                   (LOGAND 1 (THE (UNSIGNED-BYTE 64) DST)))))
;;                        (PF (GENERAL-PF-SPEC 64 RESULT))
;;                        (ZF (ZF-SPEC RESULT))
;;                        (SF (GENERAL-SF-SPEC 64 RESULT))
;;                        (OF 0)
;;                        (OUTPUT-RFLAGS
;;                         (MBE
;;                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                                    :CF CF
;;                                                    :PF PF
;;                                                    :ZF ZF
;;                                                    :SF SF
;;                                                    :OF OF)
;;                          :EXEC
;;                          (THE
;;                           (UNSIGNED-BYTE 32)
;;                           (!RFLAGSBITS->CF
;;                            CF
;;                            (!RFLAGSBITS->PF
;;                             PF
;;                             (!RFLAGSBITS->ZF
;;                              ZF
;;                              (!RFLAGSBITS->SF
;;                               SF
;;                               (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
;;                        (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
;;                                              (!RFLAGSBITS->AF 1 0))))
;;                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
;;                  (OTHERWISE
;;                   (IF
;;                    (<= 64 SRC)
;;                    (B*
;;                        ((PF (GENERAL-PF-SPEC 64 RESULT))
;;                         (ZF (ZF-SPEC RESULT))
;;                         (SF (GENERAL-SF-SPEC 64 RESULT))
;;                         (OUTPUT-RFLAGS
;;                          (MBE
;;                           :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                                     :PF PF
;;                                                     :ZF ZF
;;                                                     :SF SF)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->PF
;;                             PF
;;                             (!RFLAGSBITS->ZF
;;                              ZF
;;                              (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
;;                         (UNDEFINED-FLAGS
;;                          (MBE
;;                           :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->CF
;;                             1
;;                             (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
;;                      (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
;;                    (B*
;;                        ((CF
;;                          (MBE
;;                           :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
;;                           :EXEC
;;                           (LET*
;;                            ((SHFT (THE (SIGNED-BYTE 64)
;;                                        (- 1 (THE (UNSIGNED-BYTE 64) SRC)))))
;;                            (THE
;;                             (UNSIGNED-BYTE 1)
;;                             (LOGAND
;;                              1
;;                              (THE (UNSIGNED-BYTE 64)
;;                                   (ASH (THE (UNSIGNED-BYTE 64) DST)
;;                                        (THE (SIGNED-BYTE 64) SHFT))))))))
;;                         (PF (GENERAL-PF-SPEC 64 RESULT))
;;                         (ZF (ZF-SPEC RESULT))
;;                         (SF (GENERAL-SF-SPEC 64 RESULT))
;;                         (OUTPUT-RFLAGS
;;                          (MBE
;;                           :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
;;                                                     :CF CF
;;                                                     :PF PF
;;                                                     :ZF ZF
;;                                                     :SF SF)
;;                           :EXEC
;;                           (THE
;;                            (UNSIGNED-BYTE 32)
;;                            (!RFLAGSBITS->CF
;;                             CF
;;                             (!RFLAGSBITS->PF
;;                              PF
;;                              (!RFLAGSBITS->ZF
;;                               ZF
;;                               (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
;;                         (UNDEFINED-FLAGS
;;                          (MBE
;;                           :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
;;                           :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
;;                      (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
;;               (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
;;                                   :EXEC OUTPUT-RFLAGS))
;;               (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
;;                                     :EXEC UNDEFINED-FLAGS)))
;;            (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
;;   :otf-flg t
;;   :hints (("Goal" :expand ()
;;            :in-theory (e/d (acl2::bvashr ;acl2::bvsx
;;                             SAR-SPEC-64 ACL2::BVSHR
;;                                         ;;ACL2::LOGEXT-CASES
;;                             acl2::bvchop-of-logtail-becomes-slice
;;                             acl2::<-of-bvchop-and-2
;;                             acl2::slice-alt-def
;;                             )
;;                            ( ;ACL2::BVCAT-EQUAL-REWRITE ACL2::BVCAT-EQUAL-REWRITE-ALT
;;                             acl2::BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE
;;                             ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE ;loop
;;                             ACL2::LOGtail-OF-LOGext ;loop
;;                             )))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; There are only 2 of these
(defthm shlx-spec-32-alt-def
  (equal (shlx-spec-32 src cnt)
         (acl2::bvshl 32 src (acl2::bvchop 6 cnt))) ; could change the model to chop to 5 bits
  :hints (("Goal" :in-theory (enable shlx-spec-32 acl2::bvshl))))

(defthm shlx-spec-64-alt-def
  (equal (shlx-spec-64 src cnt)
         (acl2::bvshl 64 src (acl2::bvchop 6 cnt)))
  :hints (("Goal" :in-theory (enable shlx-spec-64 acl2::bvshl))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; There are only 2 of these
(defthm shrx-spec-32-alt-def
  (equal (shrx-spec-32 src cnt)
         (acl2::bvshr 32 src (acl2::bvchop 6 cnt))) ; could change the model to chop to 5 bits
  :hints (("Goal" :in-theory (enable shrx-spec-32 acl2::bvshr acl2::logtail-of-bvchop-becomes-slice))))

(defthm shrx-spec-64-alt-def
  (equal (shrx-spec-64 src cnt)
         (acl2::bvshr 64 src (acl2::bvchop 6 cnt)))
  :hints (("Goal" :in-theory (enable shrx-spec-64 acl2::bvshr acl2::logtail-of-bvchop-becomes-slice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; There are only 2 of these
;;todo: redefining bvashr could make this nicer
;; or could change the model to chop CNT to 5 bits, since the caller already does that
(defthm sarx-spec-32-alt-def
  (equal (sarx-spec-32 src cnt)
         (if (< (acl2::bvchop 6 cnt) 32) ; should always be true, since the caller chops it
             (acl2::bvashr 32 src (acl2::bvchop 6 cnt))
           (if (equal (acl2::getbit 31 src) 0)
               0
             4294967295)))
  :hints (("Goal" :in-theory (enable sarx-spec-32 acl2::bvashr acl2::bvshr acl2::bvsx
                                     acl2::logtail-of-bvchop-becomes-slice
                                     acl2::bvchop-of-logtail-becomes-slice))))

(defthm sarx-spec-64-alt-def
  (equal (sarx-spec-64 src cnt)
         (acl2::bvashr 64 src (acl2::bvchop 6 cnt)))
  :hints (("Goal" :in-theory (enable sarx-spec-64 acl2::bvashr acl2::bvshr acl2::bvsx
                                     acl2::logtail-of-bvchop-becomes-slice
                                     acl2::bvchop-of-logtail-becomes-slice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: make these local:

;gen!
(defthm *-of-/-linear-when-both-negative-free-linear
  (implies (and (< free i)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (< i 0)
                )
           (< (* i (/ j)) (- free)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable acl2::<-of-*-of-/-arg1))))

;gen!
(defthm *-of-/-linear-when-i-negative-and-positive-linear
  (implies (and (< i free)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (<= 0 i))
           (< (- free) (* i (/ j))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable acl2::<-of-*-of-/-arg1))))

;(in-theory (disable <-WHEN-CANONICAL-ADDRESS-P-IMPOSSIBLE <-WHEN-CANONICAL-ADDRESS-P)) ;todo bad



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This avoids a case split when doing the sign extension.
(defthm x86-cbw/cwd/cdqe-alt-def
  (equal (x86-cbw/cwd/cdqe
           proc-mode start-rip temp-rip prefixes rex-byte opcode modr/m sib x86)

  (b* ((?ctx 'x86-cbw/cwd/cdqe))
    (b*
        (((the (integer 1 8)
            register-size)
          (select-operand-size
            proc-mode nil
            rex-byte nil prefixes nil nil nil x86))
         ((the (integer 1 4) src-size)
          (ash register-size -1))
         ((the (unsigned-byte 32) src)
          (mbe
            :logic
            (rgfi-size src-size *rax* rex-byte x86)
            :exec
            (case src-size
              (1 (rr08 *rax* rex-byte x86))
              (2 (rr16 *rax* x86))
              (4 (rr32 *rax* x86))
              (otherwise 0))))
         (old-bits (* 8 src-size))
         (new-bits (* 8 register-size))
         (dst (acl2::bvsx new-bits old-bits src))
         ;; (dst
         ;;   (if (logbitp (the (integer 0 32)
         ;;                  (1- (the (integer 0 32)
         ;;                        (ash src-size 3))))
         ;;                src)
         ;;       (trunc register-size
         ;;                      (case src-size
         ;;                        (1 (n08-to-i08 src))
         ;;                        (2 (n16-to-i16 src))
         ;;                        (t (n32-to-i32 src))))
         ;;     src))
         (x86 (!rgfi-size register-size
                                  *rax* dst rex-byte x86))
         (x86 (write-*ip proc-mode temp-rip x86)))
      x86)))
  :hints (("Goal" :in-theory (enable x86-cbw/cwd/cdqe
                                     acl2::bvsx
                                     rr32
                                     rr16
                                     rr08))))

;; avoids a cae split.  also avoids a call of THE and an unused let var
(DEFthm X86-CWD/CDQ/CQO-alt-def
  (equal (X86-CWD/CDQ/CQO PROC-MODE START-RIP TEMP-RIP PREFIXES REX-BYTE OPCODE MODR/M SIB x86)
         (B* ((SRC-SIZE
               (SELECT-OPERAND-SIZE
                 PROC-MODE NIL
                 REX-BYTE NIL PREFIXES NIL NIL NIL X86))
              (SRC (RGFI-SIZE SRC-SIZE *RAX* REX-BYTE X86))
              ;; rdx gets the high part of the sign-extension
              ;; avoids a case split and supports putting the parts back together (e.g., to do a divide):
              (RDX (acl2::slice (+ -1 (* 16 src-size))
                                (* 8 src-size)
                                (acl2::bvsx (* 16 src-size) (* 8 src-size) src)))
              (X86 (!RGFI-SIZE SRC-SIZE *RDX* RDX REX-BYTE X86))
              (X86 (WRITE-*IP PROC-MODE TEMP-RIP X86)))
           X86))
  :hints (("Goal" :in-theory (enable X86-CWD/CDQ/CQO))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm add-af-spec32-of-bvchop-32-arg1
  (equal (add-af-spec32 (acl2::bvchop 32 dst) src)
         (add-af-spec32 dst src))
  :hints (("Goal" :in-theory (enable add-af-spec32))))

(defthm add-af-spec32-of-bvchop-32-arg2
  (equal (add-af-spec32 dst (acl2::bvchop 32 src))
         (add-af-spec32 dst src))
  :hints (("Goal" :in-theory (enable add-af-spec32))))

;; these clean up the flags expressions

(defthm gpr-add-spec-1-alt-def
  (equal (gpr-add-spec-1 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 8 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (raw-result (the (unsigned-byte 9)
                            (+ (the (unsigned-byte 8) dst)
                               (the (unsigned-byte 8) src))))
              (signed-raw-result (the (signed-byte 9)
                                   (+ (the (signed-byte 8) (n08-to-i08 dst))
                                      (the (signed-byte 8)
                                        (n08-to-i08 src)))))
              (result (the (unsigned-byte 8)
                        (n-size 8 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec8 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec8 result)))
              (af (the (unsigned-byte 1)
                    (add-af-spec8 dst src)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec8 result)))
              (of (the (unsigned-byte 1)
                    (of-spec8 signed-raw-result)))
              (output-rflags (change-rflagsbits input-rflags
                                                :cf cf
                                                :pf pf
                                                :af af
                                                :zf zf
                                                :sf sf
                                                :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-add-spec-1 rflag-rows-enables))))

(defthm gpr-add-spec-2-alt-def
  (equal (gpr-add-spec-2 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst) :exec dst))
              (src (mbe :logic (n-size 16 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (raw-result (the (unsigned-byte 17)
                            (+ (the (unsigned-byte 16) dst)
                               (the (unsigned-byte 16) src))))
              (signed-raw-result (the (signed-byte 17)
                                   (+ (the (signed-byte 16) (n16-to-i16 dst))
                                      (the (signed-byte 16)
                                        (n16-to-i16 src)))))
              (result (the (unsigned-byte 16)
                        (n-size 16 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec16 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec16 result)))
              (af (the (unsigned-byte 1)
                    (add-af-spec16 dst src)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec16 result)))
              (of (the (unsigned-byte 1)
                    (of-spec16 signed-raw-result)))
              (output-rflags (change-rflagsbits input-rflags
                                                :cf cf
                                                :pf pf
                                                :af af
                                                :zf zf
                                                :sf sf
                                                :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-add-spec-2 rflag-rows-enables))))

(defthm gpr-add-spec-4-alt-def
  (equal (gpr-add-spec-4 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 32 dst) :exec dst))
              (src (mbe :logic (n-size 32 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (raw-result (the (unsigned-byte 33)
                            (+ (the (unsigned-byte 32) dst)
                               (the (unsigned-byte 32) src))))
              (signed-raw-result (the (signed-byte 33)
                                   (+ (the (signed-byte 32) (n32-to-i32 dst))
                                      (the (signed-byte 32)
                                        (n32-to-i32 src)))))
              (result (the (unsigned-byte 32)
                        (n-size 32 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec32 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec32 result)))
              (af (the (unsigned-byte 1)
                    (add-af-spec32 dst src)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec32 result)))
              (of (the (unsigned-byte 1)
                    (of-spec32 signed-raw-result)))
              (output-rflags (change-rflagsbits input-rflags
                                                :cf cf
                                                :pf pf
                                                :af af
                                                :zf zf
                                                :sf sf
                                                :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-add-spec-4 rflag-rows-enables))))

;; for rewriting
(defthmd GPR-ADD-SPEC-4-better
  (equal (gpr-add-spec-4 dst src input-rflags)
         (let ((dst (acl2::bvchop 32 dst)) ; drop?
               (src (acl2::bvchop 32 src)) ; drop?
               (result ;; (acl2::bvplus 32 dst src) ;; todo: put back, but this broke some proofs (normal form change)
                (acl2::bvchop 32 (+ (acl2::bvchop 32 dst) (acl2::bvchop 32 src))) ; todo: simplify!
                ))
           (MV result
               (!RFLAGSBITS->CF
                (cf-spec32 (+ dst src))
                (!RFLAGSBITS->PF
                 (pf-spec32 result)
                 (!RFLAGSBITS->AF
                  (add-af-spec32 dst src)
                  (!RFLAGSBITS->ZF
                   (zf-spec result)
                   (!RFLAGSBITS->SF
                    (sf-spec32 result)
                    (!RFLAGSBITS->OF
                     (of-spec32 (+ (logext 32 dst)
                                   (logext 32 src)))
                     (acl2::bvchop 32 input-rflags) ; drop the bvchop?
                     ))))))
               0)))
  :hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
                                    GPR-ADD-SPEC-4
                                    ;; ZF-SPEC
                                    acl2::bvchop-of-sum-cases
                                    acl2::bvplus) ((:e tau-system))))))

;; todo: try this:
;; for rewriting
;; (defthmd GPR-ADD-SPEC-4-better
;;   (equal (gpr-add-spec-4 dst src input-rflags)
;;          (let (;(dst (acl2::bvchop 32 dst)) ; drop?
;;                ;(src (acl2::bvchop 32 src)) ; drop?
;;                (result ;; (acl2::bvplus 32 dst src) ;; todo: put back, but this broke some proofs (normal form change)
;;                 (acl2::bvchop 32 (+ (acl2::bvchop 32 dst) (acl2::bvchop 32 src))) ; todo: simplify!
;;                 ))
;;            (MV result
;;                (!RFLAGSBITS->CF
;;                  ;; todo: make an add-cf-spec32:
;;                 (cf-spec32 (+ (acl2::bvchop 32 dst) (acl2::bvchop 32 src)))
;;                 (!RFLAGSBITS->PF
;;                  (pf-spec32 result)
;;                  (!RFLAGSBITS->AF
;;                   (add-af-spec32 dst src)
;;                   (!RFLAGSBITS->ZF
;;                    (zf-spec result)
;;                    (!RFLAGSBITS->SF
;;                     (sf-spec32 result)
;;                     (!RFLAGSBITS->OF
;;                      (of-spec32 (+ (logext 32 dst)
;;                                    (logext 32 src)))
;;                      (acl2::bvchop 32 input-rflags) ; drop the bvchop?
;;                      ))))))
;;                0)))
;;   :hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
;;                                     GPR-ADD-SPEC-4
;;                                     ;; ZF-SPEC
;;                                     acl2::bvchop-of-sum-cases
;;                                     acl2::bvplus) ((:e tau-system))))))


;; todo: add alt-def rules for gpr-add-spec-1, etc, that clean up the flags expressions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Improve rflags handling, insert open-carry
(defthm gpr-adc-spec-1-alt-def
  (equal (gpr-adc-spec-1 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 8 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (input-cf (the (unsigned-byte 1)
                          (rflagsbits->cf input-rflags)))
              (raw-result (the (unsigned-byte 9)
                            (+ (the (unsigned-byte 8) dst)
                               (the (unsigned-byte 8) src)
                               (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (signed-raw-result
                (the (signed-byte 9)
                  (+ (the (signed-byte 8) (n08-to-i08 dst))
                     (the (signed-byte 8) (n08-to-i08 src))
                     (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (result (the (unsigned-byte 8)
                        (n-size 8 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec8 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec8 result)))
              (af (the (unsigned-byte 1)
                    (adc-af-spec8 dst src input-cf)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec8 result)))
              (of (the (unsigned-byte 1)
                    (of-spec8 signed-raw-result)))
              (output-rflags
                (change-rflagsbits input-rflags
                                            :cf cf
                                            :pf pf
                                            :af af
                                            :zf zf
                                            :sf sf
                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-adc-spec-1
                                      rflag-rows-enables
                                      x::open-carry))))

;; Improve rflags handling, insert open-carry
(defthm gpr-adc-spec-2-alt-def
  (equal (gpr-adc-spec-2 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst) :exec dst))
              (src (mbe :logic (n-size 16 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (input-cf (the (unsigned-byte 1)
                          (rflagsbits->cf input-rflags)))
              (raw-result (the (unsigned-byte 17)
                            (+ (the (unsigned-byte 16) dst)
                               (the (unsigned-byte 16) src)
                               (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (signed-raw-result
                (the (signed-byte 17)
                  (+ (the (signed-byte 16) (n16-to-i16 dst))
                     (the (signed-byte 16) (n16-to-i16 src))
                     (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (result (the (unsigned-byte 16)
                        (n-size 16 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec16 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec16 result)))
              (af (the (unsigned-byte 1)
                    (adc-af-spec16 dst src input-cf)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec16 result)))
              (of (the (unsigned-byte 1)
                    (of-spec16 signed-raw-result)))
              (output-rflags
                (change-rflagsbits input-rflags
                                            :cf cf
                                            :pf pf
                                            :af af
                                            :zf zf
                                            :sf sf
                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-adc-spec-2
                                      rflag-rows-enables
                                      x::open-carry))))

;; Improve rflags handling, insert open-carry
(defthm gpr-adc-spec-4-alt-def
  (equal (gpr-adc-spec-4 dst src input-rflags)
         (b*
             ((dst (mbe :logic (n-size 32 dst) :exec dst))
              (src (mbe :logic (n-size 32 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (input-cf (the (unsigned-byte 1)
                          (rflagsbits->cf input-rflags)))
              (raw-result (the (unsigned-byte 33)
                            (+ (the (unsigned-byte 32) dst)
                               (the (unsigned-byte 32) src)
                               (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (signed-raw-result
                (the (signed-byte 33)
                  (+ (the (signed-byte 32) (n32-to-i32 dst))
                     (the (signed-byte 32) (n32-to-i32 src))
                     (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (result (the (unsigned-byte 32)
                        (n-size 32 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec32 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec32 result)))
              (af (the (unsigned-byte 1)
                    (adc-af-spec32 dst src input-cf)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec32 result)))
              (of (the (unsigned-byte 1)
                    (of-spec32 signed-raw-result)))
              (output-rflags
                (change-rflagsbits input-rflags
                                            :cf cf
                                            :pf pf
                                            :af af
                                            :zf zf
                                            :sf sf
                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-adc-spec-4
                                      rflag-rows-enables
                                      x::open-carry))))

;; Improve rflags handling, insert open-carry
(defthm gpr-adc-spec-8-alt-def
  (equal (gpr-adc-spec-8 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 64 dst) :exec dst))
              (src (mbe :logic (n-size 64 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (input-cf (the (unsigned-byte 1)
                          (rflagsbits->cf input-rflags)))
              (raw-result (the (unsigned-byte 65)
                            (+ (the (unsigned-byte 64) dst)
                               (the (unsigned-byte 64) src)
                               (the (unsigned-byte 1) (x::open-carry input-cf)))))
              (signed-raw-result
                (the (signed-byte 65)
                  (+ (the (signed-byte 64) (n64-to-i64 dst))
                     (the (signed-byte 64) (n64-to-i64 src))
                     (the (unsigned-byte 1) input-cf))))
              (result (the (unsigned-byte 64)
                        (n-size 64 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec64 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec64 result)))
              (af (the (unsigned-byte 1)
                    (adc-af-spec64 dst src input-cf)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec64 result)))
              (of (the (unsigned-byte 1) ; todo: can we do better here?
                    (of-spec64 signed-raw-result)))
              (output-rflags
                (!rflagsbits->cf
                  cf
                  (!rflagsbits->pf
                    pf
                    (!rflagsbits->af
                      af
                      (!rflagsbits->zf
                        zf
                        (!rflagsbits->sf
                          sf
                          (!rflagsbits->of of input-rflags)))))))
                  ;; (output-rflags (mbe :logic (n32 output-rflags)
                  ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags))
         )
  :hints (("Goal" :in-theory (enable* gpr-adc-spec-8
                                      rflag-rows-enables
                                      x::open-carry))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets rid of change-rflagsbits, and some fixing.
;; todo: also put in bvplus
;todo: more!  and see the better ones too
(defthm GPR-add-SPEC-8-alt-def
  (equal (gpr-add-spec-8 dst src input-rflags)
         ;; proposed new body for GPR-ADD-SPEC-8:
         (b* ((dst (mbe :logic (n-size 64 dst) :exec dst))
              (src (mbe :logic (n-size 64 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (raw-result (the (unsigned-byte 65)
                            (+ (the (unsigned-byte 64) dst)
                               (the (unsigned-byte 64) src))))
              (signed-raw-result
                (the (signed-byte 65)
                  (+ (the (signed-byte 64) (n64-to-i64 dst))
                     (the (signed-byte 64)
                       (n64-to-i64 src)))))
              (result (the (unsigned-byte 64)
                        (n-size 64 raw-result)))
              (cf (the (unsigned-byte 1)
                    (cf-spec64 raw-result)))
              (pf (the (unsigned-byte 1)
                    (pf-spec64 result)))
              (af (the (unsigned-byte 1)
                    (add-af-spec64 dst src)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec64 result)))
              (of (the (unsigned-byte 1) ; todo: can we do better here?
                    (of-spec64 signed-raw-result)))
              (output-rflags
                (!rflagsbits->cf
                      cf
                      (!rflagsbits->pf
                       pf
                       (!rflagsbits->af
                          af
                          (!rflagsbits->zf
                               zf
                               (!rflagsbits->sf
                                    sf
                                    (!rflagsbits->of of input-rflags)))))))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* GPR-add-SPEC-8
                                      ;sub-cf-spec8
                                      ;sub-pf-spec8
                                      ;ZF-SPEC
                                      ;acl2::bvchop-of-sum-cases
                                      rflag-RoWs-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Better rflags handling
(defthm gpr-and-spec-1-alt-def
  (equal (gpr-and-spec-1 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 8 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 8) result)
               (mbe :logic (part-select (logand dst src)
                                        :low 0
                                        :width 8)
                    :exec (logand dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec8 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec8 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                :cf cf
                                                :pf pf
                                                :zf zf
                                                :sf sf
                                                :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-and-spec-1 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-and-spec-2-alt-def
  (equal (gpr-and-spec-2 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst) :exec dst))
              (src (mbe :logic (n-size 16 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 16) result)
               (mbe :logic (part-select (logand dst src)
                                        :low 0
                                        :width 16)
                    :exec (logand dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec16 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec16 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-and-spec-2 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-and-spec-4-alt-def
  (equal (gpr-and-spec-4 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 32 dst) :exec dst))
              (src (mbe :logic (n-size 32 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 32) result)
               (mbe :logic (part-select (logand dst src)
                                        :low 0
                                        :width 32)
                    :exec (logand dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec32 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec32 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-and-spec-4 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-and-spec-8-alt-def
  (equal (gpr-and-spec-8 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 64 dst) :exec dst))
              (src (mbe :logic (n-size 64 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 64) result)
               (mbe :logic (part-select (logand dst src)
                                        :low 0
                                        :width 64)
                    :exec (logand dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec64 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec64 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-and-spec-8 rflag-rows-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Better rflags handling
(defthm gpr-xor-spec-1-alt-def
  (equal (gpr-xor-spec-1 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 8 dst) :exec dst))
              (src (mbe :logic (n-size 8 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 8) result)
               (mbe :logic (part-select (logxor dst src)
                                        :low 0
                                        :width 8)
                    :exec (logxor dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec8 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec8 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-xor-spec-1 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-xor-spec-2-alt-def
  (equal (gpr-xor-spec-2 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 16 dst) :exec dst))
              (src (mbe :logic (n-size 16 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 16) result)
               (mbe :logic (part-select (logxor dst src)
                                        :low 0
                                        :width 16)
                    :exec (logxor dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec16 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec16 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-xor-spec-2 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-xor-spec-4-alt-def
  (equal (gpr-xor-spec-4 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 32 dst) :exec dst))
              (src (mbe :logic (n-size 32 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 32) result)
               (mbe :logic (part-select (logxor dst src)
                                        :low 0
                                        :width 32)
                    :exec (logxor dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec32 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec32 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-xor-spec-4 rflag-rows-enables))))

;; Better rflags handling
(defthm gpr-xor-spec-8-alt-def
  (equal (gpr-xor-spec-8 dst src input-rflags)
         (b* ((dst (mbe :logic (n-size 64 dst) :exec dst))
              (src (mbe :logic (n-size 64 src) :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              ((the (unsigned-byte 64) result)
               (mbe :logic (part-select (logxor dst src)
                                        :low 0
                                        :width 64)
                    :exec (logxor dst src)))
              (cf 0)
              (pf (the (unsigned-byte 1)
                    (pf-spec64 result)))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec64 result)))
              (of 0)
              (output-rflags (change-rflagsbits input-rflags
                                                            :cf cf
                                                            :pf pf
                                                            :zf zf
                                                            :sf sf
                                                            :of of))
              ;; (output-rflags (mbe :logic (n32 output-rflags)
              ;;                     :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable* gpr-xor-spec-8 rflag-rows-enables))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gpr-sbb-spec-4-alt-def
  (equal (x86isa::gpr-sbb-spec-4 dst src input-rflags)
         (b* ((dst (mbe :logic (x86isa::n-size 32 dst) :exec dst))
              (src (mbe :logic (x86isa::n-size 32 src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (x86isa::input-cf (the (unsigned-byte 1)
                                  (rflagsbits->cf input-rflags)))
              (x86isa::signed-raw-result (the (signed-byte 34)
                                           (- (the (signed-byte 32)
                                                (x86isa::n32-to-i32 dst))
                                              (the (signed-byte 33)
                                                (+ (the (signed-byte 32)
                                                     (x86isa::n32-to-i32 src))
                                                   ;; open the carry:
                                                   (x::open-carry x86isa::input-cf))))))
              (result (the (unsigned-byte 32)
                        (x86isa::n-size 32 x86isa::signed-raw-result)))
              (cf (sub-cf-spec8 dst (+ (x::open-carry x86isa::input-cf) src))
                  ;; (the (unsigned-byte 1)
                  ;;     (bool->bit (< dst
                  ;;                   (the (unsigned-byte 33)
                  ;;                     (+ x86isa::input-cf src)))))
                  )
              (pf (the (unsigned-byte 1)
                    (pf-spec32 result)))
              (af (the (unsigned-byte 1)
                    ;; open the carry:
                    (sbb-af-spec32 dst src (x::open-carry x86isa::input-cf))))
              (zf (the (unsigned-byte 1)
                    (zf-spec result)))
              (sf (the (unsigned-byte 1)
                    (sf-spec32 result)))
              (of (the (unsigned-byte 1)
                    (of-spec32 x86isa::signed-raw-result)))
              ;; changed this:
              (x86isa::output-rflags (!rflagsbits->cf cf
                                                      (!rflagsbits->pf pf
                                                                       (!rflagsbits->af af
                                                                                        (!rflagsbits->zf zf
                                                                                                         (!rflagsbits->sf sf
                                                                                                                          (!rflagsbits->of of input-rflags)))))))
              ;; (x86isa::output-rflags (mbe :logic (n32 x86isa::output-rflags)
              ;;                             :exec x86isa::output-rflags))
              (x86isa::undefined-flags 0))
           (mv result x86isa::output-rflags x86isa::undefined-flags)))
  :hints (("Goal" :in-theory (enable* x86isa::gpr-sbb-spec-4 x::open-carry rflag-rows-enables sub-cf-spec8))))
