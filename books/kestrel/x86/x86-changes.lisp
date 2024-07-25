; Some changes to the open-source x86 model
;
; Copyright (C) 2022-2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "rflags-spec-sub")
(include-book "projects/x86isa/machine/instructions/sub-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/add-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/shifts-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/or-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/divide-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/signextend" :dir :system) ; brings in ttags
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvashr" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
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
                           ACL2::PLUS-BVCAT-WITH-0 ;looped
                           ACL2::PLUS-BVCAT-WITH-0-ALT ;looped
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


;; Note that this is also used to implement comparisons
;; TODO: The :exec parts are not needed (here and elsewhere):
;; This puts in some equivalent :logic expressions for the flags
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
                (mbe
                  :logic (change-rflagsbits input-rflags
                                            :cf cf
                                            :pf pf
                                            :af af
                                            :zf zf
                                            :sf sf
                                            :of of)
                  :exec
                  (the
                      (unsigned-byte 32)
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
                                of input-rflags)))))))))
              (output-rflags
                (mbe :logic (n32 output-rflags)
                     :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags
               undefined-flags)))
  :hints (("Goal" :in-theory (enable GPR-SUB-SPEC-1
                                     sub-cf-spec8
                                     sub-pf-spec8
                                     ZF-SPEC
                                     acl2::bvchop-of-sum-cases))))

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
               (mbe
                :logic (change-rflagsbits input-rflags
                                                  :cf cf
                                                  :pf pf
                                                  :af af
                                                  :zf zf
                                                  :sf sf
                                                  :of of)
                :exec
                (the
                 (unsigned-byte 32)
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
                       of input-rflags)))))))))
              (output-rflags
               (mbe :logic (n32 output-rflags)
                    :exec output-rflags))
              (undefined-flags 0))
           (mv result output-rflags
               undefined-flags)))
  :hints (("Goal" :in-theory (enable GPR-SUB-SPEC-2
                                     sub-cf-spec16
                                     sub-pf-spec16
                                     ZF-SPEC
                                     acl2::bvchop-of-sum-cases))))

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
               (MBE
                :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                          :CF CF
                                          :PF PF
                                          :AF AF
                                          :ZF ZF
                                          :SF SF
                                          :OF OF)
                :EXEC
                (THE
                 (UNSIGNED-BYTE 32)
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
                       OF INPUT-RFLAGS)))))))))
              (OUTPUT-RFLAGS
               (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                    :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS 0))
           (MV RESULT OUTPUT-RFLAGS
               UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable GPR-SUB-SPEC-4
                                     sub-cf-spec32
                                     sub-pf-spec32
                                     ZF-SPEC
                                     acl2::bvchop-of-sum-cases))))

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
  :hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
                                    GPR-SUB-SPEC-4
                                    sub-cf-spec32
                                    sub-pf-spec32
                                    ZF-SPEC
                                    acl2::bvchop-of-sum-cases
                                    acl2::bvminus) ((:e tau-system))))))

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
               (MBE
                :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                          :CF CF
                                          :PF PF
                                          :AF AF
                                          :ZF ZF
                                          :SF SF
                                          :OF OF)
                :EXEC
                (THE
                 (UNSIGNED-BYTE 32)
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
                      (!RFLAGSBITS->OF OF INPUT-RFLAGS)))))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS 0))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable GPR-SUB-SPEC-8
                                     sub-cf-spec64
                                     sub-pf-spec64
                                     sf-spec64
                                     ZF-SPEC
                                     ;; ACL2::GETBIT-OF-+ ; rename
                                     ACL2::getbit-of-+
                                     acl2::bvchop-of-sum-cases
                                     ACL2::BVPLUS
                                     ACL2::LOGEXT-CASES))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm SAL/SHL-SPEC-8-redef
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

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf
                                            :of of)
                                           :exec
                                           (the (unsigned-byte 32)
                                                (!rflagsBits->cf
                                                 cf
                                                 (!rflagsBits->pf
                                                  pf
                                                  (!rflagsBits->zf
                                                   zf
                                                   (!rflagsBits->sf
                                                    sf
                                                    (!rflagsBits->of
                                                     of
                                                     input-rflags))))))))

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

                           (output-rflags (mbe :logic
                                               (change-rflagsBits
                                                input-rflags
                                                :pf pf
                                                :zf zf
                                                :sf sf)
                                               :exec
                                               (the (unsigned-byte 32)
                                                    (!rflagsBits->pf
                                                     pf
                                                     (!rflagsBits->zf
                                                      zf
                                                      (!rflagsBits->sf
                                                       sf
                                                       input-rflags))))))

                           (undefined-flags (mbe :logic
                                                 (change-rflagsBits
                                                  0
                                                  :cf 1
                                                  :af 1
                                                  :of 1)
                                                 :exec
                                                 (!rflagsBits->cf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   (!rflagsBits->of
                                                    1 0))))))
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

                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :cf cf
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :af 1
                                                :of 1)
                                               :exec
                                               (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0)))))
                      (mv output-rflags undefined-flags))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVSHL
                                   sal/shl-spec-8
                                   SF-SPEC8
                                   PF-SPEC8
                                   ash
                                   acl2::bvcat
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-16-redef
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

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf
                                            :of of)
                                           :exec
                                           (the (unsigned-byte 32)
                                                (!rflagsBits->cf
                                                 cf
                                                 (!rflagsBits->pf
                                                  pf
                                                  (!rflagsBits->zf
                                                   zf
                                                   (!rflagsBits->sf
                                                    sf
                                                    (!rflagsBits->of
                                                     of
                                                     input-rflags))))))))

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

                           (output-rflags (mbe :logic
                                               (change-rflagsBits
                                                input-rflags
                                                :pf pf
                                                :zf zf
                                                :sf sf)
                                               :exec
                                               (the (unsigned-byte 32)
                                                    (!rflagsBits->pf
                                                     pf
                                                     (!rflagsBits->zf
                                                      zf
                                                      (!rflagsBits->sf
                                                       sf
                                                       input-rflags))))))

                           (undefined-flags (mbe :logic
                                                 (change-rflagsBits
                                                  0
                                                  :cf 1
                                                  :af 1
                                                  :of 1)
                                                 :exec
                                                 (!rflagsBits->cf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   (!rflagsBits->of
                                                    1 0))))))
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

                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :cf cf
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :af 1
                                                :of 1)
                                               :exec
                                               (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0)))))
                      (mv output-rflags undefined-flags))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVSHL
                                   sal/shl-spec-16
                                   SF-SPEC16
                                   PF-SPEC16
                                   ash
                                   acl2::bvcat
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-32-redef
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

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf
                                            :of of)
                                           :exec
                                           (the (unsigned-byte 32)
                                                (!rflagsBits->cf
                                                 cf
                                                 (!rflagsBits->pf
                                                  pf
                                                  (!rflagsBits->zf
                                                   zf
                                                   (!rflagsBits->sf
                                                    sf
                                                    (!rflagsBits->of
                                                     of
                                                     input-rflags))))))))

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

                           (output-rflags (mbe :logic
                                               (change-rflagsBits
                                                input-rflags
                                                :pf pf
                                                :zf zf
                                                :sf sf)
                                               :exec
                                               (the (unsigned-byte 32)
                                                    (!rflagsBits->pf
                                                     pf
                                                     (!rflagsBits->zf
                                                      zf
                                                      (!rflagsBits->sf
                                                       sf
                                                       input-rflags))))))

                           (undefined-flags (mbe :logic
                                                 (change-rflagsBits
                                                  0
                                                  :cf 1
                                                  :af 1
                                                  :of 1)
                                                 :exec
                                                 (!rflagsBits->cf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   (!rflagsBits->of
                                                    1 0))))))
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

                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :cf cf
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->cf
                                                   cf
                                                   (!rflagsBits->pf
                                                    pf
                                                    (!rflagsBits->zf
                                                     zf
                                                     (!rflagsBits->sf
                                                      sf
                                                      input-rflags)))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :af 1
                                                :of 1)
                                               :exec
                                               (!rflagsBits->af
                                                1
                                                (!rflagsBits->of
                                                 1
                                                 0)))))
                      (mv output-rflags undefined-flags))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              (undefined-flags (mbe :logic (n32 undefined-flags)
                                    :exec undefined-flags)))

           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVSHL
                                   sal/shl-spec-32
                                   SF-SPEC32
                                   PF-SPEC32
                                   ash
                                   acl2::bvcat
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

(defthm SAL/SHL-SPEC-64-redef
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
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                             (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                           :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                           :EXEC
                           (!RFLAGSBITS->CF
                                1
                                (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0))))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                      (B*
                       ((CF (PART-SELECT DST
                                         :LOW (- 64 SRC)
                                         :WIDTH 1))
                        (PF (GENERAL-PF-SPEC 64 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 64 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                           :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                           :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                      :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVSHL
                                   sal/shl-spec-64
                                   SF-SPEC64
                                   PF-SPEC64
                                   ash
                                   acl2::bvcat
                                   )
                                  (;x::BVCAT-OF-MINUS-BECOMES-BVSHL ;loop
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm SHR-SPEC-8-redef
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
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                             (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                               1
                               (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                           :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                           :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                      :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable SHR-SPEC-8
                                     ACL2::BVSHR
                                     acl2::slice))))

(defthm SHR-SPEC-16-redef
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
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                          :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable SHR-SPEC-16
                                     ACL2::BVSHR
                                     acl2::slice))))

(defthm SHR-SPEC-32-redef
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
                        (MBE
                         :LOGIC
                         (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF
                                                    :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF
                               OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC
                          (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                     :PF PF
                                                     :ZF ZF
                                                     :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0
                                                            :CF 1
                                                            :AF 1
                                                            :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF
                             1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC
                          (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                     :CF CF
                                                     :PF PF
                                                     :ZF ZF
                                                     :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF
                               SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE :LOGIC (CHANGE-RFLAGSBITS 0
                                                                :AF 1
                                                                :OF 1)
                              :EXEC (!RFLAGSBITS->AF
                                     1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS
                         UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS
               (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                    :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS
               (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS
               UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable SHR-SPEC-32
                                     ACL2::BVSHR
                                     acl2::slice))))

(defthm SHR-SPEC-64-redef
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
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                          :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable SHR-SPEC-64
                                     ACL2::BVSHR
                                     acl2::slice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Uses bvor for the result
(defthm GPR-OR-SPEC-1-redef
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
               (mbe
                :logic (change-rflagsbits input-rflags
                                          :cf cf
                                          :pf pf
                                          :zf zf
                                          :sf sf
                                          :of of)
                :exec
                (the
                 (unsigned-byte 32)
                 (!rflagsbits->cf
                  cf
                  (!rflagsbits->pf
                   pf
                   (!rflagsbits->zf
                    zf
                    (!rflagsbits->sf
                     sf
                     (!rflagsbits->of of input-rflags))))))))
              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))
              (undefined-flags (!rflagsbits->af 1 0)))
           (mv result output-rflags undefined-flags)))
  :hints (("Goal" :in-theory (enable GPR-OR-SPEC-1
                                     ACL2::BVOR))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-2-redef
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
               (MBE
                :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                          :CF CF
                                          :PF PF
                                          :ZF ZF
                                          :SF SF
                                          :OF OF)
                :EXEC
                (THE
                 (UNSIGNED-BYTE 32)
                 (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->ZF
                    ZF
                    (!RFLAGSBITS->SF
                     SF
                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
         )
  :hints (("Goal" :in-theory (enable GPR-OR-SPEC-2
                                     ACL2::BVOR))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-4-redef
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
               (MBE
                :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                          :CF CF
                                          :PF PF
                                          :ZF ZF
                                          :SF SF
                                          :OF OF)
                :EXEC
                (THE
                 (UNSIGNED-BYTE 32)
                 (!RFLAGSBITS->CF
                  CF
                  (!RFLAGSBITS->PF
                   PF
                   (!RFLAGSBITS->ZF
                    ZF
                    (!RFLAGSBITS->SF
                     SF
                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :hints (("Goal" :in-theory (enable GPR-OR-SPEC-4
                                     ACL2::BVOR))))

;; Uses bvor for the result
(defthm GPR-OR-SPEC-8-redef
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
                   (MBE
                    :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                              :CF CF
                                              :PF PF
                                              :ZF ZF
                                              :SF SF
                                              :OF OF)
                    :EXEC
                    (THE
                     (UNSIGNED-BYTE 32)
                     (!RFLAGSBITS->CF
                      CF
                      (!RFLAGSBITS->PF
                           PF
                           (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
                  (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                      :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (!RFLAGSBITS->AF 1 0)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
         )
  :hints (("Goal" :in-theory (enable GPR-OR-SPEC-8
                                     ACL2::BVOR))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;move and gen
;; (defthm bvchop-of-logext-when-<
;;   (equal (ACL2::BVCHOP 8 (LOGEXT 7 x))
;;          (acl2::bvcat 1 (acl2::getbit 6 x) 7 x)))

;todo: rule for (ACL2::BVCHOP 8 (LOGEXT 7 x)) when top bit is 1

;; todo: these have gross case splits for shift amounts that are too large
(defthm SaR-SPEC-8-redef
  (equal (SaR-SPEC-8 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 8 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;;              (NEG-SRC (THE (SIGNED-BYTE 9) (- SRC)))
              ;; (RAW-RESULT-NOT-SIGN-EXTENDED
              ;;  (THE (UNSIGNED-BYTE 8)
              ;;       (ASH (THE (UNSIGNED-BYTE 8) DST)
              ;;            (THE (SIGNED-BYTE 9) NEG-SRC))))
              ;; (RAW-RESULT
              ;;  (IF
              ;;   (EQL
              ;;    (MBE
              ;;     :LOGIC (LOGBIT 7 DST)
              ;;     :EXEC
              ;;     (LOGAND 1
              ;;             (THE (UNSIGNED-BYTE 1)
              ;;                  (ASH (THE (UNSIGNED-BYTE 8) DST) -7))))
              ;;    1)
              ;;   (LOGHEAD 8
              ;;            (ASH (MBE :LOGIC (LOGEXT 8 DST)
              ;;                      :EXEC (FAST-LOGEXT 8 DST))
              ;;                 NEG-SRC))
              ;;   RAW-RESULT-NOT-SIGN-EXTENDED))
              ;; (RESULT (MBE :LOGIC (N-SIZE 8 RAW-RESULT)
              ;;              :EXEC RAW-RESULT))
              (result (if (< (ACL2::BVCHOP 6 SRC) 8)
                          (acl2::bvashr 8 dst src)
                        (ACL2::REPEATBIT 8 (ACL2::GETBIT 7 DST))))
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
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                          :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (SaR-SPEC-8
                                   ACL2::BVaSHR
                                   ACL2::BVSX-REWRITE ;acl2::bvsx loops with ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE
                                   ACL2::BVSHR
                                   acl2::bvcat
;ACL2::LOGTAIL-OF-BVCHOP-BECOMES-SLICE
;ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   acl2::slice ; loops with ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE
;acl2::logext-cases ;bad
                                   ACL2::BVCHOP-OF-LOGTAIL
                                   RFLAGSBITS
                                   zf-spec
;PF-SPEC8

;logapp ; slow
                                   logext)
                                  (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

(defthm SaR-SPEC-16-redef
  (equal (SaR-SPEC-16 dst src input-rflags)
         (B*
             ((DST (MBE :LOGIC (N-SIZE 16 DST) :EXEC DST))
              (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
              (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                 :EXEC INPUT-RFLAGS))
              ;; (NEG-SRC (THE (SIGNED-BYTE 17) (- SRC)))
              ;; (RAW-RESULT-NOT-SIGN-EXTENDED
              ;;      (THE (UNSIGNED-BYTE 16)
              ;;           (ASH (THE (UNSIGNED-BYTE 16) DST)
              ;;                (THE (SIGNED-BYTE 17) NEG-SRC))))
              ;; (RAW-RESULT
              ;;  (IF
              ;;   (EQL
              ;;    (MBE
              ;;        :LOGIC (LOGBIT 15 DST)
              ;;        :EXEC (LOGAND 1
              ;;                      (THE (UNSIGNED-BYTE 1)
              ;;                           (ASH (THE (UNSIGNED-BYTE 16) DST)
              ;;                                -15))))
              ;;    1)
              ;;   (LOGHEAD 16
              ;;            (ASH (MBE :LOGIC (LOGEXT 16 DST)
              ;;                      :EXEC (FAST-LOGEXT 16 DST))
              ;;                 NEG-SRC))
              ;;   RAW-RESULT-NOT-SIGN-EXTENDED))
              ;; (RESULT (MBE :LOGIC (N-SIZE 16 RAW-RESULT)
              ;;              :EXEC RAW-RESULT))
              (result (if (< (ACL2::BVCHOP 6 SRC) 16)
                          (acl2::bvashr 16 dst src)
                        (ACL2::REPEATBIT 16 (ACL2::GETBIT 15 DST))))
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
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF
                              SF
                              (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                             ZF
                             (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            1
                            (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                             PF
                             (!RFLAGSBITS->ZF
                              ZF
                              (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                          :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                     (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
              (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                  :EXEC OUTPUT-RFLAGS))
              (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                    :EXEC UNDEFINED-FLAGS)))
           (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
         )
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (SaR-SPEC-16
                                   ACL2::BVaSHR
                                   ACL2::BVSX-REWRITE
                                   ACL2::BVSHR
                                   acl2::bvcat
                                   acl2::slice
                                   ACL2::BVCHOP-OF-LOGTAIL
                                   RFLAGSBITS
                                   zf-spec
                                   logext)
                                  (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

(defthm SaR-SPEC-32-redef
  (equal (SaR-SPEC-32 dst src input-rflags)
         (B*
                 ((DST (MBE :LOGIC (N-SIZE 32 DST) :EXEC DST))
                  (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
                  (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                     :EXEC INPUT-RFLAGS))
                  ;; (NEG-SRC (THE (SIGNED-BYTE 33) (- SRC)))
                  ;; (RAW-RESULT-NOT-SIGN-EXTENDED
                  ;;      (THE (UNSIGNED-BYTE 32)
                  ;;           (ASH (THE (UNSIGNED-BYTE 32) DST)
                  ;;                (THE (SIGNED-BYTE 33) NEG-SRC))))
                  ;; (RAW-RESULT
                  ;;  (IF
                  ;;   (EQL
                  ;;    (MBE
                  ;;        :LOGIC (LOGBIT 31 DST)
                  ;;        :EXEC (LOGAND 1
                  ;;                      (THE (UNSIGNED-BYTE 1)
                  ;;                           (ASH (THE (UNSIGNED-BYTE 32) DST)
                  ;;                                -31))))
                  ;;    1)
                  ;;   (LOGHEAD 32
                  ;;            (ASH (MBE :LOGIC (LOGEXT 32 DST)
                  ;;                      :EXEC (FAST-LOGEXT 32 DST))
                  ;;                 NEG-SRC))
                  ;;   RAW-RESULT-NOT-SIGN-EXTENDED))
                  ;; (RESULT (MBE :LOGIC (N-SIZE 32 RAW-RESULT)
                  ;;              :EXEC RAW-RESULT))
                  (result (if (< (ACL2::BVCHOP 6 SRC) 32)
                              (acl2::bvashr 32 dst src)
                            (ACL2::REPEATBIT 32 (ACL2::GETBIT 31 DST))))
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
                                   (LOGAND 1 (THE (UNSIGNED-BYTE 32) DST)))))
                       (PF (GENERAL-PF-SPEC 32 RESULT))
                       (ZF (ZF-SPEC RESULT))
                       (SF (GENERAL-SF-SPEC 32 RESULT))
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
                       (UNDEFINED-FLAGS (THE (UNSIGNED-BYTE 32)
                                             (!RFLAGSBITS->AF 1 0))))
                      (MV OUTPUT-RFLAGS UNDEFINED-FLAGS)))
                    (OTHERWISE
                     (IF
                      (<= 32 SRC)
                      (B*
                       ((PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                             (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                               1
                               (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))
                      (B*
                       ((CF
                         (MBE
                          :LOGIC (PART-SELECT DST :LOW (1- SRC) :WIDTH 1)
                          :EXEC
                          (LET*
                           ((SHFT (THE (SIGNED-BYTE 32)
                                       (- 1 (THE (UNSIGNED-BYTE 32) SRC)))))
                           (THE
                            (UNSIGNED-BYTE 1)
                            (LOGAND
                                 1
                                 (THE (UNSIGNED-BYTE 32)
                                      (ASH (THE (UNSIGNED-BYTE 32) DST)
                                           (THE (SIGNED-BYTE 32) SHFT))))))))
                        (PF (GENERAL-PF-SPEC 32 RESULT))
                        (ZF (ZF-SPEC RESULT))
                        (SF (GENERAL-SF-SPEC 32 RESULT))
                        (OUTPUT-RFLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                           :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                           :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                      :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS))
       )
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (SaR-SPEC-32
                                   ACL2::BVaSHR
                                   ACL2::BVSX-REWRITE
                                   ACL2::BVSHR
                                   acl2::bvcat
                                   acl2::slice
                                   ACL2::BVCHOP-OF-LOGTAIL
                                   RFLAGSBITS
                                   zf-spec
                                   logext)
                                  (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

(defthm SaR-SPEC-64-redef
  (equal (SaR-SPEC-64 dst src input-rflags)
         (B*
                 ((DST (MBE :LOGIC (N-SIZE 64 DST) :EXEC DST))
                  (SRC (MBE :LOGIC (N-SIZE 6 SRC) :EXEC SRC))
                  (INPUT-RFLAGS (MBE :LOGIC (N32 INPUT-RFLAGS)
                                     :EXEC INPUT-RFLAGS))
                  ;; (NEG-SRC (THE (SIGNED-BYTE 65) (- SRC)))
                  ;; (RAW-RESULT-NOT-SIGN-EXTENDED
                  ;;      (THE (UNSIGNED-BYTE 64)
                  ;;           (ASH (THE (UNSIGNED-BYTE 64) DST)
                  ;;                (THE (SIGNED-BYTE 65) NEG-SRC))))
                  ;; (RAW-RESULT
                  ;;  (IF
                  ;;   (EQL
                  ;;    (MBE
                  ;;        :LOGIC (LOGBIT 63 DST)
                  ;;        :EXEC (LOGAND 1
                  ;;                      (THE (UNSIGNED-BYTE 1)
                  ;;                           (ASH (THE (UNSIGNED-BYTE 64) DST)
                  ;;                                -63))))
                  ;;    1)
                  ;;   (LOGHEAD 64
                  ;;            (ASH (MBE :LOGIC (LOGEXT 64 DST)
                  ;;                      :EXEC (FAST-LOGEXT 64 DST))
                  ;;                 NEG-SRC))
                  ;;   RAW-RESULT-NOT-SIGN-EXTENDED))
                  ;; (RESULT (MBE :LOGIC (N-SIZE 64 RAW-RESULT)
                  ;;              :EXEC RAW-RESULT))
                  (result (if (< (ACL2::BVCHOP 6 SRC) 64)
                          (acl2::bvashr 64 dst src)
                        (ACL2::REPEATBIT 64 (ACL2::GETBIT 63 DST))))
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
                       (OF 0)
                       (OUTPUT-RFLAGS
                        (MBE
                         :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                   :CF CF
                                                   :PF PF
                                                   :ZF ZF
                                                   :SF SF
                                                   :OF OF)
                         :EXEC
                         (THE
                          (UNSIGNED-BYTE 32)
                          (!RFLAGSBITS->CF
                           CF
                           (!RFLAGSBITS->PF
                            PF
                            (!RFLAGSBITS->ZF
                                ZF
                                (!RFLAGSBITS->SF
                                     SF
                                     (!RFLAGSBITS->OF OF INPUT-RFLAGS))))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                             (UNSIGNED-BYTE 32)
                             (!RFLAGSBITS->PF
                                  PF
                                  (!RFLAGSBITS->ZF
                                       ZF
                                       (!RFLAGSBITS->SF SF INPUT-RFLAGS))))))
                        (UNDEFINED-FLAGS
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS 0 :CF 1 :AF 1 :OF 1)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                               1
                               (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))))
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
                         (MBE
                          :LOGIC (CHANGE-RFLAGSBITS INPUT-RFLAGS
                                                    :CF CF
                                                    :PF PF
                                                    :ZF ZF
                                                    :SF SF)
                          :EXEC
                          (THE
                           (UNSIGNED-BYTE 32)
                           (!RFLAGSBITS->CF
                            CF
                            (!RFLAGSBITS->PF
                                 PF
                                 (!RFLAGSBITS->ZF
                                      ZF
                                      (!RFLAGSBITS->SF SF INPUT-RFLAGS)))))))
                        (UNDEFINED-FLAGS
                         (MBE
                           :LOGIC (CHANGE-RFLAGSBITS 0 :AF 1 :OF 1)
                           :EXEC (!RFLAGSBITS->AF 1 (!RFLAGSBITS->OF 1 0)))))
                       (MV OUTPUT-RFLAGS UNDEFINED-FLAGS))))))
                  (OUTPUT-RFLAGS (MBE :LOGIC (N32 OUTPUT-RFLAGS)
                                      :EXEC OUTPUT-RFLAGS))
                  (UNDEFINED-FLAGS (MBE :LOGIC (N32 UNDEFINED-FLAGS)
                                        :EXEC UNDEFINED-FLAGS)))
                 (MV RESULT OUTPUT-RFLAGS UNDEFINED-FLAGS)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (SaR-SPEC-64
                                   ACL2::BVaSHR
                                   ACL2::BVSX-REWRITE
                                   ACL2::BVSHR
                                   ;acl2::bvcat
                                   acl2::slice
                                   ACL2::BVCHOP-OF-LOGTAIL
                                   RFLAGSBITS
                                   zf-spec
                                   logext
                                   ;ACL2::LOGAPP-BECOMES-BVCAT-WHEN-BV
                                   )
                                  (ACL2::LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-8
  (equal (mv-nth 0 (DIV-SPEC-8 dst src))
         (if (acl2::bvlt 16
                   (+ -1 (expt 2 8))
                   (acl2::bvdiv 16 DST (ACL2::BVCHOP 8 SRC)))
             (LIST (CONS 'QUOTIENT
                         (acl2::bvdiv 16 dst (acl2::bvchop 8 src)))
                   (CONS 'REMAINDER
                         (acl2::bvmod 16 dst (acl2::bvchop 8 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-8
  (equal (mv-nth 1 (DIV-SPEC-8 dst src))
         (if (acl2::bvlt 16
                   (+ -1 (expt 2 8))
                   (acl2::bvdiv 16 DST (ACL2::BVCHOP 8 SRC)))
             0
           (acl2::bvdiv 16 dst (acl2::bvchop 8 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-8
  (equal (mv-nth 2 (DIV-SPEC-8 dst src))
         (if (acl2::bvlt 16
                   (+ -1 (expt 2 8))
                   (acl2::bvdiv 16 DST (ACL2::BVCHOP 8 SRC)))
             0
           (acl2::bvmod 16 dst (acl2::bvchop 8 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-8
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-16
  (equal (mv-nth 0 (DIV-SPEC-16 dst src))
         (if (acl2::bvlt 64
                   (+ -1 (expt 2 16))
                   (acl2::bvdiv 32 DST (ACL2::BVCHOP 16 SRC)))
             (LIST (CONS 'QUOTIENT
                         (acl2::bvdiv 32 dst (acl2::bvchop 16 src)))
                   (CONS 'REMAINDER
                         (acl2::bvmod 32 dst (acl2::bvchop 16 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-16
  (equal (mv-nth 1 (DIV-SPEC-16 dst src))
         (if (acl2::bvlt 32
                   (+ -1 (expt 2 16))
                   (acl2::bvdiv 32 DST (ACL2::BVCHOP 16 SRC)))
             0
           (acl2::bvdiv 32 dst (acl2::bvchop 16 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-16
  (equal (mv-nth 2 (DIV-SPEC-16 dst src))
         (if (acl2::bvlt 32
                   (+ -1 (expt 2 16))
                   (acl2::bvdiv 32 DST (ACL2::BVCHOP 16 SRC)))
             0
           (acl2::bvmod 32 dst (acl2::bvchop 16 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-16
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-32
  (equal (mv-nth 0 (DIV-SPEC-32 dst src))
         (if (acl2::bvlt 64
                   (+ -1 (expt 2 32))
                   (acl2::bvdiv 64 DST (ACL2::BVCHOP 32 SRC)))
             (LIST (CONS 'QUOTIENT
                         (acl2::bvdiv 64 dst (acl2::bvchop 32 src)))
                   (CONS 'REMAINDER
                         (acl2::bvmod 64 dst (acl2::bvchop 32 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-32
  (equal (mv-nth 1 (DIV-SPEC-32 dst src))
         (if (acl2::bvlt 64
                   (+ -1 (expt 2 32))
                   (acl2::bvdiv 64 DST (ACL2::BVCHOP 32 SRC)))
             0
           (acl2::bvdiv 64 dst (acl2::bvchop 32 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-32
  (equal (mv-nth 2 (DIV-SPEC-32 dst src))
         (if (acl2::bvlt 64
                   (+ -1 (expt 2 32))
                   (acl2::bvdiv 64 DST (ACL2::BVCHOP 32 SRC)))
             0
           (acl2::bvmod 64 dst (acl2::bvchop 32 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-32
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this value is whether it overflows
(defthm mv-nth-0-of-div-spec-64
  (equal (mv-nth 0 (DIV-SPEC-64 dst src))
         (if (acl2::bvlt 128
                   (+ -1 (expt 2 64))
                   (acl2::bvdiv 128 DST (ACL2::BVCHOP 64 SRC)))
             (LIST (CONS 'QUOTIENT
                         (acl2::bvdiv 128 dst (acl2::bvchop 64 src)))
                   (CONS 'REMAINDER
                         (acl2::bvmod 128 dst (acl2::bvchop 64 src))))
           nil))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the quotient
(defthm mv-nth-1-of-div-spec-64
  (equal (mv-nth 1 (DIV-SPEC-64 dst src))
         (if (acl2::bvlt 128
                   (+ -1 (expt 2 64))
                   (acl2::bvdiv 128 DST (ACL2::BVCHOP 64 SRC)))
             0
           (acl2::bvdiv 128 dst (acl2::bvchop 64 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;; this value is the remainder
(defthm mv-nth-2-of-div-spec-64
  (equal (mv-nth 2 (DIV-SPEC-64 dst src))
         (if (acl2::bvlt 128
                   (+ -1 (expt 2 64))
                   (acl2::bvdiv 128 DST (ACL2::BVCHOP 64 SRC)))
             0
           (acl2::bvmod 128 dst (acl2::bvchop 64 src))))
  :hints (("Goal" :in-theory (e/d (DIV-SPEC-64
                                   acl2::bvdiv
                                   acl2::bvmod
                                   acl2::bvlt)
                                  (ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm shlx-spec-32-redef
  (equal (shlx-spec-32 src cnt)
         (acl2::bvshl 32 src (acl2::bvchop 6 cnt))) ; could change the model to chop to 5 bits
  :hints (("Goal" :in-theory (enable shlx-spec-32 acl2::bvshl))))

(defthm shlx-spec-64-redef
  (equal (shlx-spec-64 src cnt)
         (acl2::bvshl 64 src (acl2::bvchop 6 cnt)))
  :hints (("Goal" :in-theory (enable shlx-spec-64 acl2::bvshl))))

(defthm shrx-spec-32-redef
  (equal (shrx-spec-32 src cnt)
         (acl2::bvshr 32 src (acl2::bvchop 6 cnt))) ; could change the model to chop to 5 bits
  :hints (("Goal" :in-theory (enable shrx-spec-32 acl2::bvshr acl2::logtail-of-bvchop-becomes-slice))))

(defthm shrx-spec-64-redef
  (equal (shrx-spec-64 src cnt)
         (acl2::bvshr 64 src (acl2::bvchop 6 cnt)))
  :hints (("Goal" :in-theory (enable shrx-spec-64 acl2::bvshr acl2::logtail-of-bvchop-becomes-slice))))

;;todo: redefining bvashr could make this nicer
;; or could change the model to chop CNT to 5 bits, since the caller already does that
(defthm sarx-spec-32-redef
  (equal (sarx-spec-32 src cnt)
         (if (< (acl2::bvchop 6 cnt) 32) ; should always be true, since the caller chops it
             (acl2::bvashr 32 src (acl2::bvchop 6 cnt))
           (if (equal (acl2::getbit 31 src) 0)
               0
             4294967295)))
  :hints (("Goal" :in-theory (enable sarx-spec-32 acl2::bvashr acl2::bvshr acl2::bvsx
                                     acl2::logtail-of-bvchop-becomes-slice
                                     acl2::bvchop-of-logtail-becomes-slice))))

(defthm sarx-spec-64-redef
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

(defthm acl2::logext-of-truncate
  (implies (and (signed-byte-p acl2::size acl2::i)
                (posp acl2::size)
                (integerp acl2::j))
           (equal (logext acl2::size (truncate acl2::i acl2::j))
                  (if (and (equal (- (expt 2 (+ -1 acl2::size)))
                                  acl2::i)
                           (equal -1 acl2::j))
                      (- (expt 2 (+ -1 acl2::size)))
                    (truncate acl2::i acl2::j)))))

;todo: add versions for other sizes
(defthm mv-nth-1-of-idiv-spec-32
  (equal (mv-nth 1 (idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (acl2::sbvlt 64 res -2147483648)
               0
             (if (acl2::sbvlt 64 2147483647 res)
                 0
               (acl2::bvchop 32 res)))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(defthm mv-nth-0-of-idiv-spec-32
  (equal (mv-nth 0 (idiv-spec-32 dst src))
         (let ((res (acl2::sbvdiv 64 dst (acl2::bvsx 64 32 src))))
           (if (acl2::sbvlt 64 res -2147483648)
               (LIST (CONS 'QUOTIENT-INT
                           (TRUNCATE (LOGEXT 64 DST)
                                     (LOGEXT 32 SRC)))
                     (CONS 'REMAINDER-INT
                           (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
             (if (acl2::sbvlt 64 2147483647 res)
                 (LIST (CONS 'QUOTIENT-INT
                             (TRUNCATE (LOGEXT 64 DST)
                                       (LOGEXT 32 SRC)))
                       (CONS 'REMAINDER-INT
                             (REM (LOGEXT 64 DST) (LOGEXT 32 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-32 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

;todo: add versions for other sizes
(defthm mv-nth-1-of-idiv-spec-64
  (equal (mv-nth 1 (idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (acl2::sbvlt 128 res (- (expt 2 63)))
               0
             (if (acl2::sbvlt 128 (+ -1 (expt 2 63)) res)
                 0
               (acl2::bvchop 64 res)))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

(defthm mv-nth-0-of-idiv-spec-64
  (equal (mv-nth 0 (idiv-spec-64 dst src))
         (let ((res (acl2::sbvdiv 128 dst (acl2::bvsx 128 64 src))))
           (if (acl2::sbvlt 128 res (- (expt 2 63)))
               (LIST (CONS 'QUOTIENT-INT
                           (TRUNCATE (LOGEXT 128 DST)
                                     (LOGEXT 64 SRC)))
                     (CONS 'REMAINDER-INT
                           (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
             (if (acl2::sbvlt 128 (+ -1 (expt 2 63)) res)
                 (LIST (CONS 'QUOTIENT-INT
                             (TRUNCATE (LOGEXT 128 DST)
                                       (LOGEXT 64 SRC)))
                       (CONS 'REMAINDER-INT
                             (REM (LOGEXT 128 DST) (LOGEXT 64 SRC))))
               nil))))
  :hints (("Goal" :in-theory (e/d (idiv-spec-64 acl2::sbvdiv acl2::sbvlt)
                                  (acl2::sbvlt-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This avoids a case split when doing the sign extension.
(defthm x86-cbw/cwd/cdqe-redef
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
