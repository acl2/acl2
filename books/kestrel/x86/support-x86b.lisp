; Supporting material for x86 code proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; This file brings in the whole x86 model.  That gets us fetch-decode-execute, etc.

(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute, ONE-BYTE-OPCODE-EXECUTE, etc.
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "support-x86") ; todo

;; some of these are for symbolic execution:
(in-theory (acl2::enable* x86isa::X86-EFFECTIVE-ADDR-FROM-SIB
                          x86isa::instruction-decoding-and-spec-rules ;this one is a ruleset
                          x86isa::jcc/cmovcc/setcc-spec
                          x86isa::gpr-and-spec-4
                          x86isa::gpr-xor-spec-4
                          x86isa::GPR-ADD-SPEC-4

                          x86isa::one-byte-opcode-execute ;; x86isa::one-byte-opcode-execute
                          ;; !rgfi-size
                          x86isa::x86-operand-to-reg/mem

                          ;;These appear to eventually call xw (via
                          ;;!rgfi), so we'll keep them enabled
                          ;;since xw is our normal form:
                          x86isa::wr08
                          x86isa::wr16
                          x86isa::wr32
                          x86isa::wr64

                          ;;These appear to eventually call xr (via
                          ;;rgfi), so we'll keep them enabled
                          ;;since xw is our normal form:
                          x86isa::rr08
                          x86isa::rr16
                          x86isa::rr32
                          x86isa::rr64

                          x86isa::wml32
                          x86isa::wml64
                          x86isa::riml08
                          x86isa::riml32

                          x86isa::x86-operand-from-modr/m-and-sib-bytes
                          x86isa::riml-size

                          x86isa::check-instruction-length

                          x86isa::select-segment-register

                          x86isa::n08-to-i08
                          x86isa::n16-to-i16
                          x86isa::n32-to-i32
                          x86isa::n64-to-i64
                          x86isa::n128-to-i128

                          x86isa::two-byte-opcode-decode-and-execute
                          x86isa::x86-effective-addr-when-64-bit-modep
                          x86isa::x86-effective-addr-32/64
                          ;; Flags
                          x86isa::write-user-rflags
                          x86isa::zf-spec))

;; should some of these be local?
(in-theory (disable logcount
                    ;x86isa::write-user-rflags-and-xw
                    byte-listp
                    x86isa::combine-bytes
                    member-equal
                    get-prefixes-opener-lemma-zero-cnt ;for speed
                    x86isa::create-canonical-address-list
                    (:e x86isa::create-canonical-address-list)
                    zf-spec))

;; splits the simulation!
(defthm x86-fetch-decode-execute-of-set-rip-split
  (equal (x86-fetch-decode-execute (xw :rip nil (if test rip1 rip2) x86))
         (if test
             (x86-fetch-decode-execute (xw :rip nil rip1 x86))
           (x86-fetch-decode-execute (xw :rip nil rip2 x86)))))

;; splits the simulation!
(defthm x86-fetch-decode-execute-of-if
  (equal (x86-fetch-decode-execute (if test x86_1 x86_2))
         (if test
             (x86-fetch-decode-execute x86_1)
           (x86-fetch-decode-execute x86_2))))

(acl2::defopeners x86-fetch-decode-execute :hyps ((not (ms x86)) (not (x86isa::fault x86))))
(in-theory (disable x86isa::x86-fetch-decode-execute-base)) ;disable because for ACL2 reasoning there is an opener rule

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Avoids the b* at the top level
(defthm x86isa::get-prefixes-does-not-modify-x86-state-in-app-view-new
  (implies (app-view x86)
           (equal (mv-nth 3
                          (get-prefixes x86isa::proc-mode
                                        x86isa::start-rip x86isa::prefixes
                                        x86isa::rex-byte x86isa::cnt x86))
                  x86))
  :hints (("Goal" :use x86isa::get-prefixes-does-not-modify-x86-state-in-app-view)))

(defthm get-one-byte-prefix-array-code-of-if
  (equal (get-one-byte-prefix-array-code (if test b1 b2))
         (if test
             (get-one-byte-prefix-array-code b1)
           (get-one-byte-prefix-array-code b2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 64-bit-mode-one-byte-opcode-modr/m-p$inline-of-if
  (equal (64-bit-mode-one-byte-opcode-modr/m-p$inline (if test tp ep))
         (if test
             (64-bit-mode-one-byte-opcode-modr/m-p$inline tp)
             (64-bit-mode-one-byte-opcode-modr/m-p$inline ep))))

;TODO: we could just build this kind of thing into axe..
(defthm 64-bit-mode-one-byte-opcode-modr/m-p$inline-of-if-when-constants
  (implies (syntaxp (and (quotep tp)
                         (quotep ep)))
           (equal (64-bit-mode-one-byte-opcode-modr/m-p$inline (if test tp ep))
                  (if test
                      (64-bit-mode-one-byte-opcode-modr/m-p$inline tp)
                    (64-bit-mode-one-byte-opcode-modr/m-p$inline ep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm feature-flags-opener
  (implies (consp features)
           (equal (feature-flags features)
                  (if (equal 0 (feature-flag (first features)))
                      0
                    (feature-flags (rest features)))))
  :hints (("Goal" :in-theory (enable feature-flags))))

;; maybe not needed since we have the constant-opener for the call on nil
(defthm feature-flags-base
  (implies (not (consp features))
           (equal (feature-flags features)
                  1))
  :hints (("Goal" :in-theory (enable feature-flags))))

(acl2::defopeners get-prefixes)


;todo: make defopeners use the untranslated body
;todo: make defopeners check for redundancy
;todo: make defopeners suppress printing
(acl2::defopeners one-byte-opcode-execute :hyps ((syntaxp (and (quotep x86isa::prefixes)
                                                               (quotep x86isa::rex-byte)
                                                               (quotep x86isa::opcode)
                                                               (quotep x86isa::modr/m)
                                                               (quotep x86isa::sib)))))

(in-theory (disable x86isa::one-byte-opcode-execute))


;helps get rid of irrelevant stuff (even though we expect to not really need this)
(defthm mv-nth-0-of-get-prefixes-of-xw-of-irrel
  (implies (or (eq :rgf field)
               (eq :rip field)
               (eq :undef field)) ;gen
           (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (xw field index value x86)))
                  (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
  :hints (("Goal" :induct (GET-PREFIXES proc-mode START-RIP PREFIXES rex-byte CNT X86)
           :in-theory (e/d ( ;xw
                            add-to-*ip
                            get-prefixes)
                           (;acl2::unsigned-byte-p-from-bounds
                            ;acl2::bvchop-identity
                            ;x86isa::part-install-width-low-becomes-bvcat-32
                            ;for speed:
                            ;CANONICAL-ADDRESS-P-BETWEEN
                            ;x86isa::PART-SELECT-WIDTH-LOW-BECOMES-SLICE
                            ;x86isa::SLICE-OF-PART-INSTALL-WIDTH-LOW
                            ;acl2::MV-NTH-OF-IF
                            x86isa::GET-PREFIXES-OPENER-LEMMA-NO-PREFIX-BYTE
                            )))))

(defthm mv-nth-1-of-get-prefixes-of-xw-of-irrel
  (implies (or (eq :rgf field)
               (eq :rip field)
               (eq :undef field)) ;gen
           (equal (mv-nth 1
                          (get-prefixes proc-mode start-rip prefixes rex-byte
                                        cnt (xw field index value x86)))
                  (mv-nth 1
                          (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
  :hints (("Goal" :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
           :in-theory (e/d (get-prefixes
                            add-to-*ip)
                                  (;acl2::unsigned-byte-p-from-bounds
                                   ;acl2::bvchop-identity
                                   ;x86isa::part-install-width-low-becomes-bvcat-32
                                   combine-bytes-when-singleton ;for speed
                                   x86isa::get-prefixes-opener-lemma-no-prefix-byte ;for speed
                                   ;x86isa::part-select-width-low-becomes-slice ;for speed
                                   ACL2::ZP-OPEN
                                   ;acl2::MV-NTH-OF-IF
                                   )))))


;seems needed - todo
(in-theory (enable x86isa::GPR-SUB-SPEC-8$INLINE))
