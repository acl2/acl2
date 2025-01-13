; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

;; ----------------------------------------------------------------------

(include-book "instructions/top"
              :ttags (:syscall-exec :other-non-det :undef-flg))
(include-book "two-byte-opcodes-dispatch"
              :ttags (:syscall-exec :other-non-det :undef-flg))
(include-book "three-byte-opcodes-dispatch"
              :ttags (:syscall-exec :other-non-det :undef-flg))
(include-book "vex-opcodes-dispatch"
              :ttags (:syscall-exec :other-non-det :undef-flg))
(include-book "evex-opcodes-dispatch"
              :ttags (:syscall-exec :other-non-det :undef-flg))
(include-book "cpuid")
(include-book "dispatch-macros")
(include-book "get-prefixes")
(include-book "interrupt-servicing")
(include-book "std/strings/hexify" :dir :system)
(include-book "catalogue-doc")
(include-book "inst-doc")

(local (include-book "dispatch-creator"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d ()
                       (app-view-rml08-no-error
                        (:meta acl2::mv-nth-cons-meta)
                        rme08-value-when-error
                        member-equal))))

;; ----------------------------------------------------------------------

(local (xdoc::set-default-parents x86-decoder))

;; ----------------------------------------------------------------------

;; One-byte Opcode Map:

(make-event

 (b* ((dispatch
       (create-dispatch-for-opcodes #ux00 256 :one-byte (w state))))

   `(define one-byte-opcode-execute
      ((proc-mode     :type (integer 0 #.*num-proc-modes-1*))
       (start-rip     :type (signed-byte   #.*max-linear-address-size*))
       (temp-rip      :type (signed-byte   #.*max-linear-address-size*))
       (prefixes      :type (unsigned-byte #.*prefixes-width*))
       (rex-byte      :type (unsigned-byte 8))
       (opcode        :type (unsigned-byte 8))
       (modr/m        :type (unsigned-byte 8))
       (sib           :type (unsigned-byte 8))
       x86)

      :parents (x86-decoder)
      ;; The following arg will avoid binding __function__ to
      ;; one-byte-opcode-execute. The automatic __function__ binding
      ;; that comes with define causes stack overflows during the guard
      ;; proof of this function.
      :no-function t
      :short "Top-level dispatch function."
      :long "<p>@('one-byte-opcode-execute') is the doorway to all the opcode
     maps (for non-AVX/AVX512 instructions).</p>"

      :guard (and (prefixes-p prefixes)
                  (modr/m-p modr/m)
                  (sib-p sib)
                  (rip-guard-okp proc-mode temp-rip))
      :guard-hints (("Goal"
                     :do-not '(preprocess)
                     :in-theory (e/d () (unsigned-byte-p signed-byte-p))))

      (case opcode ,@dispatch)

      ///

      (defthm x86p-one-byte-opcode-execute
        (implies (x86p x86)
                 (x86p (one-byte-opcode-execute
                        proc-mode start-rip temp-rip
                        prefixes rex-byte opcode modr/m sib x86)))))))

;; ----------------------------------------------------------------------

;; Can be smashed by tty-raw.lsp
(define write-tty ((c :type (unsigned-byte 8))
                       x86)
  :parents (tty)
  :short "Write a byte to the TTY."
  :long "<p>This function writes a byte to the @('tty-out') field of the x86
  state by consing the byte to the front of it. Including @('tty-raw.lsp') in
  raw lisp smashes this function to write to a TCP port instead.</p>"
  :returns (x86 x86p :hyp (x86p x86))
  (!tty-out (cons c (tty-out x86)) x86))

(define read-tty (x86)
  :parents (tty)
  :short "Read a byte from the TTY."
  :long "<p>This function reads a byte from the @('tty-in') field of the x86
  stobj by extracting and returning its @('car') and writing the @('cdr') to
  the @('tty-in') field. If the @('tty-in') field is empty (i.e. it is
  @('nil')), this function returns @('nil') and the @('x86') stobj is
  unmodified. Including @('tty-raw.lsp') in raw lisp smashes this function to
  read from a TCP port instead.</p>"
  :returns (mv byt
               (x86 x86p :hyp (x86p x86)))
  :guard-hints (("Goal" :in-theory (disable ELEM-P-OF-XR-TTY-IN)
                 :use (:instance ELEM-P-OF-XR-TTY-IN (i nil) (x86$a x86))))
  (b* ((buf (tty-in x86))
       ((when (null buf)) (mv nil x86))
       (byt (car buf))
       (x86 (!tty-in (cdr buf) x86)))
      (mv byt x86))
  ///
  (defthm unsigned-byte-p-8-non-nil-read-tty
          (implies (and (x86p x86)
                        (mv-nth 0 (read-tty x86)))
                   (unsigned-byte-p 8 (mv-nth 0 (read-tty x86))))
          :hints (("Goal" :in-theory (disable ELEM-P-OF-XR-TTY-IN)
                   :use (:instance ELEM-P-OF-XR-TTY-IN (i nil) (x86$a x86))))))

(define x86-exec-peripherals (x86)
  :parents (peripherals)
  :short "Execute the peripherals"
  :guard-hints (("Goal" :use ((:instance ELEM-P-OF-XR-LAST-CLOCK-EVENT (i nil) (x86$a x86))
                              (:instance ELEM-P-OF-XR-TIME-STAMP-COUNTER (i nil) (x86$a x86)))
                        :in-theory (disable ELEM-P-OF-XR-LAST-CLOCK-EVENT ELEM-P-OF-XR-TIME-STAMP-COUNTER)))
  :returns (x86 x86p :hyp (x86p x86))
  (b* (((when (app-view x86)) x86)
       ;; Increment the time stamp counter
       (time-stamp-counter (n64 (1+ (time-stamp-counter x86))))
       (x86 (!time-stamp-counter time-stamp-counter x86))

       ;; This is part of the clock device.
       (x86 (if (app-view x86)
              x86
              (wm-low-64 #x100 time-stamp-counter x86)))

       (last-clock-event (last-clock-event x86))
       (x86 (if (and (> last-clock-event 100000)
                     (equal (rflagsBits->intf (rflags x86)) 1)
                     (not (inhibit-interrupts-one-instruction x86))
                     (not (equal (memi #x108 x86) 0))
                     (not (fault x86)))
              (b* ((x86 (!last-clock-event 0 x86))
                   (x86 (!fault (cons '(:interrupt 32) (fault x86)) x86)))
                  x86)
              (!last-clock-event (1+ last-clock-event) x86)))

       ;; Time to check for any TTY output
       ;; The TTY protocol is simple. If 0x3F9 is nonzero
       ;; 0x3F8 has an output character. (physical addresses of course)
       (x86 (b* ((tty-byte-valid (not (equal (memi #x3F9 x86) 0)))
                 ((when (not tty-byte-valid)) x86)
                 (tty-output-byte (memi #x3F8 x86))
                 (x86 (!memi #x3F9 0 x86))
                 (x86 (write-tty tty-output-byte x86)))
              x86))
       ;; We check if the tty input buffer is empty
       ;; If so, we write the new byte and set valid flag
       (x86 (b* ((tty-write-byte-valid (not (equal (memi #x3FB x86) 0)))
                 ((when tty-write-byte-valid) x86)
                 ((mv tty-input x86) (read-tty x86))
                 ((when (equal tty-input nil)) x86)
                 (x86 (!memi #x3FA tty-input x86))
                 (x86 (!memi #x3FB 1 x86)))
                x86)))
      x86))

(define x86-fetch-decode-execute (x86)

  :parents (x86-decoder)
  :short "Top-level step function"

  :long "<p>@('x86-fetch-decode-execute') is the step function of our x86
  interpreter.  It fetches one instruction by looking up the memory address
  indicated by the instruction pointer @('rip'), decodes that instruction, and
  dispatches control to the appropriate instruction semantic function.</p>"

  :prepwork
  ((local
     (defthm guard-helper-1
             (implies (and (<= 0 (+ x y))
                           (<= (+ x y) a)
                           (unsigned-byte-p 32 a)
                           (integerp x) (integerp y))
                      (signed-byte-p 48 (+ x y)))))

   (local
     (defthm guard-helper-2
             (implies (and (<= 0 (+ x y))
                           (<= (+ x y) a)
                           (unsigned-byte-p 32 a)
                           (integerp x) (integerp y))
                      (signed-byte-p 64 (+ x y)))))

   (local
     (defthm guard-helper-3
             (implies (unsigned-byte-p 8 b0)
                      (and
                        (unsigned-byte-p 32 (logior 98 (ash b0 8)))
                        (unsigned-byte-p 24 (logior 196 (ash b0 8)))
                        (unsigned-byte-p 24 (logior 197 (ash b0 8)))))))

   (local
     (defthm guard-helper-4
             (implies (and (unsigned-byte-p 4 num)
                           (signed-byte-p 48 rip))
                      (and (signed-byte-p 64 (+ 1 rip num))
                           (signed-byte-p 64 (+ 2 rip num))))))

   (local
     (defthm guard-helper-5
             (implies (unsigned-byte-p 4 num)
                      (signed-byte-p 48 (+ 1 num)))))

   (local
     (defthm dumb-integerp-of-mv-nth-1-rme08-rule
             (implies (force (x86p x86))
                      (integerp (mv-nth 1 (rme08 proc-mode eff-addr seg-reg r-x x86))))
             :rule-classes (:rewrite :type-prescription)))

   (local
     (defthm unsigned-byte-p-from-<=
             (implies (and (<= x y)
                           (unsigned-byte-p n y)
                           (natp x))
                      (unsigned-byte-p n x))))

   (local (in-theory (e/d* ()
                           (signed-byte-p
                             unsigned-byte-p
                             not (tau-system)))))

   ;; For RoW proofs involving these bitstructs' accessors and updaters:
   (local (in-theory (e/d (!vex-prefixes->byte0-is-vex-prefixes
                            !vex-prefixes->byte1-is-vex-prefixes
                            !vex-prefixes->byte2-is-vex-prefixes
                            !evex-prefixes->byte0-is-evex-prefixes
                            !evex-prefixes->byte1-is-evex-prefixes
                            !evex-prefixes->byte2-is-evex-prefixes
                            !evex-prefixes->byte3-is-evex-prefixes)
                          ()))))

  :guard-hints
  (("Goal" :in-theory (e/d (modr/m-p
                             prefixes-p
                             vex-prefixes-byte0-p
                             add-to-*ip
                             add-to-*ip-is-i48p-rewrite-rule)
                           ())))

  (b* (;; We don't want our interpreter to take a step if the machine is in a
       ;; bad state.  Such checks are made in x86-run but I am duplicating them
       ;; here in case this function is being used at the top-level.
       ((when (or (ms x86) (fault x86))) x86)
       (app-view? (app-view x86))

       (inhibit-interrupts-one-instruction? (inhibit-interrupts-one-instruction x86))
       (x86 (b* ((ctx 'x86-fetch-decode-execute)

                 (proc-mode (x86-operation-mode x86))
                 (64-bit-modep (equal proc-mode #.*64-bit-mode*))

                 (start-rip (the (signed-byte #.*max-linear-address-size*)
                                 (read-*ip proc-mode x86)))

                 ((mv flg
                      (the (unsigned-byte #.*prefixes-width*) prefixes)
                      (the (unsigned-byte 8) rex-byte)
                      x86)
                  (get-prefixes proc-mode start-rip 0 0 15 x86))
                 ;; Among other errors (including if there are 15 prefix (legacy and REX)
                 ;; bytes, which leaves no room for an opcode byte in a legal
                 ;; instruction), if get-prefixes detects a non-canonical address while
                 ;; attempting to fetch prefixes, flg will be non-nil.
                 ((when flg)
                  (!!ms-fresh :error-in-reading-prefixes flg))

                 ((the (unsigned-byte 8) opcode/vex/evex-byte)
                  (prefixes->nxt prefixes))

                 ((the (unsigned-byte 4) prefix-length)
                  (prefixes->num prefixes))

                 ((mv flg temp-rip) (add-to-*ip proc-mode start-rip (1+ prefix-length) x86))
                 ((when flg) (!!ms-fresh :increment-error flg))

                 (vex-byte0? (or (equal opcode/vex/evex-byte #.*vex2-byte0*)
                                 (equal opcode/vex/evex-byte #.*vex3-byte0*)))
                 ;; If opcode/vex/evex-byte is either 0xC4 (*vex3-byte0*) or 0xC5
                 ;; (*vex2-byte0*), then we always have a VEX-encoded instruction in the
                 ;; 64-bit mode.  But in the 32-bit mode, these bytes may not signal the
                 ;; start of the VEX prefixes.  0xC4 and 0xC5 map to LES and LDS
                 ;; instructions (respectively) in the 32-bit mode if bits[7:6] of the
                 ;; next byte, which we call les/lds-distinguishing-byte below, are *not*
                 ;; 11b.  Otherwise, they signal the start of VEX prefixes in the 32-bit
                 ;; mode too.

                 ;; Though the second byte acts as the distinguishing byte only in the
                 ;; 32-bit mode, we always read the first two bytes of a VEX prefix in
                 ;; this function for simplicity.
                 ((mv flg les/lds-distinguishing-byte x86)
                  (if vex-byte0?
                    (rme08-opt proc-mode temp-rip #.*cs* :x x86)
                    (mv nil 0 x86)))
                 ((when flg)
                  (!!ms-fresh :les/lds-distinguishing-byte-read-error flg))
                 ;; If the instruction is indeed LDS or LES in the 32-bit mode, temp-rip
                 ;; is incremented after the ModR/M is detected (see add-to-*ip following
                 ;; modr/m? below).
                 ((when (and vex-byte0?
                             (or 64-bit-modep
                                 (and (not 64-bit-modep)
                                      (equal (part-select
                                               les/lds-distinguishing-byte
                                               :low 6 :high 7)
                                             #b11)))))
                  ;; Handle VEX-encoded instructions separately.
                  (b* (((mv flg temp-rip)
                        (add-to-*ip proc-mode temp-rip 1 x86))
                       ((when flg)
                        (!!ms-fresh :vex-byte1-increment-error flg))
                       (vex-prefixes
                         (!vex-prefixes->byte0 opcode/vex/evex-byte 0))
                       (vex-prefixes
                         (!vex-prefixes->byte1 les/lds-distinguishing-byte vex-prefixes)))
                      (vex-decode-and-execute
                        proc-mode
                        start-rip temp-rip prefixes rex-byte vex-prefixes x86)))

                 (opcode/evex-byte opcode/vex/evex-byte)

                 (evex-byte0? (equal opcode/evex-byte #.*evex-byte0*))
                 ;; Byte 0x62 is byte0 of the 4-byte EVEX prefix.  In 64-bit mode, this
                 ;; byte indicates the beginning of the EVEX prefix --- note that in the
                 ;; pre-AVX512 era, this would lead to a #UD, but we don't model that
                 ;; here.

                 ;; Similar to the VEX prefix situation, things are more complicated in
                 ;; the 32-bit mode, where 0x62 aliases to the 32-bit only BOUND
                 ;; instruction.  The Intel Manuals (May, 2018) don't seem to say
                 ;; anything explicitly about how one differentiates between the EVEX
                 ;; prefix and the BOUND instruction in 32-bit mode.  However, a legal
                 ;; BOUND instruction must always have a memory operand as its second
                 ;; operand, which means that ModR/M.mod != 0b11 (see Intel Vol. 2, Table
                 ;; 2-2).  So, if bits [7:6] of the byte following 0x62 are NOT 0b11,
                 ;; then 0x62 refers to a legal BOUND instruction.  Otherwise, it signals
                 ;; the beginning of the EVEX prefix.

                 ;; Again, similar to the VEX prefix situation: though the second byte
                 ;; acts as the distinguishing byte only in the 32-bit mode, we always
                 ;; read the first two bytes of an EVEX prefix in this function for
                 ;; simplicity.
                 ((mv flg bound-distinguishing-byte x86)
                  (if evex-byte0?
                    (rme08-opt proc-mode temp-rip #.*cs* :x x86)
                    (mv nil 0 x86)))
                 ((when flg)
                  (!!ms-fresh :bound-distinguishing-byte-read-error flg))
                 ;; If the instruction is indeed BOUND in the 32-bit mode, temp-rip is
                 ;; incremented after the ModR/M is detected (see add-to-*ip following
                 ;; modr/m? below).
                 ((when (and evex-byte0?
                             (or 64-bit-modep
                                 (and (not 64-bit-modep)
                                      (equal (part-select
                                               bound-distinguishing-byte
                                               :low 6 :high 7)
                                             #b11)))))
                  ;; Handle EVEX-encoded instructions separately.
                  (b* (((mv flg temp-rip)
                        (add-to-*ip proc-mode temp-rip 1 x86))
                       ((when flg)
                        (!!ms-fresh :evex-byte1-increment-error flg))
                       (evex-prefixes
                         (!evex-prefixes->byte0 opcode/evex-byte 0))
                       (evex-prefixes
                         (!evex-prefixes->byte1 bound-distinguishing-byte evex-prefixes)))
                      (evex-decode-and-execute
                        proc-mode
                        start-rip temp-rip prefixes rex-byte evex-prefixes x86)))


                 (opcode-byte opcode/evex-byte)

                 ;; Possible values of opcode-byte:

                 ;; The opcode-byte should not contain any of the (legacy) prefixes, REX
                 ;; bytes, VEX prefixes, and EVEX prefixes -- by this point, all these
                 ;; prefix bytes should have been processed.  So, here are the kinds of
                 ;; values opcode-byte can have:

                 ;; 1. An opcode of the one-byte opcode map: this function prefetches the
                 ;;    ModR/M and SIB bytes for these opcodes.  The function
                 ;;    one-byte-opcode-execute case-splits on this opcode byte and calls
                 ;;    the appropriate instruction semantic function.

                 ;; 2. #x0F -- two-byte or three-byte opcode indicator: modr/m? is set to
                 ;;    NIL (see *64-bit-mode-one-byte-has-modr/m-ar* and
                 ;;    *32-bit-mode-one-byte-has-modr/m-ar*).  No ModR/M and SIB bytes
                 ;;    are prefetched by this function for the two-byte or three-byte
                 ;;    opcode maps.  In one-byte-opcode-execute, we call
                 ;;    two-byte-opcode-decode-and-execute, where we fetch the ModR/M and
                 ;;    SIB bytes for the two-byte opcodes or dispatch control to
                 ;;    three-byte-opcode-decode-and-execute when appropriate (i.e., when
                 ;;    the byte following #x0F is either #x38 or #x3A).  Note that in
                 ;;    this function, temp-rip will not be incremented beyond this point
                 ;;    for these opcodes --- i.e., it points at the byte *following*
                 ;;    #x0F.

                 ;; The modr/m and sib byte prefetching in this function is biased
                 ;; towards the one-byte opcode map.  The functions
                 ;; two-byte-opcode-decode-and-execute and
                 ;; three-byte-opcode-decode-and-execute do their own prefetching.  We
                 ;; made this choice to take advantage of the fact that the most
                 ;; frequently encountered instructions are from the one-byte opcode map.
                 ;; Another reason is that the instruction encoding syntax is clearer to
                 ;; understand this way; this is a nice way of seeing how one opcode map
                 ;; "escapes" into another.

                 (modr/m? (one-byte-opcode-ModR/M-p proc-mode opcode-byte))
                 ((mv flg (the (unsigned-byte 8) modr/m) x86)
                  (if modr/m?
                    (if (or vex-byte0? evex-byte0?)
                      ;; The above will be true only if the instruction is LES or LDS
                      ;; or BOUND in the 32-bit mode.
                      (mv nil les/lds-distinguishing-byte x86)
                      (rme08-opt proc-mode temp-rip #.*cs* :x x86))
                    (mv nil 0 x86)))
                 ((when flg)
                  (!!ms-fresh :modr/m-byte-read-error flg))

                 ((mv flg temp-rip)
                  (if modr/m?
                    (add-to-*ip proc-mode temp-rip 1 x86)
                    (mv nil temp-rip)))
                 ((when flg) (!!ms-fresh :increment-error flg))

                 (sib? (and modr/m?
                            (b* ((p4? (eql #.*addr-size-override*
                                           (the (unsigned-byte 8) (prefixes->adr prefixes))))
                                 (16-bit-addressp (eql 2 (select-address-size
                                                           proc-mode p4? x86))))
                                (x86-decode-SIB-p modr/m 16-bit-addressp))))

                 ((mv flg (the (unsigned-byte 8) sib) x86)
                  (if sib?
                    (rme08-opt proc-mode temp-rip #.*cs* :x x86)
                    (mv nil 0 x86)))
                 ((when flg)
                  (!!ms-fresh :sib-byte-read-error flg))

                 ((mv flg temp-rip)
                  (if sib?
                    (add-to-*ip proc-mode temp-rip 1 x86)
                    (mv nil temp-rip)))
                 ((when flg) (!!ms-fresh :increment-error flg))

                 (x86 (one-byte-opcode-execute
                        proc-mode start-rip temp-rip prefixes rex-byte opcode-byte
                        modr/m sib x86)))
                x86))

       ((when app-view?) x86)

       (x86 (if (enable-peripherals x86)
              (x86-exec-peripherals x86)
              x86))
       (x86 (if (and (fault x86)
                     (handle-exceptions x86))
              (handle-faults x86)
              x86))

       (x86 (if inhibit-interrupts-one-instruction?
              (!inhibit-interrupts-one-instruction nil x86)
              x86)))
      x86)


  ///

  (defrule x86p-x86-fetch-decode-execute
           (implies (x86p x86)
                    (x86p (x86-fetch-decode-execute x86)))
           ;; for speed:
           :disable (xw-xw-inter-field-arrange-writes
                     mv-nth-0-of-add-to-*ip-when-64-bit-modep
                     mv-nth-1-of-add-to-*ip-when-64-bit-modep
                     bitops::part-select-width-low$inline
                     bitops::part-select-low-high$inline
                     mv-nth
                     i48p-xr-rip
                     right-shift-to-logtail
                     acl2::logtail-identity
                     get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix
                     get-prefixes-opener-lemma-group-2-prefix
                     get-prefixes-opener-lemma-group-1-prefix
                     get-prefixes-opener-lemma-group-4-prefix
                     get-prefixes-opener-lemma-group-3-prefix
                     get-prefixes-opener-lemma-zero-cnt
                     get-prefixes-opener-lemma-no-prefix-byte
                     get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix
                     get-prefixes-does-not-modify-x86-state-in-app-view
                     num-prefixes-get-prefixes-bound)
           :enable add-to-*ip-is-i48p-rewrite-rule)

  (defthmd ms-fault-and-x86-fetch-decode-and-execute
           (implies (and (x86p x86)
                         (or (ms x86) (fault x86)))
                    (equal (x86-fetch-decode-execute x86) x86)))

  (defthm x86-fetch-decode-execute-opener
    ;; Note that this opener lemma applies to all supported modes of operation
    ;; (see x86-operation-mode).

    ;; TODO: Extend to VEX and EVEX prefixes.
    (implies
     (and
      (app-view x86)
      (not (ms x86))
      (not (fault x86))
      (equal proc-mode (x86-operation-mode x86))
      (equal start-rip (read-*ip proc-mode x86))
      (not (mv-nth 0 (get-prefixes proc-mode start-rip 0 0 15 x86)))
      (equal prefixes (mv-nth 1 (get-prefixes proc-mode start-rip 0 0 15 x86)))
      (equal rex-byte (mv-nth 2 (get-prefixes proc-mode start-rip 0 0 15 x86)))
      (equal opcode/vex/evex-byte (prefixes->nxt prefixes))
      (equal prefix-length (prefixes->num prefixes))
      (equal temp-rip0
             (mv-nth 1 (add-to-*ip proc-mode start-rip (1+ prefix-length) x86)))

      ;; *** No VEX prefixes ***
      (not (equal opcode/vex/evex-byte #.*vex3-byte0*))
      (not (equal opcode/vex/evex-byte #.*vex2-byte0*))
      ;; *** No EVEX prefixes ***
      (not (equal opcode/vex/evex-byte #.*evex-byte0*))

      (equal modr/m?
             (one-byte-opcode-ModR/M-p proc-mode opcode/vex/evex-byte))
      (equal modr/m (if modr/m?
                        (mv-nth 1 (rme08 proc-mode temp-rip0 #.*cs* :x x86))
                      0))
      (equal temp-rip1 (if modr/m?
                           (mv-nth 1 (add-to-*ip proc-mode temp-rip0 1 x86))
                         temp-rip0))
      (equal p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))
      (equal 16-bit-addressp (equal 2 (select-address-size proc-mode p4? x86)))
      (equal sib? (and modr/m? (x86-decode-sib-p modr/m 16-bit-addressp)))
      (equal sib (if sib? (mv-nth 1 (rme08 proc-mode temp-rip1 #.*cs* :x x86)) 0))

      (equal temp-rip2 (if sib?
                           (mv-nth 1 (add-to-*ip proc-mode temp-rip1 1 x86))
                         temp-rip1))

      (or (app-view x86) (not (marking-view x86)))
      (not (mv-nth 0 (add-to-*ip proc-mode start-rip (1+ prefix-length) x86)))
      (if modr/m?
          (and (not (mv-nth 0 (add-to-*ip proc-mode temp-rip0 1 x86)))
               (not (mv-nth 0 (rme08 proc-mode temp-rip0 #.*cs* :x x86))))
        t)
      (if sib?
          (and (not (mv-nth 0 (add-to-*ip proc-mode temp-rip1 1 x86)))
               (not (mv-nth 0 (rme08 proc-mode temp-rip1 #.*cs* :x x86))))
        t)
      (x86p x86)
      ;; Print the rip and the first opcode byte of the instruction
      ;; under consideration after all the non-trivial hyps (above) of
      ;; this rule have been relieved:
      (syntaxp
       (and (not (cw "~% [ x86instr @ rip: ~p0 ~%" start-rip))
            (not (cw "              op0: ~s0 ] ~%"
                     (str::hexify (unquote opcode/vex/evex-byte)))))))
     (equal
      (x86-fetch-decode-execute x86)
      (one-byte-opcode-execute
       proc-mode start-rip temp-rip2 prefixes rex-byte
       opcode/vex/evex-byte modr/m sib x86)))
    :hints (("Goal"
             :cases ((app-view x86))
             :in-theory (e/d ()
                             (one-byte-opcode-execute
                              signed-byte-p
                              not
                              member-equal))))))

(in-theory (e/d (vex-decode-and-execute
                 evex-decode-and-execute
                 one-byte-opcode-execute
                 two-byte-opcode-execute
                 first-three-byte-opcode-execute
                 second-three-byte-opcode-execute)
                ()))

;; ----------------------------------------------------------------------

;; Running the interpreter:

;; Schedule: (in the M1 style)

(defun binary-clk+ (i j)
  (+ (nfix i) (nfix j)))

(defthm clk+-associative
  (implies (binary-clk+ (binary-clk+ i j) k)
           (binary-clk+ i (binary-clk+ j k))))

(defmacro clk+ (&rest args)
  (if (endp args)
      0
    (if (endp (cdr args))
        (car args)
      `(binary-clk+ ,(car args)
                    (clk+ ,@(cdr args))))))

(define x86-run
  ;; I fixed n to a fixnum for efficiency.  Also, executing more than
  ;; 2^59 instructions in one go seems kind of daunting.
  ((n :type (unsigned-byte 59))
   x86)

  :parents (x86-decoder)
  :short "Top-level specification function for the x86 ISA model"
  :long "<p>@('x86-run') returns the x86 state obtained by executing
  @('n') instructions or until it halts, whatever comes first.  It
  simply called the step function @(see x86-fetch-decode-execute)
  recursively.</p>"

  :returns (x86 x86p :hyp (x86p x86))

  (cond ((fault x86)
         x86)
        ((ms x86)
         x86)
        ((mbe :logic (zp n)
              :exec (equal 0 n))
         x86)
        (t (let* ((x86 (x86-fetch-decode-execute x86))
                  (n (the (unsigned-byte 59) (1- n))))
             (x86-run n x86))))


  ///

  (defthmd x86-run-and-x86-fetch-decode-and-execute-commutative
    ;; x86-fetch-decode-execute and x86-run can commute.
    (implies (and (natp k)
                  (x86p x86)
                  (not (ms x86))
                  (not (fault x86)))
             (equal (x86-run k (x86-fetch-decode-execute x86))
                    (x86-fetch-decode-execute (x86-run k x86))))
    :hints (("Goal" :in-theory (e/d
                                (ms-fault-and-x86-fetch-decode-and-execute) ()))))


  ;; Some opener theorems for x86-run:

  (defthm x86-run-halted
    (implies (or (ms x86) (fault x86))
             (equal (x86-run n x86) x86)))

  (defthm x86-run-opener-not-ms-not-fault-zp-n
    (implies (and (syntaxp (quotep n))
                  (zp n))
             (equal (x86-run n x86) x86)))

  (defthm x86-run-opener-not-ms-not-zp-n
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (syntaxp (quotep n))
                  (not (zp n)))
             (equal (x86-run n x86)
                    (x86-run (1- n) (x86-fetch-decode-execute x86)))))

  ;; To enable compositional reasoning, we prove the following two
  ;; theorems:

  (defthm x86-run-plus
    (implies (and (natp n1)
                  (natp n2)
                  (syntaxp (quotep n1)))
             (equal (x86-run (clk+ n1 n2) x86)
                    (x86-run n2 (x86-run n1 x86)))))

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defthmd x86-run-plus-1
      (implies (and (natp n1)
                    (natp n2)
                    (syntaxp (quotep n1)))
               (equal (x86-run (clk+ n1 n2) x86)
                      (x86-run n1 (x86-run n2 x86)))))))

(in-theory (disable binary-clk+))

;; ----------------------------------------------------------------------

;; Some variants of x86-run:

(define x86-run-steps1
  ((n :type (unsigned-byte 59))
   (n0 :type (unsigned-byte 59))
   x86)

  :enabled t
  :guard (and (natp n)
              (natp n0)
              (<= n n0))

  (b* ((diff (the (unsigned-byte 59) (- n0 n)))
       ;; (- (if (equal (mod diff 100000000) 0)
       ;;      (save-x86 "x86-state" x86)
       ;;      nil))
       )
      (cond ((ms x86)
             (mv diff x86))
            ((fault x86)
             (mv diff x86))
            ((zp n)
             (let* ((ctx 'x86-run)
                    (x86 (!!ms-fresh :timeout t)))
               (mv diff x86)))
            (t (b* ((x86 (x86-fetch-decode-execute x86))
                    (n-1 (the (unsigned-byte 59) (1- n))))
                   (x86-run-steps1 n-1 n0 x86))))))

(defun next-n-bytes-null-p (addr len x86)
  (declare (xargs :stobjs (x86)
                  :mode :program))
  (b* (((when (equal len 0)) (mv t x86))
       ((mv flg val x86) (rvm08 addr x86))
       ((when flg) (mv t x86))
       ((when (not (equal val 0))) (mv nil x86)))
      (next-n-bytes-null-p (1+ addr) (1- len) x86)))

(define x86-run-steps
  ((n :type (unsigned-byte 59))
   x86)

  :parents (x86-decoder)
  :short "An alternative to @(see x86-run)"
  :long "<p> @('x86-run-steps') returns two values --- number of steps
  taken by the machine before it comes to a halt and the x86 state.
  Note that the number of steps will always be less than or equal to
  @('n').</p>"

  (x86-run-steps1 n n x86)

  ///

  (defthm x86-run-steps1-is-x86-run-ms
    (implies (ms x86)
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (x86-run n x86))))

  (defthm x86-run-steps1-is-x86-run-zp-n
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (zp n))
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (!ms (list (list* 'x86-run
                                      :rip (rip x86)
                                      '(:timeout t)))
                         (x86-run n x86))))
    :hints (("Goal" :expand (x86-run n x86))))

  (defthm x86-run-steps1-open
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (not (zp n)))
             (equal (mv-nth 1 (x86-run-steps1 n n0 x86))
                    (mv-nth 1 (x86-run-steps1 (1- n) n0
                                              (x86-fetch-decode-execute x86)))))))

(in-theory (disable x86-run-steps1))

(define x86-fetch-decode-execute-halt
  ((halt-address :type (signed-byte   #.*max-linear-address-size*))
   x86)
  :enabled t
  :parents (x86-decoder)
  :inline t
  :no-function t

  :short "Alternative version of @(tsee x86-fetch-decode-execute) that sets the
  @('MS') field if @('rip') is equal to @('halt-address')"

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ((local (in-theory (e/d* () (signed-byte-p unsigned-byte-p not)))))

  (if (equal (the (signed-byte #.*max-linear-address-size*)
               (rip x86))
             halt-address)
      (b* ((ctx 'x86-fetch-decode-execute-halt))
        (!!ms-fresh))
    (x86-fetch-decode-execute x86)))

(define x86-run-halt
  ((halt-address :type (signed-byte   #.*max-linear-address-size*))
   (n            :type (unsigned-byte 59))
   x86)

  :parents (x86-decoder)
  :short "Alternative version of @(tsee x86-run) that uses @(tsee
  x86-fetch-decode-execute-halt) instead of @(tsee x86-fetch-decode-execute)"

  :returns (x86 x86p :hyp (x86p x86))

  (cond ((fault x86) x86)
        ((ms x86) x86)
        ((mbe :logic (zp n) :exec (equal 0 n)) x86)
        (t (let* ((x86 (x86-fetch-decode-execute-halt halt-address x86))
                  (n (the (unsigned-byte 59) (1- n))))
             (x86-run-halt halt-address n x86)))))

(define x86-run-halt-count
  ((halt-address :type (signed-byte   #.*max-linear-address-size*))
   (n            :type (unsigned-byte 59))
   x86
   (n0        :type (unsigned-byte 59)))

  :guard (<= n n0) ;; n == n0, to begin with.

  :short "A combination in functionality of @(tsee x86-run-steps) and @(tsee
  x86-run-halt)"

  :long "<p>Run @('n') instructions or till @('halt-address') is reached,
  whichever comes first.  This function also returns the number of times @(tsee
  x86-fetch-decode-execute-halt) is executed.  Note that
  @('x86-fetch-decode-execute-halt') is executed one more time than @(tsee
  x86-fetch-decode-execute) --- i.e., when @('rip == halt-address').</p>"

  :returns (mv (steps natp :hyp (and (natp n0) (natp n))
                      :rule-classes :type-prescription)
               (x86 x86p :hyp (x86p x86)))

  (if (mbt (<= n n0))

      (cond ((or (fault x86)
                 (ms x86)
                 (mbe :logic (zp n) :exec (equal 0 n)))
             (mv (the (unsigned-byte 59) (- n0 n)) x86))
            (t
             (let* ((x86 (x86-fetch-decode-execute-halt halt-address x86))
                    (n (the (unsigned-byte 59) (1- n))))
               (x86-run-halt-count halt-address n x86 n0))))

    (mv 0 x86)))

;; ----------------------------------------------------------------------
