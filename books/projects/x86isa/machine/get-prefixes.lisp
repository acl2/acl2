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

(include-book "top-level-memory")
(include-book "prefix-modrm-sib-decoding")
(include-book "decoding-and-spec-utils")

;; ----------------------------------------------------------------------

(defsection x86-decoder
  :parents (machine)
  :short "Definitions of the x86 fetch, decode, and execute function
  and the top-level run function"
  )

(local (xdoc::set-default-parents x86-decoder))

;; ----------------------------------------------------------------------

(define get-prefixes
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (start-rip :type (signed-byte #.*max-linear-address-size*))
   (prefixes  :type (unsigned-byte #.*prefixes-width*))
   (rex-byte  :type (unsigned-byte 8))
   (cnt       :type (integer 0 15))
   x86)

  :guard (prefixes-p prefixes)
  :guard-hints
  (("Goal" :in-theory
    (e/d ()
         (negative-logand-to-positive-logand-with-integerp-x
          signed-byte-p))))

  :measure (nfix cnt)
  :hints (("Goal" :in-theory (e/d () ((tau-system)))))

  :returns
  (mv flg

      ;; This is in fact a (unsigned-byte-p *prefixes-width*)
      ;; (i.e. a prefixes-p, see (defbitstruct prefixes ...)),
      ;; as proved later in this DEFINE form.
      (new-prefixes natp :rule-classes :type-prescription
                    :hyp (forced-and (natp prefixes)
                                     (canonical-address-p start-rip)
                                     (x86p x86))
                    :hints
                    (("Goal"
                      :in-theory
                      (e/d ()
                           (force
                            (force)
                            unsigned-byte-p
                            acl2::zp-open not
                            unsigned-byte-p
                            signed-byte-p
                            negative-logand-to-positive-logand-with-integerp-x
                            acl2::ash-0
                            unsigned-byte-p-of-logior
                            acl2::zip-open
                            bitops::unsigned-byte-p-incr)))))

      ;; This is in fact an (unsigned-byte-p 8),
      ;; as proved later in this DEFINE form.
      (new-rex-byte natp :rule-classes :type-prescription
                    :hyp (forced-and (natp rex-byte)
                                     (natp prefixes)
                                     (x86p x86))
                    :hints
                    (("Goal"
                      :in-theory
                      (e/d ()
                           (force
                            (force)
                            acl2::zp-open not
                            unsigned-byte-p
                            signed-byte-p
                            negative-logand-to-positive-logand-with-integerp-x
                            acl2::ash-0
                            unsigned-byte-p-of-logior
                            acl2::zip-open
                            bitops::unsigned-byte-p-incr)))))

      (new-x86 x86p
               :hyp (forced-and (x86p x86)
                                (canonical-address-p start-rip))
               :hints
               (("Goal"
                 :in-theory
                 (e/d ()
                      (acl2::zp-open
                       force (force)
                       not
                       unsigned-byte-p
                       signed-byte-p
                       acl2::ash-0
                       acl2::zip-open
                       bitops::logtail-of-logior
                       unsigned-byte-p-of-logtail
                       acl2::logtail-identity
                       bitops::logand-with-negated-bitmask
                       (:linear bitops::logior-<-0-linear-1)
                       (:linear bitops::logior-<-0-linear-2)
                       (:linear bitops::logand->=-0-linear-1)
                       (:linear bitops::logand->=-0-linear-2)
                       bitops::logtail-natp
                       natp-of-get-one-byte-prefix-array-code
                       acl2::ifix-when-not-integerp
                       ;; bitops::basic-signed-byte-p-of-+
                       default-<-1
                       negative-logand-to-positive-logand-with-integerp-x))))))

  :parents (x86-decoder)

  :short "Fetch and store legacy and REX prefixes, if any, of an instruction"

  :long "<p>The function @('get-prefixes') fetches the legacy and REX prefixes
  of an instruction and also returns the first byte following the last such
  prefix.  The input @('start-rip') points to the first byte of an instruction,
  which may potentially be a legacy prefix.  The initial value of @('cnt')
  should be @('15') so that the result @('(- 15 cnt)') returned at the end of
  the recursion is the correct number of legacy and/or REX bytes parsed by this
  function.</p>

  <h3>Legacy Prefixes</h3>

  <p>From Intel Manual, Vol. 2, May 2018, Section 2.1.1 (Instruction
  Prefixes):</p>

  <p><em>Instruction prefixes are divided into four groups, each with a set of
     allowable prefix codes. For each instruction, it is only useful to include
     up to one prefix code from each of the four groups (Groups 1, 2, 3,
     4). Groups 1 through 4 may be placed in any order relative to each
     other.</em></p>

  <p>Despite the quote from the Intel Manual above, the order of the legacy
  prefixes does matter when there is more than one prefix from the same group
  --- <b>all but the last prefix from a single prefix group are ignored</b>.
  The only <b>exception</b> in this case is for <b>Group 1</b> prefixes --- see
  below for details.</p>

  <p>Examples:</p>

  <ul>
  <li>@('0x64_88_00')    is @('mov byte ptr fs:[rax], al')</li>
  <li>@('0x65_88_00')    is @('mov byte ptr gs:[rax], al')</li>
  <li>@('0x64_65_88_00') is @('mov byte ptr gs:[rax], al')</li>
  <li>@('0x65_64_88_00') is @('mov byte ptr fs:[rax], al')</li>
  </ul>

  <ul>
  <li>@('0xf2_a4')    is @('repne movsb byte ptr [rdi], byte ptr [rsi]')</li>
  <li>@('0xf3_a4')    is @('repe  movsb byte ptr [rdi], byte ptr [rsi]')</li>
  <li>@('0xf2_f3_a4') is @('repe  movsb byte ptr [rdi], byte ptr [rsi]')</li>
  <li>@('0xf3_f2_a4') is @('repne movsb byte ptr [rdi], byte ptr [rsi]')</li>
  </ul>

  <p>We now discuss the Group 1 exception below.</p>

  <p>@('0xf0_f2_a4') is <b>NOT</b> <br/>
  @('repne movsb byte ptr [rdi], byte ptr [rsi]') <br/>
  It is: <br/>
  @('lock repne movsb byte ptr [rdi], byte ptr [rsi]') <br/>

  Note that lock and rep/repne are Group 1 prefixes.  It is important to record
  the lock prefix, even if it is overshadowed by a rep/repne prefix, because
  the former instruction will not @('#UD'), but the latter instruction will.
  This is akin to the lock prefix being in a separate group than the rep/repne
  prefixes; in fact, AMD manuals (Section 1.2.1: Summary of Legacy Prefixes,
  Vol. 3 May 2018 Edition) treat them as such.</p>

  <p>For details about how mandatory prefixes are picked from legacy prefixes,
  see @(see mandatory-prefixes-computation).</p>

  <h3>REX Prefixes</h3>

  <p>A REX prefix (applicable only to 64-bit mode) is treated as a null prefix
  if it is followed by a legacy prefix.  Here is an illustrative example (using
  Intel's XED, x86 Encoder Decoder --- see
  @('https://intelxed.github.io/')):</p>

  <ul>

  <li>@('xed -64 -d 48670100') is @('add dword ptr [eax], eax'); the REX.W
  prefix does not have any effect on the operand size, which remains 32 (i.e.,
  the default operand size in the 64-bit mode).</li>

  <li>@('xed -64 -d 67480100') is @('add qword ptr [eax], rax'); the REX prefix
  has the intended effect of promoting the operand size to 64 bits.</li>

  </ul>

  <p>Note that the prefixes structure output of this function does not include
  the REX byte (which is a separate return value of this function), but its
  @(':num-prefixes') field includes a count of the REX prefixes encountered.
  This is because adding an 8-bit field to the prefixes structure to store a
  REX byte will make it a bignum, thereby impacting execution efficiency.</p>"

  :prepwork

  ((defthm return-type-of-prefixes->num-linear
     (< (prefixes->num prefixes) 16)
     :hints (("Goal" :in-theory (e/d (prefixes->num) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->lck-linear
     (< (prefixes->lck prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->lck) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->rep-linear
     (< (prefixes->rep prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->rep) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->seg-linear
     (< (prefixes->seg prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->seg) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->opr-linear
     (< (prefixes->opr prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->opr) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->adr-linear
     (< (prefixes->adr prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->adr) ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->nxt-linear
     (< (prefixes->nxt prefixes) 256)
     :hints (("Goal" :in-theory (e/d (prefixes->nxt prefixes-fix)
                                     ())))
     :rule-classes :linear)

   (defthm return-type-of-prefixes->num-rewrite
     (unsigned-byte-p 4 (prefixes->num prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->num) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->lck-rewrite
     (unsigned-byte-p 8 (prefixes->lck prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->lck) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->rep-rewrite
     (unsigned-byte-p 8 (prefixes->rep prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->rep) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->seg-rewrite
     (unsigned-byte-p 8 (prefixes->seg prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->seg) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->opr-rewrite
     (unsigned-byte-p 8 (prefixes->opr prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->opr) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->adr-rewrite
     (unsigned-byte-p 8 (prefixes->adr prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->adr) ())))
     :rule-classes :rewrite)

   (defthm return-type-of-prefixes->nxt-rewrite
     (unsigned-byte-p 8 (prefixes->nxt prefixes))
     :hints (("Goal" :in-theory (e/d (prefixes->nxt prefixes-fix)
                                     ())))
     :rule-classes :rewrite)

   (defthm return-type-of-!prefixes->*-linear
     (and (unsigned-byte-p 52 (!prefixes->num x prefixes))
          (unsigned-byte-p 52 (!prefixes->lck x prefixes))
          (unsigned-byte-p 52 (!prefixes->rep x prefixes))
          (unsigned-byte-p 52 (!prefixes->seg x prefixes))
          (unsigned-byte-p 52 (!prefixes->opr x prefixes))
          (unsigned-byte-p 52 (!prefixes->adr x prefixes))
          (unsigned-byte-p 52 (!prefixes->nxt x prefixes)))
     :hints (("Goal" :in-theory
              (e/d* (!prefixes->num
                     !prefixes->lck
                     !prefixes->rep
                     !prefixes->seg
                     !prefixes->opr
                     !prefixes->adr
                     !prefixes->nxt
                     prefixes-fix
                     4bits-fix
                     8bits-fix)
                    (unsigned-byte-p
                     bitops::logand-with-negated-bitmask))))
     :rule-classes
     ((:rewrite)
      (:linear :corollary
               (and (< (!prefixes->num x prefixes) #.*2^52*)
                    (< (!prefixes->lck x prefixes) #.*2^52*)
                    (< (!prefixes->rep x prefixes) #.*2^52*)
                    (< (!prefixes->seg x prefixes) #.*2^52*)
                    (< (!prefixes->opr x prefixes) #.*2^52*)
                    (< (!prefixes->adr x prefixes) #.*2^52*)
                    (< (!prefixes->nxt x prefixes) #.*2^52*)))))

   (defthm loghead-ash-0
     (implies (and (natp i)
                   (natp j)
                   (natp x)
                   (<= i j))
              (equal (loghead i (ash x j))
                     0))
     :hints (("Goal"
              :in-theory (e/d* (acl2::ihsext-inductions
                                acl2::ihsext-recursive-redefs)
                               ()))))

   (local
    (defthm signed-byte-p-48-lemma
      (implies (signed-byte-p 48 start-rip)
               (equal (signed-byte-p 48 (1+ start-rip))
                      (< (1+ start-rip) *2^47*)))))

   (local (in-theory (e/d () (unsigned-byte-p)))))


  (if (mbe :logic (zp cnt)
           :exec (eql cnt 0))
      ;; Error, too many prefix bytes --- invalid instruction length.
      (mv t prefixes rex-byte x86)

    (b* ((ctx 'get-prefixes)
         ((mv flg (the (unsigned-byte 8) byte) x86)
          (rme08-opt proc-mode start-rip #.*cs* :x x86))
         ((when flg)
          (mv (cons ctx flg) byte rex-byte x86))

         (prefix-byte-group-code
          (the (integer 0 4) (get-one-byte-prefix-array-code byte))))

      (case prefix-byte-group-code

        (0
         (b* ((rex? (and
                     (eql proc-mode #.*64-bit-mode*)
                     (equal (the (unsigned-byte 4) (ash byte -4)) 4)))
              ((when rex?)
               (mv-let
                 (flg next-rip)
                 (add-to-*ip proc-mode start-rip 1 x86)
                 (if flg
                     (mv flg prefixes rex-byte x86)
                   (get-prefixes
                    proc-mode next-rip prefixes
                    byte ;; REX prefix, overwriting a previously encountered REX,
                    ;; if any
                    (the (integer 0 15) (1- cnt))
                    x86)))))
           ;; Storing the number of prefixes seen and the first byte
           ;; following the prefixes in "prefixes":
           (let ((prefixes
                  (the (unsigned-byte #.*prefixes-width*)
                    (!prefixes->nxt byte prefixes))))
             (mv nil
                 (the (unsigned-byte #.*prefixes-width*)
                   (!prefixes->num (- 15 cnt) prefixes))
                 rex-byte ;; Preserving rex-byte
                 x86))))

        (1
         ;; LOCK (F0), REPE (F3), REPNE (F2)
         (b* (((mv flg next-rip)
               (add-to-*ip proc-mode start-rip 1 x86))
              ((when flg)
               (mv flg prefixes rex-byte x86))
              ((the (unsigned-byte #.*prefixes-width*) prefixes)
               (if (equal byte #.*lock*)
                   (!prefixes->lck byte prefixes)
                 (!prefixes->rep byte prefixes))))
           ;; Storing the group 1 prefix (possibly overwriting a
           ;; previously seen group 1 prefix) and going on...
           (get-prefixes
            proc-mode next-rip prefixes
            0 ;; Nullify a previously read REX prefix, if any
            (the (integer 0 15) (1- cnt)) x86)))

        (2
         ;; ES (26), CS (2E), SS (36), DS (3E), FS (64), GS (65)
         (b* (((mv flg next-rip)
               (add-to-*ip proc-mode start-rip 1 x86))
              ((when flg)
               (mv flg prefixes rex-byte x86)))

           (if (or
                ;; In 64-bit mode, all segment override prefixes except FS
                ;; and GS overrides are treated as null prefixes.  So a
                ;; segment override prefix other than the FS and GS overrides
                ;; cannot overshadow a FS/GS override.  In case two or more
                ;; FS/GS overrides are present, all but the last are ignored.

                ;; Source: XED (https://intelxed.github.io/)
                ;; Some tests:
                ;; xed -64 -d 260f0100     => sgdt ptr [rax]
                ;; xed -64 -d 640f0100     => sgdt ptr fs:[rax]
                ;; xed -64 -d 64260f0100   => sgdt ptr fs:[rax]
                ;; xed -64 -d 6426650f0100 => sgdt ptr gs:[rax]
                (and (eql proc-mode #.*64-bit-mode*)
                     (or (equal byte #.*fs-override*)
                         (equal byte #.*gs-override*)))
                ;; All segment overrides are active in the 32-bit mode, and
                ;; all but the last one are ignored.
                (not (eql proc-mode #.*64-bit-mode*)))

               ;; Storing the group 2 prefix (possibly overwriting a
               ;; previously seen group 2 prefix) and going on...

               (get-prefixes
                proc-mode next-rip
                (the (unsigned-byte #.*prefixes-width*)
                  (!prefixes->seg byte prefixes))
                0 ;; Nullify a previously read REX prefix, if any
                (the (integer 0 15) (1- cnt))
                x86)

             ;; We will be here if we are in the 64-bit mode and have seen a
             ;; null segment override prefix; we will not store the prefix
             ;; but simply decrement cnt.
             (get-prefixes proc-mode next-rip prefixes
                           0 ;; Nullify a previously read REX prefix, if any
                           (the (integer 0 15) (1- cnt)) x86))))

        (3
         ;; Operand-Size Override (66)
         (mv-let
           (flg next-rip)
           (add-to-*ip proc-mode start-rip 1 x86)
           (if flg
               (mv flg prefixes rex-byte x86)
             ;; Storing the group 3 prefix (possibly overwriting a
             ;; previously seen group 3 prefix) and going on...
             (get-prefixes
              proc-mode next-rip
              (the (unsigned-byte #.*prefixes-width*)
                (!prefixes->opr byte prefixes))
              0 ;; Nullify a previously read REX prefix, if any
              (the (integer 0 15) (1- cnt))
              x86))))

        (4
         ;; Address-Size Override (67)
         (mv-let
           (flg next-rip)
           (add-to-*ip proc-mode start-rip 1 x86)
           (if flg
               (mv flg prefixes rex-byte x86)
             ;; Storing the group 4 prefix (possibly overwriting a
             ;; previously seen group 4 prefix) and going on...
             (get-prefixes
              proc-mode next-rip
              (the (unsigned-byte #.*prefixes-width*)
                (!prefixes->adr byte prefixes))
              0 ;; Nullify a previously read REX prefix, if any
              (the (integer 0 15) (1- cnt))
              x86))))

        (otherwise
         (mv t prefixes rex-byte x86)))))

  ///

  (local (in-theory (e/d () (acl2::zp-open not))))

  (defthm-unsigned-byte-p prefixes-width-p-of-get-prefixes.new-prefixes
    ;; [Shilpi] I tried to use defret here instead of defthm-unsigned-byte-p, but I got
    ;; into trouble, probably because of the different order of lambda
    ;; expansions in defret.
    :hyp (and (unsigned-byte-p #.*prefixes-width* prefixes)
              (canonical-address-p start-rip)
              (x86p x86))
    :bound #.*prefixes-width*
    :concl (mv-nth 1 (get-prefixes
                      proc-mode start-rip prefixes rex-byte cnt x86))
    :hints (("Goal"
             :induct (get-prefixes
                      proc-mode start-rip prefixes rex-byte cnt x86)
             :in-theory (e/d ()
                             (signed-byte-p
                              acl2::ash-0
                              acl2::zip-open
                              bitops::logtail-of-logior
                              unsigned-byte-p-of-logtail
                              acl2::logtail-identity
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              ;; bitops::basic-signed-byte-p-of-+
                              default-<-1
                              force (force)))))
    :gen-linear t)

  (defthm-unsigned-byte-p byte-p-of-get-prefixes.new-rex-byte
    ;; [Shilpi] I tried to use defret here instead of defthm-unsigned-byte-p, but I got
    ;; into trouble, probably because of the different order of lambda
    ;; expansions in defret.
    :hyp (and (unsigned-byte-p 8 rex-byte)
              (natp prefixes)
              (x86p x86))
    :bound 8
    :concl (mv-nth 2 (get-prefixes
                      proc-mode start-rip prefixes rex-byte cnt x86))
    :hints (("Goal"
             :induct (get-prefixes
                      proc-mode start-rip prefixes rex-byte cnt x86)
             :in-theory (e/d ()
                             (unsigned-byte-p
                              signed-byte-p
                              acl2::ash-0
                              acl2::zip-open
                              bitops::logtail-of-logior
                              unsigned-byte-p-of-logtail
                              acl2::logtail-identity
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              ;; bitops::basic-signed-byte-p-of-+
                              default-<-1
                              force (force)))))
    :gen-linear t)

  (defret get-prefixes-does-not-modify-x86-state-in-app-view
    (implies (app-view x86)
             (equal new-x86 x86))
    :hints (("Goal"
             :in-theory
             (union-theories
              '(get-prefixes
                rme08-does-not-affect-state-in-app-view)
              (theory 'minimal-theory)))))

  (local
   (in-theory (e/d
               (rme08 rml08 rvm08)
               (force
                (force)
                signed-byte-p-48-lemma
                signed-byte-p
                bitops::logior-equal-0
                acl2::zp-open
                not
                (:congruence acl2::int-equiv-implies-equal-logand-2)
                (:congruence acl2::int-equiv-implies-equal-loghead-2)))))


  (defthm num-prefixes-get-prefixes-bound
    (implies (and (<= cnt 15)
                  (x86p x86)
                  (canonical-address-p start-rip)
                  (unsigned-byte-p #.*prefixes-width* prefixes)
                  (< (part-select prefixes :low 0 :high 2) 5))
             (<=
              (prefixes->num
               (mv-nth
                1
                (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
              15))
    :hints (("Goal"
             :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
             :in-theory (e/d (rme08 rme08-value-when-error)
                             (signed-byte-p
                              unsigned-byte-p rme08 rml08
                              (force) force
                              canonical-address-p
                              not acl2::zp-open
                              acl2::ash-0
                              acl2::zip-open
                              bitops::logtail-of-logior
                              unsigned-byte-p-of-logtail
                              acl2::logtail-identity
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              ;; bitops::basic-signed-byte-p-of-+
                              default-<-1))))
    :rule-classes :linear)

  (defthm get-prefixes-opener-lemma-zero-cnt
    (implies (zp cnt)
             (equal (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
                    (mv t prefixes rex-byte x86)))
    :hints (("Goal" :in-theory (e/d (get-prefixes) ()))))

  (local
   (defthmd get-prefixes-opener-lemma-no-prefix-byte-pre
     ;; Note that this lemma is applicable in the system-level view too.
     ;; This lemma would be used for those instructions which do not have
     ;; any prefix byte.
     (b* (((mv flg byte byte-x86)
           (rme08 proc-mode start-rip #.*cs* :x x86))
          (prefix-byte-group-code
           (get-one-byte-prefix-array-code byte)))
       (implies
        (and (not flg)
             (zp prefix-byte-group-code)
             (not (zp cnt)))
        (equal
         (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
         (b* ((rex? (and
                     (eql proc-mode #.*64-bit-mode*)
                     (equal (ash byte -4) 4)))
              ((when rex?)
               (mv-let
                 (flg next-rip)
                 (add-to-*ip proc-mode start-rip 1 byte-x86)
                 (if flg
                     (mv flg prefixes rex-byte byte-x86)
                   (get-prefixes
                    proc-mode next-rip prefixes
                    byte ;; REX prefix, overwriting a previously encountered REX,
                    ;; if any
                    (the (integer 0 15) (1- cnt))
                    byte-x86)))))
           ;; Storing the number of prefixes seen and the first byte
           ;; following the prefixes in "prefixes":
           (let ((prefixes
                  (!prefixes->nxt byte prefixes)))
             (mv nil
                 (!prefixes->num (- 15 cnt) prefixes)
                 rex-byte ;; Preserving rex-byte
                 byte-x86))))))
     :hints (("Goal"
              :induct
              (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
              :in-theory (e/d () (unsigned-byte-p))))))

  (defthm get-prefixes-opener-lemma-no-prefix-byte
    ;; This lemma is applicable in all the views of the x86isa model. This
    ;; lemma would be used for those instructions which do not have any prefix
    ;; byte --- either legacy or rex.
    (implies
     (b* (((mv flg byte &)
           (rme08 proc-mode start-rip #.*cs* :x x86))
          (prefix-byte-group-code
           (get-one-byte-prefix-array-code byte)))
       (and (not flg)
            (zp prefix-byte-group-code)
            (if (equal proc-mode #.*64-bit-mode*)
                (not (equal (ash byte -4) 4))
              t)
            (not (zp cnt))))
     (equal
      (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
      (let ((prefixes
             (!prefixes->nxt
              (mv-nth 1 (rme08 proc-mode start-rip #.*cs* :x x86))
              prefixes)))
        (mv nil
            (!prefixes->num (- 15 cnt) prefixes)
            rex-byte ;; Preserving rex-byte
            (mv-nth 2 (rme08 proc-mode start-rip #.*cs* :x x86))))))
    :hints (("Goal" :in-theory (e/d (get-prefixes-opener-lemma-no-prefix-byte-pre)
                                    (rme08 get-prefixes)))))

  (defthm get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix
    ;; Note that this lemma is applicable only in 64-bit mode.
    ;; This lemma is applicable in all the views of the x86isa model.
    (implies
     (b* (((mv flg byte &)
           (rme08 proc-mode start-rip #.*cs* :x x86))
          (prefix-byte-group-code
           (get-one-byte-prefix-array-code byte)))
       (and (equal proc-mode #.*64-bit-mode*)
            (not flg)
            (zp prefix-byte-group-code)
            (equal (ash byte -4) 4)
            (not (zp cnt))))
     (equal
      (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
      (b* (((mv & byte byte-x86)
            (rme08 proc-mode start-rip #.*cs* :x x86))
           ((mv flg next-rip)
            (add-to-*ip proc-mode start-rip 1 byte-x86)))
        (if flg
            (mv flg prefixes rex-byte byte-x86)
          (get-prefixes
           proc-mode next-rip prefixes
           byte ;; REX prefix, overwriting a previously encountered REX,
           ;; if any
           (1- cnt)
           byte-x86)))))
    :hints (("Goal" :in-theory (e/d (get-prefixes-opener-lemma-no-prefix-byte-pre)
                                    (rme08 get-prefixes)))))

  (defthm get-prefixes-opener-lemma-group-1-prefix
    (b* (((mv flg byte byte-x86)
          (rme08 proc-mode start-rip #.*cs* :x x86))
         (prefix-byte-group-code (get-one-byte-prefix-array-code byte)))
      (implies
       (and (or (app-view x86)
                (not (marking-view x86)))
            (not flg) ;; No error in reading a byte
            (equal prefix-byte-group-code 1)
            (not (zp cnt))
            (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
       (equal (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
              (let ((prefixes
                     (if (equal byte #.*lock*)
                         (!prefixes->lck byte prefixes)
                       (!prefixes->rep byte prefixes))))
                (get-prefixes
                 proc-mode (1+ start-rip) prefixes 0 (1- cnt) byte-x86)))))
    :hints (("Goal"
             :in-theory
             (e/d* (add-to-*ip)
                   (rb
                    unsigned-byte-p
                    negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-2-prefix
    (b* (((mv flg byte byte-x86)
          (rme08 proc-mode start-rip #.*cs* :x x86))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code
           byte)))
      (implies
       (and (or (app-view x86)
                (and (not (app-view x86))
                     (not (marking-view x86))))
            (not flg) ;; No error in reading a byte
            (equal prefix-byte-group-code 2)
            (not (zp cnt))
            (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
       (equal (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
              (if (or
                   (and (eql proc-mode #.*64-bit-mode*)
                        (or (equal byte #.*fs-override*)
                            (equal byte #.*gs-override*)))
                   (not (eql proc-mode #.*64-bit-mode*)))
                  (get-prefixes proc-mode (1+ start-rip)
                                (!prefixes->seg byte prefixes)
                                0
                                (1- cnt) byte-x86)
                (get-prefixes
                 proc-mode (1+ start-rip) prefixes 0 (1- cnt) byte-x86)))))
    :hints (("Goal"
             :in-theory
             (e/d* (add-to-*ip)
                   (rb
                    unsigned-byte-p
                    negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-3-prefix
          (b* (((mv flg byte x862) (rme08 proc-mode start-rip #.*cs* :x x86))
               (prefix-byte-group-code (get-one-byte-prefix-array-code byte)))
              (implies (and (not flg) ;; No error in reading a byte
                            (equal prefix-byte-group-code 3)
                            (not (zp cnt))
                            (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x862))))
                       (equal (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
                              (get-prefixes proc-mode (1+ start-rip)
                                            (!prefixes->opr byte prefixes)
                                            0
                                            (1- cnt) x862))))
          :hints (("Goal"
                   :in-theory
                   (e/d* (add-to-*ip)
                         (rb
                           unsigned-byte-p
                           negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-4-prefix
          (b* (((mv flg byte x862) (rme08 proc-mode start-rip #.*cs* :x x86))
               (prefix-byte-group-code (get-one-byte-prefix-array-code byte)))
              (implies (and (not flg) ;; No error in reading a byte
                            (equal prefix-byte-group-code 4)
                            (not (zp cnt))
                            (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x862))))
                       (equal (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
                              (get-prefixes proc-mode (1+ start-rip)
                                            (!prefixes->adr
                                              byte
                                              prefixes)
                                            0
                                            (1- cnt) x862))))
          :hints (("Goal"
                   :in-theory
                   (e/d* (add-to-*ip)
                         (rb
                           unsigned-byte-p
                           negative-logand-to-positive-logand-with-integerp-x)))))

  (local
   (defret xr-msr-and-seg-hidden-of-get-prefixes-in-app-view
     (implies (app-view x86)
              (and
               (equal (xr :msr idx new-x86)
                      (xr :msr idx x86))
               (equal (xr :seg-hidden-base idx new-x86)
                      (xr :seg-hidden-base idx x86))
               (equal (xr :seg-hidden-limit idx new-x86)
                      (xr :seg-hidden-limit idx x86))
               (equal (xr :seg-hidden-attr idx new-x86)
                      (xr :seg-hidden-attr idx x86))))
     :hints (("Goal"
              :in-theory (e/d () (las-to-pas rb rme08 rml08))))))

  (local
   (defret xr-msr-of-get-prefixes-in-sys-view
     (implies (not (app-view x86))
              (and
               (equal (xr :msr idx new-x86)
                      (xr :msr idx x86))
               (equal (xr :seg-hidden-base idx new-x86)
                      (xr :seg-hidden-base idx x86))
               (equal (xr :seg-hidden-limit idx new-x86)
                      (xr :seg-hidden-limit idx x86))
               (equal (xr :seg-hidden-attr idx new-x86)
                      (xr :seg-hidden-attr idx x86))))
     :hints (("Goal"
              :induct <call>
              :in-theory (e/d ()
                              (unsigned-byte-p get-prefixes-opener-lemma-group-4-prefix
                               get-prefixes-opener-lemma-group-3-prefix
                               las-to-pas rb rme08 rml08))))))

  (local
   (defret xr-msr-of-get-prefixes
     (and
      (equal (xr :msr idx new-x86)
             (xr :msr idx x86))
      (equal (xr :seg-hidden-base idx new-x86)
             (xr :seg-hidden-base idx x86))
      (equal (xr :seg-hidden-limit idx new-x86)
             (xr :seg-hidden-limit idx x86))
      (equal (xr :seg-hidden-attr idx new-x86)
             (xr :seg-hidden-attr idx x86)))
     :hints (("Goal"
              :cases ((app-view x86))
              :do-not-induct t
              :in-theory (e/d () (get-prefixes las-to-pas rb rme08 rml08))))))

  (defret 64-bit-modep-of-get-prefixes
    (equal (64-bit-modep new-x86)
           (64-bit-modep x86))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (64-bit-modep) ()))))

  (defret x86-operation-mode-of-get-prefixes
    (equal (x86-operation-mode new-x86)
           (x86-operation-mode x86))
    :hints (("Goal" :in-theory (e/d (x86-operation-mode) (get-prefixes))))))
