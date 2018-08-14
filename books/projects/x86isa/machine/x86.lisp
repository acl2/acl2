; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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

(in-package "X86ISA")

;; ----------------------------------------------------------------------

(include-book "instructions/top"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "std/strings/hexify" :dir :system)

(local (include-book "dispatch"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d ()
                       (app-view-rml08-no-error
                        (:meta acl2::mv-nth-cons-meta)
                        rme08-value-when-error
                        member-equal))))

;; ----------------------------------------------------------------------

(defsection x86-decoder
  :parents (machine)
  :short "Definitions of the x86 fetch, decode, and execute function
  and the top-level run function"
  )

(defsection implemented-opcodes
  :parents (x86isa instructions x86-decoder)
  :short "Intel Opcodes Supported in @('x86isa')"
  :long

  "<h3>How to Read the Opcode Tables</h3>

 <p>The opcode tables have 2^8 = 256 rows, one row for each relevant opcode
 byte (i.e., the only opcode byte for one-byte opcodes in @(see
 one-byte-opcodes-table), the second opcode byte for the two-byte opcodes in
 @(see two-byte-opcodes-table), and the third opcode byte for the three-byte
 opcodes in @(see 0F-38-three-byte-opcodes-table) and @(see
 0F-3A-three-byte-opcodes-table)).  Each row lists the opcode, the name of the
 Intel instruction corresponding to it, and the instruction semantic function
 that implements that opcode.</p>

 <p>Often, just the opcode byte is not enough to determine the x86 instruction.
 We may need to know the processor's mode of operation (e.g., 32-bit or 64-bit
 mode), the value in the fields of the ModR/M byte (the so-called opcode
 extensions grouped together in Intel Volume 2, Table A-6), the mandatory
 prefixes, etc.  The following keywords are used to describe such information
 in these tables.</p>

 <ul>
   <li>@(':i64'):    Invalid in 64-bit mode</li>
   <li>@(':o64'):    Valid only in 64-bit mode</li>
   <li>@(':reg'):    Value of ModR/M.reg</li>
   <li>@(':mod'):    Value of ModR/M.mod</li>
   <li>@(':r/m'):    Value of ModR/M.r/m</li>
   <li>@(':66'):     Mandatory Prefix 0x66</li>
   <li>@(':F2'):     Mandatory Prefix 0xF2</li>
   <li>@(':F3'):     Mandatory Prefix 0xF3</li>
   <li>@(':No-Pfx'): No Mandatory Prefix</li>
 </ul>

 <p>Instead of the instruction semantic function, these tables may also list
 <i>Reserved</i> or <i>Unimplemented</i> for certain opcodes.  <i>Reserved</i>
 stands for opcodes that Intel deems reserved --- an x86 processor is supposed
 to throw a @('#UD') (undefined instruction) exception if that opcode is
 encountered --- we call @(tsee x86-illegal-instruction) in such cases.
 <i>Unimplemented</i> stands for legal x86 instructions that are not yet
 supported in @('x86isa') --- we call @(tsee x86-step-unimplemented) in such
 cases.</p>"

  )

(local (xdoc::set-default-parents x86-decoder))

;; ----------------------------------------------------------------------

(define get-prefixes
  ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
   (start-rip :type (signed-byte   #.*max-linear-address-size*))
   (prefixes  :type (unsigned-byte 55))
   (cnt       :type (integer 0 15))
   x86)

  :guard-hints
  (("Goal" :in-theory
    (e/d ()
         (negative-logand-to-positive-logand-with-integerp-x
          signed-byte-p))))

  :measure (nfix cnt)

  :parents (x86-decoder)

  :long "<p>From Intel Manual, Vol. 2, May 2018, Section 2.1.1 (Instruction
  Prefixes):</p>

  <p><em>Instruction prefixes are divided into four groups, each with a set of
     allowable prefix codes. For each instruction, it is only useful to include
     up to one prefix code from each of the four groups (Groups 1, 2, 3,
     4). Groups 1 through 4 may be placed in any order relative to each
     other.</em></p>

  <p>The function @('get-prefixes') fetches the prefixes of an instruction and
  also returns the first byte following the last prefix.  The input
  @('start-rip') points to the first byte of an instruction, which may
  potentially be a legacy prefix.  The initial value of @('cnt') should be
  @('15') so that the result @('(- 15 cnt)') returned at the end of the
  recursion is the correct number of prefix bytes parsed by this function.</p>

  <p>Despite the quote from the Intel Manual above, the order of the prefixes
  does matter in at least two cases: (1) when there are mandatory prefixes,
  and (2) when there is more than one prefix from the same group.  We discuss
  these two situations below.</p>

  <ul>

  <li><p>We keep overwriting the @(':last-prefix') field in every recursive
  call with the code for prefix read from the instruction
  stream (@('*lck-pfx*'), @('*rep-pfx*'), @('*seg-pfx*'), @('*opr-pfx*'), or
  @('*adr-pfx*')) --- this way, at the end of this function, we'll have the
  last legacy prefix in the current instruction.  This information can be
  useful if we have mandatory prefixes
  (i.e., for two- and three-byte opcode maps) --- the last prefix is the
  mandatory prefix, and the other prefixes are simply the usual modifiers.</p>

  <p>If the value of @(':last-prefix') indicates anything other than the three
  SIMD prefixes (0x66, 0xF2, or 0xF3), then it's irrelevant as far as the
  mandatory prefix is concerned.  This is because all the functions that take
  the mandatory prefix as input (e.g., modr/m detecting functions like @(tsee
  64-bit-mode-two-byte-opcode-ModR/M-p), opcode dispatch functions like @(tsee
  second-three-byte-opcode-execute), etc.), detect the no mandatory prefix case
  by checking that @(':last-prefix') does not indicate a SIMD prefix.</p></li>

  <li><p>From <a
  href='http://wiki.osdev.org/X86-64_Instruction_Encoding#Legacy_Prefixes'>OSDev
  Wiki</a>:</p>

     <p><em>When there are two or more prefixes from a single group,
     the behavior is undefined. Some processors ignore the subsequent
     prefixes from the same group, or use only the last prefix
     specified for any group.</em></p>

  <p>Older versions of this function
   (in @('x86isa') books before Jul. 2018) didn't tolerate more than one prefix
  from a single prefix group, though we did accept redundant prefixes --- this
  was due to descriptions such as the above on non-Intel sources.  However,
  after running tests on modern x86 machines (circa ~2015-2018), we have
  changed this function to ignore all but the last prefix from a single prefix
  group.  The only exception in this case is for Group 1 prefixes --- see below
  for details.  For example:</p>

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
  @('lock repne movsb byte ptr [rdi], byte ptr [rsi]')</p>

  <p>Note that lock and rep/repne are Group 1 prefixes.  It is important to
  record the lock prefix, even if it is overshadowed by a rep/repne prefix,
  because the former instruction will not @('#UD'), but the latter instruction
  will.</p>

  <p>If you run into an example of where this is inconsistent with an x86
  machine, please do get in touch!</p></li>

  </ul>"

  :prepwork

  ((defthm loghead-ash-0
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

   (local
    (encapsulate
      ()
      (local (include-book "arithmetic-5/top" :dir :system))

      (defthm get-prefixes-storing-last-byte-lemma
        (implies (unsigned-byte-p 8 byte)
                 (<
                  (logior (logand
                           #x7FFFFFFFF00FFF
                           (logior #x20000000000000 (loghead 52 prefixes)))
                          (ash byte 12))
                  #x80000000000000))
        :rule-classes :linear)

      (defthm negative-logand-to-positive-logand-with-n55p-x
        (implies (and (< n 0)
                      (syntaxp (quotep n))
                      (equal m 55)
                      (integerp n)
                      (n55p x))
                 (equal (logand n x)
                        (logand (logand (1- (ash 1 m)) n) x)))))))


  (if (mbe :logic (zp cnt)
           :exec (eql cnt 0))
      ;; Error, too many prefix bytes --- invalid instruction length.
      (mv t prefixes x86)

    (b* ((ctx 'get-prefixes)
         ((mv flg (the (unsigned-byte 8) byte) x86)
          (rme08 proc-mode start-rip *cs* :x x86))
         ((when flg)
          (mv (cons ctx flg) byte x86))

         (prefix-byte-group-code
          (the (integer 0 4) (get-one-byte-prefix-array-code byte))))

      (if (mbe :logic (zp prefix-byte-group-code)
               :exec  (eql 0 prefix-byte-group-code))

          ;; Storing the number of prefixes seen and the first byte
          ;; following the prefixes in "prefixes"...
          (let ((prefixes
                 (!prefixes-slice :next-byte byte prefixes)))
            (mv nil (!prefixes-slice :num-prefixes (- 15 cnt) prefixes)
                x86))

        (case prefix-byte-group-code

          (1
           ;; LOCK (F0), REPE (F3), REPNE (F2)
           (mv-let
             (flg next-rip)
             (add-to-*ip proc-mode start-rip 1 x86)
             (if flg
                 (mv flg prefixes x86)
               ;; Storing the group 1 prefix (possibly overwriting a
               ;; previously seen group 1 prefix) and going on...
               (b* ((prefixes
                     (if (equal byte #.*lock*)
                         (!prefixes-slice
                          :lck byte
                          (!prefixes-slice
                           :last-prefix #.*lck-pfx* prefixes))
                       (!prefixes-slice
                        :rep byte
                        (!prefixes-slice
                         :last-prefix #.*rep-pfx* prefixes)))))
                 (get-prefixes
                  proc-mode next-rip prefixes
                  (the (integer 0 15) (1- cnt)) x86)))))

          (2
           ;; ES (26), CS (2E), SS (36), DS (3E), FS (64), GS (65)
           (mv-let
             (flg next-rip)
             (add-to-*ip proc-mode start-rip 1 x86)
             (if flg
                 (mv flg prefixes x86)
               ;; Storing the group 2 prefix (possibly overwriting a
               ;; previously seen group 2 prefix) and going on...
               (get-prefixes
                proc-mode next-rip
                (!prefixes-slice
                 :seg byte
                 (!prefixes-slice :last-prefix #.*seg-pfx* prefixes))
                (the (integer 0 15) (1- cnt))
                x86))))

          (3
           ;; Operand-Size Override (66)
           (mv-let
             (flg next-rip)
             (add-to-*ip proc-mode start-rip 1 x86)
             (if flg
                 (mv flg prefixes x86)
               ;; Storing the group 3 prefix (possibly overwriting a
               ;; previously seen group 3 prefix) and going on...
               (get-prefixes
                proc-mode next-rip
                (!prefixes-slice
                 :opr byte
                 (!prefixes-slice :last-prefix #.*opr-pfx* prefixes))
                (the (integer 0 15) (1- cnt))
                x86))))

          (4
           ;; Address-Size Override (67)
           (mv-let
             (flg next-rip)
             (add-to-*ip proc-mode start-rip 1 x86)
             (if flg
                 (mv flg prefixes x86)
               ;; Storing the group 4 prefix (possibly overwriting a
               ;; previously seen group 4 prefix) and going on...
               (get-prefixes
                proc-mode next-rip
                (!prefixes-slice
                 :adr byte
                 (!prefixes-slice :last-prefix #.*adr-pfx* prefixes))
                (the (integer 0 15) (1- cnt))
                x86))))

          (otherwise
           (mv t prefixes x86))))))

  ///

  (local (in-theory (e/d () (acl2::zp-open not))))

  (defthm natp-get-prefixes
    (implies (forced-and (natp prefixes)
                         (canonical-address-p start-rip)
                         (x86p x86))
             (natp (mv-nth 1 (get-prefixes
                              proc-mode start-rip prefixes cnt x86))))
    :hints (("Goal" :in-theory (e/d ()
                                    (force
                                     (force)
                                     unsigned-byte-p
                                     signed-byte-p
                                     negative-logand-to-positive-logand-with-integerp-x
                                     acl2::ash-0
                                     unsigned-byte-p-of-logior
                                     acl2::zip-open
                                     bitops::unsigned-byte-p-incr))))
    :rule-classes :type-prescription)

  (defthm-usb n55p-get-prefixes
    :hyp (and (n55p prefixes)
              (canonical-address-p start-rip)
              (x86p x86))
    :bound 55
    :concl (mv-nth 1 (get-prefixes proc-mode start-rip prefixes cnt x86))
    :hints (("Goal"
             :in-theory (e/d ()
                             (signed-byte-p
                              acl2::ash-0
                              acl2::zip-open
                              bitops::logtail-of-logior
                              unsigned-byte-p-of-logtail
                              acl2::logtail-identity
                              ash-monotone-2
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              bitops::basic-signed-byte-p-of-+
                              default-<-1
                              force (force)))))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d () (get-prefixes)))))

  (defthm x86p-get-prefixes
    (implies (forced-and (x86p x86)
                         (canonical-address-p start-rip))
             (x86p (mv-nth
                    2
                    (get-prefixes proc-mode start-rip prefixes cnt x86))))
    :hints (("Goal"
             :in-theory (e/d ()
                             (unsigned-byte-p
                              signed-byte-p
                              acl2::ash-0
                              acl2::zip-open
                              bitops::logtail-of-logior
                              unsigned-byte-p-of-logtail
                              acl2::logtail-identity
                              ash-monotone-2
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              bitops::basic-signed-byte-p-of-+
                              default-<-1
                              negative-logand-to-positive-logand-with-integerp-x
                              negative-logand-to-positive-logand-with-n55p-x
                              force (force))))))

  (defthm get-prefixes-does-not-modify-x86-state-in-app-view
    (implies (app-view x86)
             (equal (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86))
                    x86))
    :hints (("Goal"
             :in-theory
             (union-theories
              '(get-prefixes
                rme08-does-not-affect-state-in-app-view)
              (theory 'minimal-theory)))))

  (defthm get-prefixes-does-not-modify-x86-state-in-system-level-non-marking-view
    (implies (and (not (app-view x86))
                  (not (marking-view x86))
                  (x86p x86)
                  (not (mv-nth
                        0 (get-prefixes proc-mode start-rip prefixes cnt x86))))
             (equal (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86))
                    x86))
    :hints (("Goal"
             :in-theory (union-theories
                         '(get-prefixes
                           mv-nth-2-rme08-in-system-level-non-marking-view)
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
                  (n55p prefixes)
                  (< (part-select prefixes :low 0 :high 2) 5))
             (<=
              (prefixes-slice
               :num-prefixes
               (mv-nth 1 (get-prefixes proc-mode start-rip prefixes cnt x86)))
              15))
    :hints (("Goal"
             :induct (get-prefixes proc-mode start-rip prefixes cnt x86)
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
                              ash-monotone-2
                              bitops::logand-with-negated-bitmask
                              (:linear bitops::logior-<-0-linear-1)
                              (:linear bitops::logior-<-0-linear-2)
                              (:linear bitops::logand->=-0-linear-1)
                              (:linear bitops::logand->=-0-linear-2)
                              bitops::logtail-natp
                              natp-of-get-one-byte-prefix-array-code
                              acl2::ifix-when-not-integerp
                              bitops::basic-signed-byte-p-of-+
                              default-<-1))))
    :rule-classes :linear)

  (defthm get-prefixes-opener-lemma-zero-cnt
    (implies (zp cnt)
             (equal (get-prefixes proc-mode start-rip prefixes cnt x86)
                    (mv t prefixes x86)))
    :hints (("Goal" :in-theory (e/d (get-prefixes) ()))))

  (defthm get-prefixes-opener-lemma-no-prefix-byte
    ;; Note that this lemma is applicable in the system-level view too.
    ;; This lemma would be used for those instructions which do not have
    ;; any prefix byte.
    (implies (and
              (let* ((flg (mv-nth 0 (rme08 proc-mode start-rip *cs* :x x86)))
                     (prefix-byte-group-code
                      (get-one-byte-prefix-array-code
                       (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86)))))
                (and (not flg)
                     (zp prefix-byte-group-code)))
              (not (zp cnt)))
             (and
              (equal (mv-nth 0
                             (get-prefixes proc-mode start-rip prefixes cnt x86))
                     nil)
              (equal (mv-nth 1
                             (get-prefixes proc-mode start-rip prefixes cnt x86))
                     (let ((prefixes
                            (!prefixes-slice
                             :next-byte
                             (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86))
                             prefixes)))
                       (!prefixes-slice :num-prefixes (- 15 cnt) prefixes))))))

  (defthm get-prefixes-opener-lemma-group-1-prefix
    (b* (((mv flg byte x86)
          (rme08 proc-mode start-rip *cs* :x x86))
         (prefix-byte-group-code (get-one-byte-prefix-array-code byte)))
      (implies
       (and (or (app-view x86)
                (not (marking-view x86)))
            (not flg) ;; No error in reading a byte
            (equal prefix-byte-group-code 1)
            (not (zp cnt))
            (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
       (equal (get-prefixes proc-mode start-rip prefixes cnt x86)
              (let ((prefixes
                     (if (equal byte #.*lock*)
                         (!prefixes-slice
                          :lck byte
                          (!prefixes-slice
                           :last-prefix #.*lck-pfx* prefixes))
                       (!prefixes-slice
                        :rep byte
                        (!prefixes-slice
                         :last-prefix #.*rep-pfx* prefixes)))))
                (get-prefixes proc-mode (1+ start-rip) prefixes (1- cnt) x86)))))
    :hints (("Goal"
             :in-theory
             (e/d* (add-to-*ip)
                   (rb
                    unsigned-byte-p
                    negative-logand-to-positive-logand-with-n55p-x
                    negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-2-prefix
    (implies (and (or (app-view x86)
                      (and (not (app-view x86))
                           (not (marking-view x86))))
                  (let* ((flg (mv-nth 0 (rme08 proc-mode start-rip *cs* :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 2)))
                  (not (zp cnt))
                  (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
             (equal (get-prefixes proc-mode start-rip prefixes cnt x86)
                    (get-prefixes proc-mode (1+ start-rip)
                                  (!prefixes-slice
                                   :seg
                                   (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86))
                                   (!prefixes-slice
                                    :last-prefix
                                    #.*seg-pfx*
                                    prefixes))
                                  (1- cnt) x86)))
    :hints (("Goal" :in-theory (e/d* (add-to-*ip)
                                     (rb
                                      unsigned-byte-p
                                      negative-logand-to-positive-logand-with-n55p-x
                                      negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-3-prefix
    (implies (and (or (app-view x86)
                      (and (not (app-view x86))
                           (not (marking-view x86))))
                  (let* ((flg (mv-nth 0 (rme08 proc-mode start-rip *cs* :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 3)))
                  (not (zp cnt))
                  (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
             (equal (get-prefixes proc-mode start-rip prefixes cnt x86)
                    (get-prefixes proc-mode (1+ start-rip)
                                  (!prefixes-slice
                                   :opr
                                   (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86))
                                   (!prefixes-slice
                                    :last-prefix
                                    #.*opr-pfx*
                                    prefixes))
                                  (1- cnt) x86)))
    :hints (("Goal" :in-theory (e/d* (add-to-*ip)
                                     (rb
                                      unsigned-byte-p
                                      negative-logand-to-positive-logand-with-n55p-x
                                      negative-logand-to-positive-logand-with-integerp-x)))))

  (defthm get-prefixes-opener-lemma-group-4-prefix
    (implies (and (or (app-view x86)
                      (and (not (app-view x86))
                           (not (marking-view x86))))
                  (let* ((flg (mv-nth 0 (rme08 proc-mode start-rip *cs* :x x86)))
                         (prefix-byte-group-code
                          (get-one-byte-prefix-array-code
                           (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86)))))
                    (and (not flg) ;; No error in reading a byte
                         (equal prefix-byte-group-code 4)))
                  (not (zp cnt))
                  (not (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))))
             (equal (get-prefixes proc-mode start-rip prefixes cnt x86)
                    (get-prefixes proc-mode (1+ start-rip)
                                  (!prefixes-slice
                                   :adr
                                   (mv-nth 1 (rme08 proc-mode start-rip *cs* :x x86))
                                   (!prefixes-slice
                                    :last-prefix
                                    #.*adr-pfx*
                                    prefixes))
                                  (1- cnt) x86)))
    :hints (("Goal" :in-theory (e/d* (add-to-*ip)
                                     (rb
                                      unsigned-byte-p
                                      negative-logand-to-positive-logand-with-n55p-x
                                      negative-logand-to-positive-logand-with-integerp-x)))))

  (local
   (defthm xr-msr-and-seg-hidden-of-get-prefixes-in-app-view
     (implies (app-view x86)
              (and
               (equal (xr :msr idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
                      (xr :msr idx x86))
               (equal (xr :seg-hidden idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
                      (xr :seg-hidden idx x86))))
     :hints (("Goal"
              :in-theory (e/d () (las-to-pas rb rme08 rml08))))))

  (local
   (defthm xr-msr-of-get-prefixes-in-sys-view
     (implies (not (app-view x86))
              (and
               (equal (xr :msr idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
                      (xr :msr idx x86))
               (equal (xr :seg-hidden idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
                      (xr :seg-hidden idx x86))))
     :hints (("Goal"
              :induct (get-prefixes proc-mode start-rip prefixes cnt x86)
              :in-theory (e/d ()
                              (unsigned-byte-p
                               (:linear <=-logior)
                               negative-logand-to-positive-logand-with-n55p-x
                               las-to-pas rb rme08 rml08))))))

  (local
   (defthm xr-msr-of-get-prefixes
     (and
      (equal (xr :msr idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
             (xr :msr idx x86))
      (equal (xr :seg-hidden idx (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
             (xr :seg-hidden idx x86)))
     :hints (("Goal"
              :cases ((app-view x86))
              :do-not-induct t
              :in-theory (e/d () (get-prefixes las-to-pas rb rme08 rml08))))))

  (defrule 64-bit-modep-of-get-prefixes
    (equal (64-bit-modep (mv-nth 2 (get-prefixes proc-mode start-rip prefixes cnt x86)))
           (64-bit-modep x86))
    :in-theory (e/d (64-bit-modep) ())
    :do-not-induct t)

  (defrule x86-operation-mode-of-get-prefixes
    (equal (x86-operation-mode
            (mv-nth 2
                    (get-prefixes
                     proc-mode start-rip prefixes cnt x86)))
           (x86-operation-mode x86))
    :in-theory (e/d (x86-operation-mode) (get-prefixes))))

;; ----------------------------------------------------------------------

;; We set this limit back to the default one once we've defined all the opcode
;; dispatch functions.
(set-rewrite-stack-limit (+ 500 acl2::*default-rewrite-stack-limit*))

;; ----------------------------------------------------------------------

;; Three-byte Opcode Maps:

(make-event
 (b* (((mv table-doc-string dispatch)
       (create-dispatch-from-opcode-map
        *0F-38-three-byte-opcode-map-lst*
        (w state)
        :escape-bytes #ux0F_38_00)))

   `(progn
      (define first-three-byte-opcode-execute
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (start-rip        :type (signed-byte   #.*max-linear-address-size*))
         (temp-rip         :type (signed-byte   #.*max-linear-address-size*))
         (prefixes         :type (unsigned-byte 55))
         (mandatory-prefix :type (unsigned-byte 8))
         (rex-byte         :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8))
         (modr/m           :type (unsigned-byte 8))
         (sib              :type (unsigned-byte 8))
         x86)

        ;; #x0F #x38 are the first two opcode bytes.

        :parents (x86-decoder)
        ;; The following arg will avoid binding __function__ to
        ;; first-three-byte-opcode-execute. The automatic __function__ binding
        ;; that comes with define causes stack overflows during the guard proof
        ;; of this function.
        :no-function t
        :ignore-ok t
        :short "First three-byte opcode dispatch function."
        :long "<p>@('first-three-byte-opcode-execute) is the doorway to the
     first three-byte opcode map, i.e., to all three-byte opcodes whose first
     two opcode bytes are @('0F 38').</p>"
        :guard-hints (("Goal"
                       :do-not '(preprocess)
                       :in-theory
                       (e/d
                        ()
                        (unsigned-byte-p signed-byte-p))))

        (let ((opcode (+ #ux0F_38_00 opcode)))
          (case opcode ,@dispatch))

        ///

        (defthm x86p-first-three-byte-opcode-execute
          (implies (and (x86p x86)
                        (canonical-address-p temp-rip))
                   (x86p
                    (first-three-byte-opcode-execute
                     proc-mode start-rip temp-rip prefixes
                     mandatory-prefix rex-byte opcode modr/m sib x86)))))

      (defsection 0F-38-three-byte-opcodes-table
        :parents (implemented-opcodes)
        :short "@('x86isa') Support for Opcodes in the @('0F 38') Three Byte
        Map; see @(see implemented-opcodes) for details."
        :long ,table-doc-string))))

(make-event
 (b* (((mv table-doc-string dispatch)
       (create-dispatch-from-opcode-map
        *0F-3A-three-byte-opcode-map-lst*
        (w state)
        :escape-bytes #ux0F_3A_00)))

   `(progn
      (define second-three-byte-opcode-execute
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (start-rip        :type (signed-byte   #.*max-linear-address-size*))
         (temp-rip         :type (signed-byte   #.*max-linear-address-size*))
         (prefixes         :type (unsigned-byte 55))
         (mandatory-prefix :type (unsigned-byte 8))
         (rex-byte         :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8))
         (modr/m           :type (unsigned-byte 8))
         (sib              :type (unsigned-byte 8))
         x86)

        ;; #x0F #x3A are the first two opcode bytes.

        :parents (x86-decoder)
        ;; The following arg will avoid binding __function__ to
        ;; second-three-byte-opcode-execute. The automatic __function__ binding that
        ;; comes with define causes stack overflows during the guard proof of this
        ;; function.
        :no-function t
        :ignore-ok t
        :short "Second three-byte opcode dispatch function."
        :long "<p>@('second-three-byte-opcode-execute) is the doorway to the second
     three-byte opcode map, i.e., to all three-byte opcodes whose second two
     opcode bytes are @('0F 3A').</p>"
        :guard-hints (("Goal"
                       :do-not '(preprocess)
                       :in-theory (e/d () (unsigned-byte-p signed-byte-p))))

        (let ((opcode (+ #ux0F_3A_00 opcode)))
          (case opcode ,@dispatch))

        ///

        (defthm x86p-second-three-byte-opcode-execute
          (implies (and (x86p x86)
                        (canonical-address-p temp-rip))
                   (x86p (second-three-byte-opcode-execute
                          proc-mode start-rip temp-rip prefixes
                          mandatory-prefix rex-byte opcode modr/m sib x86)))))

      (defsection 0F-3A-three-byte-opcodes-table
        :parents (implemented-opcodes)
        :short "@('x86isa') Support for Opcodes in the @('0F 3A') Three Byte
        Map; see @(see implemented-opcodes) for details."
        :long ,table-doc-string))))

(define three-byte-opcode-decode-and-execute
  ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
   (start-rip          :type (signed-byte #.*max-linear-address-size*))
   (temp-rip           :type (signed-byte #.*max-linear-address-size*))
   (prefixes           :type (unsigned-byte 55))
   (rex-byte           :type (unsigned-byte 8))
   (second-escape-byte :type (unsigned-byte 8))
   x86)

  :ignore-ok t
  :guard (or (equal second-escape-byte #x38)
             (equal second-escape-byte #x3A))
  :guard-hints (("Goal" :do-not '(preprocess)
                 :in-theory (e/d*
                             (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                             (unsigned-byte-p
                              (:type-prescription bitops::logand-natp-type-2)
                              (:type-prescription bitops::ash-natp-type)
                              acl2::loghead-identity
                              not
                              tau-system
                              (tau-system)))))
  :parents (x86-decoder)
  :short "Decoder and dispatch function for three-byte opcodes, where @('0x0F
  0x38') are the first two opcode bytes"
  :long "<p>Source: Intel Manual, Volume 2, Appendix A-2</p>"

  (b* ((ctx 'three-byte-opcode-decode-and-execute)

       ((mv flg0 (the (unsigned-byte 8) opcode) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg0)
        (!!ms-fresh :opcode-byte-access-error flg0))

       ;; Possible values of opcode: all values denote opcodes of the first or
       ;; second three-byte map, depending on the value of second-escape-byte.
       ;; The function first-three-byte-opcode-execute or
       ;; second-three-byte-opcode-execute case-splits on this opcode byte and
       ;; calls the appropriate instruction semantic function.

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :increment-error flg))

       ((the (unsigned-byte 8) mandatory-prefix)
        (case (prefixes-slice :last-prefix prefixes)
          (#.*rep-pfx* (prefixes-slice :rep prefixes)) ;; F3 or F2
          (#.*opr-pfx* (prefixes-slice :opr prefixes)) ;; 66
          (otherwise 0)))

       (modr/m?
        (three-byte-opcode-ModR/M-p
         proc-mode 0 0 ;; vex-prefixes evex-prefixes
         mandatory-prefix second-escape-byte opcode))
       ((mv flg1 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg1) (!!ms-fresh :modr/m-byte-read-error flg1))

       ((mv flg temp-rip) (if modr/m?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg))

       (sib? (and modr/m?
                  (b* ((p4? (eql #.*addr-size-override*
                                 (prefixes-slice :adr prefixes)))
                       (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
                    (x86-decode-SIB-p modr/m 16-bit-addressp))))
       ((mv flg2 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg2)
        (!!ms-fresh :sib-byte-read-error flg2))

       ((mv flg temp-rip) (if sib?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg)))

    (case second-escape-byte
      (#x38
       (first-three-byte-opcode-execute
        proc-mode start-rip temp-rip prefixes rex-byte
        mandatory-prefix opcode modr/m sib x86))
      (#x3A
       (second-three-byte-opcode-execute
        proc-mode start-rip temp-rip prefixes rex-byte
        mandatory-prefix opcode modr/m sib x86))
      (otherwise
       ;; Unreachable.
       (!!ms-fresh :illegal-value-of-second-escape-byte second-escape-byte))))

  ///

  (defrule x86p-three-byte-opcode-decode-and-execute
    (implies (and (canonical-address-p temp-rip)
                  (x86p x86))
             (x86p (three-byte-opcode-decode-and-execute
                    proc-mode start-rip temp-rip prefixes rex-byte escape-byte x86)))
    :enable add-to-*ip-is-i48p-rewrite-rule
    :disable signed-byte-p))

;; ----------------------------------------------------------------------

;; Two-byte Opcode Map:

(make-event
 (b* (((mv table-doc-string dispatch)
       (create-dispatch-from-opcode-map
        *two-byte-opcode-map-lst*
        (w state)
        :escape-bytes #ux0F_00)))

   `(progn
      (define two-byte-opcode-execute
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (start-rip        :type (signed-byte   #.*max-linear-address-size*))
         (temp-rip         :type (signed-byte   #.*max-linear-address-size*))
         (prefixes         :type (unsigned-byte 55))
         (mandatory-prefix :type (unsigned-byte 8))
         (rex-byte         :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8))
         (modr/m           :type (unsigned-byte 8))
         (sib              :type (unsigned-byte 8))
         x86)

        :parents (x86-decoder)
        ;; The following arg will avoid binding __function__ to
        ;; two-byte-opcode-execute. The automatic __function__ binding that comes
        ;; with define causes stack overflows during the guard proof of this
        ;; function.
        :no-function t
        :short "Two-byte opcode dispatch function."
        :long "<p>@('two-byte-opcode-execute') is the doorway to the two-byte
     opcode map, and will lead to the three-byte opcode map if @('opcode') is
     either @('#x38') or @('#x3A').</p>"
        :guard-hints (("Goal"
                       :do-not '(preprocess)
                       :in-theory (e/d (member-equal)
                                       (unsigned-byte-p signed-byte-p))))

        (case opcode ,@dispatch)

        ///

        (defthm x86p-two-byte-opcode-execute
          (implies (and (x86p x86)
                        (canonical-address-p temp-rip))
                   (x86p (two-byte-opcode-execute
                          proc-mode start-rip temp-rip prefixes mandatory-prefix
                          rex-byte opcode modr/m sib x86)))))

      (defsection two-byte-opcodes-table
        :parents (implemented-opcodes)
        :short "@('x86isa') Support for Opcodes in the Two-Byte Map (i.e.,
        first opcode byte is 0x0F); see @(see implemented-opcodes) for details."
        :long ,table-doc-string))))

(define two-byte-opcode-decode-and-execute
  ((proc-mode     :type (integer 0 #.*num-proc-modes-1*))
   (start-rip     :type (signed-byte #.*max-linear-address-size*))
   (temp-rip      :type (signed-byte #.*max-linear-address-size*))
   (prefixes      :type (unsigned-byte 55))
   (rex-byte      :type (unsigned-byte 8))
   (escape-byte   :type (unsigned-byte 8))
   x86)

  :ignore-ok t
  :guard (equal escape-byte #x0F)
  :guard-hints (("Goal" :do-not '(preprocess)
                 :in-theory (e/d*
                             (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                             (unsigned-byte-p
                              (:type-prescription bitops::logand-natp-type-2)
                              (:type-prescription bitops::ash-natp-type)
                              acl2::loghead-identity
                              not
                              tau-system
                              (tau-system)))))
  :parents (x86-decoder)
  :short "Decoder and dispatch function for two-byte opcodes"
  :long "<p>Source: Intel Manual, Volume 2, Appendix A-2</p>"

  (b* ((ctx 'two-byte-opcode-decode-and-execute)

       ((mv flg0 (the (unsigned-byte 8) opcode) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg0)
        (!!ms-fresh :opcode-byte-access-error flg0))

       ;; Possible values of opcode:

       ;; 1. #x38 and #x3A: These are escapes to the two three-byte opcode
       ;;    maps.  Function three-byte-opcode-decode-and-execute is called
       ;;    here, which also fetches the ModR/M and SIB bytes for these
       ;;    opcodes.

       ;; 2. All other values denote opcodes of the two-byte map.  The function
       ;;    two-byte-opcode-execute case-splits on this opcode byte and calls
       ;;    the appropriate instruction semantic function.

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :increment-error flg))

       ((the (unsigned-byte 8) mandatory-prefix)
        (case (prefixes-slice :last-prefix prefixes)
          (#.*rep-pfx* (prefixes-slice :rep prefixes)) ;; F3 or F2
          (#.*opr-pfx* (prefixes-slice :opr prefixes)) ;; 66
          (otherwise 0)))

       (modr/m?
        (two-byte-opcode-ModR/M-p
         proc-mode 0 0 ;; vex-prefixes evex-prefixes
         mandatory-prefix opcode))
       ((mv flg1 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg1) (!!ms-fresh :modr/m-byte-read-error flg1))

       ((mv flg temp-rip) (if modr/m?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg))

       (sib? (and modr/m?
                  (b* ((p4? (eql #.*addr-size-override*
                                 (prefixes-slice :adr prefixes)))
                       (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
                    (x86-decode-SIB-p modr/m 16-bit-addressp))))
       ((mv flg2 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg2)
        (!!ms-fresh :sib-byte-read-error flg2))

       ((mv flg temp-rip) (if sib?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg)))

    (two-byte-opcode-execute
     proc-mode start-rip temp-rip prefixes mandatory-prefix
     rex-byte opcode modr/m sib x86))

  ///

  (defrule x86p-two-byte-opcode-decode-and-execute
    (implies (and (canonical-address-p temp-rip)
                  (x86p x86))
             (x86p (two-byte-opcode-decode-and-execute
                    proc-mode start-rip temp-rip prefixes
                    rex-byte escape-byte x86)))
    :enable add-to-*ip-is-i48p-rewrite-rule
    :disable signed-byte-p))

;; ----------------------------------------------------------------------

;; One-byte Opcode Map:

(make-event

 (b* (((mv table-doc-string dispatch)
       (create-dispatch-from-opcode-map
        *one-byte-opcode-map-lst*
        (w state)
        :escape-bytes #ux00)))

   `(progn
      (define one-byte-opcode-execute
        ((proc-mode     :type (integer 0 #.*num-proc-modes-1*))
         (start-rip     :type (signed-byte   #.*max-linear-address-size*))
         (temp-rip      :type (signed-byte   #.*max-linear-address-size*))
         (prefixes      :type (unsigned-byte 55))
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
     maps.</p>"
        :guard-hints (("Goal"
                       :do-not '(preprocess)
                       :in-theory (e/d () (unsigned-byte-p signed-byte-p))))

        (case opcode ,@dispatch)

        ///

        (defthm x86p-one-byte-opcode-execute
          (implies (and (x86p x86)
                        (canonical-address-p temp-rip))
                   (x86p (one-byte-opcode-execute
                          proc-mode start-rip temp-rip
                          prefixes rex-byte opcode modr/m sib x86)))))

      (defsection one-byte-opcodes-table
        :parents (implemented-opcodes)
        :short "@('x86isa') Support for Opcodes in the One-Byte Map; see @(see
        implemented-opcodes) for details."
        :long ,table-doc-string))))

;; ----------------------------------------------------------------------

;; VEX-encoded instructions:

(local
 (defthm dumb-integerp-of-mv-nth-1-rme08-rule
   (implies (force (x86p x86))
            (integerp (mv-nth 1 (rme08 proc-mode eff-addr seg-reg r-x x86))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm unsigned-byte-p-24-of-vex-prefixes-rule
   (implies
    (unsigned-byte-p 8 byte)
    (and (unsigned-byte-p 24 (logior #xC400 (ash byte 16)))
         (unsigned-byte-p 24 (logior #xC500 (ash byte 16)))))))

(make-event
 `(define vex-0F-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                              opcode byte")
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the two-byte opcode map"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))
    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86)))

    (case opcode
      ,@(avx-case-gen *vex-0F-opcodes* t state))))

(make-event
 `(define vex-0F38-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                             opcode byte")
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the first
    three-byte opcode map"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86)))

    (case opcode
      ,@(avx-case-gen *vex-0F38-opcodes* t state))))

(make-event
 `(define vex-0F3A-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                            opcode byte")
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the second
    three-byte opcode map"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86)))

    (case opcode
      ,@(avx-case-gen *vex-0F3A-opcodes* t state))))

(define vex-decode-and-execute
  ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
   (start-rip              :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                           "@('temp-rip') points to the byte following the
                            first two VEX prefixes that were already read and
                            placed in the @('vex-prefixes') structure in @(tsee
                            x86-fetch-decode-execute).")
   (prefixes               :type (unsigned-byte 55))
   (rex-byte               :type (unsigned-byte 8))
   (vex-prefixes           :type (unsigned-byte 24)
                           "Only @('byte0') and @('byte1') fields are populated
                            when this function is called.")
   x86)

  :guard (vex-prefixes-byte0-p vex-prefixes)

  :guard-hints
  (("Goal"
    :in-theory
    (e/d (vex-prefixes-byte0-p
          vex-prefixes-map-p add-to-*ip
          add-to-*ip-is-i48p-rewrite-rule)
         (bitops::logand-with-negated-bitmask not (tau-system)))))
  :prepwork
  ((local
    (defthm vex-decode-and-execute-guard-helper
      (implies (and (unsigned-byte-p 8 byte-1)
                    (unsigned-byte-p 8 byte-2))
               (and
                (<
                 (logior
                  (logand #xffffff00
                          (logior (logand #xffffffff00ffffff vex-prefixes)
                                  (ash byte-1
                                       24)))
                  byte-2)
                 4294967296)
                (<=
                 0
                 (logior byte-1
                         (logand #xffffff00
                                 (logior (logand #xffffffff00ffffff vex-prefixes)
                                         (ash byte-2 24)))))
                (<
                 (logior byte-1
                         (logand #xffffff00
                                 (logior (logand #xffffffff00ffffff vex-prefixes)
                                         (ash byte-2 24))))
                 4294967296)))))

   (local
    (defthm logtail-16-of-unsigned-byte-p-8
      (implies (unsigned-byte-p 8 byte)
               (equal (logtail 16 byte) 0)))))

  :parents (x86-decoder)

  :long "<p>@('vex-decode-and-execute') dispatches control to VEX-encoded
  instructions.</p>

  <p><i>Reference: Intel Vol. 2A, Section 2.3: Intel Advanced Vector
   Extensions (Intel AVX)</i></p>"

  (b* ((ctx 'vex-decode-and-execute)
       ;; Reference for the following checks that lead to #UD:
       ;; Intel Vol. 2,
       ;; Section 2.3.2 - VEX and the LOCK prefix
       ;; Section 2.3.3 - VEX and the 66H, F2H, and F3H prefixes
       ;; Section 2.3.4 - VEX and the REX prefix

       ;; Any VEX-encoded instruction with mandatory (SIMD) prefixes, lock
       ;; prefix, and REX prefixes (i.e., 66, F2, F3, F0, and 40-4F) preceding
       ;; VEX will #UD.  Therefore, we fetch VEX prefixes after the legacy
       ;; prefixes (function get-prefixes) and the REX prefix have been
       ;; detected and fetched in x86-fetch-decode-execute.

       ((when (not (equal rex-byte 0)))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :rex rex-byte))
       ;; TODO: Intel Vol. 2A Sections 2.3.2 and 2.3.3 say "Any VEX-encoded
       ;; instruction with a LOCK/66H/F2H/F3H prefix preceding VEX will #UD."
       ;; So, should I check :last-byte here instead?
       ((when (equal (prefixes-slice :lck prefixes) #.*lock*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :lock-prefix))
       ((when (equal (prefixes-slice :rep prefixes) #.*mandatory-f2h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :F2-prefix))
       ((when (equal (prefixes-slice :rep prefixes) #.*mandatory-f3h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :F3-prefix))
       ((when (equal (prefixes-slice :opr prefixes) #.*mandatory-66h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :66-prefix))

       (vex2-prefix?
        (equal (vex-prefixes-slice :byte0 vex-prefixes) #.*vex2-byte0*))
       (vex3-prefix?
        (equal (vex-prefixes-slice :byte0 vex-prefixes) #.*vex3-byte0*))
       (vex-byte1 (vex-prefixes-slice :byte1 vex-prefixes))
       ;; VEX3 Byte 1 #UD Checks for M-MMMM field:
       ;; References: Intel Vol. 2, Figure 2-9 and Section 2.3.6.1
       ((mv vex3-0F-map? vex3-0F38-map? vex3-0F3A-map?)
        (if vex3-prefix?
            (mv (equal (vex3-byte1-slice :m-mmmm vex-byte1) #.*v0F*)
                (equal (vex3-byte1-slice :m-mmmm vex-byte1) #.*v0F38*)
                (equal (vex3-byte1-slice :m-mmmm vex-byte1) #.*v0F3A*))
          (mv nil nil nil)))
       ((when (and vex3-prefix?
                   (not (or vex3-0F-map? vex3-0F38-map? vex3-0F3A-map?))))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :m-mmmm vex-byte1))

       ;; Completely populating the vex-prefixes structure --- filling out only
       ;; next-byte for vex2-prefixes and both byte2 and next-byte for
       ;; vex3-prefix:
       ((mv flg0 (the (unsigned-byte 8) byte2/next-byte) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg0)
        (!!ms-fresh :vex-byte2/next-byte-read-error flg0))
       ((mv flg1 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg1)
        (!!ms-fresh :increment-error flg1))
       (vex-prefixes
        (if vex3-prefix?
            (!vex-prefixes-slice :byte2 byte2/next-byte vex-prefixes)
          vex-prefixes))
       ((mv flg2 (the (unsigned-byte 8) next-byte) x86)
        (if vex3-prefix?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg2)
        (!!ms-fresh :next-byte-read-error flg2))
       ((mv flg3 temp-rip)
        (if vex3-prefix?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg3)
        (!!ms-fresh :increment-error flg3))

       (opcode
        (the (unsigned-byte 8)
          (if vex3-prefix? next-byte byte2/next-byte)))

       ;; All VEX- and EVEX-encoded instructions require a ModR/M byte.
       ;; Reference: Intel Manual, Vol. 2, Figure 2-8 (Instruction Encoding
       ;; Format with VEX Prefix) and Figure 2-10 (AVX-512 Instruction Format
       ;; and the EVEX Prefix)
       ((mv flg4 (the (unsigned-byte 8) modr/m) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg4)
        (!!ms-fresh :modr/m-byte-read-error flg4))
       ((mv flg5 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg5) (!!ms-fresh :increment-error flg5))

       (sib? (b* ((p4? (eql #.*addr-size-override*
                            (prefixes-slice :adr prefixes)))
                  (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
               (x86-decode-SIB-p modr/m 16-bit-addressp)))
       ((mv flg6 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg6)
        (!!ms-fresh :sib-byte-read-error flg6))
       ((mv flg7 temp-rip)
        (if sib?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg7) (!!ms-fresh :increment-error flg7)))

    (cond
     ((mbe :logic (vex-prefixes-map-p #ux0F vex-prefixes)
           :exec (or vex2-prefix? (and vex3-prefix? vex3-0F-map?)))
      (vex-0F-execute start-rip temp-rip vex-prefixes opcode modr/m sib x86))
     ((mbe :logic (vex-prefixes-map-p #ux0F_38 vex-prefixes)
           :exec (and vex3-prefix? vex3-0F38-map?))
      (vex-0F38-execute start-rip temp-rip vex-prefixes opcode modr/m sib x86))
     ((mbe :logic (vex-prefixes-map-p #ux0F_3A vex-prefixes)
           :exec (and vex3-prefix? vex3-0F3A-map?))
      (vex-0F3A-execute start-rip temp-rip vex-prefixes opcode modr/m sib x86))
     (t
      ;; Unreachable.
      (!!ms-fresh :illegal-value-of-VEX-m-mmmm))))

  ///

  (defthm x86p-vex-decode-and-execute
    (implies (and (x86p x86)
                  (canonical-address-p temp-rip))
             (x86p
              (vex-decode-and-execute
               proc-mode
               start-rip temp-rip prefixes rex-byte vex-prefixes x86)))
    :hints (("Goal" :in-theory (e/d (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                                    ())))))

;; ----------------------------------------------------------------------

;; EVEX-encoded instructions:

(local
 (defthm unsigned-byte-p-40-of-evex-prefixes-rule
   (implies
    (unsigned-byte-p 8 byte)
    (unsigned-byte-p 40 (logior #x6200 (ash byte 16))))))

(make-event
 `(define evex-0F-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                              opcode byte")
     (evex-prefixes           :type (unsigned-byte 32)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the two-byte opcode map"
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))
    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86))
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(avx-case-gen *evex-0F-opcodes* nil state))))

(make-event
 `(define evex-0F38-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                             opcode byte")
     (evex-prefixes           :type (unsigned-byte 32)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the first
    three-byte opcode map"
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86))
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(avx-case-gen *evex-0F38-opcodes* nil state))))

(make-event
 `(define evex-0F3A-execute
    ((start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                            opcode byte")
     (evex-prefixes           :type (unsigned-byte 32)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the second
    three-byte opcode map"
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (and (canonical-address-p temp-rip)
                                 (x86p x86))
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(avx-case-gen *evex-0F3A-opcodes* nil state))))

(define evex-decode-and-execute
  ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
   (start-rip              :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                           "@('temp-rip') points to the byte following the
                            first two EVEX prefixes that were already read and
                            placed in the @('evex-prefixes') structure in @(tsee
                            x86-fetch-decode-execute).")
   (prefixes               :type (unsigned-byte 55))
   (rex-byte               :type (unsigned-byte 8))
   (evex-prefixes          :type (unsigned-byte 32)
                           "Only @('byte0') and @('byte1') fields are populated
                            when this function is called.")
   x86)

  :ignore-ok t

  :guard-hints
  (("Goal"
    :in-theory
    (e/d (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
         (bitops::logand-with-negated-bitmask))))

  :parents (x86-decoder)

  :long "<p>@('evex-decode-and-execute') dispatches control to EVEX-encoded
  instructions.</p>

  <p><i>Reference: Intel Vol. 2A, Section 2.6: Intel(R) AVX-512
  Encoding</i></p>"

  (b* ((ctx 'evex-decode-and-execute)

       ;; Though I can't find it anywhere explicitly in the Intel manuals, it
       ;; seems reasonable to expect that like the VEX-encoded instructions,
       ;; the use of mandatory and REX prefixes should cause a #UD here too.

       ((when (not (equal rex-byte 0)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :rex rex-byte))
       ((when (equal (prefixes-slice :lck prefixes) #.*lock*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :lock-prefix))
       ((when (equal (prefixes-slice :rep prefixes) #.*mandatory-f2h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :F2-prefix))
       ((when (equal (prefixes-slice :rep prefixes) #.*mandatory-f3h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :F3-prefix))
       ((when (equal (prefixes-slice :opr prefixes) #.*mandatory-66h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :66-prefix))

       ;; EVEX Byte 1:
       (evex-byte1 (evex-prefixes-slice :byte1 evex-prefixes))
       ;; EVEX Byte 1 #UD Checks
       ;; Reference: Intel Vol. 2, Section 2.6.11.2 (Opcode Independent #UD)
       ((when (not (equal (evex-byte1-slice :res evex-byte1) 0)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :byte1-reserved-bits))
       ((mv evex-0F-map? evex-0F38-map? evex-0F3A-map?)
        (mv (equal (evex-byte1-slice :mm evex-byte1) #.*v0F*)
            (equal (evex-byte1-slice :mm evex-byte1) #.*v0F38*)
            (equal (evex-byte1-slice :mm evex-byte1) #.*v0F3A*)))
       ((when (not (or evex-0F-map? evex-0F38-map? evex-0F3A-map?)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :mm evex-byte1))

       ;; EVEX Byte 2:
       ((mv flg0 (the (unsigned-byte 8) evex-byte2) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg0)
        (!!ms-fresh :evex-byte2-read-error flg0))
       ((mv flg1 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg1)
        (!!ms-fresh :increment-error flg1))
       (evex-prefixes
        (!evex-prefixes-slice :byte2 evex-byte2 evex-prefixes))
       ;; EVEX Byte 2 #UD Check
       ;; Reference: Intel Vol. 2, Section 2.6.11.2 (Opcode Independent #UD)
       ((when (not (equal (evex-byte2-slice :res evex-byte2) 1)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :byte2-reserved-bit))

       ;; EVEX Byte 3:
       ((mv flg2 (the (unsigned-byte 8) evex-byte3) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg2)
        (!!ms-fresh :evex-byte3-read-error flg2))
       ((mv flg3 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg3)
        (!!ms-fresh :increment-error flg3))

       ;; Opcode:
       ((mv flg4 (the (unsigned-byte 8) opcode) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg4)
        (!!ms-fresh :opcode-read-error flg4))
       ((mv flg5 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg5)
        (!!ms-fresh :increment-error flg5))

       ;; All VEX- and EVEX-encoded instructions require a ModR/M byte.
       ;; Reference: Intel Manual, Vol. 2, Figure 2-8 (Instruction Encoding
       ;; Format with VEX Prefix) and Figure 2-10 (AVX-512 Instruction Format
       ;; and the EVEX Prefix)
       ((mv flg6 (the (unsigned-byte 8) modr/m) x86)
        (rme08 proc-mode temp-rip *cs* :x x86))
       ((when flg6)
        (!!ms-fresh :modr/m-byte-read-error flg6))
       ((mv flg7 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg7) (!!ms-fresh :increment-error flg7))

       (sib? (b* ((p4? (eql #.*addr-size-override*
                            (prefixes-slice :adr prefixes)))
                  (16-bit-addressp
                   (eql 2 (select-address-size proc-mode p4? x86))))
               (x86-decode-SIB-p modr/m 16-bit-addressp)))
       ((mv flg8 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg8)
        (!!ms-fresh :sib-byte-read-error flg8))
       ((mv flg9 temp-rip)
        (if sib?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg9) (!!ms-fresh :increment-error flg9)))

    (cond
     (evex-0F-map?
      (evex-0F-execute start-rip temp-rip evex-prefixes opcode modr/m sib x86))
     (evex-0F38-map?
      (evex-0F38-execute start-rip temp-rip evex-prefixes opcode modr/m sib x86))
     (evex-0F3A-map?
      (evex-0F3A-execute start-rip temp-rip evex-prefixes opcode modr/m sib x86))
     (t
      ;; Unreachable.
      (!!ms-fresh :illegal-value-of-EVEX-mm))))

  ///

  (defthm x86p-evex-decode-and-execute
    (implies (and (x86p x86)
                  (canonical-address-p temp-rip))
             (x86p
              (evex-decode-and-execute
               proc-mode
               start-rip temp-rip prefixes rex-byte evex-prefixes x86)))
    :hints (("Goal" :in-theory (e/d (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                                    ((tau-system)))))))

;; ----------------------------------------------------------------------

;; Setting this limit back to the default value:
(set-rewrite-stack-limit acl2::*default-rewrite-stack-limit*)

;; ----------------------------------------------------------------------

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

   (local (in-theory (e/d* ()
                           (signed-byte-p unsigned-byte-p not
                                          (tau-system))))))

  :guard-hints
  (("Goal" :in-theory (e/d (vex-prefixes-byte0-p
                            add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                           ())))

  (b* ((ctx 'x86-fetch-decode-execute)
       (proc-mode (x86-operation-mode x86))
       (64-bit-modep (equal proc-mode #.*64-bit-mode*))
       ;; We don't want our interpreter to take a step if the machine is in a
       ;; bad state.  Such checks are made in x86-run but I am duplicating them
       ;; here in case this function is being used at the top-level.
       ((when (or (ms x86) (fault x86))) x86)

       (start-rip (the (signed-byte #.*max-linear-address-size*)
                    (read-*ip proc-mode x86)))

       ((mv flg0 (the (unsigned-byte 55) prefixes) x86)
        (get-prefixes proc-mode start-rip 0 15 x86))
       ;; Among other errors (including if there are 15 prefix bytes, which
       ;; leaves no room for an opcode byte in a legal instruction), if
       ;; get-prefixes detects a non-canonical address while attempting to
       ;; fetch prefixes, flg0 will be non-nil.
       ((when flg0)
        (!!ms-fresh :error-in-reading-prefixes flg0))

       ((the (unsigned-byte 8) opcode/rex/vex/evex-byte)
        (prefixes-slice :next-byte prefixes))

       ((the (unsigned-byte 4) prefix-length)
        (prefixes-slice :num-prefixes prefixes))

       ((mv flg temp-rip) (add-to-*ip proc-mode start-rip (1+ prefix-length) x86))
       ((when flg) (!!ms-fresh :increment-error flg))

       ;; If opcode/rex/vex/evex-byte is a rex byte, it is filed away in
       ;; "rex-byte". A REX byte has the form 4xh, but this applies only to
       ;; 64-bit mode; in 32-bit mode, 4xh is an opcode for INC or DEC, so in
       ;; 32-bit mode, there is no REX byte "by construction".
       ((the (unsigned-byte 8) rex-byte)
        (if (and 64-bit-modep
                 (equal (the (unsigned-byte 4)
                          (ash opcode/rex/vex/evex-byte -4))
                        4))
            opcode/rex/vex/evex-byte
          0))

       ((mv flg1 (the (unsigned-byte 8) opcode/vex/evex-byte) x86)
        (if (equal 0 rex-byte)
            (mv nil opcode/rex/vex/evex-byte x86)
          (rme08 proc-mode temp-rip *cs* :x x86)))
       ((when flg1)
        (!!ms-fresh :opcode/vex/evex-byte-read-error flg1))

       ((mv flg2 temp-rip)
        (if (equal rex-byte 0)
            (mv nil temp-rip)
          (add-to-*ip proc-mode temp-rip 1 x86)))
       ((when flg2) (!!ms-fresh :increment-error flg2))

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
       ((mv flg3 les/lds-distinguishing-byte x86)
        (if vex-byte0?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg3)
        (!!ms-fresh :les/lds-distinguishing-byte-read-error flg3))
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
        (b* (((mv flg1-vex temp-rip)
              (add-to-*ip proc-mode temp-rip 1 x86))
             ((when flg1-vex)
              (!!ms-fresh :vex-byte1-increment-error flg1-vex))
             (vex-prefixes
              (!vex-prefixes-slice
               :byte0 opcode/vex/evex-byte 0))
             (vex-prefixes
              (!vex-prefixes-slice
               :byte1 les/lds-distinguishing-byte vex-prefixes)))
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
       ((mv flg4 bound-distinguishing-byte x86)
        (if evex-byte0?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg4)
        (!!ms-fresh :bound-distinguishing-byte-read-error flg4))
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
        (b* (((mv flg1-evex temp-rip)
              (add-to-*ip proc-mode temp-rip 1 x86))
             ((when flg1-evex)
              (!!ms-fresh :evex-byte1-increment-error flg1-evex))
             (evex-prefixes
              (!evex-prefixes-slice :byte0 opcode/evex-byte 0))
             (evex-prefixes
              (!evex-prefixes-slice
               :byte1 bound-distinguishing-byte evex-prefixes)))
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
       ((mv flg5 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (if (or vex-byte0? evex-byte0?)
                ;; The above will be true only if the instruction is LES or LDS
                ;; or BOUND in the 32-bit mode.
                (mv nil les/lds-distinguishing-byte x86)
              (rme08 proc-mode temp-rip *cs* :x x86))
          (mv nil 0 x86)))
       ((when flg5)
        (!!ms-fresh :modr/m-byte-read-error flg5))

       ((mv flg6 temp-rip)
        (if modr/m?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg6) (!!ms-fresh :increment-error flg6))

       (sib? (and modr/m?
                  (b* ((p4? (eql #.*addr-size-override*
                                 (prefixes-slice :adr prefixes)))
                       (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
                    (x86-decode-SIB-p modr/m 16-bit-addressp))))

       ((mv flg7 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip *cs* :x x86)
          (mv nil 0 x86)))
       ((when flg7)
        (!!ms-fresh :sib-byte-read-error flg7))

       ((mv flg8 temp-rip)
        (if sib?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg8) (!!ms-fresh :increment-error flg8)))

    (one-byte-opcode-execute
     proc-mode start-rip temp-rip prefixes rex-byte opcode-byte
     modr/m sib x86))

  ///

  (defrule x86p-x86-fetch-decode-execute
    (implies (x86p x86)
             (x86p (x86-fetch-decode-execute x86)))
    :enable add-to-*ip-is-i48p-rewrite-rule)

  (defthmd ms-fault-and-x86-fetch-decode-and-execute
    (implies (and (x86p x86)
                  (or (ms x86) (fault x86)))
             (equal (x86-fetch-decode-execute x86) x86)))

  (defthm x86-fetch-decode-execute-opener
    ;; TODO: Extend to VEX and EVEX prefixes when necessary.
    (implies
     (and
      (not (ms x86))
      (not (fault x86))
      (equal proc-mode (x86-operation-mode x86))
      (equal start-rip (read-*ip proc-mode x86))
      (equal 64-bit-modep (equal proc-mode #.*64-bit-mode*))
      (not (mv-nth 0 (get-prefixes proc-mode start-rip 0 15 x86)))
      (equal prefixes (mv-nth 1 (get-prefixes proc-mode start-rip 0 15 x86)))
      (equal opcode/rex/vex/evex-byte
             (prefixes-slice :next-byte prefixes))
      (equal prefix-length (prefixes-slice :num-prefixes prefixes))
      (equal temp-rip0
             (if (equal prefix-length 0)
                 (mv-nth 1 (add-to-*ip proc-mode start-rip 1 x86))
               (mv-nth 1 (add-to-*ip proc-mode start-rip (1+ prefix-length) x86))))
      (equal rex-byte (if (and 64-bit-modep
                               (equal (ash opcode/rex/vex/evex-byte -4) 4))
                          opcode/rex/vex/evex-byte
                        0)) ; rex-byte is 0 in 32-bit mode
      (equal opcode/vex/evex-byte (if (equal rex-byte 0)
                                      opcode/rex/vex/evex-byte
                                    (mv-nth 1 (rme08 proc-mode temp-rip0 *cs* :x x86))))
      (equal temp-rip1 (if (equal rex-byte 0)
                           temp-rip0
                         (mv-nth 1 (add-to-*ip proc-mode temp-rip0 1 x86))))

      ;; *** No VEX prefixes ***
      (not (equal opcode/vex/evex-byte #.*vex3-byte0*))
      (not (equal opcode/vex/evex-byte #.*vex2-byte0*))
      ;; *** No EVEX prefixes ***
      (not (equal opcode/vex/evex-byte #.*evex-byte0*))

      (equal modr/m?
             (one-byte-opcode-ModR/M-p proc-mode opcode/vex/evex-byte))
      (equal modr/m (if modr/m?
                        (mv-nth 1 (rme08 proc-mode temp-rip1 *cs* :x x86))
                      0))
      (equal temp-rip2 (if modr/m?
                           (mv-nth 1 (add-to-*ip proc-mode temp-rip1 1 x86))
                         temp-rip1))
      (equal p4? (equal #.*addr-size-override*
                        (prefixes-slice :adr prefixes)))
      (equal 16-bit-addressp (equal 2 (select-address-size proc-mode p4? x86)))
      (equal sib? (and modr/m? (x86-decode-sib-p modr/m 16-bit-addressp)))
      (equal sib (if sib? (mv-nth 1 (rme08 proc-mode temp-rip2 *cs* :x x86)) 0))

      (equal temp-rip3 (if sib?
                           (mv-nth 1 (add-to-*ip proc-mode temp-rip2 1 x86))
                         temp-rip2))

      (or (app-view x86)
          (not (marking-view x86)))
      (not (if (equal prefix-length 0)
               (mv-nth 0 (add-to-*ip proc-mode start-rip 1 x86))
             (mv-nth 0 (add-to-*ip proc-mode start-rip (1+ prefix-length) x86))))
      (if (and (equal prefix-length 0)
               (equal rex-byte 0)
               (not modr/m?))
          ;; One byte instruction --- all we need to know is that
          ;; the new RIP is canonical, not that there's no error
          ;; in reading a value from that address.
          t
        (not (mv-nth 0 (rme08 proc-mode temp-rip0 *cs* :x x86))))
      (if (equal rex-byte 0)
          t
        (not (mv-nth 0 (add-to-*ip proc-mode temp-rip0 1 x86))))
      (if modr/m?
          (and (not (mv-nth 0 (add-to-*ip proc-mode temp-rip1 1 x86)))
               (not (mv-nth 0 (rme08 proc-mode temp-rip1 *cs* :x x86))))
        t)
      (if sib?
          (and (not (mv-nth 0 (add-to-*ip proc-mode temp-rip2 1 x86)))
               (not (mv-nth 0 (rme08 proc-mode temp-rip2 *cs* :x x86))))
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
       proc-mode start-rip temp-rip3 prefixes rex-byte
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

(define x86-run-steps1
  ((n :type (unsigned-byte 59))
   (n0 :type (unsigned-byte 59))
   x86)

  :enabled t
  :guard (and (natp n)
              (natp n0)
              (<= n n0))

  (let* ((diff (the (unsigned-byte 59) (- n0 n))))

    (cond ((ms x86)
           (mv diff x86))
          ((fault x86)
           (mv diff x86))
          ((zp n)
           (let* ((ctx 'x86-run)
                  (x86 (!!ms-fresh :timeout t)))
             (mv diff x86)))
          (t (let* ((x86 (x86-fetch-decode-execute x86))
                    (n-1 (the (unsigned-byte 59) (1- n))))
               (x86-run-steps1 n-1 n0 x86))))))

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

;; ----------------------------------------------------------------------

(define x86-fetch-decode-execute-halt
  ((halt-address :type (signed-byte   #.*max-linear-address-size*))
   x86)
  :enabled t
  :parents (x86-decoder)
  :inline t

  :short "Alternative version of @(tsee x86-fetch-decode-execute) that sets the
  @('MS') field if @('rip') is equal to @('halt-address')"

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ((local (in-theory (e/d* () (signed-byte-p unsigned-byte-p not)))))

  (b* ((ctx __function__))
    (if (equal (the (signed-byte #.*max-linear-address-size*)
                 (rip x86))
               halt-address)
        (!!ms-fresh)
      (x86-fetch-decode-execute x86))))

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

;; ----------------------------------------------------------------------