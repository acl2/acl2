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
; Robert Krug         <rkrug@cs.utexas.edu>
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-structures" :dir :utils)
(include-book "physical-memory" :ttags (:undef-flg :include-raw))
(include-book "clause-processors/find-matching" :dir :system)

;; [Shilpi]: For now, I've removed nested paging and all paging modes
;; except IA-32e paging from our model.

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection paging
  :parents (machine)
  :short "Specification of x86 Paging"
  )

(defsection ia32e-paging
  :parents (paging)
  :short "Specification of Paging in the 64-bit Mode"
  )

(local (xdoc::set-default-parents ia32e-paging))

;; ======================================================================

(define same-page ((lin-addr integerp)
                   (lin-addr-2 integerp))
  (or (equal lin-addr lin-addr-2)
      (and (mbt (and (integerp lin-addr)
                     (integerp lin-addr-2)))
           (equal (logtail 12 lin-addr)
                  (logtail 12 lin-addr-2))))
  ///
  (defequiv same-page)

  (local (defthmd equal-logtail-i-implies-equal-logtail-j-for-j>=i
                  (implies (and (natp i)
                                (integerp x)
                                (integerp y)
                                (integerp j)
                                (>= j i)
                                (equal (logtail i x)
                                       (logtail i y)))
                           (equal (logtail j x)
                                  (logtail j y)))
                  :hints (("Goal" :in-theory (enable logtail**
                                                     bitops::logtail-induct)))))

  (defthm same-page-implies-logtails>=12-equal
          (implies (and (integerp i)
                        (>= i 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (equal (logtail i x)
                          (logtail i y)))
          :hints (("Goal" :use (:instance equal-logtail-i-implies-equal-logtail-j-for-j>=i (i 12) (j i) (x x) (y y)))))

  (defthm same-page-address-construction
          (implies (same-page x y)
                   (same-page (logior (loghead i x)
                                      (ash z i))
                              (logior (loghead i y)
                                      (ash z i))))
          :rule-classes :congruence)

  (defthm same-page-implies-logapp<=12-equal
          (implies (and (integerp n)
                        (<= n 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (same-page (logapp n x z)
                              (logapp n y z)))
          :hints (("Goal" :in-theory (enable logtail**
                                             bitops::logtail-induct
                                             logapp**
                                             bitops::logapp-induct))))

  (defthm same-page-implies-same-page-logheads
          (implies (same-page a b)
                   (same-page (loghead n a) (loghead n b)))
          :rule-classes :congruence)

  (local (defthmd logext-maintains-logtail-equals
                  (implies (and (integerp k)
                                (> k n)
                                (natp n)
                                (integerp x)
                                (integerp y)
                                (equal (logtail n x)
                                       (logtail n y)))
                           (equal (logtail n (logext k x))
                                  (logtail n (logext k y))))
                  :hints (("Goal" :in-theory (enable logtail**
                                                     bitops::logtail-induct
                                                     logext**
                                                     bitops::logext-induct)))))

  (defthm logexting-maintains-same-page
          (implies (and (integerp n)
                        (> n 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (same-page (logext n x)
                              (logext n y)))
          :hints (("Goal" :use (:instance logext-maintains-logtail-equals (n 12) (k n)))))

  (defthmd logtails<=12-equal-implies-same-page
           (implies (and (integerp x)
                         (integerp y)
                         (natp n)
                         (<= n 12)
                         (equal (logtail n x) (logtail n y)))
                    (same-page x y))
           :hints (("Goal" :use (:instance equal-logtail-i-implies-equal-logtail-j-for-j>=i (j 12) (i n))))))

(defthm 0-loghead-of-ash
        (implies (and (natp n)
                      (natp m)
                      (<= n m))
                 (equal (loghead n (ash x m))
                        0))
        :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                           ash** bitops::ash**-induct))))

(define same-page-offset ((lin-addr integerp)
                          (lin-addr-2 integerp))
  (equal (loghead 12 lin-addr)
         (loghead 12 lin-addr-2))
  ///
  (defequiv same-page-offset)

  (defthm same-page-offset-addr-construction
          (implies (and (natp n)
                        (>= n 12))
                   (same-page-offset (logior (loghead n x)
                                             (ash y n))
                                     x)))

  (defthm logexted-is-same-page
          (implies (and (natp n)
                        (>= n 12))
                   (same-page-offset (logext n x)
                                     x)))

  (local (defthmd equal-loghead-implies-equal-more-restrictive-logheads
                  (implies (and (natp n)
                                (natp m)
                                (<= m n)
                                (equal (loghead n x)
                                       (loghead n y)))
                           (equal (loghead m x)
                                  (loghead m y)))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct)))))

  (defthm same-page-offset-implies-same-logheads
          (implies (and (natp n)
                        (<= n 12)
                        (same-page-offset y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (equal (loghead n x)
                          (loghead n y)))
          :hints (("Goal" :use (:instance equal-loghead-implies-equal-more-restrictive-logheads
                                          (n 12) (m n) (x x) (y y))))))

(defthm loghead-zero-smaller
  (implies (and (equal (loghead n x) 0)
                (natp n)
                (<= m n))
           (equal (loghead m x) 0))
  :hints (("Goal" :in-theory (e/d*
                              (acl2::ihsext-recursive-redefs
                               acl2::ihsext-inductions)
                              ()))))

(defthm-unsigned-byte-p n64p-xr-ctr
  :hyp t
  :bound 64
  :concl (xr :ctr i x86)
  :gen-linear t
  :gen-type t)

(define good-lin-addr-p (lin-addr x86)

  :parents (ia32e-paging)

  (b* ((cr0 (the (unsigned-byte 32) (n32 (ctri *cr0* x86))))
       (cr4 (the (unsigned-byte 22) (n22 (ctri *cr4* x86))))
       ;; Remember that *ia32_efer-idx* and *ia32_efer* are
       ;; different.  The latter is the "address" of the register on
       ;; the real machine and the former is the index of the
       ;; register in the x86 stobj.
       (ia32-efer (the (unsigned-byte 12)
                       (n12 (msri *ia32_efer-idx* x86)))))

      (cond ((equal (cr0Bits->pg cr0) 0)
             ;; Paging is off
             (n32p lin-addr))
            ((equal (cr4Bits->pae cr4) 0)
             ;; 32-bit paging
             (n32p lin-addr))
            ((equal (ia32_eferBits->lme ia32-efer) 0)
             ;; PAE paging
             (n32p lin-addr))
            (t
              ;; IA32e paging
              (canonical-address-p lin-addr)))))

(define page-fault-err-no
  ((p-flag :type (unsigned-byte 1))
   (r-w-x  :type (member :r :w :x))
   (cpl    :type (unsigned-byte 2))
   (rsvd   :type (unsigned-byte 1))
   (smep   :type (unsigned-byte 1))
   (pae    :type (unsigned-byte 1))
   (nxe    :type (unsigned-byte 1)))

  :parents (ia32e-paging)

  :returns (errno natp :rule-classes :type-prescription)

  ;; From Section 4.7 (Page Fault Exceptions), Vol. 3A of the Intel
  ;; Manual:
  ;;
  ;; P flag (bit 0). This flag is 0 if there is no valid translation
  ;; for the linear address because the P flag was 0 in one of the
  ;; paging-structure entries used to translate that address.
  ;;
  ;; W/R (bit 1). If the access causing the page-fault exception was a
  ;; write, this flag is 1; otherwise, it is 0. This flag describes
  ;; the access causing the page-fault exception, not the access
  ;; rights specified by paging.
  ;;
  ;; U/S (bit 2). If a user-mode (CPL= 3) access caused the page-fault
  ;; exception, this flag is 1; it is 0 if a supervisor-mode (CPL < 3)
  ;; access did so. This flag describes the access causing the
  ;; page-fault exception, not the access rights specified by paging.
  ;;
  ;; RSVD flag (bit 3). This flag is 1 if there is no valid
  ;; translation for the linear address because a reserved bit was set
  ;; in one of the paging-structure entries used to translate that
  ;; address. (Because reserved bits are not checked in a
  ;; paging-structure entry whose P flag is 0, bit 3 of the error code
  ;; can be set only if bit 0 is also set.)
  ;;
  ;; Bits reserved in the paging-structure entries are reserved for
  ;; future functionality. Software developers should be aware that
  ;; such bits may be used in the future and that a paging-structure
  ;; entry that causes a page-fault exception on one processor might
  ;; not do so in the future.
  ;;
  ;; I/D flag (bit 4). This flag is 1 if (1) the access causing the
  ;; page-fault exception was an instruction fetch; and (2) either (a)
  ;; CR4.SMEP = 1; or (b) both (i) CR4.PAE = 1 (either PAE paging or
  ;; ia32e paging is in use); and (ii) IA32_EFER.NXE = 1. Otherwise,
  ;; the flag is 0. This flag describes the access causing the
  ;; page-fault exception, not the access rights specified by paging.

  (logior (if (equal p-flag 1)
              1 ;;  (ash 1 0)
            0)
          (if (equal r-w-x :w)
              2 ;;  (ash 1 1)
            0)
          (if (equal cpl 3)
              4 ;;  (ash 1 2)o
            0)
          (if (equal rsvd 1)
              8 ;;  (ash 1 3)
            0)
          (if (and (equal r-w-x :x)
                   (or (equal smep 1)
                       (and (equal pae 1)
                            (equal nxe 1))))
              16 ;;  (ash 1 4)
            0)))

(define page-fault-exception (addr err-no x86)

  :parents (ia32e-paging)

  :returns (mv flg zero (x86 x86p :hyp :guard))

  ;; From Section 4.7 (Page Fault Exceptions), Vol. 3A of the Intel
  ;; Manual:

  ;; Page-fault exceptions occur only due to an attempt to use a linear
  ;; address. Failures to load the PDPTE registers with PAE paging (see
  ;; Section 4.4.1) cause general-protection exceptions (#GP(0)) and not
  ;; page-fault exceptions.

  (b* ((old-faults (fault x86))
       (new-faults (cons (list :page-fault err-no addr) old-faults))
       (x86 (!fault new-faults x86)))
      ;; [Shilpi]: I replaced (list :page-fault-exception err-no addr)
      ;; with t below because in the old world, the flag would differ
      ;; for every error, thereby disallowing dealing with all
      ;; page-faulting situations in one case, which slowed reasoning
      ;; down. There's no loss of information because the fault field
      ;; contains the error number and the address at which a fault
      ;; occurred.
      (mv t 0 x86))
  ///

  (defthm mv-nth-0-page-fault-exception
          (mv-nth 0 (page-fault-exception addr err-no x86)))

  (defthm mv-nth-1-page-fault-exception
          (equal (mv-nth 1 (page-fault-exception addr err-no x86))
                 0))

  (defthm xr-page-fault-exception
          (implies (not (equal fld :fault))
                   (equal (xr fld index (mv-nth 2 (page-fault-exception addr err-no x86)))
                          (xr fld index x86))))

  (defthm page-fault-exception-xw-values
          (implies (not (equal fld :fault))
                   (and (equal (mv-nth 0 (page-fault-exception addr err-no (xw fld index value x86)))
                               (mv-nth 0 (page-fault-exception addr err-no x86)))
                        (equal (mv-nth 1 (page-fault-exception addr err-no (xw fld index value x86)))
                               0))))

  (defthm page-fault-exception-xw-state
          (implies (not (equal fld :fault))
                   (equal (mv-nth 2 (page-fault-exception addr err-no (xw fld index value x86)))
                          (xw fld index value (mv-nth 2 (page-fault-exception addr err-no x86))))))

  (defrule 64-bit-modep-of-page-fault-exception
           (equal (64-bit-modep (mv-nth 2 (page-fault-exception addr err-no x86)))
                  (64-bit-modep x86)))

  (defrule x86-operation-mode-of-page-fault-exception
           (equal (x86-operation-mode (mv-nth 2 (page-fault-exception addr err-no x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode))

;; [Shilpi] Don't need functions like page-present, page-size, etc. anymore
;; since I've got efficient bitstruct functions now.  Should eliminate the
;; following and change any bind-free/syntaxp stuff too.

(define page-present
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->p entry)

  ///

  (defthm-unsigned-byte-p n01p-page-present
    :hyp t
    :bound 1
    :concl (page-present val)
    :gen-type t
    :gen-linear t))

(define page-size
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->ps entry)

  ///

  (defthm-unsigned-byte-p n01p-page-size
    :hyp t
    :bound 1
    :concl (page-size val)
    :gen-type t
    :gen-linear t))

(define page-read-write
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->r/w entry)

  ///

  (defthm-unsigned-byte-p n01p-page-read-write
    :hyp t
    :bound 1
    :concl (page-read-write val)
    :gen-type t
    :gen-linear t))

(define page-user-supervisor
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->u/s entry)

  ///

  (defthm-unsigned-byte-p n01p-page-user-supervisor
    :hyp t
    :bound 1
    :concl (page-user-supervisor val)
    :gen-type t
    :gen-linear t))

(define page-execute-disable
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->xd entry)

  ///

  (defthm-unsigned-byte-p n01p-page-execute-disable
    :hyp t
    :bound 1
    :concl (page-execute-disable val)
    :gen-type t
    :gen-linear t))

(define accessed-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->a entry)

  ///

  (defthm-unsigned-byte-p n01p-accessed-bit
    :hyp t
    :bound 1
    :concl (accessed-bit val)
    :gen-type t
    :gen-linear t))

(define dirty-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit))
  (ia32e-page-tablesBits->d entry)

  ///

  (defthm-unsigned-byte-p n01p-dirty-bit
    :hyp t
    :bound 1
    :concl (dirty-bit val)
    :gen-type t
    :gen-linear t))

(define set-accessed-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (a-entry (unsigned-byte-p 64 a-entry))
  (!ia32e-page-tablesBits->a 1 entry)

  ///

  (local (in-theory (e/d (!ia32e-page-tablesbits->a) ())))

  (defthm-unsigned-byte-p n64p-set-accessed-bit
    :hyp t
    :bound 64
    :concl (set-accessed-bit val)
    :gen-type t
    :gen-linear t))

(define set-dirty-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (d-entry (unsigned-byte-p 64 d-entry))
  (!ia32e-page-tablesBits->d 1 entry)

  ///

  (local (in-theory (e/d (!ia32e-page-tablesbits->d) ())))

  (defthm-unsigned-byte-p n64p-set-dirty-bit
    :hyp t
    :bound 64
    :concl (set-dirty-bit val)
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; We define inlined functions that compute the entry address for a
;; particular paging data structure, given the base address of the
;; structure and the original linear address.  We do this so that
;; during reasoning, we see these functions in checkpoints instead of
;; confusing arithmetic expressions involving logtail, loghead, etc.

(encapsulate

  ()

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthm break-logand-into-loghead-and-logtail
      (implies (and (natp x)
                    (natp y)
                    (natp n))
               (equal (logand x y)
                      (+
                       (* (expt 2 n)
                          (logand (logtail n x)
                                  (logtail n y)))
                       (logand (loghead n x)
                               (loghead n y)))))
      :hints (("Goal" :in-theory (e/d (loghead logtail ifix) ())))
      :rule-classes nil)

    (defthm logand-identity-lemma-for-base-addr
      (implies (and (syntaxp (quotep n))
                    (natp n)
                    (equal (loghead 12 base-addr) 0)
                    (unsigned-byte-p 52 base-addr)
                    (equal (logtail 12 n) (1- (ash 1 52))))
               (equal (logand n base-addr)
                      base-addr))
      :hints (("Goal" :in-theory (e/d (logtail loghead) ())
               :use ((:instance break-logand-into-loghead-and-logtail
                                (x n)
                                (y base-addr)
                                (n 12))))))

    (defthm adding-7-to-base-addr-lemma
      (implies (and (equal (loghead 3 x) 0)
                    (unsigned-byte-p 52 x))
               (unsigned-byte-p 52 (+ 7 x)))
      :hints (("Goal" :in-theory (e/d* (loghead) ())))))


  (local
   (defthm logior-base-addr-i-lemma
     (implies (and (equal (loghead 12 base-addr) 0)
                   (unsigned-byte-p 52 base-addr)
                   (unsigned-byte-p 12 i))
              (unsigned-byte-p 52 (logior base-addr i)))
     :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)
                                      (unsigned-byte-p))))))

  (local
   (defthm low-3-bits-of-logior-base-addr-i
     (implies (equal (loghead 12 base-addr) 0)
              (equal (loghead 3 (logior base-addr (ash x 3))) 0))))

  (local
   (defthm unsigned-byte-p-of-7+logior-base-addr-i
     (implies (and (equal (loghead 12 base-addr) 0)
                   (equal (loghead 3 i) 0)
                   (unsigned-byte-p 52 base-addr)
                   (unsigned-byte-p 12 i))
              (unsigned-byte-p 52 (+ 7 (logior base-addr i))))
     :hints (("Goal" :in-theory (e/d* ()
                                      (unsigned-byte-p))))))

  (defthm adding-7-to-shifted-bits
    (implies (and (equal (loghead 12 base-addr) 0)
                  (unsigned-byte-p 52 base-addr)
                  (unsigned-byte-p 9 x))
             ;; (< (+ 7 (logior base-addr (ash x 3)))
             ;;    *mem-size-in-bytes*)
             (unsigned-byte-p 52 (+ 7 (logior base-addr (ash x 3)))))
    :hints (("Goal"
             :use ((:instance unsigned-byte-p-of-7+logior-base-addr-i
                              (base-addr base-addr)
                              (i (ash x 3))))
             :in-theory (e/d ()
                             (unsigned-byte-p-of-7+logior-base-addr-i))))))



(encapsulate
  ()

  (local (include-book "centaur/bitops/signed-byte-p" :dir :system))
  (local (in-theory (e/d () (unsigned-byte-p))))

  (define page-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t
    :no-function t

    (if (mbt (and (unsigned-byte-p *physical-address-size* base-addr)
                  (equal (loghead 12 base-addr) 0)))

        (mbe :logic (part-install (part-select lin-addr :low 12 :high 20)
                                  base-addr :low 3 :high 11)
             :exec (the (unsigned-byte #.*physical-address-size*)
                     (logior (logand base-addr (lognot (ash 511 3)))
                             (ash (the (unsigned-byte 9)
                                    (logand 511
                                            (the (signed-byte 36)
                                              (ash lin-addr -12))))
                                  3))))
      0)

    ///

    (defthm natp-page-table-entry-addr
      (natp (page-table-entry-addr lin-addr base-addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm-unsigned-byte-p *physical-address-size*p-page-table-entry-addr
      :bound *physical-address-size*
      :concl (page-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-table-entry-addr))))
      :gen-linear t)

    (defthm page-table-entry-addr-is-a-multiple-of-8
      (equal (loghead 3 (page-table-entry-addr lin-addr base-addr)) 0))

    (defthm-unsigned-byte-p adding-7-to-page-table-entry-addr
      :bound *physical-address-size*
      :concl (+ 7 (page-table-entry-addr lin-addr base-addr))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-table-entry-addr))))
      :gen-linear t
      :gen-type t)

    (defthm page-table-entry-addr-equal-if-same-page
            (implies (same-page lin-addr lin-addr-2)
                     (equal (page-table-entry-addr lin-addr base-addr)
                            (page-table-entry-addr lin-addr-2 base-addr)))
            :hints (("Goal" :in-theory (enable same-page)))
            :rule-classes :congruence))

  (define page-directory-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t
    :no-function t

    (if (mbt (and (unsigned-byte-p *physical-address-size* base-addr)
                  (equal (loghead 12 base-addr) 0)))

        (mbe
         :logic
         (part-install (part-select lin-addr :low 21 :high 29)
                       base-addr
                       :low 3 :high 11)
         :exec
         (the (unsigned-byte #.*physical-address-size*)
           (logior (the (unsigned-byte #.*physical-address-size*)
                     (logand base-addr
                             (lognot 4088)))
                   (the (unsigned-byte 12)
                     (ash
                      (the (unsigned-byte 9)
                        (logand 511
                                (ash lin-addr -21)))
                      3)))))
      0)

    ///

    (defthm natp-page-directory-entry-addr
      (natp (page-directory-entry-addr lin-addr base-addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm-unsigned-byte-p *physical-address-size*p-page-directory-entry-addr
      :bound *physical-address-size*
      :concl (page-directory-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-directory-entry-addr))))
      :gen-linear t)

    (defthm page-directory-entry-addr-is-a-multiple-of-8
      (equal (loghead 3 (page-directory-entry-addr lin-addr base-addr)) 0))

    (defthm-unsigned-byte-p adding-7-to-page-directory-entry-addr
      :bound *physical-address-size*
      :concl (+ 7 (page-directory-entry-addr lin-addr base-addr))
      :gen-linear t
      :gen-type t
      :hints-l (("Goal" :in-theory (e/d () (page-directory-entry-addr)))))

    (defthm page-directory-entry-addr-equal-if-same-page
            (implies (same-page lin-addr lin-addr-2)
                     (equal (page-directory-entry-addr lin-addr base-addr)
                            (page-directory-entry-addr lin-addr-2 base-addr)))
            :rule-classes :congruence))

  (define page-dir-ptr-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t
    :no-function t

    (if (mbt (and (unsigned-byte-p *physical-address-size* base-addr)
                  (equal (loghead 12 base-addr) 0)))

        (mbe
         :logic
         (part-install (part-select lin-addr :low 30 :high 38)
                       base-addr :low 3 :high 11)
         :exec
         (the (unsigned-byte #.*physical-address-size*)
           (logior (the (unsigned-byte #.*physical-address-size*)
                     (logand base-addr (lognot (ash 511 3))))
                   (the (unsigned-byte 12)
                     (ash (the (unsigned-byte 9)
                            (logand 511 (ash lin-addr -30)))
                          3)))))

      0)

    ///

    (defthm natp-page-dir-ptr-table-entry-addr
      (natp (page-dir-ptr-table-entry-addr lin-addr base-addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm-unsigned-byte-p *physical-address-size*p-page-dir-ptr-table-entry-addr
      :bound *physical-address-size*
      :concl (page-dir-ptr-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-dir-ptr-table-entry-addr))))
      :gen-linear t)

    (defthm page-dir-ptr-table-entry-addr-is-a-multiple-of-8
      (equal (loghead 3 (page-dir-ptr-table-entry-addr lin-addr base-addr)) 0))

    (defthm-unsigned-byte-p adding-7-to-page-dir-ptr-table-entry-addr
      :bound *physical-address-size*
      :concl (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-dir-ptr-table-entry-addr))))
      :gen-linear t
      :gen-type t)

    (defthm page-dir-ptr-table-entry-addr-equal-if-same-page
            (implies (same-page lin-addr lin-addr-2)
                     (equal (page-dir-ptr-table-entry-addr lin-addr base-addr)
                            (page-dir-ptr-table-entry-addr lin-addr-2 base-addr)))
            :rule-classes :congruence))

  (define pml4-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t
    :no-function t

    (if (mbt (and (unsigned-byte-p *physical-address-size* base-addr)
                  (equal (loghead 12 base-addr) 0)))
        (mbe
         :logic
         (part-install
          (part-select lin-addr :low 39 :high 47)
          base-addr :low 3 :high 11)
         :exec
         (the
             (unsigned-byte #.*physical-address-size*)
           (logior
            (the (unsigned-byte #.*physical-address-size*)
              (logand base-addr (lognot (ash 511 3))))
            (the (unsigned-byte 12)
              (ash (the (unsigned-byte 9)
                     (logand 511 (ash lin-addr -39))) 3)))))

      0)

    ///

    (defthm natp-pml4-table-entry-addr
      (natp (pml4-table-entry-addr lin-addr base-addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm-unsigned-byte-p *physical-address-size*p-pml4-table-entry-addr
      :bound *physical-address-size*
      :concl (pml4-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (pml4-table-entry-addr))))
      :gen-linear t)

    (defthm pml4-table-entry-addr-is-a-multiple-of-8
      (equal (loghead 3 (pml4-table-entry-addr lin-addr base-addr)) 0))

    (defthm-unsigned-byte-p adding-7-to-pml4-table-entry-addr
      :bound *physical-address-size*
      :concl (+ 7 (pml4-table-entry-addr lin-addr base-addr))
      :gen-linear t
      :gen-type t
      :hints-l (("Goal" :in-theory (e/d () (pml4-table-entry-addr))))))

    (defthm pml4-table-entry-addr-equal-if-same-page
              (implies (same-page lin-addr lin-addr-2)
                       (equal (pml4-table-entry-addr lin-addr base-addr)
                              (pml4-table-entry-addr lin-addr-2 base-addr)))
              :hints (("Goal" :in-theory (enable pml4-table-entry-addr)))
              :rule-classes :congruence))

(in-theory (e/d () (adding-7-to-shifted-bits)))

;; ======================================================================

(local
 (defthm loghead-and-logsquash
   (implies (and (equal (loghead n x) 0)
                 (unsigned-byte-p m x))
            (equal (bitops::logsquash n x) x))
   :hints (("Goal"
            :in-theory (e/d* (bitops::ihsext-recursive-redefs
                              bitops::ihsext-inductions)
                             ())))))

(define paging-entry-no-page-fault-p
  ((structure-type :type (unsigned-byte 2)
                   "@('0'): Page Table;
                   @('1'): Page Directory;
                   @('2'): Page Directory Pointer Table;
                   @('3'): PML4 Table")
                   (lin-addr       :type (signed-byte   #.*max-linear-address-size*))
                   (entry          :type (unsigned-byte 64))
                   (u/s-acc        :type (unsigned-byte  1)
                                   "@('logand') of @('user-supervisor') field of all superior paging entries")
                   (r/w-acc        :type (unsigned-byte  1)
                                   "@('logand') of @('read-write') field of all superior paging entries")
                   (x/d-acc        :type (unsigned-byte  1)
                                   "@('logand') of @('execute-disable') field of all superior paging entries")
                   (wp             :type (unsigned-byte  1))
                   (smep           :type (unsigned-byte  1)
                                   "Supervisor Mode Execution Prevention")
                   (smap           :type (unsigned-byte  1)
                                   "Supervisor Mode Access Prevention")
                   (ac             :type (unsigned-byte 1)
                                   "@('AC') field from @('RFLAGS')")
                   (nxe            :type (unsigned-byte  1))
                   (r-w-x          :type (member  :r :w :x))
                   (cpl            :type (unsigned-byte  2))
                   x86
                   &optional
                   ;; TO-DO: For now, we are treating all supervisor-mode accesses as
                   ;; explicit. We need to detect and then account for implicit
                   ;; accesses later.
                   ((supervisor-mode-access-type
                      :type (unsigned-byte 1)
                      "@('0'): Explicit; @('1'): Implicit")
                    ;; Default value is 0.
                    '0))
  :short "Determining access rights and detecting page faults"
  :long "<p>Source for determining the access rights: Section 4.6 in
  the Intel Manuals, Vol. 3A.</p>

  <p>It is important to differentiate between:</p>

  <ol>
  <li>a supervisor-mode and a user-mode access</li>
  <li>an implicit and an explicit supervisor-mode access</li>
  <li>a supervisor-mode and a user-mode address</li>
  </ol>

  <p>These concepts are defined below.</p>

  <ul>

  <li>Every access to a linear address is either a <b>supervisor-mode
  access</b> or a <b>user-mode access</b>. For all instruction fetches
  and most data accesses, accesses made while CPL @('<') 3 are
  <b>supervisor-mode accesses</b>, while accesses made while CPL = 3 are
  <b>user-mode accesses</b>.</li>

  <li>Some operations implicitly access system data structures with
  linear addresses; the resulting accesses to those data structures are
  supervisor-mode accesses regardless of CPL. Examples of such accesses
  include the following: accesses to the global descriptor table \(GDT\)
  or local descriptor table \(LDT\) to load a segment descriptor;
  accesses to the interrupt descriptor table \(IDT\) when delivering an
  interrupt or exception; and accesses to the task-state segment \(TSS\)
  as part of a task switch or change of CPL. All these accesses are
  called <b>implicit supervisor-mode accesses</b> regardless of
  CPL. Other accesses made while CPL @('<') 3 are called <b>explicit
  supervisor-mode accesses</b>.</li>

  <li>If the U/S flag \(bit 2\) is 0 in at least one of the
  paging-structure entries, the address is a <b>supervisor-mode
  address</b>. Otherwise, the address is a <b>user-mode
  address</b>.</li>

  <p><i>TO-DO:</i> For now, we are treating all supervisor-mode accesses
  as explicit. We need to detect and then account for implicit
  accesses.</p>

  </ul>"

  :prepwork
  ((local (in-theory (e/d* ()
                           (signed-byte-p
                             unsigned-byte-p
                             bitops::logand-with-negated-bitmask
                             acl2::ifix-negative-to-negp
                             (:rewrite default-<-1)
                             (:rewrite default-<-2)
                             bitops::unsigned-byte-p-incr
                             weed-out-irrelevant-logand-when-first-operand-constant
                             negative-logand-to-positive-logand-with-integerp-x
                             (tau-system)))))

   (define paging-entry-no-page-fault-p-did-fault? ((u/s-all :type (unsigned-byte 1))
                       (r/w-all :type (unsigned-byte 1))
                       (x/d-all :type (unsigned-byte 1))
                       (wp      :type (unsigned-byte 1))
                       (smep    :type (unsigned-byte 1))
                       (smap    :type (unsigned-byte 1))
                       (ac      :type (unsigned-byte 1))
                       (nxe     :type (unsigned-byte 1))
                       (r-w-x   :type (member :r :w :x))
                       (cpl     :type (unsigned-byte 2))
                       (supervisor-mode-access-type :type (unsigned-byte 1)))
     :returns (fault? booleanp)
     :enabled t
     (or
       ;; Read fault:
       (and (equal r-w-x :r)
            (if (< cpl 3)
              (if (equal u/s-all 0)
                ;; Data may be read (implicitly or explicitly)
                ;; from any supervisor-mode address.
                nil
                ;; Data reads from user-mode pages
                (if (equal smap 0)
                  ;; If CR4.SMAP = 0, data may be read from
                  ;; any user-mode address.
                  nil
                  ;; If CR4.SMAP = 1: If EFLAGS.AC = 1 and the
                  ;; access is explicit, data may be read from any
                  ;; user-mode address. If EFLAGS.AC = 0 or the
                  ;; access is implicit, data may not be read from
                  ;; any user-mode address.
                  (or (equal supervisor-mode-access-type 1)
                      (equal ac 0))))
              ;; In user mode (CPL = 3), data may be read from
              ;; any linear address with a valid translation
              ;; for which the U/S flag (bit 2) is 1 in every
              ;; paging-structure entry controlling the trans-
              ;; lation.
              (equal u/s-all 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
            (if (< cpl 3)
              (if (equal u/s-all 0)
                ;; Data writes to supervisor-mode addresses.

                ;; If CR0.WP = 0, data may be written to
                ;; any supervisor-mode address.  If CR0.WP
                ;; = 1, data may be written to any
                ;; supervisor-mode address with a
                ;; translation for which the R/W flag (bit
                ;; 1) is 1 in every paging-structure entry
                ;; controlling the translation.
                (and (equal wp 1)
                     (equal r/w-all 0))

                ;; Data writes to user-mode addresses.

                (if (equal wp 0)
                  ;; If CR4.SMAP = 0, data may be written to
                  ;; any user-mode address.  If CR4.SMAP = 1:
                  ;; If EFLAGS.AC = 1 and the access is
                  ;; explicit, data may be written to any
                  ;; user-mode address. If EFLAGS.AC = 0 or
                  ;; the access is implicit, data may not be
                  ;; written to any user-mode address.
                  (if (equal smap 0)
                    nil
                    (or (equal supervisor-mode-access-type 1)
                        (equal ac 0)))

                  ;; If CR4.SMAP = 0, data may be written to
                  ;; any user-mode address with a translation
                  ;; for which the R/W flag is 1 in every
                  ;; paging-structure entry controlling the
                  ;; translation.
                  (if (equal smap 0)
                    (equal r/w-all 0)
                    ;; If CR4.SMAP = 1: If EFLAGS.AC = 1 and
                    ;; the access is explicit, data may be
                    ;; written to any user-mode address with a
                    ;; translation for which the R/W flag is 1
                    ;; in every paging-structure entry
                    ;; controlling the translation. If
                    ;; EFLAGS.AC = 0 or the access is implicit,
                    ;; data may not be written to any user-mode
                    ;; address.
                    (if (and (equal supervisor-mode-access-type 0)
                             (equal ac 1))
                      (equal r/w-all 0)
                      t))))
              ;; In user mode (CPL = 3), data may be written
              ;; to any linear address with a valid
              ;; translation for which both the R/W flag and
              ;; the U/S flag are 1 in every paging-structure
              ;; entry controlling the translation.
              (or (equal u/s-all 0)
                  (equal r/w-all 0))))
       ;; Instruction fetch fault:
       (and (equal r-w-x :x)
            (if (< cpl 3)

              (if (equal u/s-all 0)
                ;; Instruction fetches from supervisor-mode addresses.

                ;; If IA32_EFER.NXE = 0, instructions may be
                ;; fetched from any supervisor-mode
                ;; address. If IA32_EFER.NXE = 1,
                ;; instructions may be fetched from any
                ;; supervisor-mode address with a translation
                ;; for which the XD flag (bit 63) is 0 in
                ;; every paging-structure entry controlling
                ;; the translation.
                (if (equal nxe 0)
                  nil
                  (equal x/d-all 1))

                ;; Instruction fetches from user-mode addresses.

                (if (equal smep 0)
                  ;; If CR4.SMEP = 0, if IA32_EFER.NXE =
                  ;; 0, instructions may be fetched from
                  ;; any user-mode address, and if
                  ;; IA32_EFER.NXE = 1, instructions may
                  ;; be fetched from any user-mode address
                  ;; with a translation for which the XD
                  ;; flag is 0 in every paging-structure
                  ;; entry controlling the translation.
                  (if (equal nxe 0)
                    nil
                    (equal x/d-all 1))
                  ;; If CR4.SMEP = 1, instructions may not
                  ;; be fetched from any user-mode address.
                  t))

              ;; In user mode (CPL = 3): If IA32_EFER.NXE = 0,
              ;; instructions may be fetched from any linear
              ;; address with a valid translation for which
              ;; the U/S flag is 1 in every paging-structure
              ;; entry controlling the translation.  If
              ;; IA32_EFER.NXE = 1, instructions may be
              ;; fetched from any linear address with a valid
              ;; translation for which the U/S flag is 1 and
              ;; the XD flag is 0 in every paging-structure
              ;; entry controlling the translation.
              (or (equal u/s-all 0)
                  (and (equal nxe 1)
                       (equal x/d-all 1))))))))

  :guard (not (app-view x86))
  :returns (mv flg val (x86 x86p :hyp (x86p x86)
                            :hints (("Goal" :in-theory (e/d () (x86p))))))

  (b* ((entry (mbe :logic (loghead 64 entry)
                   :exec entry))
       (page-present (mbe :logic (page-present entry)
                          :exec (ia32e-page-tablesBits->p entry)))
       ((when (equal page-present 0))
        ;; Page not present fault:
        (let ((err-no (page-fault-err-no
                        page-present r-w-x cpl
                        0      ;; rsvd
                        smep 1 ;; pae
                        nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ;; From this point onwards, we know that the page is present.

       ;; We now extract the rest of the relevant bit fields from the
       ;; entry.  Note that we ignore those fields having to do with
       ;; the cache or TLB, since we are not modeling caches yet.
       (read-write      (mbe :logic (page-read-write entry)
                             :exec (ia32e-page-tablesBits->r/w entry)))
       (r/w-all         (the (unsigned-byte 1) (logand read-write r/w-acc)))
       (user-supervisor (mbe :logic (page-user-supervisor entry)
                             :exec (ia32e-page-tablesBits->u/s entry)))
       (u/s-all         (the (unsigned-byte 1) (logand user-supervisor u/s-acc)))
       (execute-disable (mbe :logic (page-execute-disable entry)
                             :exec (ia32e-page-tablesBits->xd  entry)))
       (x/d-all         (the (unsigned-byte 1) (logand execute-disable x/d-acc)))

       (page-size       (mbe :logic (page-size entry)
                             :exec (ia32e-page-tablesBits->ps  entry)))

       (rsvd
         (mbe :logic (if (or (and (equal structure-type 3)
                                  ;; Page size should be zero for the PML4 Table.
                                  (equal page-size 1))
                             (and
                               ;; Page size doesn't exist for the Page Table.
                               (not (equal structure-type 0))
                               (not (equal structure-type 3))
                               (equal page-size 1)
                               (if (equal structure-type 1)
                                 ;; Page Directory
                                 (not (equal (part-select entry :low 13 :high 20) 0))
                                 ;; Page Directory Pointer Table
                                 (not (equal (part-select entry :low 13 :high 29) 0))))
                             (and (equal nxe 0)
                                  (not (equal execute-disable 0))))
                       1
                       0)
              :exec  (if (or (and (equal structure-type 3)
                                  (equal page-size 1))
                             (and (not (equal structure-type 0))
                                  (not (equal structure-type 3))
                                  (equal page-size 1)
                                  (if (equal structure-type 1)
                                    (not (equal (the (unsigned-byte 8)
                                                     (logand 255
                                                             (the (unsigned-byte 51)
                                                                  (ash entry (- 13)))))
                                                0))
                                    (not (equal (the (unsigned-byte 17)
                                                     (logand #x1ffff
                                                             (the (unsigned-byte 51)
                                                                  (ash entry (- 13)))))
                                                0))))
                             (and (equal nxe 0)
                                  (not (equal (ia32e-page-tablesBits->xd entry) 0))))
                       1
                       0)))
       ((when (equal rsvd 1))
        ;; Reserved bits fault.
        (let ((err-no (page-fault-err-no
                        page-present r-w-x cpl rsvd smep
                        1 ;; pae
                        nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ((when (paging-entry-no-page-fault-p-did-fault? u/s-all r/w-all x/d-all wp smep smap
                                                       ac nxe r-w-x cpl supervisor-mode-access-type))
        (let ((err-no (page-fault-err-no
                        page-present r-w-x cpl rsvd smep
                        1 ;; pae
                        nxe)))
          (page-fault-exception lin-addr err-no x86))))
      (mv nil 0 x86))

  ///

  (local (in-theory (e/d (page-fault-exception) ())))

  (defthm mv-nth-1-paging-entry-no-page-fault-p-value
          (equal (mv-nth 1
                         (paging-entry-no-page-fault-p
                           structure-type lin-addr entry
                           u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x cpl x86
                           ignored))
                 0))

  (defthm xr-paging-entry-no-page-fault-p
          (implies (not (equal fld :fault))
                   (equal (xr fld index
                              (mv-nth 2
                                      (paging-entry-no-page-fault-p
                                        structure-type lin-addr entry
                                        u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86
                                        ignored)))
                          (xr fld index x86))))

  (defthm rm-low-64-paging-entry-no-page-fault-p
          (equal (rm-low-64 addr (mv-nth 2 (paging-entry-no-page-fault-p
                                             structure-type lin-addr entry
                                             u/s-acc r/w-acc x/d-acc
                                             wp smep smap ac nxe r-w-x cpl x86
                                             ignored)))
                 (rm-low-64 addr x86)))

  (defthm paging-entry-no-page-fault-p-xw-values
          (and (equal (mv-nth 0
                              (paging-entry-no-page-fault-p
                                structure-type lin-addr entry
                                u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl
                                (xw fld index value x86)
                                ignored))
                      (mv-nth 0
                              (paging-entry-no-page-fault-p
                                structure-type lin-addr entry
                                u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl x86
                                ignored)))
               (equal (mv-nth 1
                              (paging-entry-no-page-fault-p
                                structure-type lin-addr entry
                                u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl
                                (xw fld index value x86)
                                ignored))
                      (mv-nth 1
                              (paging-entry-no-page-fault-p
                                structure-type lin-addr entry
                                u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl x86
                                ignored)))))

  (defthm paging-entry-no-page-fault-p-xw-state
          (implies (not (equal fld :fault))
                   (equal (mv-nth 2
                                  (paging-entry-no-page-fault-p
                                    structure-type lin-addr entry
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (xw fld index value x86)
                                    ignored))
                          (xw fld index value
                              (mv-nth 2
                                      (paging-entry-no-page-fault-p
                                        structure-type lin-addr entry
                                        u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86
                                        ignored))))))

  (defthm mv-nth-2-paging-entry-no-page-fault-p-does-not-modify-x86-if-no-fault
          (implies (not (mv-nth 0 (paging-entry-no-page-fault-p
                                    structure-type lin-addr
                                    entry u/s-acc r/w-acc x/d-acc wp
                                    smep smap ac nxe r-w-x cpl x86 ignored)))
                   (equal (mv-nth
                            2
                            (paging-entry-no-page-fault-p
                              structure-type lin-addr
                              entry u/s-acc r/w-acc x/d-acc wp
                              smep smap ac nxe r-w-x cpl x86 ignored))
                          x86))
          :hints (("Goal" :in-theory (e/d (page-fault-exception)
                                          ()))))

  (define find-similar-paging-entries-from-page-present-equality-aux
    ((index natp) entry-var calls)
    (if (atom calls)
      nil
      (b* ((one-call (car calls))
           ((unless (and (true-listp one-call)
                         (true-listp (nth index one-call))
                         (equal (len (nth index one-call)) 2)))
            nil))
          (cons (list (cons entry-var    (nth 1 (nth index one-call))))
                (find-similar-paging-entries-from-page-present-equality-aux
                  index entry-var (cdr calls))))))

  (defun find-similar-paging-entries-from-page-present-equality
    (bound-entry-val entry-var mfc state)
    (declare (xargs :stobjs (state) :mode :program)
             (ignorable state))
    (b* (((mv index calls)
          (mv
            2
            (acl2::find-matches-list
              `(equal (page-present ,bound-entry-val) (page-present e))
              (acl2::mfc-clause mfc)
              nil)))
         ((mv index calls)
          (if (not calls)
            (mv 1
                (acl2::find-matches-list
                  `(equal (page-present e) (page-present ,bound-entry-val))
                  (acl2::mfc-clause mfc)
                  nil))
            (mv index calls)))
         ((when (not calls))
          ;; equality of page-present term not encountered.
          nil))
        (find-similar-paging-entries-from-page-present-equality-aux index entry-var calls)))

  (defthm mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
          (implies (and
                     (bind-free (find-similar-paging-entries-from-page-present-equality
                                  entry-1 'entry-2 mfc state)
                                (entry-2))
                     (syntaxp (not (eq entry-1 entry-2)))
                     (equal (page-present entry-1)
                            (page-present entry-2))
                     (equal (page-read-write entry-1)
                            (page-read-write entry-2))
                     (equal (page-user-supervisor entry-1)
                            (page-user-supervisor entry-2))
                     (equal (page-execute-disable entry-1)
                            (page-execute-disable entry-2))
                     (equal (page-size entry-1)
                            (page-size entry-2))
                     (if (equal structure-type 1)
                       ;; For Page Directory
                       (equal (part-select entry-1 :low 13 :high 20)
                              (part-select entry-2 :low 13 :high 20))
                       ;; For Page Directory Pointer Table
                       (if (equal structure-type 2)
                         (equal (part-select entry-1 :low 13 :high 29)
                                (part-select entry-2 :low 13 :high 29))
                         t))
                     (unsigned-byte-p 2 structure-type)
                     (unsigned-byte-p 64 entry-1)
                     (unsigned-byte-p 64 entry-2))
                   (equal (mv-nth 0
                                  (paging-entry-no-page-fault-p
                                    structure-type lin-addr entry-1
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    x86 ignored))
                          (mv-nth 0
                                  (paging-entry-no-page-fault-p
                                    structure-type lin-addr entry-2
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    x86 ignored))))
          :hints (("Goal"
                   :do-not-induct t
                   :in-theory (e/d* (page-fault-exception)
                                    (bitops::logand-with-negated-bitmask
                                      (:meta acl2::mv-nth-cons-meta)
                                      force (force))))))

  (defthm mv-nth-0-paging-entry-no-page-fault-p-is-independent-of-lin-addr
          (implies
            (not
              (mv-nth
                0
                (paging-entry-no-page-fault-p structure-type
                                              lin-addr entry u/s-acc r/w-acc
                                              x/d-acc wp smep smap ac nxe r-w-x
                                              cpl x86 supervisor-mode-access-type)))
            (equal
              (mv-nth
                0
                (paging-entry-no-page-fault-p structure-type (+ n lin-addr)
                                              entry u/s-acc r/w-acc
                                              x/d-acc wp smep smap ac nxe r-w-x
                                              cpl x86 supervisor-mode-access-type))
              nil))
          :hints (("Goal" :in-theory (e/d* ()
                                           (commutativity-of-+
                                             not
                                             bitops::logand-with-negated-bitmask)))))

  (defrule 64-bit-modep-of-paging-entry-no-page-fault-p
           (equal (64-bit-modep (mv-nth 2 (paging-entry-no-page-fault-p
                                            structure-type lin-addr entry
                                            u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86)))

  (defrule x86-operation-mode-of-paging-entry-no-page-fault-p
           (equal (x86-operation-mode (mv-nth 2 (paging-entry-no-page-fault-p
                                                  structure-type lin-addr entry
                                                  u/s-acc r/w-acc x/d-acc
                                                  wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode)

  (defthm paging-entry-no-page-fault-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                      structure-type lin-addr entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (paging-entry-no-page-fault-p
                                      structure-type lin-addr-2 entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :rule-classes :congruence)

  (defthm paging-entry-no-page-fault-val-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                      structure-type lin-addr entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 1 (paging-entry-no-page-fault-p
                                      structure-type lin-addr-2 entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :rule-classes :congruence)

  (defthm paging-entry-no-page-fault-p-invariant-under-paging-entry-no-page-fault-p
           (and (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                   structure-type lin-addr entry
                                   u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl
                                   (mv-nth 2 (paging-entry-no-page-fault-p
                                               structure-type2 lin-addr2 entry2
                                               u/s-acc2 r/w-acc2 x/d-acc2
                                               wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                               x86))))
                       (mv-nth 0 (paging-entry-no-page-fault-p
                                   structure-type lin-addr entry
                                   u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl x86)))
                (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                   structure-type lin-addr entry
                                   u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl
                                   (mv-nth 2 (paging-entry-no-page-fault-p
                                               structure-type2 lin-addr2 entry2
                                               u/s-acc2 r/w-acc2 x/d-acc2
                                               wp2 smep2 smap2 ac2 nxe2 r-w-x2 cpl2
                                               x86))))
                       (mv-nth 1 (paging-entry-no-page-fault-p
                                   structure-type lin-addr entry
                                   u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl x86))))
           :hints (("Goal" :in-theory (disable paging-entry-no-page-fault-p-did-fault?))))

  (defthm paging-entry-no-page-fault-p-invariant-under-setting-dirty-bit
          (and (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                  structure-type lin-addr (set-dirty-bit entry)
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))
                      (mv-nth 0 (paging-entry-no-page-fault-p
                                  structure-type lin-addr entry
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86)))
               (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                  structure-type lin-addr (set-dirty-bit entry)
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))
                      (mv-nth 1 (paging-entry-no-page-fault-p
                                  structure-type lin-addr entry
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (e/d (ia32e-page-tablesbits-fix !ia32e-page-tablesbits->d
                                           ia32e-page-tablesbits->u/s ia32e-page-tablesbits->r/w
                                           ia32e-page-tablesbits->xd ia32e-page-tablesbits->p
                                           ia32e-page-tablesbits->ps)
                                          (paging-entry-no-page-fault-p-did-fault?)))))

  (defthm paging-entry-no-page-fault-p-invariant-under-setting-accessed-bit
          (and (equal (mv-nth 0 (paging-entry-no-page-fault-p
                                  structure-type lin-addr (set-accessed-bit entry)
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))
                      (mv-nth 0 (paging-entry-no-page-fault-p
                                  structure-type lin-addr entry
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86)))
               (equal (mv-nth 1 (paging-entry-no-page-fault-p
                                  structure-type lin-addr (set-accessed-bit entry)
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))
                      (mv-nth 1 (paging-entry-no-page-fault-p
                                  structure-type lin-addr entry
                                  u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (e/d (ia32e-page-tablesbits-fix !ia32e-page-tablesbits->a
                                           ia32e-page-tablesbits->u/s ia32e-page-tablesbits->r/w
                                           ia32e-page-tablesbits->xd ia32e-page-tablesbits->p
                                           ia32e-page-tablesbits->ps)
                                          (paging-entry-no-page-fault-p-did-fault?))))))

;; ======================================================================

(defconst *paging-levels* '(page-table page-directory page-dir-ptr-table pml4-table))

(define ia32e-la-to-pa-page-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (u/s-acc   :type (unsigned-byte  1))
   (r/w-acc   :type (unsigned-byte  1))
   (x/d-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (smap      :type (unsigned-byte  1))
   (ac        :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d (ia32e-pte-4K-pageBits->page)
                                        (unsigned-byte-p
                                          signed-byte-p
                                          member-equal
                                          not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (app-view x86)))

    (b* (;; Fix the inputs of this function without incurring execution
         ;; overhead.
         (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (base-addr (mbe :logic (part-install
                                  0
                                  (loghead *physical-address-size* base-addr)
                                  :low 0 :width 12)
                         :exec base-addr))

         ;; First, we get the PTE (page table entry) address. A PTE is
         ;; selected using the physical address defined as follows:
         ;;     Bits 51:12 are from the PDE (base-addr here).
         ;;     Bits 11:3 are bits 20:12 of the linear address.
         ;;     Bits 2:0 are all 0.

         (p-entry-addr
           (the (unsigned-byte #.*physical-address-size*)
                (page-table-entry-addr lin-addr base-addr)))

         ;;  [Shilpi]: Removed nested paging specification at this
         ;;  point.

         ;; Now we can read the PTE.
         (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

         ((mv fault-flg val x86)
          (paging-entry-no-page-fault-p
            0 ;; structure-type
            lin-addr entry
            u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86))

         ;; Regardless of whether the above page faulted, if the entry was present,
         ;; we must set the accessed bit
         (marking-view? (marking-view x86))
         ((mv updated? updated-entry)
          (if (and marking-view?
                   (equal (mbe :logic (page-present entry)
                               :exec (ia32e-page-tablesBits->p entry))
                          1))
            (b* ((accessed (mbe :logic (accessed-bit entry)
                                :exec (ia32e-page-tablesBits->a entry))))
                (if (equal accessed 0)
                  (mv t
                      (mbe :logic (set-accessed-bit entry)
                           :exec (!ia32e-page-tablesBits->a 1 entry)))
                  (mv nil entry)))
            (mv nil entry)))

         ((when fault-flg)
          ;; If we updated the entry, we must write it before returning
          (b* ((x86 (if updated?
                      (wm-low-64 p-entry-addr updated-entry x86)
                      x86)))
              (mv 'Page-Fault val x86)))

         ;; No errors, so we proceed with the address translation.

         ((mv updated? updated-entry)
          (if marking-view?
            ;; Mark D bit
            (b* ((dirty (mbe :logic (dirty-bit entry)
                             :exec (ia32e-page-tablesBits->d entry))))
                (if (and (equal dirty 0)
                         (equal r-w-x :w))
                  (mv t (mbe :logic (set-dirty-bit updated-entry)
                             :exec (!ia32e-page-tablesBits->d 1 updated-entry)))
                  (mv updated? updated-entry)))
            (mv nil updated-entry)))

        ;; If we set one or both of the accessed and dirty bits, update the state
        (x86 (if updated?
               (wm-low-64 p-entry-addr updated-entry x86)
               x86)))

        ;; Return physical address and the modified x86 state.  Note that the
        ;; base address of the 4K frame would be just
        ;; (ash (ia32e-pte-4K-pageBits->page entry) 12).
        (mv nil

            (mbe

              :logic
              (part-install
                (part-select lin-addr :low 0 :high 11)
                (ash (ia32e-pte-4K-pageBits->page entry) 12)
                :low 0 :high 11)


              :exec
              (the (unsigned-byte #.*physical-address-size*)
                   (logior
                     (the (unsigned-byte #.*physical-address-size*)
                          (logand
                            (the (unsigned-byte #.*physical-address-size*)
                                 (ash
                                   (the (unsigned-byte 40)
                                        (ia32e-pte-4K-pageBits->page entry))
                                   12))
                            -4096))
                     (the (unsigned-byte 12)
                          (logand 4095 lin-addr)))))
            x86))

    (mv t 0 x86))


  ///

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-page-table
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1
                                         (ia32e-la-to-pa-page-table
                                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                           wp smep smap ac nxe r-w-x cpl x86))

                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
                          :gen-type t)

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-table
          (implies (x86p x86)
                   (x86p
                     (mv-nth 2
                             (ia32e-la-to-pa-page-table
                               lin-addr base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-page-table
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86))))

  (defthm xr-fault-ia32e-la-to-pa-page-table
          (implies (not (mv-nth 0
                                (ia32e-la-to-pa-page-table
                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86)))
                   (equal (xr :fault index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-ia32e-la-to-pa-page-table-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-page-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (negative-logand-to-positive-logand-with-integerp-x
                                             bitops::logand-with-negated-bitmask)))))

  (defthm ia32e-la-to-pa-page-table-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-page-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-page-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-page-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-page-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86))))))

  (defthm ia32e-la-to-pa-page-table-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-page-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl
                                        x86))))))

  (defthm mv-nth-2-ia32e-la-to-pa-page-table-system-level-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (mv-nth 0 (ia32e-la-to-pa-page-table
                                         lin-addr
                                         base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl x86))))
                   (equal (mv-nth
                            2
                            (ia32e-la-to-pa-page-table
                              lin-addr
                              base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86))
                          x86)))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-page-table
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-page-table
                                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86))
           :enable (wm-low-32 wm-low-64))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-page-table
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-page-table
                                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                                  wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-page-table)

  (defthm ia32e-la-to-pa-page-table-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-page-table
                                    lin-addr entry
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-page-table
                                                 lin-addr entry
                                                 u/s-acc r/w-acc x/d-acc
                                                 wp smep smap ac nxe r-w-x cpl x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-page-table-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-page-table
                                      lin-addr entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (ia32e-la-to-pa-page-table
                                      lin-addr-2 entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-page-table-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-page-table
                                          lin-addr entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))
                              (mv-nth 1 (ia32e-la-to-pa-page-table
                                          lin-addr-2 entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))
          :rule-classes :congruence))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa-page-directory
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (u/s-acc   :type (unsigned-byte  1))
   (r/w-acc   :type (unsigned-byte  1))
   (x/d-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (smap      :type (unsigned-byte  1))
   (ac        :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d (!ia32e-page-tablesbits->a
                                          !ia32e-pde-2mb-pagebits->a
                                          !ia32e-pde-2mb-pagebits->d
                                          !ia32e-page-tablesbits->d
                                          ia32e-page-tablesbits->d
                                          ia32e-pde-2mb-pagebits->d
                                          ia32e-page-tablesbits->a
                                          ia32e-pde-2mb-pagebits->a)
                                        (unsigned-byte-p
                                          signed-byte-p
                                          member-equal
                                          not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (app-view x86)))

    (b* (
         ;; Fix the inputs of this function without incurring execution
         ;; overhead.
         (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (base-addr (mbe :logic (part-install
                                  0
                                  (loghead *physical-address-size* base-addr)
                                  :low 0 :width 12)
                         :exec base-addr))
         ;; First, we get the PDE (page directory entry) address. A PDE
         ;; is selected using the physical address defined as follows:
         ;;     Bits 51:12 are from the PDPTE (base-addr here).
         ;;     Bits 11:3 are bits 29:21 of the linear address.
         ;;     Bits 2:0 are all 0.

         (p-entry-addr
           (the (unsigned-byte #.*physical-address-size*)
                (page-directory-entry-addr lin-addr base-addr)))

         ;;  [Shilpi]: Removed nested paging specification at this
         ;;  point.

         ;; Now we can read the PTE.
         (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

         (u/s-all
           (mbe :logic (logand u/s-acc (page-user-supervisor entry))
                :exec (the (unsigned-byte 1)
                           (logand u/s-acc (ia32e-page-tablesBits->u/s entry)))))
         (r/w-all
           (mbe :logic (logand r/w-acc (page-read-write entry))
                :exec (the (unsigned-byte 1)
                           (logand r/w-acc (ia32e-page-tablesBits->r/w entry)))))
         (x/d-all
           (mbe :logic (logand x/d-acc (page-execute-disable entry))
                :exec (the (unsigned-byte 1)
                           (logand x/d-acc (ia32e-page-tablesBits->xd entry)))))

         ((mv fault-flg val x86)
          (paging-entry-no-page-fault-p
            1 ;; structure-type
            lin-addr entry
            u/s-all r/w-all x/d-all
            wp smep smap ac nxe r-w-x cpl x86))

         ;; Regardless of whether the above page faulted, if the entry was present,
         ;; we must set the accessed bit
         (marking-view? (marking-view x86))
         ((mv updated? updated-entry)
          (if (and marking-view?
                   (equal (mbe :logic (page-present entry)
                               :exec (ia32e-page-tablesBits->p entry))
                          1))
            (b* ((accessed (mbe :logic (accessed-bit entry)
                                :exec (ia32e-page-tablesBits->a entry))))
                (if (equal accessed 0)
                  (mv t
                      (mbe :logic (set-accessed-bit entry)
                           :exec (!ia32e-page-tablesBits->a 1 entry)))
                  (mv nil entry)))
            (mv nil entry)))

         ((when fault-flg)
          ;; If we updated the entry, we must write it before returning
          (b* ((x86 (if updated?
                      (wm-low-64 p-entry-addr updated-entry x86)
                      x86)))
              (mv 'Page-Fault val x86))))

        ;; No errors at this level, so we proceed with the translation:

        (if (mbe :logic (equal (page-size entry) 1)
                 :exec (equal (ia32e-page-tablesBits->ps entry) 1))
          ;; 2MB page

          (b* (((mv updated? updated-entry)
                (if marking-view?
                  ;; Mark D bit
                  (b* ((dirty (mbe :logic (dirty-bit entry)
                                   :exec (ia32e-page-tablesBits->d entry))))
                      (if (and (equal dirty 0)
                               (equal r-w-x :w))
                        (mv t (mbe :logic (set-dirty-bit updated-entry)
                                   :exec (!ia32e-page-tablesBits->d 1 updated-entry)))
                        (mv updated? updated-entry)))
                  (mv nil entry)))

               ;; If we set one or both of the accessed and dirty bits, update the state
               (x86 (if updated?
                      (wm-low-64 p-entry-addr updated-entry x86)
                      x86)))
            ;; Return address of 2MB page frame and the modified x86 state.
            (mv nil
                (mbe
                  :logic
                  (part-install
                    (part-select lin-addr :low 0 :high 20)
                    (ash (ia32e-pde-2MB-pageBits->page entry) 21)
                    :low 0 :high 20)
                  :exec
                  (the
                    (unsigned-byte 52)
                    (logior
                      (the
                        (unsigned-byte 52)
                        (logand (the
                                  (unsigned-byte 52)
                                  (ash (the (unsigned-byte 31)
                                            (ia32e-pde-2mb-pageBits->page entry))
                                       21))
                                (lognot (1- (ash 1 21)))))
                      (the
                        (unsigned-byte 21)
                        (logand (1- (ash 1 21)) lin-addr)))))
                x86))
          ;; Go to the next level of page table structure (PT, which
          ;; references a 4KB page)
          (b* ((page-table-base-addr
                 (ash (ia32e-pde-pg-tableBits->pt entry) 12))
               ((mv flag
                    (the (unsigned-byte #.*physical-address-size*) p-addr)
                    x86)
                (ia32e-la-to-pa-page-table
                  lin-addr page-table-base-addr
                  u/s-all r/w-all x/d-all
                  wp smep smap ac nxe r-w-x cpl
                  x86))
               ;; If we updated the entry, we must write it before returning
               ;; We reread the entry because it is possible a lower level set the dirty bit on it
               ;; This requires us to set the accessed bit again
               (entry (rm-low-64 p-entry-addr x86))
               (x86 (if marking-view?
                      (b* ((accessed (mbe :logic (accessed-bit entry)
                                          :exec (ia32e-page-tablesBits->a entry)))
                           ((unless (equal accessed 0)) x86))
                          (wm-low-64 p-entry-addr (set-accessed-bit entry) x86))
                      x86))
               ((when flag) (mv flag 0 x86)))
              (mv nil p-addr x86))))

    (mv t 0 x86))

  ///

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-page-directory
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1
                                         (ia32e-la-to-pa-page-directory
                                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                           wp smep smap ac nxe r-w-x cpl
                                           x86))

                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-directory
          (implies (x86p x86)
                   (x86p
                     (mv-nth 2
                             (ia32e-la-to-pa-page-directory
                               lin-addr base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-page-directory
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-directory
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl
                                        x86)))
                          (xr fld index x86))))

  (defthm xr-fault-ia32e-la-to-pa-page-directory
          (implies (not (mv-nth 0
                                (ia32e-la-to-pa-page-directory
                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86)))
                   (equal (xr :fault index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-directory
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-page-directory-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-page-directory
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (negative-logand-to-positive-logand-with-integerp-x
                                             bitops::logand-with-negated-bitmask)))))

  (defthm ia32e-la-to-pa-page-directory-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-page-directory
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-page-directory
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-page-directory
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-page-directory
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86))))))

  (defthm ia32e-la-to-pa-page-directory-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-page-directory
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-directory
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl
                                        x86))))))

  (defthm mv-nth-2-ia32e-la-to-pa-page-directory-system-level-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (mv-nth 0 (ia32e-la-to-pa-page-directory
                                         lin-addr
                                         base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl x86))))
                   (equal (mv-nth
                            2
                            (ia32e-la-to-pa-page-directory
                              lin-addr
                              base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86))
                          x86)))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-page-directory
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-page-directory
                                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86))
           :enable (wm-low-32 wm-low-64))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-page-directory
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-page-directory
                                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                                  wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-page-directory)

  (defthm ia32e-la-to-pa-page-directory-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-page-directory
                                    lin-addr entry
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-page-directory
                                                 lin-addr entry
                                                 u/s-acc r/w-acc x/d-acc
                                                 wp smep smap ac nxe r-w-x cpl x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-page-directory-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-page-directory
                                      lin-addr entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (ia32e-la-to-pa-page-directory
                                      lin-addr-2 entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-page-directory-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-page-directory
                                          lin-addr entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))
                              (mv-nth 1 (ia32e-la-to-pa-page-directory
                                          lin-addr-2 entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa-page-dir-ptr-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (u/s-acc   :type (unsigned-byte  1))
   (r/w-acc   :type (unsigned-byte  1))
   (x/d-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (smap      :type (unsigned-byte  1))
   (ac        :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))

  :guard-hints (("Goal" :in-theory (e/d (!ia32e-page-tablesbits->a
                                          !ia32e-pde-2mb-pagebits->a
                                          !ia32e-pdpte-1gb-pagebits->a
                                          !ia32e-pde-2mb-pagebits->d
                                          !ia32e-page-tablesbits->d
                                          !ia32e-pdpte-1gb-pagebits->d
                                          ia32e-pdpte-1gb-pagebits->d
                                          ia32e-page-tablesbits->d
                                          ia32e-pde-2mb-pagebits->d
                                          ia32e-page-tablesbits->a
                                          ia32e-pde-2mb-pagebits->a
                                          ia32e-pdpte-1gb-pagebits->a)
                                        (unsigned-byte-p
                                          signed-byte-p
                                          member-equal
                                          not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (app-view x86)))

    (b* (
         ;; Fix the inputs of this function without incurring execution
         ;; overhead.
         (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (base-addr (mbe :logic (part-install
                                  0
                                  (loghead *physical-address-size* base-addr)
                                  :low 0 :width 12)
                         :exec base-addr))

         ;; First, we get the PDPTE (page directory pointer table entry)
         ;; address.  A PDPTE is selected using the physical address
         ;; defined as follows:
         ;;   Bits 51:12 are from the PML4E.
         ;;   Bits 11:3 are bits 38:30 of the linear address.
         ;;   Bits 2:0 are all 0.

         (p-entry-addr
           (the (unsigned-byte #.*physical-address-size*)
                (page-dir-ptr-table-entry-addr lin-addr base-addr)))

         ;;  [Shilpi]: Removed nested paging specification at this
         ;;  point.

         ;; Now we can read the PDPTE.
         (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

         (u/s-all
           (mbe :logic (logand u/s-acc (page-user-supervisor entry))
                :exec (the (unsigned-byte 1)
                           (logand u/s-acc (ia32e-page-tablesBits->u/s entry)))))
         (r/w-all
           (mbe :logic (logand r/w-acc (page-read-write entry))
                :exec (the (unsigned-byte 1)
                           (logand r/w-acc (ia32e-page-tablesBits->r/w entry)))))
         (x/d-all
           (mbe :logic (logand x/d-acc (page-execute-disable entry))
                :exec (the (unsigned-byte 1)
                           (logand x/d-acc (ia32e-page-tablesBits->xd entry)))))

         ((mv fault-flg val x86)
          (paging-entry-no-page-fault-p
            2 ;; structure-type
            lin-addr entry
            u/s-all r/w-all x/d-all
            wp smep smap ac nxe r-w-x cpl x86))

         ;; Regardless of whether the above page faulted, if the entry was present,
         ;; we must set the accessed bit
         (marking-view? (marking-view x86))
         ((mv updated? updated-entry)
          (if (and marking-view?
                   (equal (mbe :logic (page-present entry)
                               :exec (ia32e-page-tablesBits->p entry))
                          1))
            (b* ((accessed (mbe :logic (accessed-bit entry)
                                :exec (ia32e-page-tablesBits->a entry))))
                (if (equal accessed 0)
                  (mv t
                      (mbe :logic (set-accessed-bit entry)
                           :exec (!ia32e-page-tablesBits->a 1 entry)))
                  (mv nil entry)))
            (mv nil entry)))

         ((when fault-flg)
          ;; If we updated the entry, we must write it before returning
          (b* ((x86 (if updated?
                      (wm-low-64 p-entry-addr updated-entry x86)
                      x86)))
              (mv 'Page-Fault val x86))))

        ;; No errors at this level, so we proceed with the translation.

        (if (mbe :logic (equal (page-size entry) 1)
                 :exec (equal (ia32e-page-tablesBits->ps entry) 1))

          (b* (((mv updated? updated-entry)
                (if marking-view?
                  ;; Mark D bit
                  (b* ((dirty (mbe :logic (dirty-bit entry)
                                   :exec (ia32e-page-tablesBits->d entry))))
                      (if (and (equal dirty 0)
                               (equal r-w-x :w))
                        (mv t (mbe :logic (set-dirty-bit updated-entry)
                                   :exec (!ia32e-page-tablesBits->d 1 updated-entry)))
                        (mv updated? updated-entry)))
                  (mv nil entry)))

               ;; If we set one or both of the accessed and dirty bits, update the state
               (x86 (if updated?
                      (wm-low-64 p-entry-addr updated-entry x86)
                      x86)))
            ;;  Return address of 1GB page frame and the modified x86 state.
            (mv nil
                (mbe
                  :logic
                  (part-install
                    (part-select lin-addr :low 0 :high 29)
                    (ash (ia32e-pdpte-1GB-pageBits->page entry) 30)
                    :low 0 :high 29)
                  :exec
                  (the
                    (unsigned-byte 52)
                    (logior
                      (the
                        (unsigned-byte 52)
                        (logand (the
                                  (unsigned-byte 52)
                                  (ash
                                    (the (unsigned-byte 22)
                                         (ia32e-pdpte-1GB-pageBits->page entry))
                                    30))
                                (lognot (1- (ash 1 30)))))
                      (the (unsigned-byte 30)
                           (logand (1- (ash 1 30)) lin-addr)))))
                x86))

          ;; Go to the next level of page table structure (PD, which
          ;; will reference a 2MB page or a 4K page, eventually).
          (b* ((page-directory-base-addr
                 (ash (ia32e-pdpte-pg-dirBits->pd entry) 12))
               ((mv flag
                    (the (unsigned-byte #.*physical-address-size*) p-addr)
                    x86)
                (ia32e-la-to-pa-page-directory
                  lin-addr page-directory-base-addr u/s-all r/w-all x/d-all
                  wp smep smap ac nxe r-w-x cpl x86))
               ;; If we updated the entry, we must write it before returning
               ;; We reread the entry because it is possible a lower level set the dirty bit on it
               ;; This requires us to set the accessed bit again
               (entry (rm-low-64 p-entry-addr x86))
               (x86 (if marking-view?
                      (b* ((accessed (mbe :logic (accessed-bit entry)
                                          :exec (ia32e-page-tablesBits->a entry)))
                           ((unless (equal accessed 0)) x86))
                          (wm-low-64 p-entry-addr (set-accessed-bit entry) x86))
                      x86))
               ((when flag) (mv flag 0 x86)))
              (mv nil p-addr x86))))

    (mv t 0 x86))

  ///

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1
                                         (ia32e-la-to-pa-page-dir-ptr-table
                                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                           wp smep smap ac nxe r-w-x cpl
                                           x86))

                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
          (implies (x86p x86)
                   (x86p
                     (mv-nth 2
                             (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-page-dir-ptr-table
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl
                                        x86)))
                          (xr fld index x86))))

  (defthm xr-fault-ia32e-la-to-pa-page-dir-ptr-table
          (implies (not (mv-nth 0
                                (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe r-w-x cpl x86)))
                   (equal (xr :fault index
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-page-dir-ptr-table-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (negative-logand-to-positive-logand-with-integerp-x
                                             bitops::logand-with-negated-bitmask)))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl
                                         x86))))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl
                                        x86))))))

  (defthm mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-system-level-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                         lin-addr
                                         base-addr u/s-acc r/w-acc x/d-acc
                                         wp smep smap ac nxe r-w-x cpl x86))))
                   (equal (mv-nth
                            2
                            (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr
                              base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86))
                          x86)))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-page-dir-ptr-table
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86))
           :enable (wm-low-32 wm-low-64))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-page-dir-ptr-table
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                                  wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-page-dir-ptr-table)

  (defthm ia32e-la-to-pa-page-dir-ptr-table-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr entry
                                    u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                                 lin-addr entry
                                                 u/s-acc r/w-acc x/d-acc
                                                 wp smep smap ac nxe r-w-x cpl x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                      lin-addr entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                      lin-addr-2 entry
                                      u/s-acc r/w-acc x/d-acc
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-page-dir-ptr-table-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                          lin-addr entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))
                              (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                          lin-addr-2 entry
                                          u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa-pml4-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (smap      :type (unsigned-byte  1))
   (ac        :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p
                                          signed-byte-p
                                          member-equal
                                          not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (app-view x86)))

    (b* (

         ;; Fix the inputs of this function without incurring execution
         ;; overhead.
         (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (base-addr (mbe :logic (part-install
                                  0
                                  (loghead *physical-address-size* base-addr)
                                  :low 0 :width 12)
                         :exec base-addr))

         ;; First, we get the address of the PML4E.  A PML4E is selected
         ;; using the physical address defined as follows:
         ;;   Bits 51:12 are from CR3.
         ;;   Bits 11:3 are bits 47:39 of the linear address.
         ;;   Bits 2:0 are all 0.
         (p-entry-addr
           (the (unsigned-byte #.*physical-address-size*)
                (pml4-table-entry-addr lin-addr base-addr)))

         ;; Now, we can read the PML4E.
         (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

         (u/s-all (mbe :logic (page-user-supervisor entry)
                       :exec (ia32e-page-tablesBits->u/s entry)))
         (r/w-all (mbe :logic (page-read-write entry)
                       :exec (ia32e-page-tablesBits->r/w entry)))
         (x/d-all (mbe :logic (page-execute-disable entry)
                       :exec (ia32e-page-tablesBits->xd entry)))

         (marking-view? (marking-view x86))

         ((mv fault-flg val x86)
          (paging-entry-no-page-fault-p
            3 ;; structure-type
            lin-addr entry
            u/s-all r/w-all x/d-all
            wp smep smap ac nxe r-w-x cpl x86))
         ((when fault-flg)
          ;; Even if this entry page faulted, if the entry was present,
          ;; we must set the accessed bit
          (b* ((x86 (if (and marking-view?
                             (equal (mbe :logic (page-present entry)
                                         :exec (ia32e-page-tablesBits->p entry))
                                    1))
                      (b* ((accessed (mbe :logic (accessed-bit entry)
                                          :exec (ia32e-page-tablesBits->a entry)))
                           ((unless (equal accessed 0)) x86))
                          (wm-low-64 p-entry-addr (set-accessed-bit entry) x86))
                      x86)))
              (mv 'Page-Fault val x86)))

         ;; No errors at this level, so we proceed with the translation.
         ;; We go to the next level of page table structure, i.e., PDPT.

         (page-dir-ptr-table-base-addr
           (ash (ia32e-pml4eBits->pdpt entry) 12))
         ((mv flag
              (the (unsigned-byte #.*physical-address-size*) p-addr)
              x86)
          (ia32e-la-to-pa-page-dir-ptr-table
            lin-addr page-dir-ptr-table-base-addr u/s-all r/w-all x/d-all
            wp smep smap ac nxe r-w-x cpl
            x86))
         ;; Whether or not the next level page faulted, we must set the accessed flag
         ;; We reread the entry because it is possible a lower level set the dirty bit on it
         (entry (rm-low-64 p-entry-addr x86))
         (x86 (if marking-view?
                (b* ((accessed (mbe :logic (accessed-bit entry)
                                    :exec (ia32e-page-tablesBits->a entry)))
                     ((unless (equal accessed 0)) x86))
                    (wm-low-64 p-entry-addr (set-accessed-bit entry) x86))
                x86))
         ((when flag) (mv flag 0 x86)))
        (mv nil p-addr x86))

    (mv t 0 x86))

  ///

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-pml4-table
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1
                                         (ia32e-la-to-pa-pml4-table
                                           lin-addr base-addr
                                           wp smep smap ac nxe r-w-x cpl
                                           x86))

                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-pml4-table
          (implies (x86p x86)
                   (x86p
                     (mv-nth 2
                             (ia32e-la-to-pa-pml4-table
                               lin-addr base-addr
                               wp smep smap ac nxe r-w-x cpl
                               x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-pml4-table
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index
                              (mv-nth 2
                                      (ia32e-la-to-pa-pml4-table
                                        lin-addr base-addr
                                        wp smep smap ac nxe r-w-x cpl
                                        x86)))
                          (xr fld index x86))))

  (defthm xr-fault-ia32e-la-to-pa-pml4-table
          (implies (not (mv-nth 0
                                (ia32e-la-to-pa-pml4-table
                                  lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
                   (equal (xr :fault index
                              (mv-nth 2
                                      (ia32e-la-to-pa-pml4-table
                                        lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-pml4-table-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                                    lin-addr base-addr
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (negative-logand-to-positive-logand-with-integerp-x
                                             bitops::logand-with-negated-bitmask)))))

  (defthm ia32e-la-to-pa-pml4-table-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-pml4-table
                                         lin-addr base-addr
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-pml4-table
                                         lin-addr base-addr
                                         wp smep smap ac nxe r-w-x cpl
                                         x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-pml4-table
                                         lin-addr base-addr
                                         wp smep smap ac nxe r-w-x cpl
                                         (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-pml4-table
                                         lin-addr base-addr
                                         wp smep smap ac nxe r-w-x cpl
                                         x86))))))

  (defthm ia32e-la-to-pa-pml4-table-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl
                                    (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-pml4-table
                                        lin-addr base-addr
                                        wp smep smap ac nxe r-w-x cpl
                                        x86))))))

  (defthm mv-nth-2-ia32e-la-to-pa-pml4-table-system-level-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                         lin-addr base-addr
                                         wp smep smap ac nxe r-w-x cpl x86))))
                   (equal (mv-nth
                            2
                            (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr
                              wp smep smap ac nxe r-w-x cpl x86))
                          x86)))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-pml4-table
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                            lin-addr base-addr
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86))
           :enable (wm-low-32 wm-low-64))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-pml4-table
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                                  lin-addr ase-addr
                                                  wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-pml4-table)

  (defthm ia32e-la-to-pa-pml4-table-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr ase-addr
                                    wp smep smap ac nxe r-w-x cpl x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                                 lin-addr ase-addr
                                                 wp smep smap ac nxe r-w-x cpl x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-pml4-table-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                      lin-addr ase-addr
                                      wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                      lin-addr-2 ase-addr
                                      wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                   :use ((:instance logexting-maintains-same-page
                                    (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-pml4-table-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                          lin-addr ase-addr
                                          wp smep smap ac nxe r-w-x cpl x86))
                              (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                          lin-addr-2 ase-addr
                                          wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence))

;; ----------------------------------------------------------------------

(defabbrev cpl (x86)
  (the (unsigned-byte 2)
       (segment-selectorBits->rpl
        (the (unsigned-byte 16) (seg-visiblei #.*cs* x86)))))

(define ia32e-la-to-pa-without-tlb-internal
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (smap      :type (unsigned-byte  1))
   (ac        :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr))

  :guard-hints (("Goal" :in-theory (e/d (acl2::bool->bit bitops::logsquash)
                                        (unsigned-byte-p
                                          signed-byte-p
                                          bitops::logand-with-negated-bitmask
                                          member-equal
                                          not))))

  ;; If lin-addr is not canonical, we should throw a general
  ;; protection exception (#GP(0)).  (Or a stack fault (#SS) as
  ;; appropriate?)

  (if (mbt (not (app-view x86)))

    (b* ((lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (r-w-x (mbe :logic (if (member r-w-x '(:r :w :x))
                              r-w-x
                              :r)
                     :exec r-w-x))
         (cr3       (ctri *cr3* x86))
         (pml4-table-base-addr
           (mbe
             :logic
             (ash (cr3Bits->pdb cr3) 12)
             :exec
             (the (unsigned-byte 52)
                  (ash (the (unsigned-byte 40) (cr3Bits->pdb cr3)) 12))))
         ((mv flg phys-addr x86)
          (ia32e-la-to-pa-pml4-table lin-addr pml4-table-base-addr wp smep smap ac nxe r-w-x cpl x86))
         ((when flg) (mv t 0 x86)))
        (mv flg phys-addr x86))

    (mv t 0 x86))

  ///

  (defthm ia32e-la-to-pa-without-tlb-internal-in-non-app-view
          (implies (xr :app-view nil x86)
                   (equal (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)
                          (mv t 0 x86))))

  (local (defthm unsigned-byte-p-logapp
                 (implies (and (natp j)
                               (unsigned-byte-p i x)
                               (integerp y))
                          (unsigned-byte-p (+ i j) (logapp j y x)))))

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-without-tlb-internal
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))

                          :hints (("Goal" :in-theory (e/d () (force (force) unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) (force (force)))))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p)
                                                            (force (force) not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-without-tlb-internal
          (implies (x86p x86)
                   (x86p (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-without-tlb-internal
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm xr-fault-ia32e-la-to-pa-without-tlb-internal
          (implies (not (mv-nth 0 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                   (equal (xr :fault index (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-without-tlb-internal-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-internal-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                                   (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                       (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))))))

  (defthm ia32e-la-to-pa-without-tlb-internal-xw-rflags-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                       (xw :rflags nil value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                       (xw :rflags nil value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))))
          :hints (("Goal" :in-theory (e/d (rflagsbits->ac rflagsbits-fix) ()))))

  (defthm ia32e-la-to-pa-without-tlb-internal-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                  (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                      x86)))))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-internal-xw-rflags-state-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl
                                                  (xw :rflags nil value x86)))
                          (xw :rflags nil value
                              (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))))
          :hints (("Goal" :in-theory (e/d* (rflagsBits->ac rflagsbits-fix) (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-internal-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-without-tlb-internal-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))
                          (mv-nth 0 (ia32e-la-to-pa-without-tlb-internal lin-addr-2 wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                   :use ((:instance logexting-maintains-same-page
                                    (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-without-tlb-internal-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))
                              (mv-nth 1 (ia32e-la-to-pa-without-tlb-internal lin-addr-2 wp smep smap ac nxe r-w-x cpl x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm mv-nth-2-ia32e-la-to-pa-without-tlb-internal-system-level-non-marking-view
    (implies (and (not (marking-view x86))
                  (not (mv-nth 0 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))))
             (equal (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))
                    x86))
    :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-without-tlb-internal) (force (force))))))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-without-tlb-internal
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                  (64-bit-modep x86))
           :enable (64-bit-modep)
           :disable (force (force)))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-without-tlb-internal
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-without-tlb-internal)

  (defthm ia32e-la-to-pa-without-tlb-internal-fixes-address
          (equal (ia32e-la-to-pa-without-tlb-internal (logext 48 lin-addr) wp smep smap ac nxe r-w-x cpl x86)
                 (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)))

  (defthm ia32e-la-to-pa-without-tlb-internal-fixes-perm
          (implies (not (member-p r-w-x '(:r :w :x)))
                   (equal (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)
                          (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe :r cpl x86)))))

;; This isn't used in execution, but it's useful for reasoning
(define ia32e-la-to-pa-without-tlb
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (x86 "x86 state"))
  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr))
  (if (mbt (not (app-view x86)))

    (b* ((lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (r-w-x (mbe :logic (if (member r-w-x '(:r :w :x)) r-w-x :r)
                     :exec r-w-x))
         (cr0
           ;; CR0 is still a 32-bit register in 64-bit mode.
           (n32 (ctri *cr0* x86)))
         (cr4
           ;; CR4 has all but the low 22 bits reserved.
           (n22 (ctri *cr4* x86)))
         ;; Current privilege level (0-3), obtained from the CS segment selector [1:0]
         (cpl (the (unsigned-byte  2) (cpl x86)))
         ;; ia32-efer has all but the low 12 bits reserved.
         (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
         (wp        (cr0Bits->wp cr0))
         (smep      (cr4Bits->smep cr4))
         (smap      (cr4Bits->smap cr4))
         (ac        (rflagsBits->ac (rflags x86)))
         (nxe       (ia32_eferBits->nxe ia32-efer)))
        (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86))

    (mv t 0 x86))
  ///
  (defthm ia32e-la-to-pa-without-tlb-in-non-app-view
          (implies (xr :app-view nil x86)
                   (equal (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)
                          (mv t 0 x86))))

  (local (defthm unsigned-byte-p-logapp
                 (implies (and (natp j)
                               (unsigned-byte-p i x)
                               (integerp y))
                          (unsigned-byte-p (+ i j) (logapp j y x)))))

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa-without-tlb
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))

                          :hints (("Goal" :in-theory (e/d () (force (force) unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) (force (force)))))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p)
                                                            (force (force) not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-without-tlb
          (implies (x86p x86)
                   (x86p (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa-without-tlb
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm xr-fault-ia32e-la-to-pa-without-tlb
          (implies (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                   (equal (xr :fault index (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-without-tlb-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))))))

  (defthm ia32e-la-to-pa-without-tlb-xw-rflags-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d (rflagsbits->ac rflagsbits-fix) ()))))

  (defthm ia32e-la-to-pa-without-tlb-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                  (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                      x86)))))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-xw-rflags-state-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa-without-tlb lin-addr r-w-x
                                                  (xw :rflags nil value x86)))
                          (xw :rflags nil value
                              (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rflagsBits->ac rflagsbits-fix) (force (force))))))

  (defthm ia32e-la-to-pa-without-tlb-same-page-offset
          (implies (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                   (same-page-offset (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))
                                     lin-addr)))

  (defthm ia32e-la-to-pa-without-tlb-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))
                          (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                   :use ((:instance logexting-maintains-same-page
                                    (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-without-tlb-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))
                              (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm mv-nth-2-ia32e-la-to-pa-without-tlb-system-level-non-marking-view
    (implies (and (not (marking-view x86))
                  (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))))
             (equal (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86))
                    x86))
    :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-without-tlb) (force (force))))))

  (defrule 64-bit-modep-of-ia32e-la-to-pa-without-tlb
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                  (64-bit-modep x86))
           :enable (64-bit-modep)
           :disable (force (force)))

  (defrule x86-operation-mode-of-ia32e-la-to-pa-without-tlb
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa-without-tlb)

  (defthm ia32e-la-to-pa-without-tlb-fixes-address
          (equal (ia32e-la-to-pa-without-tlb (logext 48 lin-addr) r-w-x x86)
                 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))

  (defthm ia32e-la-to-pa-without-tlb-fixes-perm
          (implies (not (member-p r-w-x '(:r :w :x)))
                   (equal (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)
                          (ia32e-la-to-pa-without-tlb lin-addr :r x86)))))

(define ia32e-la-to-pa
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (x86 "x86 state"))

  :parents (ia32e-paging)

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr))

  :guard-hints (("Goal" :in-theory (e/d (acl2::bool->bit bitops::logsquash segment-selectorbits->rpl ia32e-la-to-pa-without-tlb)
                                        (unsigned-byte-p
                                          signed-byte-p
                                          bitops::logand-with-negated-bitmask
                                          member-equal
                                          not))))

  ;; If lin-addr is not canonical, we should throw a general
  ;; protection exception (#GP(0)).  (Or a stack fault (#SS) as
  ;; appropriate?)

  (if (mbt (not (app-view x86)))

    (b* ((lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                        :exec lin-addr))
         (r-w-x (mbe :logic (if (member r-w-x '(:r :w :x)) r-w-x :r)
                     :exec r-w-x))
         (cr0
           ;; CR0 is still a 32-bit register in 64-bit mode.
           (n32 (ctri *cr0* x86)))
         (cr4
           ;; CR4 has all but the low 22 bits reserved.
           (n22 (ctri *cr4* x86)))
         ;; Current privilege level (0-3), obtained from the CS segment selector [1:0]
         (cpl (the (unsigned-byte  2) (cpl x86)))
         ;; ia32-efer has all but the low 12 bits reserved.
         (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
         (wp        (cr0Bits->wp cr0))
         (smep      (cr4Bits->smep cr4))
         (smap      (cr4Bits->smap cr4))
         (ac        (rflagsBits->ac (rflags x86)))
         (nxe       (ia32_eferBits->nxe ia32-efer))
         (vpn (logtail 12 (loghead #.*max-linear-address-size* lin-addr)))
         (tlb (tlb x86))

         (tlb-key (make-tlb-key-fast :vpn vpn
                                     :r-w-x (case r-w-x
                                              (:r 0)
                                              (:w 1)
                                              (:x 2))
                                     :wp wp
                                     :smep smep
                                     :smap smap
                                     :ac ac
                                     :nxe nxe
                                     :cpl cpl))
         (tlb-entry (cdr (hons-get tlb-key tlb)))
         ((when tlb-entry) (mv nil 
                               (logapp 12 lin-addr tlb-entry)
                               x86))

         ;; We didn't find a valid tlb entry
         ((mv flg phys-addr x86) (mbe :exec (ia32e-la-to-pa-without-tlb-internal lin-addr wp smep smap ac nxe r-w-x cpl x86)
                                      :logic (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
         ((when flg) (mv flg phys-addr x86))
         (ppn (logtail 12 phys-addr))
         (x86 (!tlb (hons-acons tlb-key ppn tlb) x86)))
        (mv flg phys-addr x86))

    (mv t 0 x86))

  ///

  (local (defthm unsigned-byte-p-logapp
                 (implies (and (natp j)
                               (unsigned-byte-p i x)
                               (integerp y))
                          (unsigned-byte-p (+ i j) (logapp j y x)))))

  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))

                          :hints (("Goal" :in-theory (e/d () (force (force) unsigned-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) (force (force)))))
                          :gen-type t
                          :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p)
                                                            (force (force) not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa
          (implies (x86p x86)
                   (x86p (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (defthm xr-ia32e-la-to-pa
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm xr-fault-ia32e-la-to-pa
          (implies (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
                   (equal (xr :fault index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* ()
                                           (force
                                             (force)
                                             (:definition not)
                                             (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-and-ia32e-la-to-pa-in-non-marking-view
          (implies (and (not (marking-view x86))
                        (not (equal fld :fault))
                        (not (equal fld :tlb)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :tlb)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x x86))))))

  (defthm ia32e-la-to-pa-xw-rflags-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d (rflagsbits->ac rflagsbits-fix) ()))))

  (defthm ia32e-la-to-pa-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view))
                        (not (equal fld :tlb)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa lin-addr r-w-x
                                                  (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa lin-addr r-w-x
                                                      x86)))))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-xw-rflags-state-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa lin-addr r-w-x
                                                  (xw :rflags nil value x86)))
                          (xw :rflags nil value
                              (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rflagsBits->ac rflagsbits-fix) (force (force))))))

  (defrule 64-bit-modep-of-ia32e-la-to-pa
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (64-bit-modep x86))
           :enable (64-bit-modep)
           :disable (force (force)))

  (defrule x86-operation-mode-of-ia32e-la-to-pa
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa)

  (defthm ia32e-la-to-pa-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))
                          (mv-nth 0 (ia32e-la-to-pa lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                   :use ((:instance logexting-maintains-same-page
                                    (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
                              (mv-nth 1 (ia32e-la-to-pa lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (e/d () (logexting-maintains-same-page))
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthmd ia32e-la-to-pa-fixes-address
           (implies (not (canonical-address-p lin-addr))
                    (equal (ia32e-la-to-pa lin-addr r-w-x x86)
                           (ia32e-la-to-pa (logext 48 lin-addr) r-w-x x86))))

  (defthm ia32e-la-to-pa-fixes-perm
          (implies (not (member-p r-w-x '(:r :w :x)))
            (equal (ia32e-la-to-pa lin-addr r-w-x x86)
                   (ia32e-la-to-pa lin-addr :r x86)))))

(in-theory (enable ia32e-la-to-pa-without-tlb-internal))

;; ======================================================================

(defthm page-table-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-table
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86))))
           (equal
            (loghead n
                     (mv-nth 1
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              x86)))
            (loghead n lin-addr)))
  :hints
  (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-table)
                           (unsigned-byte-p)))))

(defthm page-table-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (not (equal (loghead n
                                     (mv-nth 1 (ia32e-la-to-pa-page-table
                                                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                                wp smep smap ac nxe r-w-x cpl
                                                x86)))
                            (loghead n lin-addr))))
           (mv-nth 0 (ia32e-la-to-pa-page-table
                      lin-addr base-addr u/s-acc r/w-acc x/d-acc
                      wp smep smap ac nxe r-w-x cpl
                      x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-table)
                                  (unsigned-byte-p)))))

(defthm page-table-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-table
                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86)))
           (equal
            (loghead n
                     (mv-nth 1
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              x86)))
            0))
  :hints
  (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-table)
                           (unsigned-byte-p)))))

(local
 (defthm negative-logand-to-positive-logand-n=64=for-now
   ;; TO-DO@Shilpi:
   ;; There are more general theorems called
   ;; negative-logand-to-positive-logand-with-natp-x and
   ;; negative-logand-to-positive-logand-with-integerp-x in
   ;; register-readers-and-writers.lisp.  Why don't they work
   ;; here? Which rule is interfering?
   (implies (and (equal n 64)
                 (unsigned-byte-p n x)
                 (integerp m)
                 ;; Only for negative values of m
                 (syntaxp (and (quotep m)
                               (let* ((m-abs (acl2::unquote m)))
                                 (< m-abs 0)))))
            (equal (logand m x)
                   (logand (logand (1- (expt 2 n)) m) x)))
   :hints (("Goal" :in-theory (e/d () (bitops::loghead-of-logand))))))

(defthm page-directory-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86))))
           (equal
            (loghead n
                     (mv-nth
                      1
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory)
                                  (unsigned-byte-p)))))

(defthm page-directory-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead n
                               (mv-nth
                                1
                                (ia32e-la-to-pa-page-directory
                                 lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                 wp smep smap ac nxe r-w-x cpl
                                 x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-page-directory
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl
             x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory)
                                  (unsigned-byte-p)))))

(defthm page-directory-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-directory
                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86)))
           (equal
            (loghead n
                     (mv-nth
                      1
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory)
                                  (unsigned-byte-p)))))

(defthm page-dir-ptr-table-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-dir-ptr-table
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86))))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl
               x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p
                                   acl2::loghead-identity
                                   unsigned-byte-p-when-ia32_eferbits-p
                                   unsigned-byte-p-when-12bits-p)))))

(defthm page-dir-ptr-table-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead
                       n
                       (mv-nth
                        1
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr base-addr u/s-acc r/w-acc x/d-acc
                         wp smep smap ac nxe r-w-x cpl
                         x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl
             x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p
                                   acl2::loghead-identity
                                   unsigned-byte-p-when-ia32_eferbits-p
                                   unsigned-byte-p-when-12bits-p)))))

(defthm page-dir-ptr-table-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-dir-ptr-table
                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86)))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl
               x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p
                                   acl2::loghead-identity
                                   unsigned-byte-p-when-ia32_eferbits-p
                                   unsigned-byte-p-when-12bits-p)))))

(defthm pml4-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-pml4-table
                       lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86))))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-pml4-table
               lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :do-not '(preprocess) ;; Preprocessing seems to make this theorem weirdly slow for some reason
           :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                           (unsigned-byte-p
                             acl2::loghead-identity
                             unsigned-byte-p-when-ia32_eferbits-p
                             unsigned-byte-p-when-12bits-p)))))

(defthm pml4-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead
                       n
                       (mv-nth
                        1
                        (ia32e-la-to-pa-pml4-table
                         lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-pml4-table
             lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
  :hints (("Goal" :do-not '(preprocess) ;; Preprocessing seems to make this theorem weirdly slow for some reason
           :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                           (unsigned-byte-p
                             acl2::loghead-identity
                             unsigned-byte-p-when-ia32_eferbits-p
                             unsigned-byte-p-when-12bits-p)))))

(defthm pml4-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-pml4-table
                  lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-pml4-table
               lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            0))
  :hints (("Goal" :do-not '(preprocess) ;; Preprocessing seems to make this theorem weirdly slow for some reason
           :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                           (unsigned-byte-p
                             acl2::loghead-identity
                             unsigned-byte-p-when-ia32_eferbits-p
                             unsigned-byte-p-when-12bits-p)))))

(defthm ia32e-la-to-pa-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  ()))))

(defthmd ia32e-la-to-pa-lower-12-bits-error
  (implies (and
            ;; Here's a dumb bind-free, but hey, it works for my
            ;; purposes!  I can make a nicer rule in the future or I
            ;; can simply be lazy and add to the bind-free.
            (bind-free (list (list (cons 'n ''12)))
                       (n))
            (natp n)
            (<= n 12)
            (not (equal (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (loghead n lin-addr))))
           (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  (acl2::loghead-identity
                                   unsigned-byte-p
                                   signed-byte-p
                                   force (force))))))

(defthmd ia32e-la-to-pa-without-tlb-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr r-w-x x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-without-tlb) ()))))

(defthmd ia32e-la-to-pa-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa ia32e-la-to-pa-without-tlb-lower-12-bits-value-of-address-when-error) ()))))

(defrulel ia32e-la-to-pa-lower-12-bits-alt
  ;; This local rule helps in the proof of
  ;; ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones
  ;; Note the very general LHS --- this generality is the reason why
  ;; this is a local rule.  I'll keep ia32e-la-to-pa-lower-12-bits
  ;; around for readability.
  (implies (and (bind-free (list (list (cons 'x86 'x86)))
                           (x86))
                (natp n)
                (<= n 12)
                (x86p x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (equal
            (loghead n lin-addr)
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa) ()))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones
  ;; This rule comes in useful during the guard proof of rml16.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4095)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-1*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))))
  :rule-classes :linear)

(encapsulate

  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm logtail-and-loghead-equality
    (implies (and (equal (logtail n x) (logtail n y))
                  (equal (loghead n x) (loghead n y))
                  (natp x)
                  (natp y))
             (equal x y))
    :hints (("Goal" :in-theory (enable logtail loghead)))
    :rule-classes ((:forward-chaining
                    ;; These trigger terms are no good if the hyps of
                    ;; the theorem to be proved have something like
                    ;; (and (equal (logtail n x) 0)
                    ;;      (equal (logtail n x) 0))
                    ;; But, for my use case so far, the following terms
                    ;; do fine, though (equal (loghead n x) (loghead n
                    ;; y)) is not a good candidate since logheads
                    ;; appear separately, like:
                    ;; (and (equal (loghead n x) 0)
                    ;;      (equal (loghead n x) 0))
                    :trigger-terms ((equal (logtail n x) (logtail n y))
                                    ;; (equal (loghead n x) (loghead n y))
                                    )))))

(defthm loghead-monotonic-when-upper-bits-are-equal
  ;; See also the rule logtail-and-loghead-equality.
  (implies (and (< (loghead x a) (loghead x b))
                (equal (logtail x a) (logtail x b))
                (natp a)
                (natp b))
           (< a b))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
          (acl2::loghead-identity
           unsigned-byte-p**))))
  :rule-classes :forward-chaining)

(defthm logtail-and-loghead-inequality-with-low-bits-equal
  (implies (and (<= (logtail n x) (logtail n y))
                (equal (loghead n x) (loghead n y))
                (natp n)
                (natp x)
                (natp y))
           (<= x y))
  :hints (("Goal"
           :in-theory
           (e/d*
            (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
            (acl2::loghead-identity
             unsigned-byte-p**))))
  :rule-classes nil)

(defthm logtail-monotone-1
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (logtail x a) (logtail x b)))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)))))

(defthm logtail-and-loghead-inequality
  ;; See also the rule logtail-and-loghead-equality, which is a
  ;; forward-chaining rule.  This is a :rule-classes nil instead.
  (implies (and (<= (logtail n x) (logtail n y))
                (< (loghead n x) (loghead n y))
                (natp n)
                (natp x)
                (natp y))
           (< x y))
  :hints (("Goal"
           :cases ((< (logtail n x) (logtail n y)))))
  :rule-classes nil)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093-helper
  (implies (and (< (loghead 12 x) 4093)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-3*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-3*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093
  ;; This rule comes in useful during the guard proof of rml32.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4093)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-3*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089-helper
  (implies (and (< (loghead 12 x) 4089)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-7*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-7*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089-helper
  (implies (and (equal (loghead 12 x) 4089)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-7*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-7*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090-helper
  (implies (and (equal (loghead 12 x) 4090)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-6*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-6*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4090)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-6*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081-helper
  (implies (and (< (loghead 12 x) 4081)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-15*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-15*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081
  ;; This rule comes in useful during the guard proof of rml128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081-helper
  (implies (and (equal (loghead 12 x) 4081)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-15*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-15*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081
  ;; This rule comes in useful during the guard proof of rml128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

;; ======================================================================

(define la-to-pa
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (x86 "x86 state"))

  :inline t
  :no-function t
  :enabled t

  :guard (not (app-view x86))
  :parents (ia32e-paging)

  :short "Top-level page translation function"

  (if (mbt (and (canonical-address-p lin-addr)
                (not (app-view x86))))
      (ia32e-la-to-pa lin-addr r-w-x x86)
    (mv (list :ia32e-paging-invalid-linear-address-or-not-in-sys-view
              lin-addr)
        0 x86)))

;; ======================================================================

(in-theory (e/d* () (set-accessed-bit
                     set-dirty-bit
                     page-present
                     page-size
                     page-read-write
                     page-user-supervisor
                     page-execute-disable)))

;; ======================================================================
