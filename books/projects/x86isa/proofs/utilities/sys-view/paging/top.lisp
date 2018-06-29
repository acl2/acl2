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
(include-book "common-paging-lemmas" :ttags :all)
(include-book "la-to-pa-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (unsigned-byte-p signed-byte-p))))

(defsection reasoning-about-page-tables
  :parents (system-level-marking-view-proof-utilities)
  )

(local (xdoc::set-default-parents reasoning-about-page-tables))

;; ======================================================================

;; Some congruence rules about xlation-governing-entries-paddrs:

(defthm xlation-governing-entries-paddrs-for-page-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table) ())))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-page-directory-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs lin-addr x86-1)
                  (xlation-governing-entries-paddrs lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs) ())
           :use ((:instance xlate-equiv-memory-and-cr3-cong))))
  :rule-classes :congruence)

(defthm all-xlation-governing-entries-paddrs-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (all-xlation-governing-entries-paddrs n lin-addr x86-1)
                  (all-xlation-governing-entries-paddrs n lin-addr x86-2)))
  :rule-classes :congruence)

;; ======================================================================

;; Memory reads from the state returned after a page walk:

;; TODO: Fix lin-addr and base-addr inside *entry-addr functions?

(defthm remove-logext-48-from-page-table-entry-addr
  (equal (page-table-entry-addr (logext 48 lin-addr) base-addr)
         (page-table-entry-addr lin-addr base-addr))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr logext)
                                   ()))))

(defthm remove-logext-48-from-xlation-governing-entries-paddrs-for-page-table
  (equal (xlation-governing-entries-paddrs-for-page-table
          (logext 48 lin-addr) base-addr x86)
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr base-addr x86))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                                   ()))))

(defthm remove-logext-48-from-page-directory-entry-addr
  (equal (page-directory-entry-addr (logext 48 lin-addr) base-addr)
         (page-directory-entry-addr lin-addr base-addr))
  :hints (("Goal" :in-theory (e/d* (page-directory-entry-addr logext)
                                   ()))))

(defthm remove-logext-48-from-xlation-governing-entries-paddrs-for-page-directory
  (equal (xlation-governing-entries-paddrs-for-page-directory
          (logext 48 lin-addr) base-addr x86)
         (xlation-governing-entries-paddrs-for-page-directory
          lin-addr base-addr x86))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory)
                                   ()))))

(defthm remove-logext-48-from-page-dir-ptr-table-entry-addr
  (equal (page-dir-ptr-table-entry-addr (logext 48 lin-addr) base-addr)
         (page-dir-ptr-table-entry-addr lin-addr base-addr))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-entry-addr logext)
                                   ()))))

(defthm remove-logext-48-from-xlation-governing-entries-paddrs-for-page-dir-ptr-table
  (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table
          (logext 48 lin-addr) base-addr x86)
         (xlation-governing-entries-paddrs-for-page-dir-ptr-table
          lin-addr base-addr x86))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                   ()))))

(defthm removing-irrelevant-logext-from-logtail-and-loghead
  (implies (and (<= (+ i j) n) (natp n) (natp j))
           (equal (loghead i (logtail j (logext n lin-addr)))
                  (loghead i (logtail j lin-addr))))
  :hints ((logbitp-reasoning)))

(defthm remove-logext-48-from-pml4-table-entry-addr
  (equal (pml4-table-entry-addr (logext 48 lin-addr) base-addr)
         (pml4-table-entry-addr lin-addr base-addr))
  :hints (("Goal" :in-theory (e/d* (pml4-table-entry-addr)
                                   ()))))

(defthm remove-logext-48-from-xlation-governing-entries-paddrs-for-pml4-table
  (equal (xlation-governing-entries-paddrs-for-pml4-table
          (logext 48 lin-addr) base-addr x86)
         (xlation-governing-entries-paddrs-for-pml4-table
          lin-addr base-addr x86))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table)
                                   ()))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-table
                             lin-addr base-addr (double-rewrite x86)))
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p
                                    ia32e-la-to-pa-page-table
                                    xlation-governing-entries-paddrs-for-page-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-directory
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-directory
                             lin-addr base-addr (double-rewrite x86)))
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-directory
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                    xlation-governing-entries-paddrs-for-page-directory)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-dir-ptr-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             lin-addr base-addr (double-rewrite x86)))
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-pml4-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-pml4-table
                             lin-addr base-addr (double-rewrite x86)))
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                            lin-addr base-addr
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    xlation-governing-entries-paddrs-for-pml4-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa
  (implies (disjoint-p (list index)
                       (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    xlation-governing-entries-paddrs)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

(defthm xr-mv-nth-2-ia32e-la-to-pa-when-error
  (implies (and (mv-nth 0 (ia32e-la-to-pa addr r-w-x x86))
                (not (eql fld :fault)))
           (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa addr r-w-x x86)))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    ia32e-la-to-pa-pml4-table
                                    ia32e-la-to-pa-page-dir-ptr-table
                                    ia32e-la-to-pa-page-directory
                                    ia32e-la-to-pa-page-table)
                                   (force (force))))))

(defthm xr-mem-disjoint-las-to-pas
  (implies
   (and (64-bit-modep x86) ; added
        (disjoint-p (list index)
                    (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
   (equal (xr :mem index (mv-nth 2 (las-to-pas n addr r-w-x x86)))
          (xr :mem index x86)))
  :hints (("Goal"
           :induct (las-to-pas n addr r-w-x x86)
           :in-theory (e/d* (las-to-pas
                             all-xlation-governing-entries-paddrs
                             disjoint-p
                             member-p)
                            (negative-logand-to-positive-logand-with-integerp-x
                             bitops::logand-with-negated-bitmask
                             force (force))))))

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa
  (implies (disjoint-p
            p-addrs
            (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
           (equal (read-from-physical-memory
                   p-addrs
                   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) (force (force))))))

(defthm read-from-physical-memory-and-mv-nth-2-las-to-pas
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 p-addrs
                 (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
           (equal (read-from-physical-memory
                   p-addrs (mv-nth 2 (las-to-pas n addr r-w-x x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) (force (force))))))

(defthm rm-low-64-disjoint-ia32e-la-to-pa
  (implies
   (disjoint-p (addr-range 8 index)
               (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
   (equal (rm-low-64 index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
          (rm-low-64 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (xlation-governing-entries-paddrs
                                    negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

(defthm rm-low-64-disjoint-las-to-pas
  (implies
   (and (64-bit-modep x86) ; added
        (disjoint-p
         (addr-range 8 index)
         (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
   (equal (rm-low-64 index (mv-nth 2 (las-to-pas n addr r-w-x x86)))
          (rm-low-64 index x86)))
  :hints (("Goal" :induct (las-to-pas n addr r-w-x x86)
           :in-theory (e/d* (las-to-pas
                             disjoint-p)
                            (xlation-governing-entries-paddrs
                             negative-logand-to-positive-logand-with-integerp-x
                             bitops::logand-with-negated-bitmask
                             force (force))))))

;; ======================================================================

;; Proof that the xlation-governing-entries-paddrs for every canonical
;; address are a subset of the addresses described by
;; gather-all-paging-structure-qword-addresses:

(defthm xlation-governing-entries-paddrs-for-page-table-subset-of-paging-structures
  (implies
   (and (equal base-addr (page-table-base-addr lin-addr x86))
        ;; The following hyps are not needed when an
        ;; over-approximation of paging addresses is collected.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (subset-p
    (xlation-governing-entries-paddrs-for-page-table
     lin-addr base-addr x86)
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-subset-of-paging-structures
  (implies
   (and (equal base-addr (page-directory-base-addr lin-addr x86))
        ;; The following hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (canonical-address-p lin-addr))
   (subset-p
    (xlation-governing-entries-paddrs-for-page-directory
     lin-addr base-addr x86)
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    xlation-governing-entries-paddrs-for-page-directory)
                                   (xlation-governing-entries-paddrs-for-page-table)))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-subset-of-paging-structures
  (implies (and (equal base-addr (page-dir-ptr-table-base-addr lin-addr x86))
                ;; The following hyps are not needed when an
                ;; over-approximation of paging addresses is collected
                ;; instead.
                ;; (equal
                ;;  (page-present
                ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                ;;  1)
                (equal
                 (page-size
                  (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                 0)
                ;; (equal
                ;;  (page-present
                ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
                ;;  1)
                (canonical-address-p lin-addr))
           (subset-p
            (xlation-governing-entries-paddrs-for-page-dir-ptr-table
             lin-addr base-addr x86)
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :cases ((equal
                    (page-size
                     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
                    1))
           :in-theory (e/d* (subset-p
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-subset-of-paging-structures
  (implies (and (equal base-addr (pml4-table-base-addr x86))
                (canonical-address-p lin-addr))
           (subset-p
            (xlation-governing-entries-paddrs-for-pml4-table
             lin-addr base-addr x86)
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    xlation-governing-entries-paddrs-for-pml4-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-subset-of-paging-structures
  (implies (canonical-address-p lin-addr)
           (subset-p
            (xlation-governing-entries-paddrs lin-addr x86)
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs
                             subset-p)
                            (canonical-address-p)))))

(defthm all-xlation-governing-entries-paddrs-subset-of-paging-structures
  (implies (and (canonical-address-p (+ -1 n addr))
                (canonical-address-p addr))
           (subset-p
            (all-xlation-governing-entries-paddrs n addr x86)
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (all-xlation-governing-entries-paddrs
                                    subset-p
                                    canonical-address-p
                                    signed-byte-p)
                                   ()))))

;; ======================================================================

;; Proof of xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p
;; and all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint.

(defthm xlation-governing-entries-paddrs-for-page-table-and-write-to-physical-memory
  (equal (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr
          (write-to-physical-memory p-addrs bytes x86))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-for-page-table-and-mv-nth-1-wb
  (equal (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr
          (mv-nth 1 (wb n addr w value x86)))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (wb
                                    xlation-governing-entries-paddrs-for-page-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs-for-page-directory
                        lin-addr page-directory-base-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr
                   (write-to-physical-memory p-addrs value x86))
                  (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-page-directory)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-and-mv-nth-1-wb-disjoint-p
  (implies
   (and
    (64-bit-modep x86) ; added
    (disjoint-p
     (mv-nth 1 (las-to-pas n addr :w (double-rewrite x86)))
     (xlation-governing-entries-paddrs-for-page-directory
      lin-addr page-directory-base-addr (double-rewrite x86)))
    (not (app-view x86)))
   (equal (xlation-governing-entries-paddrs-for-page-directory
           lin-addr page-directory-base-addr
           (mv-nth 1 (wb n addr w value x86)))
          (xlation-governing-entries-paddrs-for-page-directory
           lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  xlate-equiv-entries-and-page-size
                  (e-1 (rm-low-64
                        (page-directory-entry-addr lin-addr page-directory-base-addr)
                        x86))
                  (e-2 (rm-low-64
                        (page-directory-entry-addr lin-addr page-directory-base-addr)
                        (mv-nth 2 (las-to-pas n addr :w x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-page-directory)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                        lin-addr page-dir-ptr-table-base-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (write-to-physical-memory p-addrs value x86))
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 (mv-nth 1 (las-to-pas n addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                  lin-addr page-dir-ptr-table-base-addr (double-rewrite x86)))
                (not (app-view x86)))
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (mv-nth 1 (wb n addr w value x86)))
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr
                                             lin-addr page-dir-ptr-table-base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                             lin-addr page-dir-ptr-table-base-addr)
                                            (mv-nth 2 (las-to-pas n addr :w x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-write-to-physical-memory-disjoint-p
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p p-addrs
                            (xlation-governing-entries-paddrs-for-pml4-table
                             lin-addr pml4-table-base-addr (double-rewrite x86))))
           (equal (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (write-to-physical-memory p-addrs value x86))
                  (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-pml4-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 (mv-nth 1 (las-to-pas n addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-pml4-table
                  lin-addr pml4-table-base-addr (double-rewrite x86)))
                (not (app-view x86)))
           (equal (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (mv-nth 1 (wb n addr w value x86)))
                  (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                            (index (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                            (x86-1 x86)
                            (x86-2 (mv-nth 2 (las-to-pas n addr :w x86))))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr) x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                            (mv-nth 2 (las-to-pas n addr :w x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-pml4-table)
                            (force (force))))))

(defthm xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint-p
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 p-addrs
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
           (equal (xlation-governing-entries-paddrs
                   lin-addr (write-to-physical-memory p-addrs value x86))
                  (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p xlation-governing-entries-paddrs) ()))))

(defthm xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p
  (implies (and (64-bit-modep x86)
                (disjoint-p
                 (mv-nth 1 (las-to-pas n addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
           (equal (xlation-governing-entries-paddrs
                   lin-addr (mv-nth 1 (wb n addr w value x86)))
                  (xlation-governing-entries-paddrs
                   lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs)
                            (wb)))))

(defthm all-xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint-p
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 p-addrs
                 (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
           (equal (all-xlation-governing-entries-paddrs
                   n addr (write-to-physical-memory p-addrs value x86))
                  (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             all-xlation-governing-entries-paddrs)
                            ()))))

(defthm all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint
  (implies (and (64-bit-modep x86) ; added
                (disjoint-p
                 (mv-nth 1 (las-to-pas n-2 addr-2 :w (double-rewrite x86)))
                 (all-xlation-governing-entries-paddrs n-1 addr-1 (double-rewrite x86))))
           (equal (all-xlation-governing-entries-paddrs
                   n-1 addr-1 (mv-nth 1 (wb n-2 addr-2 w value x86)))
                  (all-xlation-governing-entries-paddrs
                   n-1 addr-1 (double-rewrite x86))))
  :hints (("Goal"
           :in-theory (e/d* (all-xlation-governing-entries-paddrs
                             xlation-governing-entries-paddrs) ; added
                            (;xlation-governing-entries-paddrs ; removed
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                             wb))
           :induct (all-xlation-governing-entries-paddrs n-1 addr-1 x86))))

;; ======================================================================

;; Lemmas relating ia32e-la-to-pa and las-to-pas:

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (bind-free
                 (find-l-addrs-from-las-to-pas '(n addr-1) r-w-x mfc state)
                 (n addr-1))
                (64-bit-modep x86) ; added
                (<= addr-1 addr-2)
                (< addr-2 (+ n addr-1))
                (not (mv-nth 0 (las-to-pas n addr-1 r-w-x x86)))
                (integerp addr-2) (posp n))
           (equal (mv-nth 0 (ia32e-la-to-pa addr-2 r-w-x x86)) nil))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (64-bit-modep x86) ; added
                (<= addr-1 addr-2)
                (< addr-2 (+ n addr-1))
                (not (mv-nth 0 (las-to-pas n addr-1 r-w-x x86)))
                (integerp addr-2) (posp n))
           (member-p (mv-nth 1 (ia32e-la-to-pa addr-2 r-w-x x86))
                     (mv-nth 1 (las-to-pas n addr-1 r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthmd open-mv-nth-0-las-to-pas
  (implies (and (64-bit-modep x86) ; added
                (canonical-address-p lin-addr)
                (not (zp n)))
           (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x x86))
                  (or (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))
                      (mv-nth 0 (las-to-pas (+ -1 n) (+ 1 lin-addr) r-w-x x86))))))

(defthmd open-mv-nth-1-las-to-pas
  (implies (and (64-bit-modep x86) ; added
                (not (zp n))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86))))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))
                  (cons (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
                        (mv-nth 1 (las-to-pas (+ -1 n) (+ 1 lin-addr) r-w-x x86))))))

;; ======================================================================

;; Misc. lemmas about las-to-pas that need some congruence-based
;; reasoning to be proved:

(defthm mv-nth-1-las-to-pas-returns-nil-when-error
  (implies (mv-nth 0 (las-to-pas n lin-addr r-w-x x86))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))
                  nil)))

(defthm cdr-mv-nth-1-las-to-pas-no-error
  (implies (and (64-bit-modep x86) ; added
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
                (canonical-address-p lin-addr))
           (equal (cdr (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))
                  (mv-nth 1 (las-to-pas (1- n) (1+ lin-addr) r-w-x x86)))))

(defthm mv-nth-0-las-to-pas-and-xw-mem-not-member
  (implies (and
            (64-bit-modep x86) ; added
            (not
             (member-p
              index
              (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86))))
            (integerp index)
            (unsigned-byte-p 8 byte)
            (x86p x86))
           (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                        (xw :mem index byte x86)))
                  (mv-nth 0 (las-to-pas n lin-addr r-w-x x86))))
  :hints (("Goal"
           :in-theory (e/d* (open-mv-nth-0-las-to-pas
                             disjoint-p
                             member-p)
                            (xlation-governing-entries-paddrs)))))

(defthm mv-nth-1-las-to-pas-and-xw-mem-not-member
  (implies (and
            (64-bit-modep x86) ; added
            (not
             (member-p
              index
              (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86))))
            (integerp index)
            (unsigned-byte-p 8 byte)
            (x86p x86))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                        (xw :mem index byte x86)))
                  (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))))
  :hints (("Goal"
           :in-theory (e/d* (open-mv-nth-0-las-to-pas
                             open-mv-nth-1-las-to-pas
                             disjoint-p
                             member-p)
                            (xlation-governing-entries-paddrs)))))

;; (encapsulate
;;   ()
;;   (local
;;    (defthmd mv-nth-1-las-to-pas-subset-p-helper-1
;;      (implies (and (< n-2 n-1)
;;                    (not (mv-nth 0 (las-to-pas n-1 addr r-w-x x86)))
;;                    (posp n-1) (posp n-2) (integerp addr))
;;               (subset-p (mv-nth 1 (las-to-pas n-2 addr r-w-x x86))
;;                         (mv-nth 1 (las-to-pas n-1 addr r-w-x x86))))
;;      :hints (("Goal" :in-theory (e/d* (subset-p) ())))))

;;   (local
;;    (defthmd mv-nth-1-las-to-pas-subset-p-helper-2
;;      (implies
;;       (and (signed-byte-p 48 addr-1)
;;            (< (+ addr-1 n-2) (+ addr-1 n-1))
;;            (not (mv-nth 0 (las-to-pas (+ -1 n-1) (+ 1 addr-1) r-w-x x86)))
;;            (integerp n-1)
;;            (< 0 n-2))
;;       (subset-p (mv-nth 1 (las-to-pas n-2 addr-1 r-w-x x86))
;;                 (cons (mv-nth 1 (ia32e-la-to-pa addr-1 r-w-x x86))
;;                       (mv-nth 1
;;                               (las-to-pas (+ -1 n-1)
;;                                           (+ 1 addr-1)
;;                                           r-w-x x86)))))
;;      :hints (("Goal"
;;               :do-not-induct t
;;               :use ((:instance mv-nth-1-las-to-pas-subset-p-helper-1
;;                                (addr addr-1)))
;;               :expand ((las-to-pas n-1 addr-1 r-w-x x86))
;;               :in-theory (e/d* (las-to-pas subset-p) ())))))

;;   (defthm mv-nth-1-las-to-pas-subset-p
;;     (implies (and (<= addr-1 addr-2)
;;                   (< (+ n-2 addr-2) (+ n-1 addr-1))
;;                   (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
;;                   (posp n-1) (posp n-2) (integerp addr-2))
;;              (subset-p (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x x86))
;;                        (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x x86))))
;;     :hints (("Goal" :in-theory (e/d* (mv-nth-1-las-to-pas-subset-p-helper-2 subset-p)
;;                                      ())))))

(encapsulate
  ()

  (local
   (defthmd mv-nth-1-las-to-pas-subset-p-helper-1
     (implies (and (<= n-2 n-1)
                   (not (mv-nth 0 (las-to-pas n-1 addr r-w-x x86)))
                   (integerp n-1))
              (subset-p (mv-nth 1 (las-to-pas n-2 addr r-w-x x86))
                        (mv-nth 1 (las-to-pas n-1 addr r-w-x x86))))
     :hints (("Goal" :in-theory (e/d* (subset-p las-to-pas) ())))))

  (local
   (defthmd mv-nth-1-las-to-pas-subset-p-helper-2
     (implies
      (and (64-bit-modep x86) ; added
           (<= (+ addr-1 n-2) (+ addr-1 n-1))
           (not (mv-nth 0 (las-to-pas (+ -1 n-1) (+ 1 addr-1) r-w-x x86)))
           (integerp n-1))
      (subset-p (mv-nth 1 (las-to-pas n-2 addr-1 r-w-x x86))
                (cons (mv-nth 1 (ia32e-la-to-pa addr-1 r-w-x x86))
                      (mv-nth 1
                              (las-to-pas (+ -1 n-1)
                                          (+ 1 addr-1)
                                          r-w-x x86)))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance mv-nth-1-las-to-pas-subset-p-helper-1
                               (addr addr-1)))
              :expand ((las-to-pas n-1 addr-1 r-w-x x86))
              :in-theory (e/d* (las-to-pas subset-p) ())))))

  (defthm mv-nth-1-las-to-pas-subset-p
    (implies (and (64-bit-modep x86) ; added
                  (<= addr-1 addr-2)
                  (<= (+ n-2 addr-2) (+ n-1 addr-1))
                  (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                  (integerp n-1) (integerp addr-2))
             (subset-p (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x x86))
                       (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (las-to-pas
                                      mv-nth-1-las-to-pas-subset-p-helper-2
                                      subset-p)
                                     ())))))

;; ======================================================================

;; Lemmas to aid in inferring disjointness of las-to-pas and
;; translation-governing addresses:

(local
 (defthmd mv-nth-0-las-to-pas-subset-p-helper
   ;; This is a pretty expensive rule --- a more general version of
   ;;  mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free.
   (implies (and (equal addr-1 addr-2)
                 (<= (+ n-2 addr-2) (+ n-1 addr-1))
                 (integerp n-1)
                 (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x (double-rewrite x86)))))
            (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                   nil))
   :hints (("Goal" :in-theory (e/d* (subset-p) ())))))

(defthmd mv-nth-0-las-to-pas-subset-p
  ;; This is a pretty expensive rule --- a more general version of
  ;;  mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free.
  (implies (and (bind-free
                 (find-l-addrs-from-las-to-pas '(n-1 addr-1) r-w-x mfc state)
                 (n-1 addr-1))
                (64-bit-modep x86) ; added
                (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x (double-rewrite x86))))
                (<= (+ n-2 addr-2) (+ n-1 addr-1))
                (<= addr-1 addr-2)
                (integerp addr-2) (integerp n-1))
           (equal (mv-nth 0 (las-to-pas n-2 addr-2 r-w-x x86))
                  nil))
  :hints (("Goal"
           :use ((:instance mv-nth-0-las-to-pas-subset-p-helper))
           :in-theory (e/d* (subset-p) ()))))

(defthm program-at-implies-error-free-address-translation
  (implies (and (program-at prog-addr bytes x86)
                (not (app-view x86)))
           (equal (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86)) nil))
  :hints (("Goal" :in-theory (e/d* (program-at rb) (force (force))))))

(defthm no-errors-when-translating-program-bytes-in-marking-view
  ;; This rule will help in fetching instruction bytes given relevant
  ;; information about the program (using program-at).

  ;; If I use (not (mv-nth 0 (las-to-pas n-bytes prog-addr :x x86)))
  ;; instead of (program-at prog-addr bytes x86) hypothesis below, this
  ;; rule would become as horrendously expensive.

  (implies (and (bind-free
                 (find-program-at-info 'prog-addr 'bytes mfc state)
                 (prog-addr bytes))
                (64-bit-modep x86) ; added
                (program-at prog-addr bytes x86)

                ;; We don't need the following hypothesis because we
                ;; have program-at-implies-error-free-address-translation.
                ;; (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86)))

                ;; <n,addr> is a subset of <(len bytes),prog-addr>.
                (<= prog-addr addr)
                (< (+ n addr) (+ (len bytes) prog-addr))
                (posp n) (canonical-address-p addr)
                (not (app-view x86)))
           (equal (mv-nth 0 (las-to-pas n addr :x x86)) nil))
  :hints (("Goal"
           :use ((:instance program-at-implies-error-free-address-translation)
                 (:instance mv-nth-0-las-to-pas-subset-p
                            (n-1 (len bytes)) (addr-1 prog-addr)
                            (n-2 n) (addr-2 addr)
                            (r-w-x :x)))
           :in-theory (e/d* (program-at
                             signed-byte-p)
                            (program-at-implies-error-free-address-translation)))))

(defthm mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
  ;; This rule is tailored to rewrite
  ;; (disjoint-p (mv-nth 1 (las-to-pas n addr r-w-x x86))
  ;;             other-p-addrs)
  ;; to t, given that <n,addr> is a subset of <prog-len, prog-addr>.

  ;; Disjointness of l-addrs with other addresses should be expressed
  ;; in terms of disjoint-p$.
  (implies
   (and
    (bind-free (find-l-addrs-from-las-to-pas '(prog-len prog-addr) r-w-x mfc state)
               (prog-len prog-addr))
    (64-bit-modep x86) ; added
    ;; Note: This is in terms of disjoint-p$.
    (disjoint-p$
     (mv-nth 1 (las-to-pas prog-len prog-addr r-w-x (double-rewrite x86)))
     other-p-addrs)
    (not (mv-nth 0 (las-to-pas prog-len prog-addr r-w-x (double-rewrite x86))))
    ;; <n,addr> is a non-strict subset of <prog-len,prog-addr>.
    (<= (+ n addr) (+ prog-len prog-addr))
    (<= prog-addr addr)
    (posp prog-len) (posp n) (integerp addr))
   (disjoint-p (mv-nth 1 (las-to-pas n addr r-w-x x86))
               other-p-addrs))
  :hints
  (("Goal"
    :in-theory (e/d* (disjoint-p disjoint-p$ subset-p member-p las-to-pas)
                     (mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)))))

(defthm disjoint-p-all-xlation-governing-entries-paddrs-subset-p
  (implies
   (and
    (bind-free (find-l-addrs-from-fn
                'all-xlation-governing-entries-paddrs
                'n-2 'lin-addr-2 mfc state)
               (n-2 lin-addr-2))
    (disjoint-p$ other-p-addrs
                 (all-xlation-governing-entries-paddrs
                  n-2 lin-addr-2 (double-rewrite x86)))
    ;; <n-1,lin-addr-1> is a non-strict subset of <n-2,lin-addr-2>.
    (< (+ n-1 lin-addr-1) (+ n-2 lin-addr-2))
    (<= lin-addr-2 lin-addr-1)
    (posp n-2) (integerp lin-addr-1) (integerp lin-addr-2))
   (disjoint-p other-p-addrs
               (all-xlation-governing-entries-paddrs n-1 lin-addr-1 x86)))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    member-p
                                    disjoint-p
                                    disjoint-p$
                                    all-xlation-governing-entries-paddrs)
                                   ()))))

;; (defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses
;;   (implies (and
;;             (or
;;              (disjoint-p
;;               x
;;               (open-qword-paddr-list
;;                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
;;              (disjoint-p$
;;               x
;;               (open-qword-paddr-list
;;                (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
;;             (canonical-address-p addr)
;;             (canonical-address-p (+ -1 n addr)))
;;            (disjoint-p
;;             x
;;             (all-xlation-governing-entries-paddrs n addr x86)))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance all-xlation-governing-entries-paddrs-subset-of-paging-structures)
;;                  (:instance disjoint-p-subset-p
;;                             (x x)
;;                             (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
;;                             (a x)
;;                             (b (all-xlation-governing-entries-paddrs n addr x86))))
;;            :in-theory (e/d* (disjoint-p-commutative disjoint-p$)
;;                             (all-xlation-governing-entries-paddrs-subset-of-paging-structures
;;                              disjoint-p-subset-p))))
;;   :rule-classes :rewrite)

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
  (implies (and
            (disjoint-p
             x
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (canonical-address-p addr)
            (canonical-address-p (+ -1 n addr)))
           (disjoint-p
            x
            (all-xlation-governing-entries-paddrs n addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance all-xlation-governing-entries-paddrs-subset-of-paging-structures)
                 (:instance disjoint-p-subset-p
                            (x x)
                            (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                            (a x)
                            (b (all-xlation-governing-entries-paddrs n addr x86))))
           :in-theory (e/d* (disjoint-p-commutative disjoint-p$)
                            (all-xlation-governing-entries-paddrs-subset-of-paging-structures
                             disjoint-p-subset-p))))
  :rule-classes :rewrite)

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
  (implies (and
            (disjoint-p$
             x
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (canonical-address-p addr)
            (canonical-address-p (+ -1 n addr)))
           (disjoint-p
            x
            (all-xlation-governing-entries-paddrs n addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p$)
                            (all-xlation-governing-entries-paddrs-subset-of-paging-structures
                             disjoint-p-subset-p))))
  :rule-classes :rewrite)

(define find-l-addrs-from-disjoint-p$-of-two-las-to-pas-aux ((vars-1 true-listp)
                                                             (vars-2 true-listp)
                                                             calls)
  :guard (and (equal (len vars-1) (len vars-2))
              (equal (len vars-1) 2))
  (if (atom calls)
      nil
    (b* ((one-call (car calls))
         ((unless (and (true-listp one-call) (equal 3 (len one-call))))
          ;; (cw "~%One-call: ~p0~%" one-call)
          nil)
         (mv-nth-term-1 (nth 1 one-call))
         (mv-nth-term-2 (nth 2 one-call))
         ((unless (and (true-listp mv-nth-term-1) (equal 3 (len mv-nth-term-1))
                       (true-listp mv-nth-term-2) (equal 3 (len mv-nth-term-2))))
          ;; (cw "~%mv-nth-term-1: ~p0 mv-nth-term-2: ~p1~%" mv-nth-term-1 mv-nth-term-2)
          nil)
         (term-1 (nth 2 mv-nth-term-1))
         (term-2 (nth 2 mv-nth-term-2))
         ((unless (and (true-listp term-1) (equal 5 (len term-1))
                       (true-listp term-2) (equal 5 (len term-2))))
          ;; (cw "~%term-1: ~p0 term-2: ~p1~%" term-1 term-2)
          nil)
         ((list n-var-1 addr-var-1) vars-1)
         ((list n-var-2 addr-var-2) vars-2))
      (cons (list (cons n-var-1    (nth 1 term-1))
                  (cons addr-var-1 (nth 2 term-1))
                  (cons n-var-2    (nth 1 term-2))
                  (cons addr-var-2 (nth 2 term-2)))
            (find-l-addrs-from-disjoint-p$-of-two-las-to-pas-aux vars-1 vars-2 (cdr calls))))))

(defun find-l-addrs-from-disjoint-p$-of-two-las-to-pas
    (vars-1 r-w-x-1 vars-2 r-w-x-2 mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  ;; Narrows the matches by looking at only those calls of las-to-pas
  ;; which have "r-w-x" in the permission field.
  (b* ((calls (acl2::find-matches-list
               `(disjoint-p$ (mv-nth 1 (las-to-pas n-1 addr-1 ,r-w-x-1 x86-1))
                             (mv-nth 1 (las-to-pas n-2 addr-2 ,r-w-x-2 x86-2)))
               (acl2::mfc-clause mfc) nil))
       ((when (not calls))
        ;; Term not encountered.
        nil))
    (find-l-addrs-from-disjoint-p$-of-two-las-to-pas-aux vars-1 vars-2 calls)))

(defthm two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
  (implies
   (and
    (bind-free (find-l-addrs-from-disjoint-p$-of-two-las-to-pas
                '(n-1 lin-addr-1) r-w-x-1 '(n-2 lin-addr-2) r-w-x-2 mfc state)
               (n-1 lin-addr-1 n-2 lin-addr-2))
    (64-bit-modep x86) ; added
    (disjoint-p$
     (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1  (double-rewrite x86)))
     (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x-2  (double-rewrite x86))))
    ;; <ns-1,addr-1> is a non-strict subset of <n-1,lin-addr-1>.
    (<= (+ ns-1 addr-1) (+ n-1 lin-addr-1))
    (<= lin-addr-1 addr-1)
    ;; <ns-2,addr-2> is a non-strict subset of <n-2,lin-addr-2>.
    (<= (+ ns-2 addr-2) (+ n-2 lin-addr-2))
    (<= lin-addr-2 addr-2)
    (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 r-w-x-1 x86)))
    (not (mv-nth 0 (las-to-pas n-2 lin-addr-2 r-w-x-2 x86)))
    (posp n-1) (posp n-2) (integerp addr-1) (integerp addr-2))
   (disjoint-p
    (mv-nth 1 (las-to-pas ns-1 addr-1 r-w-x-1 x86))
    (mv-nth 1 (las-to-pas ns-2 addr-2 r-w-x-2 x86))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance mv-nth-1-las-to-pas-subset-p
                            (n-1 n-1) (addr-1 lin-addr-1)
                            (n-2 ns-1) (addr-2 addr-1)
                            (r-w-x r-w-x-1))
                 (:instance mv-nth-1-las-to-pas-subset-p
                            (n-1 n-2) (addr-1 lin-addr-2)
                            (n-2 ns-2) (addr-2 addr-2)
                            (r-w-x r-w-x-2))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 x86)))
                            (y (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x-2 x86)))
                            (a (mv-nth 1 (las-to-pas ns-1 addr-1 r-w-x-1 x86)))
                            (b (mv-nth 1 (las-to-pas ns-2 addr-2 r-w-x-2 x86)))))
           :in-theory (e/d* (disjoint-p$)
                            (mv-nth-1-las-to-pas-subset-p
                             disjoint-p-subset-p)))))

(define find-first-arg-of-disjoint-p$-candidates (var calls)
  (if (atom calls)
      nil
    (b* ((one-call (car calls))
         ((unless (and (true-listp one-call) (equal 3 (len one-call))))
          ;; (cw "~%One-call: ~p0~%" one-call)
          nil)
         (term-1 (nth 1 one-call)))
      (cons (list (cons var term-1))
            (find-first-arg-of-disjoint-p$-candidates var (cdr calls))))))

(defun find-first-arg-of-disjoint-p$-for-all-paging-structures (var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-matches-list
               `(disjoint-p$ x (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86-var)))
               (acl2::mfc-clause mfc) nil))
       ((when (not calls))
        ;; Term not encountered.
        nil))
    (find-first-arg-of-disjoint-p$-candidates var calls)))

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
  (implies
   (and
    (bind-free (find-first-arg-of-disjoint-p$-for-all-paging-structures
                'x mfc state)
               (x))
    (subset-p y x)
    (disjoint-p$ x
                 (open-qword-paddr-list
                  (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
   (disjoint-p y
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$
                                    disjoint-p
                                    subset-p
                                    infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2)
                                   ())))
  :rule-classes :rewrite)

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p
  ;; This rule is meant to apply only during instruction fetches.
  (implies
   (and
    (bind-free (find-program-at-info 'super-addr 'bytes mfc state)
               (super-addr bytes))
    (64-bit-modep x86) ; added
    ;; I don't need the following program-at hyp, but it makes searching
    ;; for free vars more efficient.
    (program-at super-addr bytes x86)
    (disjoint-p$
     (mv-nth 1 (las-to-pas (len bytes) super-addr :x (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (mv-nth 0 (las-to-pas (len bytes) super-addr :x (double-rewrite x86))))
    ;; Both <n-1,lin-addr-1> and <n-2,lin-addr-2> are non-strict subsets of
    ;; <(len bytes),super-addr>.
    (<= (+ n-1 lin-addr-1) (+ (len bytes) super-addr))
    (<= (+ n-2 lin-addr-2) (+ (len bytes) super-addr))
    (<= super-addr lin-addr-1)
    (<= super-addr lin-addr-2)
    (canonical-address-p super-addr)
    (canonical-address-p (+ -1 (len bytes) super-addr))
    (posp (len bytes))
    (posp n-1) (integerp lin-addr-1) (integerp lin-addr-2))
   (disjoint-p
    (mv-nth 1 (las-to-pas n-1 lin-addr-1 :x x86))
    (all-xlation-governing-entries-paddrs n-2 lin-addr-2 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p$ subset-p)
                            (disjoint-p-subset-p
                             mv-nth-1-las-to-pas-subset-p
                             all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                             las-to-pas))
           :use ((:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas (len bytes) super-addr :x x86)))
                            (y (all-xlation-governing-entries-paddrs (len bytes) super-addr x86))
                            (a (mv-nth 1 (las-to-pas n-1 lin-addr-1 :x x86)))
                            (b (all-xlation-governing-entries-paddrs n-2 lin-addr-2 x86)))
                 (:instance mv-nth-1-las-to-pas-subset-p
                            (n-1 (len bytes)) (addr-1 super-addr)
                            (n-2 n-1) (addr-2 lin-addr-1)
                            (r-w-x :x))
                 (:instance all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                            (n-1 n-2) (addr-1 lin-addr-2)
                            (n-2 (len bytes)) (addr-2 super-addr)))))

  :rule-classes :rewrite)

;; ======================================================================

;; Commuting physical memory writes with page table traversals:

(encapsulate
  ()

  ;; The book page-walk-side-effects.lisp characterizes the effects of
  ;; a page walk in terms of EQUAL instead of XLATE-EQUIV-MEMORY,
  ;; which is an aberration for this library.  However, this
  ;; characterization is useful in proving theorems like
  ;; xw-mem-and-ia32e-la-to-pa-page-table-commute.  We include this
  ;; book locally so that EQUAL doesn't pollute our canonical forms
  ;; that rely on XLATE-EQUIV-MEMORY.

  (local (include-book "page-walk-side-effects"))

  (defthm xw-mem-and-ia32e-la-to-pa-page-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-table
                lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-table
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (bitops::logand-with-negated-bitmask)))))


  (defthm xw-mem-and-ia32e-la-to-pa-page-directory-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value
                        (mv-nth 2 (ia32e-la-to-pa-page-directory
                                   lin-addr
                                   base-addr u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-directory
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal"
             :in-theory (e/d* ()
                              (bitops::logand-with-negated-bitmask
                               |(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|)))))

  (defthm xw-mem-and-ia32e-la-to-pa-page-dir-ptr-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
                                      bitops::logand-with-negated-bitmask)))))

  (defthm xw-mem-and-ia32e-la-to-pa-pml4-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                                    lin-addr base-addr
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-pml4-table
                               lin-addr base-addr
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
                                      bitops::logand-with-negated-bitmask)))))

  (defthm xw-mem-and-ia32e-la-to-pa-commute
    (implies (and (disjoint-p
                   (list index)
                   (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                  (canonical-address-p lin-addr)
                  (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value
                        (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x
                                              (xw :mem index value x86))))))

  (local
   (define xw-mem-and-las-to-pas-commute-ind-hint
     (n lin-addr r-w-x index value x86)
     :enabled t
     :verify-guards nil
     (if (zp n)
         (mv t nil n lin-addr r-w-x index value x86)
       (b* (((unless (canonical-address-p lin-addr))
             (mv t nil n lin-addr r-w-x index value x86))
            ((mv flg p-addr x86)
             (ia32e-la-to-pa lin-addr r-w-x x86))
            ((when flg) (mv flg nil n lin-addr r-w-x index value x86))
            ((mv flgs p-addrs n lin-addr r-w-x index value x86)
             (xw-mem-and-las-to-pas-commute-ind-hint
              (1- n) (1+ lin-addr) r-w-x index value x86)))
         (mv flgs (if flgs nil (cons p-addr p-addrs)) n lin-addr r-w-x index value x86)))))


  (defthm xw-mem-and-las-to-pas-commute
    (implies
     (and (64-bit-modep x86) ; added
          (disjoint-p (list index)
                      (all-xlation-governing-entries-paddrs
                       n lin-addr (double-rewrite x86)))
          (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
          (x86p x86) (integerp index) (unsigned-byte-p 8 value))
     (equal (xw :mem index value (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
            (mv-nth 2 (las-to-pas n lin-addr r-w-x (xw :mem index value x86)))))
    :hints
    (("Goal"
      :induct (xw-mem-and-las-to-pas-commute-ind-hint
               n lin-addr r-w-x index value x86)
      :in-theory (e/d* (disjoint-p
                        las-to-pas
                        member-p
                        all-xlation-governing-entries-paddrs
                        signed-byte-p)
                       (mv-nth-2-ia32e-la-to-pa-in-terms-of-updates-no-errors)))))

  ) ;; End of encapsulate ;

(defthm write-to-physical-memory-and-mv-nth-2-ia32e-la-to-pa-commute
  (implies (and (disjoint-p
                 p-addrs
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-listp p-addrs)
                (x86p x86))
           (equal (write-to-physical-memory
                   p-addrs value (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (mv-nth 2 (ia32e-la-to-pa
                             lin-addr r-w-x
                             (write-to-physical-memory p-addrs value (double-rewrite x86))))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs value x86)
           :in-theory (e/d* (disjoint-p) ()))))

(defthm write-to-physical-memory-and-mv-nth-2-las-to-pas-commute
  (implies
   (and (64-bit-modep x86) ; added
        (disjoint-p p-addrs
                    (all-xlation-governing-entries-paddrs
                     n lin-addr (double-rewrite x86)))
        (physical-address-listp p-addrs)
        (x86p x86))
   (equal
    (write-to-physical-memory p-addrs value (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
    (mv-nth 2 (las-to-pas n lin-addr r-w-x
                          (write-to-physical-memory p-addrs value (double-rewrite x86))))))
  :hints
  (("Goal" :induct (cons (las-to-pas n lin-addr r-w-x x86)
                         (write-to-physical-memory p-addrs value x86))
    :in-theory (e/d* (disjoint-p las-to-pas all-xlation-governing-entries-paddrs) ()))))

;; ======================================================================
