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
(include-book "paging-basics" :ttags :all)
(include-book "../bind-free-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

(local (xdoc::set-default-parents gather-paging-structures))

;; ======================================================================

;; Defining xlation-governing-entries-paddrs of linear addresses:

(defthm |(logand -4096 base-addr) = base-addr when low 12 bits are 0|
  (implies (and (equal (loghead 12 base-addr) 0)
                (physical-address-p base-addr))
           (equal (logand -4096 base-addr) base-addr))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                    bitops::ihsext-inductions)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm page-present=0-and-paging-entry-no-page-fault-p
  (implies
   (equal (page-present entry) 0)
   (equal (mv-nth 0
                  (paging-entry-no-page-fault-p
                   structure-type lin-addr
                   entry u-s-acc r/w-acc x/d-acc wp
                   smep smap ac nxe r-w-x cpl x86 ignored))
          t))
  :hints
  (("Goal"
    :in-theory (e/d* (paging-entry-no-page-fault-p
                      page-fault-exception page-present)
                     ()))))

(defthm page-size=1-and-paging-entry-no-page-fault-p-for-structure-type=3
  (implies
   (equal (page-size entry) 1)
   (equal (mv-nth 0
                  (paging-entry-no-page-fault-p
                   3 lin-addr
                   entry u-s-acc r/w-acc x/d-acc wp
                   smep smap ac nxe r-w-x cpl x86 ignored))
          t))
  :hints
  (("Goal"
    :in-theory (e/d* (paging-entry-no-page-fault-p
                      page-fault-exception page-size)
                     ()))))

;; Note that xlation-governing-entries-paddrs-* do not talk about
;; validity of paging entries.

(define xlation-governing-entries-paddrs-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :ignore-ok t

  (b* ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr)))
    ;; 4K pages
    (addr-range 8 page-table-entry-addr))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86)))))

  (defthm xlation-governing-entries-paddrs-for-page-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     ()))))

  (defthm ia32e-la-to-pa-page-table-values-and-xw-mem-not-member
    (implies (and (not (member-p index
                                 (xlation-governing-entries-paddrs-for-page-table
                                  lin-addr base-addr (double-rewrite x86))))
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table disjoint-p member-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x))))))

(define xlation-governing-entries-paddrs-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (page-size page-directory-entry) 1))
       ((when pde-ps?)
        (addr-range 8 page-directory-entry-addr))

       ;; 4K pages:
       (page-table-base-addr
        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-addresses
        (xlation-governing-entries-paddrs-for-page-table
         lin-addr page-table-base-addr x86)))

    (append
     (addr-range 8 page-directory-entry-addr) page-table-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-directory-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm xlation-governing-entries-paddrs-for-page-directory-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm ia32e-la-to-pa-page-directory-values-and-xw-mem-not-member
    (implies (and (not (member-p index
                                 (xlation-governing-entries-paddrs-for-page-directory
                                  lin-addr
                                  base-addr (double-rewrite x86))))
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-directory
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (page-size page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
        (addr-range 8 page-dir-ptr-table-entry-addr))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
        (xlation-governing-entries-paddrs-for-page-directory
         lin-addr page-directory-base-addr x86)))

    (append (addr-range 8 page-dir-ptr-table-entry-addr) page-directory-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-directory)))))

  (defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-directory)))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))
       (pml4te-ps? (equal (page-size pml4-entry) 1))

       ((when pml4te-ps?) (addr-range 8 pml4-entry-addr))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
        (xlation-governing-entries-paddrs-for-page-dir-ptr-table
         lin-addr ptr-table-base-addr x86)))

    (append (addr-range 8 pml4-entry-addr) ptr-table-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-pml4-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm xlation-governing-entries-paddrs-for-pml4-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-dir-ptr-table)))))

  (defthm ia32e-la-to-pa-pml4-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('xlation-governing-entries-paddrs') returns a
  @('true-listp') of physical addresses that govern the translation of
  a linear address @('lin-addr') to its corresponding physical address
  @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

<ol>
<li>The addresses of the relevant PML4 entry</li>

<li>The addresses of the relevant PDPT entry</li>

<li>The addresses of the relevant PD entry</li>

<li>The addresses of the relevant PT entry</li>

</ol>"

  :guard (not (xr :app-view 0 x86))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-pml4-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (if (mbt (not (app-view x86)))
      (b* ((cr3       (ctri *cr3* x86))
           ;; PML4 Table:
           (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

        (xlation-governing-entries-paddrs-for-pml4-table
         lin-addr pml4-base-addr x86))
    nil)

  ///

  (defthm xlation-governing-entries-paddrs-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (xlation-governing-entries-paddrs lin-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm xlation-governing-entries-paddrs-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs lin-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal"
             :in-theory (e/d* () (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm ia32e-la-to-pa-values-and-xw-mem-not-member
    (implies (and (not (member-p index (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm xlation-governing-entries-paddrs-and-!flgi
    (equal (xlation-governing-entries-paddrs lin-addr (!flgi index value x86))
           (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (!flgi) (xlation-governing-entries-paddrs force (force))))))

  (defthm xlation-governing-entries-paddrs-and-!flgi-undefined
    (equal (xlation-governing-entries-paddrs lin-addr (!flgi-undefined index x86))
           (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (xlation-governing-entries-paddrs force (force))))))

  (defthm xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint
    (implies (and (disjoint-p (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)) p-addrs)
                  (physical-address-listp p-addrs))
             (equal (xlation-governing-entries-paddrs lin-addr (write-to-physical-memory p-addrs bytes x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal" :induct (write-to-physical-memory p-addrs bytes x86)
             :in-theory (e/d* (disjoint-p disjoint-p-commutative) (xlation-governing-entries-paddrs))))))

(define all-xlation-governing-entries-paddrs
  ((n        natp)
   (lin-addr canonical-address-p)
   x86)
  :guard (and (not (xr :app-view 0 x86))
              (canonical-address-p (+ n lin-addr)))
  :guard-hints (("Goal" :in-theory (e/d* (signed-byte-p) ())))
  :enabled t
  (if (zp n)
      nil
    (append (xlation-governing-entries-paddrs lin-addr x86)
            (all-xlation-governing-entries-paddrs (1- n) (1+ lin-addr) x86)))
  ///

  (defthm all-xlation-governing-entries-paddrs-and-zero-bytes
    (equal (all-xlation-governing-entries-paddrs 0 lin-addr x86) nil))

  (local
   (defthm xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs-helper
     (implies (and (integerp n) (< 0 n))
              (subset-p (xlation-governing-entries-paddrs a x86)
                        (all-xlation-governing-entries-paddrs n a x86)))
     :hints (("Goal" :expand (all-xlation-governing-entries-paddrs n a x86)))))

  (defthm xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
    (implies (and (<= addr a) (< a (+ n addr))
                  (posp n) (integerp a) (integerp addr))
             (equal (subset-p (xlation-governing-entries-paddrs a x86)
                              (all-xlation-governing-entries-paddrs n addr x86))
                    t))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
    (implies
     (and (<= addr-2 addr-1)
          (<= (+ n-1 addr-1) (+ n-2 addr-2))
          (posp n-2) (integerp addr-1) (integerp addr-2))
     (equal
      (subset-p (all-xlation-governing-entries-paddrs n-1 addr-1 x86)
                (all-xlation-governing-entries-paddrs n-2 addr-2 x86))
      t))
    :hints (("Goal" :in-theory (e/d* (subset-p member-p) ()))))

  (defthm all-xlation-governing-entries-paddrs-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (all-xlation-governing-entries-paddrs n addr (xw fld index value x86))
                    (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs)))))

  (defthm all-xlation-governing-entries-paddrs-and-xw-mem-not-member
    (implies (not (member-p index (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
             (equal (all-xlation-governing-entries-paddrs n addr (xw :mem index value x86))
                    (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs)))))

  (defthm all-xlation-governing-entries-paddrs-and-!flgi
    (equal (all-xlation-governing-entries-paddrs n addr (!flgi index value x86))
           (all-xlation-governing-entries-paddrs n addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs force (force))))))

  (defthm all-xlation-governing-entries-paddrs-and-!flgi-undefined
    (equal (all-xlation-governing-entries-paddrs n addr (!flgi-undefined index x86))
           (all-xlation-governing-entries-paddrs n addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs force (force)))))))

;; ======================================================================

(local
 (defthmd disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-helper
   (implies
    (and
     (disjoint-p
      (all-xlation-governing-entries-paddrs n a (double-rewrite x86))
      other-p-addrs)
     (posp n) (integerp a))
    (disjoint-p (xlation-governing-entries-paddrs a x86)
                other-p-addrs))
   :hints (("Goal" :in-theory (e/d* (member-p) ())))))

(defthm disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs
  (implies
   (and
    (bind-free
     (find-l-addrs-from-fn 'all-xlation-governing-entries-paddrs 'n 'addr mfc state)
     (n addr))
    (disjoint-p
     (all-xlation-governing-entries-paddrs n addr (double-rewrite x86))
     other-p-addrs)
    (<= addr a) (< a (+ n addr))
    (posp n) (integerp a) (integerp addr))
   (disjoint-p (xlation-governing-entries-paddrs a x86)
               other-p-addrs))
  :hints (("Goal" :use ((:instance disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-helper)))))

(defthm disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
  ;; TODO Very expensive because of the bind-frees!
  (implies
   (and
    (bind-free
     (find-l-addrs-from-fn
      'all-xlation-governing-entries-paddrs 'n-2 'addr-2 mfc state)
     (n-2 addr-2))
    (bind-free
     (find-arg-of-fn 'disjoint-p 2 'other-p-addrs mfc state)
     (other-p-addrs))
    (disjoint-p (all-xlation-governing-entries-paddrs n-2 addr-2 (double-rewrite x86))
                other-p-addrs)
    (subset-p other-p-addrs-subset other-p-addrs)
    (<= addr-2 addr-1)
    (< (+ n-1 addr-1) (+ n-2 addr-2))
    (posp n-2) (integerp addr-1) (integerp addr-2))
   (disjoint-p (all-xlation-governing-entries-paddrs n-1 addr-1 x86)
               other-p-addrs-subset))
  :hints
  (("Goal" :in-theory (e/d* (subset-p member-p)
                            (xlation-governing-entries-paddrs)))))

;; ======================================================================

;; Other misc. events:

(defthm ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p p-addrs (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (physical-address-listp p-addrs)
                (canonical-address-p lin-addr))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p) (xlation-governing-entries-paddrs)))))

(defthm rm-low-64-and-paging-entry-no-page-fault-p
  (equal (rm-low-64 index
                    (mv-nth
                     2
                     (paging-entry-no-page-fault-p structure-type lin-addr
                                                   entry u/s-acc r/w-acc x/d-acc wp smep
                                                   smap ac nxe r-w-x cpl x86 ignored)))
         (rm-low-64 index x86))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32) ()))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-wm-low-64
  (equal (mv-nth
          0
          (paging-entry-no-page-fault-p
           structure-type lin-addr
           entry u/s-acc r/w-acc x/d-acc
           wp smep smap ac nxe r-w-x cpl
           (wm-low-64 index value x86)
           ignored))
         (mv-nth
          0
          (paging-entry-no-page-fault-p
           structure-type lin-addr
           entry u/s-acc r/w-acc x/d-acc
           wp smep smap ac nxe r-w-x cpl
           x86
           ignored)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-and-wm-low-64-if-no-error
  (implies (not (mv-nth
                 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl x86 ignored)))
           (equal (mv-nth
                   2
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr
                    entry u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    (wm-low-64 index value x86)
                    ignored))
                  (wm-low-64 index value x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p) ()))))


(defthm mv-nth-0-paging-entry-no-page-fault-p-and-write-to-physical-memory
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  (write-to-physical-memory p-addrs bytes x86)
                  ignored))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86 ignored)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-mv-nth-1-wb
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl
                  (mv-nth 1 (wb n addr w value x86))
                  access-type))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl x86
                  access-type)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-table-values-and-write-to-translation-governing-address
  ;; Similar lemmas can be found in proofs/zero-copy/zero-copy.lisp.
  (b* ((p-addrs (xlation-governing-entries-paddrs-for-page-table
                 lin-addr base-addr x86))
       (page-table-entry (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86)))
    (implies (and (not (mv-nth 0
                               (ia32e-la-to-pa-page-table
                                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (page-present page-table-entry)
                         (page-present value))
                  (equal (page-read-write page-table-entry)
                         (page-read-write value))
                  (equal (page-user-supervisor page-table-entry)
                         (page-user-supervisor value))
                  (equal (page-execute-disable page-table-entry)
                         (page-execute-disable value))
                  (equal (page-size page-table-entry)
                         (page-size value))
                  (unsigned-byte-p 64 value)
                  (canonical-address-p lin-addr)
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (x86p x86))
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs value x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs value x86)))
                         (logior (loghead 12 lin-addr)
                                 (ash (loghead 40 (logtail 12 value))
                                      12))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
                            (entry-1
                             (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86))
                            (entry-2 value)
                            (structure-type 0)
                            (ignored 0)))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table
                             page-table-entry-addr
                             xlation-governing-entries-paddrs-for-page-table)
                            (mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
                             wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================
