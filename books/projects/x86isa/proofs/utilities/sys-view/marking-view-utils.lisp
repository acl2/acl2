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
(include-book "common-system-level-utils")
(include-book "paging/top")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(local (xdoc::set-default-parents system-level-marking-view-proof-utilities))

(define replace-element (x y lst)
  (if (atom lst)
      lst
    (if (equal (car lst) x)
        (cons y (replace-element x y (cdr lst)))
      (cons (car lst) (replace-element x y (cdr lst)))))
  ///
  (defthm true-listp-of-replace-element
    (implies (true-listp lst)
             (true-listp (replace-element x y lst)))))

;; ======================================================================

;; Combining nests of (mv-nth 2 (las-to-pas ...)) when linear
;; addresses are in sequence:

(local
 (define r-w-x-irrelevant-ind-scheme (n lin-addr r-w-x-1 r-w-x-2 x86-1 x86-2)
   :verify-guards nil
   :non-executable t
   :enabled t
   (if (or (zp n) (not (xlate-equiv-memory x86-1 x86-2)))
       (mv nil nil x86-1 x86-2)
     (b* (((unless (canonical-address-p lin-addr))
           (mv t nil x86-1 x86-2))
          ((mv flg-1 p-addr-1 x86-1)
           (ia32e-la-to-pa lin-addr r-w-x-1 x86-1))
          ((mv flg-2 p-addr-2 x86-2)
           (ia32e-la-to-pa lin-addr r-w-x-2 x86-2))
          ((unless (and (equal flg-1 flg-2)
                        (equal p-addr-1 p-addr-2)
                        (xlate-equiv-memory x86-1 x86-2)))
           (mv t nil x86-1 x86-2))
          ((when flg-1) (mv flg-1 nil x86-1 x86-2))
          ((mv flgs p-addrs x86-1 x86-2)
           (r-w-x-irrelevant-ind-scheme
            (1- n) (1+ lin-addr) r-w-x-1 r-w-x-2 x86-1 x86-2)))
       (mv flgs (if flgs nil (cons p-addr-1 p-addrs)) x86-1 x86-2)))))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-las-to-pas
                            'r-w-x-1 n lin-addr mfc state)
                           (r-w-x-1))
                (syntaxp (and (not (eq r-w-x-2 r-w-x-1))
                              ;; r-w-x-2 must be smaller than r-w-x-1.
                              (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-1 x86)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-2 x86)))
                (64-bit-modep x86))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x-2 x86))
                  (mv-nth 1 (las-to-pas n lin-addr r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* (las-to-pas) ())
           :induct (r-w-x-irrelevant-ind-scheme n lin-addr r-w-x-1 r-w-x-2 x86 x86))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x-1 x86)
                         (las-to-pas n lin-addr r-w-x-2 x86)))
            nil)))

(defthm r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-las-to-pas
                            'r-w-x-1 n lin-addr mfc state)
                           (r-w-x-1))
                (syntaxp (and (not (eq r-w-x-2 r-w-x-1))
                              ;; r-w-x-2 must be smaller than r-w-x-1.
                              (term-order r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-1 (double-rewrite x86))))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-2 (double-rewrite x86)))))
           (equal (mv-nth 2 (las-to-pas n lin-addr r-w-x-2 x86))
                  (mv-nth 2 (las-to-pas n lin-addr r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* (las-to-pas) ())
           :induct (r-w-x-irrelevant-ind-scheme n lin-addr r-w-x-1 r-w-x-2 x86 x86))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x-1 x86)
                         (las-to-pas n lin-addr r-w-x-2 x86)))
            nil)))

(defthm combine-mv-nth-2-las-to-pas-same-r-w-x
  (implies (and (equal lin-addr-2 (+ n-1 lin-addr-1))
                (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86))))
                (posp n-1) (posp n-2))
           (equal (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x
                                        (mv-nth 2 (las-to-pas n-1 lin-addr-1 r-w-x x86))))
                  (mv-nth 2 (las-to-pas (+ n-1 n-2) lin-addr-1 r-w-x x86)))
           ;; TODO: Do I need the following instead?
           ;; (equal (mv-nth 2 (las-to-pas n-1 lin-addr-1 r-w-x
           ;;                              (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x x86))))
           ;;        (mv-nth 2 (las-to-pas (+ n-1 n-2) lin-addr-1 r-w-x x86)))
           )
  :hints (("Goal" :in-theory (e/d* (las-to-pas zp) ()))))

;; ======================================================================

;; Lemmas about interaction of memory writes and paging walkers:

(defthm xr-mem-wb-in-sys-view
  (implies
   (and (disjoint-p
         (list index)
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
        (disjoint-p
         (list index)
         (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86)))
   (equal (xr :mem index (mv-nth 1 (wb n-w write-addr w value x86)))
          (xr :mem index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wb disjoint-p member-p)
                            (write-to-physical-memory
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-32-wb-in-sys-view-disjoint
  (implies (and
            (disjoint-p
             (addr-range 4 index)
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
            (disjoint-p
             (addr-range 4 index)
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (64-bit-modep (double-rewrite x86)))
           (equal (rm-low-32 index (mv-nth 1 (wb n-w write-addr w value x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-wb-in-sys-view-disjoint
  (implies (and
            (disjoint-p
             (addr-range 8 index)
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
            (disjoint-p
             (addr-range 8 index)
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (integerp index)
            (64-bit-modep (double-rewrite x86)))
           (equal (rm-low-64 index (mv-nth 1 (wb n-w write-addr w value x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rm-low-32-wb-in-sys-view-disjoint
                            (index index))
                 (:instance rm-low-32-wb-in-sys-view-disjoint
                            (index (+ 4 index))))
           :in-theory (e/d* (rm-low-64)
                            (rm-low-32-wb-in-sys-view-disjoint
                             wb (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm las-to-pas-values-and-write-to-physical-memory-disjoint
  ;; Generalization of
  ;; ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint.
  (implies
   (and (disjoint-p
         p-addrs
         (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
        (physical-address-listp p-addrs)
        (64-bit-modep (double-rewrite x86))
        (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                 (write-to-physical-memory p-addrs value x86)))
           (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
    (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                 (write-to-physical-memory p-addrs value x86)))
           (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal" :induct (las-to-pas n lin-addr r-w-x
                                      (write-to-physical-memory p-addrs value x86))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             signed-byte-p
                             all-xlation-governing-entries-paddrs)
                            (xlation-governing-entries-paddrs)))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr base-addr (double-rewrite x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0)
        (64-bit-modep (double-rewrite x86)))
   (and
    (equal (mv-nth 0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
    (equal (mv-nth 1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-table
                             xlation-governing-entries-paddrs-for-page-table
                             wb)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-directory-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYS-VIEW-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-directory
          lin-addr base-addr (double-rewrite x86)))
        (64-bit-modep (double-rewrite x86)))
   (xlate-equiv-entries
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-page-directory
                  lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0)
                (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 21)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-directory
                             xlation-governing-entries-paddrs-for-page-directory)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-dir-ptr-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYS-VIEW-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-dir-ptr-table
          lin-addr base-addr (double-rewrite x86)))
        (64-bit-modep (double-rewrite x86)))
   (xlate-equiv-entries
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (xlation-governing-entries-paddrs-for-page-dir-ptr-table
              lin-addr base-addr (double-rewrite x86)))
            (canonical-address-p lin-addr)
            (physical-address-p base-addr)
            (equal (loghead 12 base-addr) 0)
            (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 30)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))

           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-pml4-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYS-VIEW-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-pml4-table
          lin-addr base-addr (double-rewrite x86)))
        (64-bit-modep (double-rewrite x86)))
   (xlate-equiv-entries
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table
                             disjoint-p-commutative)
                            (force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (xlation-governing-entries-paddrs-for-pml4-table
              lin-addr base-addr (double-rewrite x86)))
            (canonical-address-p lin-addr)
            (physical-address-p base-addr)
            (equal (loghead 12 base-addr) 0)
            (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (double-rewrite x86))))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-pml4-table
                             xlation-governing-entries-paddrs-for-pml4-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                             (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                             (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa
                             xlation-governing-entries-paddrs)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  ;; This is a theorem that, at first glance, seems suspicious;
  ;; there's just one hypothesis --- the disjointness of the write's
  ;; physical addresses from the translation-governing addresses of
  ;; the linear region <n,lin-addr>.  All this says is: if the write
  ;; does not affect the translation-governing entries of
  ;; <n,lin-addr>, it can't change the address mapping of
  ;; <n,lin-addr>.

  ;; This is *different* from saying that after the write, a read from
  ;; <n, lin-addr> will return the same value --- for that to happen,
  ;; we need (at least) to know that the physical addresses
  ;; corresponding to <n,lin-addr> and <n-w,write-addr> are disjoint
  ;; too.
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                         (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
            (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                         (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :induct (las-to-pas n lin-addr r-w-x
                               (mv-nth 1 (wb n-w write-addr w value x86)))
           :in-theory (e/d* ()
                            (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                             wb
                             xlation-governing-entries-paddrs
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x x86)))
            nil)))

;; ======================================================================

;; Lemmas about interaction of top-level memory reads and writes:

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint
  ;; Similar to rb-wb-disjoint-in-sys-view
  (implies (and (disjoint-p
                 p-addrs
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (disjoint-p
                 p-addrs
                 (all-xlation-governing-entries-paddrs
                  n-w write-addr (double-rewrite x86)))
                (not (app-view x86))
                (64-bit-modep (double-rewrite x86)))
           (equal (read-from-physical-memory p-addrs
                                             (mv-nth 1 (wb n-w write-addr w value x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthm rb-wb-disjoint-in-sys-view
  (implies (and
            (disjoint-p
             ;; The physical addresses pertaining to the read
             ;; operation are disjoint from those pertaining to the
             ;; write operation.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
            (disjoint-p
             ;; The physical addresses corresponding to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the write.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the write are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (not (app-view x86))
            (64-bit-modep (double-rewrite x86)))
           (and
            (equal (mv-nth 0 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (rb n lin-addr r-w-x (double-rewrite x86))))
            (equal (mv-nth 1 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (rb n lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (x86-1 (mv-nth 2 (las-to-pas n-w write-addr :w x86)))
                            (x86-2 x86)))
           :in-theory (e/d* (disjoint-p-commutative)
                            (wb
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))

(defthmd rb-wb-equal-in-sys-view
  (implies (and (equal
                 ;; The physical addresses pertaining to the read
                 ;; operation are equal to those pertaining to the
                 ;; write operation.
                 (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (disjoint-p
                 ;; The physical addresses pertaining to the write are
                 ;; disjoint from the xlation-governing-entries-paddrs
                 ;; pertaining to the read.
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))

                (no-duplicates-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (unsigned-byte-p (ash n-w 3) value)
                (natp n-w)
                (64-bit-modep (double-rewrite x86))
                (x86p x86))
           (equal (mv-nth 1 (rb n lin-addr r-w-x
                                (mv-nth 1 (wb n-w write-addr w value x86))))
                  value))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* (disjoint-p-commutative) (force (force)))
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (x86-1 (mv-nth 2 (las-to-pas n-w write-addr :w x86)))
                            (x86-2 x86))))))

;; ======================================================================

(globally-disable '(rb
                    wb
                    canonical-address-p
                    program-at
                    las-to-pas
                    all-xlation-governing-entries-paddrs
                    unsigned-byte-p
                    signed-byte-p))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (riml-size
             rml-size
             wiml-size
             wml-size
             rml08 riml08 wml08 wiml08
             rml16 riml16 wml16 wiml16
             rml32 riml32 wml32 wiml32
             rml64 riml64 wml64 wiml64
             rme08 rime08 wme08 wime08 ea-to-la)
            ()))

;; ======================================================================

(defthm xlate-equiv-memory-is-equal-in-app-view
  ;; TODO: Move to paging/gather-paging-structures.lisp?
  (implies (app-view x86-1)
           (iff (xlate-equiv-memory x86-1 x86-2)
                (equal x86-1 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ()))))

(defthm xlate-equiv-memory-is-equal-in-non-64-bit-mode
  ;; TODO: Move to paging/gather-paging-structures.lisp?
  (implies (not (64-bit-modep x86-1))
           (iff (xlate-equiv-memory x86-1 x86-2)
                (equal x86-1 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ()))))

(defsection xlate-equiv-memory-and-rml08
  :parents (system-level-marking-view-proof-utilities)

  (defthmd xlate-equiv-memory-and-rvm08
    (implies (and (xr :app-view 0 (double-rewrite x86-1))
                  (xlate-equiv-memory (double-rewrite x86-1) x86-2))
             (and (equal (mv-nth 0 (rvm08 lin-addr x86-1))
                         (mv-nth 0 (rvm08 lin-addr x86-2)))
                  (equal (mv-nth 1 (rvm08 lin-addr x86-1))
                         (mv-nth 1 (rvm08 lin-addr x86-2)))))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory)
                                     (force (force))))))


  (defthm xlate-equiv-memory-and-mv-nth-0-rml08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rml08 lin-addr r-w-x x86-1))
                    (mv-nth 0 (rml08 lin-addr r-w-x x86-2))))
    :hints
    (("Goal" :cases ((xr :app-view 0 x86-1))
      :in-theory (e/d* (rml08 disjoint-p member-p)
                       (force (force)))
      :use ((:instance xlate-equiv-memory-and-rvm08))))
    :rule-classes :congruence)

  (defthmd xlate-equiv-memory-and-xr-mem-from-rest-of-memory
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'xlate-equiv-memory-and-xr-mem-from-rest-of-memory
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (not (equal x86-1 x86-2)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p (list j)
                      (open-qword-paddr-list
                       (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
          (natp j)
          (< j *mem-size-in-bytes*))
     (equal (xr :mem j x86-1) (xr :mem j x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory disjoint-p) ()))))

  (defthm xlate-equiv-memory-and-mv-nth-1-rml08
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'xlate-equiv-memory-and-mv-nth-1-rml08
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (not (equal x86-1 x86-2)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (list (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (double-rewrite x86-1))))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (equal (mv-nth 1 (rml08 lin-addr r-w-x x86-1))
            (mv-nth 1 (rml08 lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :cases ((xr :app-view 0 x86-1))
             :in-theory (e/d* (rml08
                               rb
                               disjoint-p
                               member-p
                               las-to-pas)
                              (force (force)))
             :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                              (j (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                              (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                              (x86-2 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
                   (:instance xlate-equiv-memory-and-rvm08)))))

  (defthm xlate-equiv-memory-and-two-mv-nth-2-rml08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (rml08 lin-addr r-w-x x86-1))
                                 (mv-nth 2 (rml08 lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rml08 rb) (force (force)))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-mv-nth-2-rml08
    (implies (64-bit-modep (double-rewrite x86))
             (xlate-equiv-memory (mv-nth 2 (rml08 lin-addr r-w-x x86)) x86))
    :hints (("Goal" :in-theory (e/d* (rml08 rb) (force (force)))))))

;; ======================================================================

;; Get-prefixes in system-level marking view:

(defsection get-prefixes-in-system-level-marking-view
  :parents (system-level-marking-view-proof-utilities)

  (local (in-theory (e/d* () ((tau-system) not))))

  (local
   (defthmd xr-not-mem-and-get-prefixes-in-sys-view
     (implies
      (and (not (app-view x86))
           (not (equal fld :mem))
           (not (equal fld :fault)))
      (equal (xr fld index
                 (mv-nth
                  3 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
             (xr fld index x86)))
     :hints (("Goal"
              :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
              :in-theory (e/d* (get-prefixes rml08 rb las-to-pas)
                               (rme08
                                negative-logand-to-positive-logand-with-integerp-x
                                unsigned-byte-p-of-logior
                                acl2::loghead-identity
                                not force (force)))))))

  (defthmd xr-not-mem-and-get-prefixes
    (implies
     (and (not (equal fld :mem))
          (not (equal fld :fault)))
     (equal (xr fld index (mv-nth
                           3
                           (get-prefixes
                            proc-mode start-rip prefixes rex-byte cnt x86)))
            (xr fld index x86)))
    :hints
    (("Goal"
      :cases ((app-view x86))
      :in-theory (e/d* (xr-not-mem-and-get-prefixes-in-sys-view)
                       (negative-logand-to-positive-logand-with-integerp-x
                        unsigned-byte-p-of-logior
                        acl2::loghead-identity
                        not force (force))))))

  ;; The following make-events generate a bunch of rules that together
  ;; say the same thing as xr-not-mem-and-get-prefixes, but these
  ;; rules are more efficient than xr-not-mem-and-get-prefixes as they
  ;; match less frequently.
  (make-event
   (generate-xr-over-write-thms
    (remove-elements-from-list
     '(:mem :fault)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 3
    :prepwork '((local (in-theory (e/d (xr-not-mem-and-get-prefixes) ()))))))

  (local
   (encapsulate
     ()
     (local
      (in-theory (e/d ()
                      ((:definition member-equal)
                       (:definition rme08$inline)
                       (:linear mv-nth-1-idiv-spec)
                       (:linear mv-nth-1-div-spec)
                       (:rewrite mv-nth-2-ia32e-la-to-pa-system-level-non-marking-view)
                       (:definition marking-view$inline)
                       (:type-prescription booleanp-marking-view-type)
                       (:rewrite ia32e-la-to-pa-in-app-view)
                       (:type-prescription 64-bit-modep)
                       (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                       (:rewrite two-page-walks-ia32e-la-to-pa)
                       (:rewrite xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa)
                       (:rewrite default-+-2)
                       (:rewrite default-+-1)
                       (:rewrite r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors)
                       (:type-prescription x86p)
                       (:rewrite xr-ia32e-la-to-pa)
                       (:rewrite xr-mv-nth-2-ia32e-la-to-pa-when-error)
                       (:rewrite canonical-address-p-limits-thm-3)
                       (:rewrite canonical-address-p-limits-thm-2)
                       (:rewrite canonical-address-p-limits-thm-1)
                       (:rewrite canonical-address-p-limits-thm-0)
                       (:rewrite r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
                       (:type-prescription len)
                       (:definition len)
                       (:rewrite acl2::fold-consts-in-+)
                       (:linear acl2::expt->-1)
                       (:type-prescription booleanp-app-view-type)
                       (:rewrite default-cdr)
                       (:linear ash-monotone-2)
                       (:definition rb-1)
                       (:linear member-p-pos-value)
                       (:linear member-p-pos-1-value)
                       (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-view)
                       (:rewrite acl2::zp-when-integerp)
                       (:rewrite default-<-2)
                       (:meta acl2::cancel_times-equal-correct)
                       (:meta acl2::cancel_plus-equal-correct)
                       (:rewrite acl2::zp-when-gt-0)
                       (:type-prescription member-equal)
                       (:meta acl2::cancel_plus-lessp-correct)
                       (:rewrite acl2::logtail-identity)
                       (:rewrite acl2::<-0-+-negative-1)
                       (:rewrite default-<-1)
                       (:linear ash-n-3-bound)
                       (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors)
                       (:type-prescription acl2::|x < y  =>  0 < -x+y|)
                       (:type-prescription natp-of-rb-1.val)
                       (:type-prescription integerp-of-mv-nth-1-rb-1)
                       (:rewrite 64-bit-modep-of-ia32e-la-to-pa)
                       (:type-prescription acl2::expt-type-prescription-integerp)
                       (:rewrite rb-1-returns-no-error-app-view)
                       (:rewrite unsigned-byte-p-when-cr8bits-p)
                       (:rewrite unsigned-byte-p-when-4bits-p)
                       (:type-prescription natp)
                       (:type-prescription acl2::logtail-type)
                       (:rewrite mv-nth-1-las-to-pas-when-error)
                       (:type-prescription unsigned-byte-p)
                       (:rewrite xr-mem-disjoint-ia32e-la-to-pa)
                       (:rewrite acl2::expt-with-violated-guards)
                       (:type-prescription disjoint-p)
                       (:rewrite rb-1-returns-x86-app-view)
                       (:linear size-of-rb-1)
                       (:rewrite read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa)
                       (:rewrite get-prefixes-opener-lemma-group-4-prefix)
                       (:rewrite acl2::ifix-when-not-integerp)
                       (:rewrite ea-to-la-when-64-bit-modep-and-not-fs/gs)
                       (:rewrite get-prefixes-opener-lemma-group-3-prefix)
                       (:rewrite get-prefixes-opener-lemma-group-2-prefix)
                       (:rewrite no-errors-when-translating-program-bytes-in-marking-view)
                       (:rewrite
                        all-mem-except-paging-structures-equal-aux-and-xr-mem-from-rest-of-memory)
                       (:rewrite
                        all-mem-except-paging-structures-equal-and-xr-mem-from-rest-of-memory)
                       (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
                       (:type-prescription cr8bits-p$inline)
                       (:type-prescription 4bits-p)
                       (:rewrite cr8bits-p-when-unsigned-byte-p)
                       (:rewrite 4bits-p-when-unsigned-byte-p)
                       (:rewrite rme08-when-64-bit-modep-and-fs/gs)
                       (:type-prescription acl2::expt-type-prescription-positive)
                       (:type-prescription acl2::expt-type-prescription-nonzero)
                       (:linear acl2::expt-is-increasing-for-base>1)
                       (:rewrite default-car)
                       (:rewrite disjoint-p-subset-p)
                       (:rewrite rationalp-implies-acl2-numberp)
                       (:type-prescription n08p-mv-nth-1-rvm08)
                       (:rewrite
                        get-prefixes-does-not-modify-x86-state-in-system-level-non-marking-view)
                       (:rewrite bitops::unsigned-byte-p-incr)
                       (:linear size-of-combine-bytes-of-take)
                       (:linear size-of-combine-bytes)
                       (:linear bitops::expt-2-lower-bound-by-logbitp)
                       (:rewrite get-prefixes-does-not-modify-x86-state-in-app-view)
                       (:rewrite x86p-mv-nth-2-rvm08-unchanged)
                       (:rewrite rvm08-no-error)
                       (:rewrite xr-rme08-state-sys-view)
                       (:rewrite acl2::distributivity-of-minus-over-+)
                       (:rewrite !prefixes->seg$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->seg$inline-of-8bits-fix-seg-normalize-const)
                       (:rewrite !prefixes->rep$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->rep$inline-of-8bits-fix-rep-normalize-const)
                       (:rewrite !prefixes->lck$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->lck$inline-of-8bits-fix-lck-normalize-const)
                       (:rewrite !prefixes->opr$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->opr$inline-of-8bits-fix-opr-normalize-const)
                       (:rewrite !prefixes->adr$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->adr$inline-of-8bits-fix-adr-normalize-const)
                       (:rewrite acl2::zp-open)
                       (:rewrite default-unary-minus)
                       (:rewrite !prefixes->nxt$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->nxt$inline-of-8bits-fix-nxt-normalize-const)
                       (:rewrite !prefixes->num$inline-of-prefixes-fix-x-normalize-const)
                       (:rewrite !prefixes->num$inline-of-4bits-fix-num-normalize-const)))))

     (defthmd xr-fault-and-get-prefixes-in-sys-view
       (implies
        (and (not (app-view x86))
             (canonical-address-p start-rip)
             (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
        (equal
         (xr :fault index
             (mv-nth
              3
              (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
         (xr :fault index x86)))
       :hints
       (("Goal"
         :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
         :in-theory
         (e/d*
          (get-prefixes rb las-to-pas)
          (negative-logand-to-positive-logand-with-integerp-x
           mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
           unsigned-byte-p-of-logior
           subset-p
           not force (force))))))))

  (defthm xr-fault-and-get-prefixes
    (implies
     (and (canonical-address-p start-rip)
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
     (equal
      (xr :fault index
          (mv-nth
           3
           (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
      (xr :fault index x86)))
    :hints
    (("Goal"
      :cases ((app-view x86))
      :in-theory
      (e/d*
       (xr-fault-and-get-prefixes-in-sys-view)
       (get-prefixes
        negative-logand-to-positive-logand-with-integerp-x
        mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
        unsigned-byte-p-of-logior
        subset-p
        not force (force))))))

  (defthmd get-prefixes-xw-values-in-sys-view
    (implies
     (and (not (app-view x86))
          (not (equal fld :mem))
          (not (equal fld :rflags))
          (not (equal fld :ctr))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden-base))
          (not (equal fld :seg-hidden-limit))
          (not (equal fld :seg-hidden-attr))
          (not (equal fld :msr))
          (not (equal fld :fault))
          (not (equal fld :app-view))
          (not (equal fld :marking-view)))
     (and
      (equal
       (mv-nth
        0
        (get-prefixes
         #.*64-bit-mode* start-rip prefixes rex-byte cnt
         (xw fld index value x86)))
       (mv-nth
        0
        (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt
                  (xw fld index value x86)))
       (mv-nth 1 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
      (equal
       (mv-nth 2 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt
                  (xw fld index value x86)))
       (mv-nth 2 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))))
    :hints
    (("Goal"
      :induct (get-prefixes *64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :expand (get-prefixes *64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw fld index value x86))
      :in-theory (e/d* (get-prefixes
                        rb
                        las-to-pas)
                       (rml08
                        get-prefixes-opener-lemma-no-prefix-byte
                        negative-logand-to-positive-logand-with-integerp-x
                        unsigned-byte-p-of-logior
                        acl2::ash-0
                        acl2::zip-open
                        acl2::ifix-when-not-integerp
                        acl2::loghead-identity
                        (:t bitops::logior-natp-type)
                        (:t natp-of-get-prefixes.new-prefixes)
                        (:t natp-of-get-prefixes.new-rex-byte)
                        (:t n08p-mv-nth-1-rml08)
                        force (force))))))

  (defthmd get-prefixes-xw-state-in-sys-view
    (implies
     (and (not (app-view x86))
          (not (equal fld :mem))
          (not (equal fld :rflags))
          (not (equal fld :ctr))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden-base))
          (not (equal fld :seg-hidden-limit))
          (not (equal fld :seg-hidden-attr))
          (not (equal fld :msr))
          (not (equal fld :fault))
          (not (equal fld :app-view))
          (not (equal fld :marking-view)))
     (equal
      (mv-nth 3 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                              (xw fld index value x86)))
      (xw fld index value
          (mv-nth 3 (get-prefixes
                     #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :expand (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw fld index value x86))
      :in-theory (e/d* (get-prefixes
                        las-to-pas
                        rb)
                       (rml08
                        negative-logand-to-positive-logand-with-integerp-x
                        unsigned-byte-p-of-logior
                        acl2::ash-0
                        acl2::zip-open
                        acl2::ifix-when-not-integerp
                        acl2::loghead-identity
                        (:t bitops::logior-natp-type)
                        (:t natp-of-get-prefixes.new-prefixes)
                        (:t natp-of-get-prefixes.new-rex-byte)
                        (:t n08p-mv-nth-1-rml08)
                        force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (replace-element 'proc-mode #.*64-bit-mode*
                     (acl2::formals 'get-prefixes (w state)))
    :output-index 0
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-sys-view
                                        get-prefixes-xw-state-in-sys-view)
                                       ()))))
    :hyps '(not (app-view x86))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :seg-hidden-base
            :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (replace-element 'proc-mode #.*64-bit-mode*
                     (acl2::formals 'get-prefixes (w state)))
    :output-index 1
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-sys-view
                                        get-prefixes-xw-state-in-sys-view)
                                       ()))))
    :hyps '(not (app-view x86))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (replace-element 'proc-mode #.*64-bit-mode*
                     (acl2::formals 'get-prefixes (w state)))
    :output-index 2
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-sys-view
                                        get-prefixes-xw-state-in-sys-view)
                                       ()))))
    :hyps '(not (app-view x86))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (replace-element
     'proc-mode #.*64-bit-mode* (acl2::formals 'get-prefixes (w state)))
    :output-index 3
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-sys-view
                                        get-prefixes-xw-state-in-sys-view)
                                       ()))))
    :hyps '(not (app-view x86))))

  (defthm get-prefixes-xw-rflags-not-ac-state-in-sys-view
    (implies
     (and (not (app-view x86))
          (equal (rflagsBits->ac value)
                 (rflagsBits->ac (rflags x86))))
     (equal
      (mv-nth 3 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                              (xw :rflags 0 value x86)))
      (xw :rflags 0 value
          (mv-nth 3 (get-prefixes
                     #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))))
    :hints
    (("Goal"
      :induct (get-prefixes *64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :expand
      (get-prefixes *64-bit-mode* start-rip prefixes rex-byte cnt
                    (xw :rflags 0 value x86))
      :in-theory (e/d* (get-prefixes)
                       (negative-logand-to-positive-logand-with-integerp-x
                        unsigned-byte-p-of-logior
                        acl2::ash-0
                        acl2::zip-open
                        acl2::ifix-when-not-integerp
                        acl2::loghead-identity
                        (:t bitops::logior-natp-type)
                        (:t natp-of-get-prefixes.new-prefixes)
                        (:t natp-of-get-prefixes.new-rex-byte)
                        (:t n08p-mv-nth-1-rml08)
                        force (force))))))

  (defthm get-prefixes-xw-rflags-not-ac-values-in-sys-view
    (implies
     (and (not (app-view x86))
          (equal (rflagsBits->ac value)
                 (rflagsBits->ac (rflags x86))))
     (and
      (equal
       (mv-nth 0 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt
                  (xw :rflags 0 value x86)))
       (mv-nth 0 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt
                  (xw :rflags 0 value x86)))
       (mv-nth 1 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))
      (equal
       (mv-nth 2 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt
                  (xw :rflags 0 value x86)))
       (mv-nth 2 (get-prefixes
                  #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :expand (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw :rflags 0 value x86))
      :in-theory (e/d* (get-prefixes)
                       (bitops::logtail-of-logior
                        bitops::logtail-of-logand
                        bitops::logsquash-cancel
                        bitops::unsigned-byte-p-of-0-x
                        (:linear <=-logior)
                        unsigned-byte-p-of-logior
                        negative-logand-to-positive-logand-with-integerp-x
                        rml08
                        (tau-system)
                        force (force))))))

  ;; Opener lemmas:

  (local
   (in-theory (e/d ()
                   ((:linear <=-logior)
                    (:rewrite bitops::unsigned-byte-p-of-0-x)
                    (:rewrite acl2::natp-rw)
                    (:rewrite acl2::natp-when-integerp)
                    (:linear bitops::logand-<-0-linear)
                    (:linear bitops::logand->=-0-linear-2)
                    (:linear bitops::upper-bound-of-logand . 2)
                    (:linear bitops::logior-<-0-linear-2)
                    (:type-prescription bitops::logtail-natp)
                    (:linear bitops::logior->=-0-linear)
                    (:type-prescription bitops::logand-natp-type-2)
                    (:rewrite default-<-1)
                    (:type-prescription natp)
                    (:linear bitops::logior-<-0-linear-1)))))


  (defthm get-prefixes-opener-lemma-group-1-prefix-in-marking-view
    (b* (((mv flg byte new-x86) (rml08 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code byte)))
      (implies
       (and
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (not flg)
        (equal prefix-byte-group-code 1)
        (not (app-view x86)))
       (equal
        (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
        (get-prefixes #.*64-bit-mode* (+ 1 start-rip)
                      (if (equal byte #.*lock*)
                          (!prefixes->lck byte prefixes)
                        (!prefixes->rep byte prefixes))
                      0
                      (+ -1 cnt)
                      new-x86))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :in-theory (e/d* (get-prefixes
                        las-to-pas)
                       (acl2::ash-0
                        acl2::zip-open
                        byte-listp
                        unsigned-byte-p-of-logior
                        negative-logand-to-positive-logand-with-integerp-x
                        force (force))))))

  (defthm get-prefixes-opener-lemma-group-2-prefix-in-marking-view
    (b* (((mv flg byte new-x86) (rml08 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code byte)))
      (implies (and
                (canonical-address-p (1+ start-rip))
                (not (zp cnt))
                (not flg)
                (equal prefix-byte-group-code 2)
                (not (app-view x86)))
               (equal
                (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
                (if (or (equal byte #.*fs-override*)
                        (equal byte #.*gs-override*))
                    (get-prefixes #.*64-bit-mode*
                                  (1+ start-rip)
                                  (!prefixes->seg byte prefixes)
                                  0
                                  (1- cnt)
                                  new-x86)
                  (get-prefixes
                   #.*64-bit-mode* (1+ start-rip) prefixes 0 (1- cnt)
                   new-x86)))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :in-theory (e/d* (get-prefixes
                        las-to-pas)
                       (acl2::ash-0
                        acl2::zip-open
                        byte-listp
                        unsigned-byte-p-of-logior
                        negative-logand-to-positive-logand-with-integerp-x
                        force (force))))))

  (defthm get-prefixes-opener-lemma-group-3-prefix-in-marking-view
    (b* (((mv flg byte new-x86)
          (rml08 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code byte)))
      (implies
       (and
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (not flg)
        (equal prefix-byte-group-code 3)
        (not (app-view x86)))
       (equal
        (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
        (get-prefixes #.*64-bit-mode*
                      (1+ start-rip)
                      (!prefixes->opr byte prefixes)
                      0
                      (1- cnt)
                      new-x86))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :in-theory (e/d* (get-prefixes
                        las-to-pas)
                       (acl2::ash-0
                        acl2::zip-open
                        byte-listp
                        unsigned-byte-p-of-logior
                        negative-logand-to-positive-logand-with-integerp-x
                        force (force))))))

  (defthm get-prefixes-opener-lemma-group-4-prefix-in-marking-view
    (b* (((mv flg byte new-x86)
          (rml08 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code byte)))
      (implies (and (canonical-address-p (1+ start-rip))
                    (not (zp cnt))
                    (not flg)
                    (equal prefix-byte-group-code 4)
                    (not (app-view x86)))
               (equal
                (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
                (get-prefixes #.*64-bit-mode* (1+ start-rip)
                              (!prefixes->adr byte prefixes)
                              0
                              (1- cnt)
                              new-x86))))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :in-theory (e/d* (get-prefixes
                        las-to-pas)
                       (acl2::ash-0
                        acl2::zip-open
                        byte-listp
                        unsigned-byte-p-of-logior
                        negative-logand-to-positive-logand-with-integerp-x
                        force (force))))))

  ;; Get-prefixes and xlate-equiv-memory:

  ;; The following definition has not been changed after extending GET-PREFIXES
  ;; to use ADD-TO-*IP instead of just incrementing RIP by 1 (and checking that
  ;; the resulting address is canonical). In other words, the following
  ;; definition implicitly assumes execution in 64-bit mode, which is what
  ;; currently these proof utilities assume anyhow (usually via explicit
  ;; (64-BIT-MODEP (DOUBLE-REWRITE X86)) hypotheses in theorems. If we generalize these proof
  ;; utilities to include 32-bit mode, then we will probably need to edit the
  ;; following definition to mirror GET-PREFIXES in using ADD-TO-*IP.
  (defun-nx get-prefixes-two-x86-induct-hint
    (start-rip prefixes rex-byte cnt x86-1 x86-2)
    (declare (xargs :measure (nfix cnt)))
    (if (zp cnt)
        ;; Error, too many prefix bytes
        (mv nil prefixes x86-1 x86-2)

      (b* ((ctx 'get-prefixes-two-x86-induct-hint)
           ((mv flg-1 byte-1 x86-1)
            (rml08 start-rip :x x86-1))
           ((mv flg-2 byte-2 x86-2)
            (rml08 start-rip :x x86-2))
           ((when flg-1)
            (mv (cons ctx flg-1) byte-1 x86-1))
           ((when flg-2)
            (mv (cons ctx flg-2) byte-2 x86-2))
           ;; Quit if byte-1 and byte-2 aren't equal...
           ((when (not (equal byte-1 byte-2)))
            (mv nil prefixes x86-1 x86-2))
           (byte byte-1)

           (prefix-byte-group-code
            (get-one-byte-prefix-array-code byte)))


        (case prefix-byte-group-code

          (0
           (b* ((rex? (equal (the (unsigned-byte 4) (ash byte -4)) 4))
                ((when rex?)
                 (let ((next-rip (the (signed-byte
                                       #.*max-linear-address-size+1*)
                                   (1+ start-rip))))
                   (if (canonical-address-p next-rip)
                       (get-prefixes-two-x86-induct-hint
                        next-rip prefixes
                        byte ;; REX prefix, overwriting a previously encountered REX,
                        ;; if any
                        (the (integer 0 15) (1- cnt))
                        x86-1 x86-2)
                     (mv (cons 'non-canonical-address next-rip)
                         prefixes rex-byte x86-1 x86-2)))))
             ;; Storing the number of prefixes seen and the first byte
             ;; following the prefixes in "prefixes":
             (let ((prefixes
                    (!prefixes->nxt byte prefixes)))
               (mv nil
                   (!prefixes->num (- 15 cnt) prefixes)
                   rex-byte ;; Preserving rex-byte
                   x86-1 x86-2))))

          (1
           ;; LOCK (F0), REPE (F3), REPNE (F2)
           (b* ((next-rip (the (signed-byte
                                #.*max-linear-address-size+1*)
                            (1+ start-rip)))
                ((when (not (canonical-address-p next-rip)))
                 (mv (cons 'non-canonical-address next-rip)
                     prefixes rex-byte x86-1 x86-2))
                (prefixes
                 (if (equal byte #.*lock*)
                     (!prefixes->lck byte prefixes)
                   (!prefixes->rep byte prefixes))))
             ;; Storing the group 1 prefix (possibly overwriting a
             ;; previously seen group 1 prefix) and going on...
             (get-prefixes-two-x86-induct-hint
              next-rip prefixes
              0 ;; Nullify a previously read REX prefix, if any
              (the (integer 0 15) (1- cnt)) x86-1 x86-2)))

          (2
           ;; ES (26), CS (2E), SS (36), DS (3E), FS (64), GS (65)
           (b* ((next-rip (the (signed-byte
                                #.*max-linear-address-size+1*)
                            (1+ start-rip)))
                ((when (not (canonical-address-p next-rip)))
                 (mv (cons 'non-canonical-address next-rip)
                     prefixes rex-byte x86-1 x86-2)))

             (if (or (equal byte #.*fs-override*)
                     (equal byte #.*gs-override*))

                 ;; Storing the group 2 prefix (possibly overwriting a
                 ;; previously seen group 2 prefix) and going on...
                 (get-prefixes-two-x86-induct-hint
                  next-rip
                  (!prefixes->seg byte prefixes)
                  0 ;; Nullify a previously read REX prefix, if any
                  (the (integer 0 15) (1- cnt))
                  x86-1 x86-2)

               ;; We will be here if we are in the 64-bit mode and have seen a
               ;; null segment override prefix; we will not store the prefix
               ;; but simply decrement cnt.
               (get-prefixes-two-x86-induct-hint
                next-rip prefixes
                0 ;; Nullify a previously read REX prefix, if any
                (the (integer 0 15) (1- cnt)) x86-1 x86-2))))

          (3
           ;; Operand-Size Override (66)
           (b* ((next-rip (the (signed-byte
                                #.*max-linear-address-size+1*)
                            (1+ start-rip)))
                ((when (not (canonical-address-p next-rip)))
                 (mv (cons 'non-canonical-address next-rip)
                     prefixes rex-byte x86-1 x86-2)))
             ;; Storing the group 3 prefix (possibly overwriting a
             ;; previously seen group 3 prefix) and going on...
             (get-prefixes-two-x86-induct-hint
              next-rip
              (!prefixes->opr byte prefixes)
              0 ;; Nullify a previously read REX prefix, if any
              (the (integer 0 15) (1- cnt))
              x86-1 x86-2)))

          (4
           ;; Address-Size Override (67)
           (b* ((next-rip (the (signed-byte
                                #.*max-linear-address-size+1*)
                            (1+ start-rip)))
                ((when (not (canonical-address-p next-rip)))
                 (mv (cons 'non-canonical-address next-rip)
                     prefixes rex-byte x86-1 x86-2)))
             ;; Storing the group 4 prefix (possibly overwriting a
             ;; previously seen group 4 prefix) and going on...
             (get-prefixes-two-x86-induct-hint
              next-rip
              (!prefixes->adr byte prefixes)
              0 ;; Nullify a previously read REX prefix, if any
              (the (integer 0 15) (1- cnt))
              x86-1 x86-2)))

          (otherwise
           (mv t prefixes rex-byte x86-1 x86-2))))))

  (local
   (in-theory (e/d ()
                   (unsigned-byte-p-of-logior
                    mv-nth-0-las-to-pas-subset-p
                    negative-logand-to-positive-logand-with-integerp-x
                    mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                    (:type-prescription bitops::logior-natp-type)
                    (:rewrite bitops::logtail-of-logior)
                    (:rewrite bitops::logtail-of-logand)
                    (:rewrite unsigned-byte-p-of-logand-2)
                    (:type-prescription bitops::logand-natp-type-1)
                    (:rewrite bitops::logsquash-cancel)))))

  (defthm xlate-equiv-memory-and-two-get-prefixes-values
    (implies
     (and
      (bind-free
       (find-an-xlate-equiv-x86
        'xlate-equiv-memory-and-two-get-prefixes-values
        x86-1 'x86-2 mfc state)
       (x86-2))
      (syntaxp (not (equal x86-1 x86-2)))
      (xlate-equiv-memory (double-rewrite x86-1) x86-2)
      (canonical-address-p start-rip)
      (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86-1))))
      (disjoint-p
       (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86-1)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
      (64-bit-modep (double-rewrite x86-1)))
     (and
      (equal
       (mv-nth
        0 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-1))
       (mv-nth
        0 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-2)))
      (equal
       (mv-nth
        1 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-1))
       (mv-nth
        1 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-2)))
      (equal
       (mv-nth
        2 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-1))
       (mv-nth
        2 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-2)))))
    :hints
    (("Goal"
      :induct
      (get-prefixes-two-x86-induct-hint
       start-rip prefixes rex-byte cnt x86-1 x86-2)
      :in-theory
      (e/d* (get-prefixes disjoint-p
                          member-p las-to-pas
                          mv-nth-0-las-to-pas-subset-p)
            ()))
     (if
         ;; Apply to all subgoals under a top-level induction.
         (and (consp (car id))
              (< 1 (len (car id))))
         '(:expand
           ((las-to-pas cnt start-rip :x x86-1)
            (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-1)
            (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-2))
           :use
           ((:instance xlate-equiv-memory-and-mv-nth-0-rml08-cong
                       (lin-addr start-rip)
                       (r-w-x :x))
            (:instance xlate-equiv-memory-and-mv-nth-1-rml08
                       (lin-addr start-rip)
                       (r-w-x :x)))
           :in-theory
           (e/d* (disjoint-p
                  member-p
                  get-prefixes
                  las-to-pas)
                 (rml08
                  mv-nth-0-las-to-pas-subset-p
                  xlate-equiv-memory-and-mv-nth-0-rml08-cong
                  xlate-equiv-memory-and-mv-nth-1-rml08
                  (:rewrite mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p))))
       nil)))

  (defthm xlate-equiv-memory-and-mv-nth-3-get-prefixes
    (implies
     (and (not (app-view (double-rewrite x86)))
          (marking-view (double-rewrite x86))
          (canonical-address-p start-rip)
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
          (64-bit-modep (double-rewrite x86)))
     (xlate-equiv-memory
      (mv-nth 3 (get-prefixes
                 #.*64-bit-mode* start-rip prefixes rex-byte cnt x86))
      (double-rewrite x86)))
    :hints
    (("Goal"
      :induct (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
      :in-theory (e/d* (get-prefixes mv-nth-0-las-to-pas-subset-p subset-p)
                       (rml08
                        acl2::ash-0
                        acl2::zip-open
                        cdr-create-canonical-address-list
                        force (force))))
     (if
         ;; Apply to all subgoals under a top-level induction.
         (and (consp (car id))
              (< 1 (len (car id))))
         '(:in-theory (e/d* (subset-p get-prefixes mv-nth-0-las-to-pas-subset-p)
                            (rml08
                             acl2::ash-0
                             acl2::zip-open
                             force (force)))
                      :expand ((las-to-pas cnt start-rip :x x86))
                      :use ((:instance xlate-equiv-memory-and-las-to-pas
                                       (n (+ -1 cnt))
                                       (lin-addr (+ 1 start-rip))
                                       (r-w-x :x)
                                       (x86-1
                                        (mv-nth 2
                                                (las-to-pas 1 start-rip :x x86)))
                                       (x86-2 x86))))
       nil)))

  (defthmd xlate-equiv-memory-and-two-mv-nth-3-get-prefixes
    (implies
     (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (not (app-view x86-2))
          (marking-view (double-rewrite x86-2))
          (canonical-address-p start-rip)
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86-2))))
          (64-bit-modep x86-2))
     (xlate-equiv-memory
      (mv-nth
       3 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-1))
      (mv-nth
       3 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86-2))))
    :hints
    (("Goal"
      :use
      ((:instance xlate-equiv-memory-and-mv-nth-3-get-prefixes (x86 x86-1))
       (:instance xlate-equiv-memory-and-mv-nth-3-get-prefixes (x86 x86-2)))
      :in-theory (e/d* ()
                       (xlate-equiv-memory-and-mv-nth-3-get-prefixes
                        acl2::ash-0
                        acl2::zip-open
                        cdr-create-canonical-address-list))))))

;; ======================================================================

;; rb in system-level marking view:

(defsection rb-in-system-level-marking-view
  :parents (system-level-marking-view-proof-utilities)

  (defthm xr-fault-rb-state-in-sys-view
    (implies (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
             (equal (xr :fault index (mv-nth 2 (rb n lin-addr r-w-x x86)))
                    (xr :fault index x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas rb) (force (force))))))

  (defthm rb-and-xw-flags-state-in-sys-view
    (implies (and (equal (rflagsBits->ac (double-rewrite value))
                         (rflagsBits->ac (rflags x86)))
                  (x86p x86))
             (equal (mv-nth 2 (rb n lin-addr r-w-x (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (rb n lin-addr r-w-x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb) (force (force))))))

  (defthm mv-nth-0-rb-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rb n lin-addr r-w-x x86-1))
                    (mv-nth 0 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb) (force (force)))))
    :rule-classes :congruence)

  (defthm read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'read-from-physical-memory-and-xlate-equiv-memory
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (and (not (eq x86-2 x86-1))
                        ;; x86-2 must be "smaller" than x86-1.
                        (term-order x86-2 x86-1)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (equal (read-from-physical-memory (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)) x86-1)
            (read-from-physical-memory (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)) x86-2)))
    :hints (("Goal"
             :induct (cons (las-to-pas n lin-addr r-w-x x86-1)
                           (las-to-pas n lin-addr r-w-x x86-2))
             :in-theory (e/d* (las-to-pas disjoint-p)
                              (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p force (force))))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:in-theory
                  (e/d* (las-to-pas disjoint-p)
                        (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p force (force)))
                  :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                   (j (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                                   (x86-1 x86-1)
                                   (x86-2 x86-2))))
              nil)))

  (defthm mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (and
                    (not (eq x86-2 x86-1))
                    ;; x86-2 must be "smaller" than x86-1.
                    (term-order x86-2 x86-1)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
          (64-bit-modep (double-rewrite x86-1)))
     (equal (mv-nth 1 (rb n lin-addr r-w-x x86-1))
            (mv-nth 1 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :do-not-induct t
             :use
             ((:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures)
              (:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                         (x86-1 (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-1)))
                         (x86-2 (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-2)))))
             :in-theory (e/d* (rb)
                              (read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                               force (force))))))

  (defthm mv-nth-2-rb-and-xlate-equiv-memory
    (implies (and (marking-view (double-rewrite x86))
                  (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                  (not (app-view (double-rewrite x86)))
                  (64-bit-modep (double-rewrite x86)))
             (xlate-equiv-memory (mv-nth 2 (rb n lin-addr r-w-x x86))
                                 (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthmd xlate-equiv-memory-and-two-mv-nth-2-rb
    (implies (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                  (64-bit-modep x86-2)
                  (marking-view x86-1)
                  (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))))
             (xlate-equiv-memory (mv-nth 2 (rb n lin-addr r-w-x x86-1))
                                 (mv-nth 2 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* () (mv-nth-2-rb-and-xlate-equiv-memory))
             :use ((:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-1))
                   (:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-2))))))

  (defthm mv-nth-1-rb-after-mv-nth-2-rb
    ;; This rule will come in useful when rb isn't rewritten to
    ;; rb-alt, i.e., for reads from the paging structures.  Hence,
    ;; I'll use disjoint-p$ in the hyps here instead of disjoint-p.
    (implies
     (and
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-2 lin-addr-2 (double-rewrite x86)))
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-1 lin-addr-1 (double-rewrite x86)))
      (64-bit-modep (double-rewrite x86)))
     (equal (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1
                          (mv-nth 2 (rb n-2 lin-addr-2 r-w-x-2 x86))))
            (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1 x86))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb disjoint-p$) (force (force))))))

  (defthm mv-nth-1-rb-after-mv-nth-2-las-to-pas
    (implies
     (and
      (disjoint-p
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-2 lin-addr-2 (double-rewrite x86)))
      (disjoint-p
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-1 lin-addr-1 (double-rewrite x86)))
      (not (app-view x86))
      (64-bit-modep (double-rewrite x86)))
     (equal
      (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1
                    (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x-2 x86))))
      (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb) (force (force)))))))

;; ======================================================================

;; Lemmas about gather-all-paging-structure-qword-addresses:

(defthm gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-disjoint
  (implies
   (and (disjoint-p
         p-addrs
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (physical-address-listp p-addrs))
   (equal
    (gather-all-paging-structure-qword-addresses
     (write-to-physical-memory p-addrs value x86))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal"
           :in-theory
           (e/d* (write-to-physical-memory
                  byte-listp
                  n08p
                  len
                  disjoint-p
                  gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)
                 ()))))

(defthm gather-all-paging-structure-qword-addresses-and-wb-disjoint
  (implies
   (and
    ;; We need disjoint-p$ here instead of disjoint-p because this
    ;; first hyp should be present in the top-level hyps of the
    ;; effects theorems of programs.
    (disjoint-p$
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (app-view x86))
    (64-bit-modep (double-rewrite x86)))
   (equal
    (gather-all-paging-structure-qword-addresses (mv-nth 1 (wb n-w write-addr w value x86)))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (wb disjoint-p$)
                                   (force (force) (:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================

;; Lemmas about program-at:

(local (in-theory
        (e/d* (rb
               wb
               canonical-address-p
               program-at
               las-to-pas
               all-xlation-governing-entries-paddrs
               unsigned-byte-p
               signed-byte-p)
              ())))

(defthmd program-at-and-xlate-equiv-memory
  (implies
   (and (bind-free
         (find-an-xlate-equiv-x86
          'program-at-and-xlate-equiv-memory
          x86-1 'x86-2 mfc state)
         (x86-2))
        (syntaxp (and (not (eq x86-2 x86-1))
                      ;; x86-2 must be smaller than x86-1.
                      (term-order x86-2 x86-1)))
        (xlate-equiv-memory (double-rewrite x86-1) x86-2)
        (disjoint-p
         (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86-1)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
   (equal (program-at prog-addr bytes x86-1)
          (program-at prog-addr bytes x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (program-at)
                            (mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures))
           :use ((:instance mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                            (n (len bytes))
                            (lin-addr prog-addr)
                            (r-w-x :x))))))

(defthm program-at-wb-disjoint-in-sys-view
  (implies
   (and
    (disjoint-p
     ;; The physical addresses pertaining to the write
     ;; operation are disjoint from those pertaining to the
     ;; read operation.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
    (disjoint-p
     ;; The physical addresses corresponding to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the write.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the write are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (not (app-view x86))
    (64-bit-modep (double-rewrite x86)))
   (equal (program-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
          (program-at prog-addr bytes x86)))
  :hints (("Goal"
           :in-theory (e/d (program-at)
                           (rb wb
                               disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))

;; Lemmas to read a byte of an instruction when symbolically
;; simulating a program:

(defthmd rb-unwinding-thm-in-sys-view
  (implies
   (and
    (not (mv-nth 0 (rb n lin-addr r-w-x (double-rewrite x86))))
    (disjoint-p
     (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
    (posp n)
    (64-bit-modep (double-rewrite x86)))
   (equal (mv-nth 1 (rb n lin-addr r-w-x x86))
          (logior (mv-nth 1 (rb 1 lin-addr r-w-x x86))
                  (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) r-w-x x86)) 8))))
  :hints (("Goal" :in-theory (e/d (rb disjoint-p)
                                  (acl2::mv-nth-cons-meta force (force))))))

(local
 (defthmd rml08-in-terms-of-nth-pos-and-rb-helper
   (implies (and (disjoint-p (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))
                             (all-xlation-governing-entries-paddrs n lin-addr x86))
                 (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                 (<= lin-addr addr)
                 (< addr (+ n lin-addr))
                 (posp n) (integerp lin-addr) (integerp addr)
                 (64-bit-modep (double-rewrite x86)))
            (equal (member-p
                    (mv-nth 1 (ia32e-la-to-pa addr r-w-x x86))
                    (xlation-governing-entries-paddrs addr x86))
                   nil))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance not-member-p-when-disjoint-p
                             (e (mv-nth 1 (ia32e-la-to-pa addr r-w-x x86)))
                             (x (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))
                             (y (xlation-governing-entries-paddrs addr x86))))
            :in-theory (e/d* (all-xlation-governing-entries-paddrs
                              member-p
                              disjoint-p
                              subset-p
                              disjoint-p-commutative)
                             (not-member-p-when-disjoint-p))))))


(local
 (defthmd one-read-with-rb-from-program-at-in-marking-view-helper
   ;; TODO: Ugh, I'm embarassed about putting this here when
   ;; program-at-implies-error-free-address-translation should suffice.  Remove
   ;; soon...
   (implies
    (and (program-at (+ 1 prog-addr)
                     (cdr bytes)
                     (mv-nth 2 (ia32e-la-to-pa prog-addr :x x86)))
         (not (xr :app-view 0 x86))
         (64-bit-modep (double-rewrite x86)))
    (equal (mv-nth 0
                   (las-to-pas (len (cdr bytes))
                               (+ 1 prog-addr)
                               :x x86))
           nil))
   :hints (("Goal" :in-theory (e/d* () (program-at-implies-error-free-address-translation))
            :use ((:instance program-at-implies-error-free-address-translation
                             (prog-addr (+ 1 prog-addr))
                             (bytes (cdr bytes))
                             (x86 (mv-nth 2 (ia32e-la-to-pa prog-addr :x x86)))))))))

(local
 (defthmd rb-rb-subset-helper-1
   (implies (and (posp j)
                 (x86p x86))
            (equal (loghead (ash j 3) (xr :mem index x86))
                   (xr :mem index x86)))
   :hints (("Goal" :in-theory (e/d* () (memi-is-n08p unsigned-byte-p))
            :use ((:instance memi-is-n08p (i index)))))))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-3/top" :dir :system))

   (defthmd rb-rb-subset-helper-2
     (implies (natp j)
              (equal (ash (loghead (ash j 3) x) 8)
                     (loghead (ash (1+ j) 3) (ash x 8))))
     :hints (("Goal" :in-theory (e/d* (loghead ash) ()))))))

(define las-to-pas-two-n-ind-hint ((n-1 natp) (n-2 natp)
                                   (lin-addr integerp)
                                   (r-w-x :type (member :r :w :x))
                                   x86)
  :enabled t
  :verify-guards nil
  (if (or (zp n-1) (zp n-2))
      (mv nil nil x86)
    (b* (((unless (canonical-address-p lin-addr))
          (mv t nil x86))
         ((mv flg p-addr x86)
          (ia32e-la-to-pa lin-addr r-w-x x86))
         ((when flg) (mv flg nil x86))
         ((mv flgs p-addrs x86)
          (las-to-pas-two-n-ind-hint (1- n-1) (1- n-2) (1+ lin-addr) r-w-x x86)))
      (mv flgs (if flgs nil (cons p-addr p-addrs))
          x86))))

(local
 (defthmd read-from-physical-memory-subset-p-of-las-to-pas
   (implies
    (and
     ;; (bind-free (find-n-from-las-to-pas 'i addr r-w-x mfc state)
     ;;            (i))
     (not (mv-nth 0 (las-to-pas i addr r-w-x x86)))
     (disjoint-p
      (mv-nth 1 (las-to-pas i addr r-w-x (double-rewrite x86)))
      (all-xlation-governing-entries-paddrs i addr (double-rewrite x86)))
     ;; The following hyp should follow from the one above.
     (disjoint-p
      (mv-nth 1 (las-to-pas j addr r-w-x (double-rewrite x86)))
      (all-xlation-governing-entries-paddrs j addr (double-rewrite x86)))
     (natp j) (natp i)
     (<= j i)
     (x86p x86)
     (64-bit-modep (double-rewrite x86)))
    (equal (read-from-physical-memory
            (mv-nth 1 (las-to-pas j addr r-w-x x86)) x86)
           (loghead
            (ash j 3)
            (read-from-physical-memory
             (mv-nth 1 (las-to-pas i addr r-w-x x86)) x86))))
   :hints
   (("Goal"
     :induct (las-to-pas-two-n-ind-hint i j addr r-w-x x86)
     :in-theory (e/d* (read-from-physical-memory
                       las-to-pas)
                      ()))
    (if (equal (car id) '(0 1))
        '(:use ((:instance mv-nth-0-las-to-pas-subset-p
                           (n-1 i)
                           (addr-1 addr)
                           (n-2 j)
                           (addr-2 addr))
                (:instance mv-nth-1-las-to-pas-subset-p
                           (n-1 i)
                           (addr-1 addr)
                           (n-2 j)
                           (addr-2 addr))
                (:instance all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                           (n-1 j)
                           (addr-1 addr)
                           (n-2 i)
                           (addr-2 addr)))
               :in-theory (e/d* (disjoint-p
                                 subset-p
                                 rb-rb-subset-helper-1
                                 rb-rb-subset-helper-2
                                 signed-byte-p
                                 ifix
                                 nfix
                                 rb-1-opener-theorem)
                                ((:definition member-equal)
                                 mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                                 acl2::commutativity-2-of-+
                                 infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                                 mv-nth-1-las-to-pas-subset-p
                                 all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                                 unsigned-byte-p
                                 signed-byte-p)))
      nil))))

(local
 (defthmd rb-rb-same-start-address-different-op-sizes-helper
   (implies
    (and (equal (mv-nth 1 (rb i addr r-w-x x86)) val)
         (canonical-address-p (+ -1 i addr))
         (canonical-address-p addr)
         (not (mv-nth 0 (las-to-pas i addr r-w-x x86)))
         (disjoint-p
          (mv-nth 1 (las-to-pas i addr r-w-x (double-rewrite x86)))
          (all-xlation-governing-entries-paddrs i addr (double-rewrite x86)))
         ;; The following two hyps should be inferrable from the two above...
         (not (mv-nth 0 (las-to-pas j addr r-w-x x86)))
         (disjoint-p
          (mv-nth 1 (las-to-pas j addr r-w-x (double-rewrite x86)))
          (all-xlation-governing-entries-paddrs j addr (double-rewrite x86)))
         (canonical-address-p (+ -1 j addr))
         (posp j) (posp i)
         (<= j i)
         (not (app-view x86))
         (marking-view x86)
         (x86p x86)
         (64-bit-modep (double-rewrite x86)))
    (equal (mv-nth 1 (rb j addr r-w-x x86))
           (loghead (ash j 3) val)))
   :hints (("Goal"
            :induct (las-to-pas-two-n-ind-hint i j addr r-w-x x86)
            :in-theory (e/d* (disjoint-p
                              rb-rb-subset-helper-1
                              rb-rb-subset-helper-2)
                             ((:definition member-equal)
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              acl2::commutativity-2-of-+
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                              mv-nth-1-las-to-pas-subset-p
                              all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                              disjoint-p-append-2
                              signed-byte-p
                              unsigned-byte-p)))
           ("Subgoal *1/3"
            :in-theory (e/d* (disjoint-p
                              rb-rb-subset-helper-1
                              rb-rb-subset-helper-2)
                             ((:definition member-equal)
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              acl2::commutativity-2-of-+
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                              mv-nth-1-las-to-pas-subset-p
                              all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                              disjoint-p-append-2
                              signed-byte-p
                              unsigned-byte-p))
            :use ((:instance read-from-physical-memory-subset-p-of-las-to-pas
                             (i (+ -1 i))
                             (j (+ -1 j))
                             (addr (+ 1 addr))))))))

(defthmd rb-rb-same-start-address-different-op-sizes
  (implies
   (and (equal val (mv-nth 1 (rb i addr r-w-x x86)))
        (not (mv-nth 0 (las-to-pas i addr r-w-x (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas i addr r-w-x (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs i addr (double-rewrite x86)))
        (posp j)
        (<= j i)
        (canonical-address-p (+ -1 i addr))
        (canonical-address-p (+ -1 j addr))
        (canonical-address-p addr)
        (integerp addr)
        (not (app-view x86))
        (marking-view x86)
        (x86p x86)
        (64-bit-modep (double-rewrite x86)))
   (equal (mv-nth 1 (rb j addr r-w-x x86))
          (loghead (ash j 3) val)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-rb-same-start-address-different-op-sizes-helper)
                 (:instance mv-nth-0-las-to-pas-subset-p
                            (n-1 i)
                            (addr-1 addr)
                            (n-2 j)
                            (addr-2 addr))
                 (:instance mv-nth-1-las-to-pas-subset-p
                            (n-1 i)
                            (addr-1 addr)
                            (n-2 j)
                            (addr-2 addr))
                 (:instance all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                            (n-1 j)
                            (addr-1 addr)
                            (n-2 i)
                            (addr-2 addr)))
           :in-theory (e/d* ()
                            (mv-nth-1-las-to-pas-subset-p
                             all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                             unsigned-byte-p
                             signed-byte-p)))))

(defun-nx rb-rb-induction-scheme (n-1 a-1 n-2 a-2 val x86)
;                    a-2
;   ------------------------------------------------------------------------
; ...   |   |   |   | w | w | w | w |   |   |   |   |   |   |   |   |   |  ...
;   ------------------------------------------------------------------------
;   0                    a-1                                               max
  (cond ((or (zp n-1) (zp n-2) (< n-2 n-1) (< a-1 a-2))
         (mv n-1 a-1 n-2 a-2 val x86))
        ((equal a-1 a-2)
         (mv n-1 a-1 n-2 a-2 val x86))
        ((< a-2 a-1)
         ;; Byte that won't be read by the most recent rb.
         (b* ((n-2 (1- n-2))
              (a-2 (1+ a-2))
              (val (logtail 8 val)))
           (rb-rb-induction-scheme n-1 a-1 n-2 a-2 val x86)))))

(local
 (defthmd rb-rb-subset-helper-3
   (implies
    (and (< addr-i addr-j)
         (<= (+ addr-j j) (+ addr-i i))
         (signed-byte-p 48 (+ -1 addr-i i))
         (signed-byte-p 48 (+ -1 addr-i j)))
    (signed-byte-p 48 (+ addr-i j)))
   :hints (("Goal" :in-theory (e/d* (signed-byte-p) ())))))


(local
 (encapsulate
   ()
   (local
    (in-theory (e/d* ()
                     ((:definition member-equal)
                      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
                      (:rewrite
                       infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1)
                      (:rewrite
                       infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2)
                      (:linear mv-nth-1-idiv-spec)
                      (:linear mv-nth-1-div-spec)
                      (:definition len)
                      (:rewrite cdr-mv-nth-1-las-to-pas-no-error)
                      (:rewrite default-+-1)
                      (:rewrite default-+-2)
                      (:linear ash-monotone-2)
                      (:rewrite size-of-read-from-physical-memory)
                      (:rewrite mv-nth-1-las-to-pas-when-error)
                      (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-view)
                      (:rewrite consp-mv-nth-1-las-to-pas)
                      (:rewrite acl2::loghead-identity)
                      (:rewrite unsigned-byte-p-of-logtail)
                      (:rewrite ia32e-la-to-pa-in-app-view)
                      (:rewrite bitops::basic-signed-byte-p-of-+)
                      (:rewrite default-<-2)
                      (:rewrite default-<-1)
                      (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                      (:rewrite xr-mv-nth-2-ia32e-la-to-pa-when-error)
                      (:rewrite mv-nth-2-ia32e-la-to-pa-system-level-non-marking-view)
                      (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
                      (:rewrite acl2::unsigned-byte-p-plus)
                      (:rewrite xr-ia32e-la-to-pa)
                      (:rewrite two-page-walks-ia32e-la-to-pa)
                      (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
                      (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors)
                      (:rewrite disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
                      (:rewrite r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
                      (:rewrite canonical-address-p-limits-thm-3)
                      (:rewrite r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors)
                      (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
                      (:rewrite bitops::signed-byte-p-monotonicity)
                      (:type-prescription len)
                      (:definition binary-append)
                      (:rewrite signed-byte-p-limits-thm)
                      (:rewrite canonical-address-p-limits-thm-1)
                      (:rewrite canonical-address-p-limits-thm-2)
                      (:rewrite canonical-address-p-limits-thm-0)
                      (:rewrite xr-mem-disjoint-las-to-pas)
                      (:definition open-qword-paddr-list)
                      (:rewrite unsigned-byte-p-of-ash)
                      (:type-prescription disjoint-p$)
                      (:rewrite default-cdr)
                      (:meta acl2::cancel_plus-equal-correct)
                      (:meta acl2::cancel_times-equal-correct)
                      (:definition addr-range)
                      (:rewrite car-mv-nth-1-las-to-pas)
                      (:type-prescription member-equal)
                      (:linear bitops::logior-<-0-linear-2)
                      (:linear member-p-pos-value)
                      (:linear member-p-pos-1-value)
                      (:rewrite default-car)
                      (:rewrite subset-p-cdr-y)
                      (:rewrite car-addr-range)
                      (:rewrite subset-p-of-nil)
                      (:rewrite acl2::ifix-when-not-integerp)
                      (:definition atom)
                      (:rewrite bitops::signed-byte-p-of-decrement-when-natural-signed-byte-p)
                      (:definition ifix)
                      (:rewrite acl2::expt-with-violated-guards)
                      (:rewrite size-of-rb)
                      (:type-prescription true-listp-addr-range)
                      (:type-prescription gather-all-paging-structure-qword-addresses)
                      (:type-prescription consp-addr-range)
                      (:rewrite neg-addr-range=nil)
                      (:rewrite acl2::natp-posp)
                      (:rewrite acl2::equal-constant-+)
                      (:rewrite cdr-addr-range)
                      (:rewrite equal-ash-ash)
                      (:linear acl2::expt-is-increasing-for-base>1)
                      (:rewrite acl2::posp-rw)
                      (:type-prescription natp)
                      (:rewrite acl2::nfix-when-not-natp)
                      (:rewrite loghead-of-non-integerp)
                      (:type-prescription acl2::|x < y  =>  0 < y-x|)
                      (:rewrite
                       infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
                      (:rewrite acl2::natp-when-gte-0)
                      (:linear bitops::logior-<-0-linear-1)
                      (:linear size-of-combine-bytes-of-take)
                      (:linear size-of-combine-bytes)
                      (:linear bitops::expt-2-lower-bound-by-logbitp)
                      (:rewrite bitops::unsigned-byte-p-incr)
                      (:linear size-of-rb)
                      (:rewrite
                       all-mem-except-paging-structures-equal-aux-and-xr-mem-from-rest-of-memory)
                      (:rewrite
                       all-mem-except-paging-structures-equal-and-xr-mem-from-rest-of-memory)
                      (:rewrite loghead-ash-0)
                      (:rewrite canonical-address-p-limits-thm-4)
                      (:rewrite bitops::basic-signed-byte-p-of-+-with-cin
                                . 2)
                      (:rewrite bitops::basic-signed-byte-p-of-+-with-cin
                                . 1)
                      (:rewrite
                       read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures)
                      (:rewrite acl2::natp-rw)
                      (:rewrite default-unary-minus)
                      (:rewrite acl2::zp-open)
                      (:rewrite acl2::natp-when-integerp)
                      (:rewrite loghead-zero-smaller)
                      (:type-prescription ash)
                      (:rewrite acl2::<-0-+-negative-2)
                      (:rewrite acl2::inverse-of-+-as=0)
                      (:linear size-of-rb-in-app-view)
                      (:linear bitops::upper-bound-of-logior-for-naturals)))))

   (defthmd rb-rb-subset-in-marking-view-aux
     (implies
      (and (equal (mv-nth 1 (rb i addr-i r-w-x x86)) val)
           (not (mv-nth 0 (las-to-pas i addr-i r-w-x x86)))
           (disjoint-p
            (mv-nth 1 (las-to-pas i addr-i r-w-x (double-rewrite x86)))
            (all-xlation-governing-entries-paddrs i addr-i (double-rewrite x86)))
           ;; Ugh, the following hyp is aggravating --- I can
           ;; eliminate it via rb-rb-subset-helper-4 though...
           (disjoint-p (mv-nth 1 (las-to-pas j addr-i r-w-x x86))
                       (all-xlation-governing-entries-paddrs j addr-i x86))
           ;; <j,addr-j> is a subset (not strict) of <i,addr-i>.
           ;; This non-strictness is nice because it lets me have
           ;; a better hyp in one-read-with-rb-from-program-at-in-non-marking-view ---
           ;; (< lin-addr (+ (len bytes) prog-addr))
           ;; instead of
           ;; (< (+ 1 lin-addr) (+ (len bytes) prog-addr))
           (<= (+ j addr-j) (+ i addr-i))
           (<= addr-i addr-j)
           (canonical-address-p addr-i)
           (canonical-address-p (+ -1 i addr-i))
           (canonical-address-p (+ -1 j addr-i))
           (canonical-address-p addr-j)
           (posp i) (posp j)
           (not (app-view x86))
           (marking-view x86)
           (x86p x86)
           (64-bit-modep (double-rewrite x86)))
      (equal (mv-nth 1 (rb j addr-j r-w-x x86))
             (part-select val :low (ash (- addr-j addr-i) 3) :width (ash j 3))))
     :hints (("Goal"
              :induct (list (rb-rb-induction-scheme j addr-j i addr-i val x86)
                            (las-to-pas i addr-i r-w-x x86)
                            (las-to-pas j addr-j r-w-x x86))
              :in-theory (e/d* (signed-byte-p
                                ifix
                                nfix
                                rb-1-opener-theorem)
                               (unsigned-byte-p)))
             (if (equal (car id) '(0 1))
                 '(:computed-hint-replacement
                   ((and stable-under-simplificationp
                         '(:expand
                           ((las-to-pas i addr-i r-w-x x86)))))
                   :use ((:instance rb-rb-same-start-address-different-op-sizes
                                    (addr addr-i))
                         (:instance mv-nth-0-las-to-pas-subset-p
                                    (n-1 i)
                                    (addr-1 addr-i)
                                    (n-2 j)
                                    (addr-2 addr-j))
                         (:instance mv-nth-0-las-to-pas-subset-p
                                    (n-1 i)
                                    (addr-1 addr-i)
                                    (n-2 j)
                                    (addr-2 addr-i))
                         ;; (:instance mv-nth-1-las-to-pas-subset-p
                         ;;            (n-1 i)
                         ;;            (addr-1 addr-i)
                         ;;            (n-2 j)
                         ;;            (addr-2 addr-j))
                         ;; (:instance mv-nth-1-las-to-pas-subset-p
                         ;;            (n-1 i)
                         ;;            (addr-1 addr-i)
                         ;;            (n-2 j)
                         ;;            (addr-2 addr-i))
                         )
                   :in-theory (e/d* (rb-rb-subset-helper-1
                                     rb-rb-subset-helper-2
                                     rb-rb-subset-helper-3
                                     signed-byte-p
                                     ifix
                                     nfix
                                     rb-1-opener-theorem)
                                    (unsigned-byte-p
                                     ;; mv-nth-1-las-to-pas-subset-p
                                     signed-byte-p)))
               nil)))))

(local
 (defthmd rb-rb-subset-helper-4
   (implies
    (and
     (64-bit-modep (double-rewrite x86))
     (disjoint-p
      (mv-nth 1
              (las-to-pas i addr-i r-w-x (double-rewrite x86)))
      (all-xlation-governing-entries-paddrs i addr-i (double-rewrite x86)))
     (not (mv-nth 0 (las-to-pas i addr-i r-w-x x86)))
     (<= (+ j addr-j) (+ i addr-i))
     (<= addr-i addr-j)
     (posp i))
    (disjoint-p (mv-nth 1 (las-to-pas j addr-i r-w-x x86))
                (all-xlation-governing-entries-paddrs j addr-i x86)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d* ()
                             (mv-nth-1-las-to-pas-subset-p
                              all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs))
            :use ((:instance mv-nth-1-las-to-pas-subset-p
                             (n-1 i)
                             (addr-1 addr-i)
                             (n-2 j)
                             (addr-2 addr-i))
                  (:instance all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
                             (n-2 i)
                             (addr-2 addr-i)
                             (n-1 j)
                             (addr-1 addr-i)))))))


(defthmd rb-rb-subset-in-marking-view
  (implies
   (and (equal val (mv-nth 1 (rb i addr-i r-w-x x86)))
        (not (mv-nth 0 (las-to-pas i addr-i r-w-x (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas i addr-i r-w-x (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs i addr-i (double-rewrite x86)))
        ;; <j,addr-j> is a subset (not strict) of <i,addr-i>.
        ;; This non-strictness is nice because it lets me have a better hyp in
        ;; one-read-with-rb-from-program-at-in-non-marking-view ---
        ;; (< lin-addr (+ (len bytes) prog-addr))
        ;; instead of
        ;; (< (+ 1 lin-addr) (+ (len bytes) prog-addr))
        (<= (+ j addr-j) (+ i addr-i))
        (<= addr-i addr-j)
        (canonical-address-p addr-i)
        (canonical-address-p (+ -1 i addr-i))
        (canonical-address-p (+ -1 j addr-i))
        (canonical-address-p addr-j)
        (posp i) (posp j)
        (not (app-view x86))
        (marking-view x86)
        (64-bit-modep (double-rewrite x86))
        (x86p x86))
   (equal (mv-nth 1 (rb j addr-j r-w-x x86))
          (part-select val :low (ash (- addr-j addr-i) 3) :width (ash j 3))))
  :hints (("Goal"
           :use ((:instance rb-rb-subset-helper-4)
                 (:instance rb-rb-subset-in-marking-view-aux)))))


(defthm many-reads-with-rb-from-program-at-in-marking-view
  (implies (and
            (bind-free
             (find-program-at-info 'prog-addr 'bytes mfc state)
             (prog-addr bytes))
            (program-at prog-addr bytes x86)
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (len bytes) prog-addr :x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs
              (len bytes) prog-addr (double-rewrite x86)))
            (<= prog-addr lin-addr)
            (<= (+ n lin-addr) (+ (len bytes) prog-addr))
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 n prog-addr))
            (posp n)
            (not (app-view x86))
            (marking-view x86)
            (byte-listp bytes)
            (64-bit-modep (double-rewrite x86))
            (x86p x86))
           (equal (mv-nth 1 (rb n lin-addr :x x86))
                  ;; During symbolic simulation of a program, we'd
                  ;; know the concrete value of "bytes".  Moreover,
                  ;; note that using combine-bytes instead of
                  ;; combine-n-bytes would have been expensive because
                  ;; the former would combine all program bytes
                  ;; whereas the latter only combines n of them.
                  (combine-n-bytes (- lin-addr prog-addr) n bytes)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at
                            relating-combine-bytes-and-part-select)
                           (rb
                            take nthcdr nth
                            signed-byte-p
                            not acl2::mv-nth-cons-meta))
           :use ((:instance rb-rb-subset-in-marking-view
                            (addr-i prog-addr) (i (len bytes))
                            (addr-j lin-addr)  (j n)
                            (r-w-x :x)
                            (val (combine-n-bytes 0 (len bytes) bytes)))
                 (:instance program-at-implies-canonical-addresses)))))

(defthm one-read-with-rb-from-program-at-in-marking-view
  ;; Even though we have
  ;; many-reads-with-rb-from-program-at-in-marking-view, I like having
  ;; this lemma around because it has a hyp of
  ;; (< lin-addr (+ (len bytes) prog-addr))
  ;; instead of
  ;; (<= (+ 1 lin-addr) (+ (len bytes) prog-addr)).
  (implies (and
            (bind-free
             (find-program-at-info 'prog-addr 'bytes mfc state)
             (prog-addr bytes))
            (program-at prog-addr bytes x86)
            (disjoint-p
             (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs (len bytes) prog-addr (double-rewrite x86)))
            (<= prog-addr lin-addr)
            (< lin-addr (+ (len bytes) prog-addr))
            (canonical-address-p lin-addr)
            (byte-listp bytes)
            (not (app-view x86))
            (marking-view x86)
            (64-bit-modep (double-rewrite x86))
            (x86p x86))
           (equal (mv-nth 1 (rb 1 lin-addr :x x86))
                  (nth (- lin-addr prog-addr) bytes)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at
                            relating-nth-and-combine-bytes)
                           (rb
                            nth take nthcdr
                            signed-byte-p
                            not acl2::mv-nth-cons-meta))
           :use ((:instance rb-rb-subset-in-marking-view
                            (addr-i prog-addr) (i (len bytes))
                            (addr-j lin-addr)  (j 1)
                            (r-w-x :x)
                            (val (combine-bytes bytes)))
                 (:instance program-at-implies-canonical-addresses)))))

;; ======================================================================
