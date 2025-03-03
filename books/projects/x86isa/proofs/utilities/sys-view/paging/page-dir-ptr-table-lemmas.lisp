; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
(include-book "page-directory-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "../gl-lemmas"))

(local
 (in-theory
  (e/d (multiple-of-8-disjoint-with-addr-range-and-open-qword-paddr-list-to-member-p)
       (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(defthm xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
                  x86-1 'x86-2
                  mfc state)
                 (x86-2))
                (syntaxp (and (not (eq x86-1 x86-2))
                              ;; x86-1 must be smaller than x86-2.
                              ;; (term-order x86-1 x86-2)
                              ))
                (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (xlate-equiv-entries (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                                   (index (page-dir-ptr-table-entry-addr lin-addr base-addr)))))))

(defthm xlate-equiv-structures-and-logtail-12-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 12))))))

(defthm xlate-equiv-structures-and-logtail-21-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 21))))))

(defthm xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 30))))))

(defthm xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong
  ;; (page-dir-ptr-table-entry-addr lin-addr base-addr) is either a member of
  ;; gather-all-paging-structure-qword-addresses (because it is a
  ;; quadword-aligned address) or it is a member of the rest of the
  ;; memory (all-mem-except-paging-structures-equal)....
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-entries (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ())
           :cases
           ((not (disjoint-p (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86-1)))))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-12-rm-low-64-with-page-dir-ptr-table-entry-addr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 12))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-21-rm-low-64-with-page-dir-ptr-table-entry-addr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 21))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 30))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))))
  :rule-classes :congruence)

;; ======================================================================

;; Finally, lemmas about ia32e-la-to-pa-page-dir-ptr-table:

(defthm ia32e-la-to-pa-page-dir-ptr-table-in-app-view
  (implies (app-view x86)
           (equal (ia32e-la-to-pa-page-dir-ptr-table
                   lin-addr base-addr u/s-acc r/w-acc x/d-acc wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86)
                  (mv t 0 x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table) ()))))


(defthm xlate-equiv-entries-and-ia32e-pdpte-pg-dirbits->pd
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (ia32e-pdpte-pg-dirbits->pd e-1)
                  (ia32e-pdpte-pg-dirbits->pd e-2)))
  :hints (("goal" :in-theory (e/d* (ia32e-pdpte-pg-dirbits->pd
                                    ia32e-pdpte-pg-dirbits-fix
                                    xlate-equiv-entries
                                    ia32e-page-tablesbits->xd
                                    ia32e-page-tablesbits->res2
                                    ia32e-page-tablesbits->reference-addr
                                    ia32e-page-tablesbits->res1
                                    ia32e-page-tablesbits->ps
                                    ia32e-page-tablesbits->pcd
                                    ia32e-page-tablesbits->pwt
                                    ia32e-page-tablesbits->u/s
                                    ia32e-page-tablesbits->r/w
                                    ia32e-page-tablesbits->p
                                    ia32e-page-tablesbits-fix)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-and-ia32e-pdpte-1gb-pagebits->page
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (ia32e-pdpte-1gb-pagebits->page e-1)
                  (ia32e-pdpte-1gb-pagebits->page e-2)))
  :hints (("goal" :in-theory (e/d* (ia32e-pdpte-1gb-pagebits->page
                                    ia32e-pdpte-1gb-pagebits-fix
                                    xlate-equiv-entries
                                    ia32e-page-tablesbits->xd
                                    ia32e-page-tablesbits->res2
                                    ia32e-page-tablesbits->reference-addr
                                    ia32e-page-tablesbits->res1
                                    ia32e-page-tablesbits->ps
                                    ia32e-page-tablesbits->pcd
                                    ia32e-page-tablesbits->pwt
                                    ia32e-page-tablesbits->u/s
                                    ia32e-page-tablesbits->r/w
                                    ia32e-page-tablesbits->p
                                    ia32e-page-tablesbits-fix)
                                   ())
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 30)))))
  :rule-classes :congruence)

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-2)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-2))))
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa-page-dir-ptr-table-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (xlate-equiv-structures
   (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
              lin-addr base-addr u/s-acc r/w-acc x/d-acc
              wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal"
           :cases
           ;; Either (page-dir-ptr-table-entry-addr lin-addr base-addr) is in
           ;; (gather-all-paging-structure-qword-addresses x86) or it
           ;; is in the rest of the memory. Lemmas like
           ;; (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WM-LOW-64-ENTRY-ADDR
           ;; and
           ;; XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES-WITH-WM-LOW-64-ENTRY-ADDR)
           ;; and
           ;; (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WM-LOW-64-DISJOINT
           ;; and
           ;; XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES-WITH-WM-LOW-64-DISJOINT)
           ;; should be applicable in these situations, respectively.
           ((not (disjoint-p (addr-range 8
                                         (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr))))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                             xlate-equiv-structures
                             multiple-of-8-disjoint-with-addr-range-and-open-qword-paddr-list-to-member-p)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthmd xlate-equiv-structures-and-two-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-cong
  (implies
   (xlate-equiv-structures x86-1 x86-2)
   (xlate-equiv-structures
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2))))
  :rule-classes :congruence)

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   (and (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand
                                           18446744073709547520
                                           (loghead 52 base-addr)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86)))
                      12))
                    x86))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    ia32e-pdpte-pg-dirbits->pd)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthmd all-mem-except-paging-structures-equal-with-two-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   (and (all-mem-except-paging-structures-equal x86-1 x86-2)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-1))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand
                                           18446744073709547520
                                           (loghead 52 base-addr)))
                                         x86-1))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86-1)))
                12))
              (gather-all-paging-structure-qword-addresses x86-1))
             (if (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86-1)))
                      12))
                    x86-1))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86-1)))
                         12))
                       x86-1)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86-1))
               t))
          t)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-2))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand
                                           18446744073709547520
                                           (loghead 52 base-addr)))
                                         x86-2))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86-2)))
                12))
              (gather-all-paging-structure-qword-addresses x86-2))
             (if (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86-2)))
                      12))
                    x86-2))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86-2)))
                         12))
                       x86-2)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86-2))
               t))
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; without the 64-bit mode hyp, this theorem is not true,
   ;; because ia32e-la-to-pa-page-dir-ptr-table may mark bits in the state
   (and (64-bit-modep x86)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86)))
                      12))
                    x86))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthmd xlate-equiv-memory-with-two-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-1))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-1))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86-1)))
                12))
              (gather-all-paging-structure-qword-addresses x86-1))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86-1)))
                      12))
                    x86-1))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86-1)))
                         12))
                       x86-1)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86-1))
               t))
          t)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-2))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-2))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86-2)))
                12))
              (gather-all-paging-structure-qword-addresses x86-2))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86-2)))
                      12))
                    x86-2))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86-2)))
                         12))
                       x86-2)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86-2))
               t))
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86-2))))
  ;; add the following after adding 64-bit mode hyp to previous theorem:
  :hints (("Goal" :in-theory (e/d (xlate-equiv-memory)
                                  (xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
                                   xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr)))))

(defthm two-page-dir-ptr-table-walks-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; the 64-bit mode hyp makes the proof of this theorem easy
   ;; (via xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table above),
   ;; but could this hyp be removed from here?
   (and (64-bit-modep x86)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr-2)
                                                 (logand 18446744073709547520 (loghead 52 base-addr-2)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr-2)
                                          (logand 18446744073709547520 (loghead 52 base-addr-2)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr-2)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr-2)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr-2)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr-2)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr-2)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr-2)))
                                   x86)))
                      12))
                    x86))
                  0)
                 (member-p
                  (page-table-entry-addr
                   (logext 48 lin-addr-2)
                   (ash
                    (loghead
                     40
                     (logtail
                      12
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr-2)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr-2)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr-2)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))

   (and

    (equal
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1  implicit-supervisor-access-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-dir-ptr-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2  implicit-supervisor-access-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1  implicit-supervisor-access-1 r-w-x-1 cpl-1 x86)))

    (equal
     (mv-nth
      1
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1  implicit-supervisor-access-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-dir-ptr-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2  implicit-supervisor-access-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      1
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1  implicit-supervisor-access-1 r-w-x-1 cpl-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-page-dir-ptr-table)))))

(in-theory (e/d* () (ia32e-la-to-pa-page-dir-ptr-table)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies (equal addrs (gather-all-paging-structure-qword-addresses x86))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                                    booleanp-of-xlate-equiv-entries-at-qword-addresses))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                          lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))))))))

;; ======================================================================
