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
(include-book "physical-memory-utils")
(include-book "gl-lemmas")
(include-book "bind-free-utils")
(include-book "clause-processors/find-subterms" :dir :system)
(include-book "clause-processors/find-matching" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection common-system-level-utils
  :parents (proof-utilities)

  :short "Reasoning in the system-level view"

  :long "<p>This book contains lemmas that come in useful in both the
  marking and non-marking sub-views of the system-level view.</p>" )

(local (xdoc::set-default-parents common-system-level-utils))

;; ======================================================================

(define separate-mapped-mem ((r-w-x-1    :type (member :r :w :x))
                             (n-1        posp)
                             (lin-addr-1 canonical-address-p)
                             (r-w-x-2    :type (member :r :w :x))
                             (n-2        posp)
                             (lin-addr-2 canonical-address-p)
                             x86)
  :returns (separatep booleanp :rule-classes :type-prescription)
  :guard (and (not (app-view x86))
              (canonical-address-p (+ -1 n-1 lin-addr-1))
              (canonical-address-p (+ -1 n-2 lin-addr-2)))

  :long "<p>Two memory regions are <i>truly</i> separate if:</p>
 <ul>
 <li>the linear memory regions are separate, as defined by @(see separate)</li>
 <li>their corresponding physical memory regions are separate.</li>
 </ul>

 <p>Note that this predicate ignores whether the translation of the
 memory regions results in an error.</p>"

  :non-executable t
  :enabled t

  (and
   ;; Linear memory regions are separate.
   (separate r-w-x-1 n-1 lin-addr-1 r-w-x-2 n-2 lin-addr-2)
   ;; Physical memory regions are separate.
   (b* (((mv ?r-1-err r-1-paddrs)
         (las-to-pas n-1 lin-addr-1 r-w-x-1 x86))
        ((mv ?r-2-err r-2-paddrs)
         (las-to-pas n-2 lin-addr-2 r-w-x-2 x86)))
     (and ;; (not r-1-err)
      ;; (not r-2-err)
      (disjoint-p r-1-paddrs r-2-paddrs))))

  ///

  (defthmd separate-mapped-mem-is-commutative
    (implies (separate-mapped-mem r-w-x-1 n-1 a-1 r-w-x-2 n-2 a-2 x86)
             (separate-mapped-mem r-w-x-2 n-2 a-2 r-w-x-1 n-1 a-1 x86))
    :hints (("Goal" :in-theory (e/d* (separate-is-commutative
                                      disjoint-p-commutative)
                                     ())))))

;; ======================================================================

;; Normalizing memory reads:

;; All these functions open up to rb.
(in-theory (e/d (rml16 rml32 rml64) ()))

(defthm mv-nth-2-rb-in-system-level-non-marking-view
  (implies (and (not (marking-view x86))
                (not (mv-nth 0 (rb n addr r-x x86))))
           (equal (mv-nth 2 (rb n addr r-x x86)) x86))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm mv-nth-2-rb-in-system-level-marking-view
  (implies (and (not (app-view x86))
                (marking-view x86)
                (not (mv-nth 0 (rb n addr r-x (double-rewrite x86)))))
           (equal (mv-nth 2 (rb n addr r-x x86))
                  (mv-nth 2 (las-to-pas n addr r-x (double-rewrite x86)))))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-sys-view
  (implies (not (xr :app-view nil x86))
           (equal (mv-nth 0 (rb n addr r-x x86))
                  (mv-nth 0 (las-to-pas n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

;; ======================================================================

;; Normalizing memory writes:

;; All these functions open up to wb.
(in-theory (e/d (wml16 wml32 wml64) ()))

(defthm mv-nth-0-wb-and-mv-nth-0-las-to-pas-in-sys-view
  (implies (not (xr :app-view nil x86))
           (equal (mv-nth 0 (wb n addr w value x86))
                  (mv-nth 0 (las-to-pas n addr :w (double-rewrite x86)))))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

;; ======================================================================

;; Lemmas about program-at:

(defthm program-at-pop-x86-oracle-in-sys-view
  (implies (not (app-view x86))
           (equal (program-at addr bytes (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

;; (defthm program-at-xw-in-sys-view
;;   (implies (and (not (app-view x86))
;;                 (not (equal fld :mem))
;;                 (not (equal fld :rflags))
;;                 (not (equal fld :ctr))
;;                 (not (equal fld :seg-visible))
;;                 (not (equal fld :msr))
;;                 (not (equal fld :fault))
;;                 (not (equal fld :app-view))
;;                 (not (equal fld :marking-view)))
;;            (equal (program-at l-addrs bytes (xw fld index value x86))
;;                   (program-at l-addrs bytes x86)))
;;   :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

;; The following make-event generates a bunch of rules that together
;; say the same thing as program-at-xw-in-sys-view but these
;; rules are more efficient than program-at-xw-in-sys-view as
;; they match less frequently.

(make-event
 (generate-read-fn-over-xw-thms
  (remove-elements-from-list
   '(:mem :rflags :ctr :seg-visible :msr :fault :app-view :marking-view)
   *x86-field-names-as-keywords*)
  'program-at
  (acl2::formals 'program-at (w state))
  :hyps '(not (app-view x86))
  :prepwork '((local (in-theory (e/d (program-at) (rb)))))))

(defthm program-at-xw-rflags-not-ac-values-in-sys-view
  (implies (and (not (app-view x86))
                (equal (rflagsBits->ac value)
                       (rflagsBits->ac (rflags x86))))
           (equal (program-at addr bytes (xw :rflags nil value x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

;; ======================================================================

;; Lemmas about ia32e-la-to-pa and las-to-pas when an error is
;; encountered:

(defthm mv-nth-1-ia32e-la-to-pa-when-error
  (implies (mv-nth 0 (ia32e-la-to-pa lin-addr r-x x86))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-x x86)) 0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa
                                   ia32e-la-to-pa-pml4-table)
                                  (force (force))))))

(defthm mv-nth-1-las-to-pas-when-error
  (implies (mv-nth 0 (las-to-pas n lin-addr r-x x86))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-x x86)) nil))
  :hints (("Goal" :in-theory (e/d (las-to-pas) (force (force))))))

;; ======================================================================

;; r-x field is irrelevant for address translation if no errors are
;; encountered:

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (ia32e-pde-pg-tablebits->pt
                                         (rm-low-64
                                          (page-directory-entry-addr
                                           (logext 48 lin-addr)
                                           (logand 18446744073709547520
                                                   (loghead 52 base-addr)))
                                          x86))
                                        12))
                            (u/s-acc
                             (logand
                              u/s-acc
                              (page-user-supervisor
                               (rm-low-64 (page-directory-entry-addr
                                           (logext 48 lin-addr)
                                           (logand 18446744073709547520
                                                   (loghead 52 base-addr)))
                                          x86))))
                            (r/w-acc
                             (logand
                              r/w-acc
                              (page-read-write
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr
                             (ash
                              (ia32e-pdpte-pg-dirbits->pd
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))
                              12))
                            (u/s-acc
                             (logand
                              u/s-acc
                              (page-user-supervisor
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (r/w-acc
                             (logand
                              r/w-acc
                              (page-read-write
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr
                             (ash
                              (ia32e-pml4ebits->pdpt
                               (rm-low-64 (pml4-table-entry-addr
                                           (logext 48 lin-addr)
                                           (logand 18446744073709547520
                                                   (loghead 52 base-addr)))
                                          x86))
                              12))
                            (u/s-acc
                             (page-user-supervisor
                              (rm-low-64 (pml4-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520
                                                  (loghead 52 base-addr)))
                                         x86)))
                            (r/w-acc
                             (page-read-write
                              (rm-low-64
                               (pml4-table-entry-addr (logext 48 lin-addr)
                                                      (logand 18446744073709547520
                                                              (loghead 52 base-addr)))
                               x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64
                               (pml4-table-entry-addr (logext 48 lin-addr)
                                                      (logand 18446744073709547520
                                                              (loghead 52 base-addr)))
                               x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
  (implies (and
            (bind-free (find-almost-matching-ia32e-la-to-pas
                        'r-x-1 lin-addr mfc state)
                       (r-x-1))
            (syntaxp (and (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be "smaller" than r-x-1.
                          (term-order r-x-2 r-x-1)))
            (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-1 x86)))
            (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-2 x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-x-2 x86))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-x-1 x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (cpl (cpl x86))
                            (base-addr
                             (ash (cr3bits->pdb (xr :ctr *cr3* x86)) 12))
                            (wp
                             (cr0bits->wp (loghead 32 (xr :ctr *cr0* x86))))
                            (smep
                             (cr4bits->smep (loghead 22 (xr :ctr *cr4* x86))))
                            (smap
                             (cr4bits->smap (loghead 22 (xr :ctr *cr4* x86))))
                            (ac
                             (rflagsbits->ac (xr :rflags nil x86)))
                            (nxe
                             (ia32_eferbits->nxe
                              (loghead 12 (xr :msr *ia32_efer-idx* x86))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

;; ----------------------------------------------------------------------

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr
                             (ash
                              (ia32e-pde-pg-tablebits->pt
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))
                              12))
                            (u/s-acc
                             (logand
                              u/s-acc
                              (page-user-supervisor
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (r/w-acc
                             (logand
                              r/w-acc
                              (page-read-write
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64
                                (page-directory-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr
                             (ash
                              (ia32e-pdpte-pg-dirbits->pd
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))
                              12))
                            (u/s-acc
                             (logand
                              u/s-acc
                              (page-user-supervisor
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (r/w-acc
                             (logand
                              r/w-acc
                              (page-read-write
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64
                                (page-dir-ptr-table-entry-addr
                                 (logext 48 lin-addr)
                                 (logand 18446744073709547520
                                         (loghead 52 base-addr)))
                                x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr
                             (ash
                              (ia32e-pml4ebits->pdpt
                               (rm-low-64
                                (pml4-table-entry-addr (logext 48 lin-addr)
                                                       (logand 18446744073709547520
                                                               (loghead 52 base-addr)))
                                x86))
                              12))
                            (u/s-acc
                             (page-user-supervisor
                              (rm-low-64
                               (pml4-table-entry-addr (logext 48 lin-addr)
                                                      (logand 18446744073709547520
                                                              (loghead 52 base-addr)))
                               x86)))
                            (r/w-acc
                             (page-read-write
                              (rm-low-64
                               (pml4-table-entry-addr (logext 48 lin-addr)
                                                      (logand 18446744073709547520
                                                              (loghead 52 base-addr)))
                               x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64
                               (pml4-table-entry-addr (logext 48 lin-addr)
                                                      (logand 18446744073709547520
                                                              (loghead 52 base-addr)))
                               x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'r-x-1 lin-addr mfc state)
                           (r-x-1))
                (syntaxp (and
                          (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be "smaller" than r-x-1.
                          (term-order r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-1 x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-2 x86))))
           (equal (mv-nth 2 (ia32e-la-to-pa lin-addr r-x-2 x86))
                  (mv-nth 2 (ia32e-la-to-pa lin-addr r-x-1 x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (cpl (cpl x86))
                            (base-addr
                             (ash (cr3bits->pdb (xr :ctr *cr3* x86)) 12))
                            (wp (cr0bits->wp (loghead 32 (xr :ctr *cr0* x86))))
                            (smep (cr4bits->smep (loghead 22 (xr :ctr *cr4* x86))))
                            (smap (cr4bits->smap (loghead 22 (xr :ctr *cr4* x86))))
                            (ac (rflagsbits->ac (xr :rflags nil x86)))
                            (nxe (ia32_eferbits->nxe
                                  (loghead 12 (xr :msr *ia32_efer-idx* x86))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

;; ======================================================================

;; Some misc. lemmas, needed for theorems of the kind
;; one-read-with-rb-from-program-at-in-non-marking-view:

(defthmd rb-error-free-implies-canonical-addresses
  (implies (and (not (mv-nth 0 (rb n addr r-x x86)))
                (not (zp n))
                (not (app-view x86)))
           (and (canonical-address-p (+ -1 n addr))
                (canonical-address-p addr))))

(local
 (defthm non-zero-len-of-consp
   ;; Ugh.
   (implies (consp x)
            (equal (equal (len x) 0) nil))))

(defthmd program-at-implies-canonical-addresses
  (implies (and (program-at prog-addr bytes x86)
                (consp bytes)
                (not (app-view x86)))
           (and (canonical-address-p (+ -1 (len bytes) prog-addr))
                (canonical-address-p prog-addr)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-error-free-implies-canonical-addresses
                            (n (len bytes))
                            (addr prog-addr)
                            (r-x :x)))
           :in-theory (e/d* (program-at rb) ()))))

(defthmd relating-nth-and-combine-bytes
  (implies (and (byte-listp bytes)
                (natp i)
                (< i (len bytes)))
           (equal (nth i bytes)
                  (loghead 8 (logtail (ash i 3) (combine-bytes bytes)))))
  :hints (("Goal" :in-theory (e/d* (nth
                                    logtail-n>=8-of-byte
                                    loghead-n->=8-of-a-byte)
                                   (member-equal)))))

;; ======================================================================
