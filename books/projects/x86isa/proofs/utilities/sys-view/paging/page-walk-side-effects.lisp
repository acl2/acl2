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

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(defthmd wm-low-32-and-rm-low-32-writing-the-read-simple
  (implies (x86p x86)
           (equal (wm-low-32 addr (rm-low-32 addr x86) x86)
                  x86))
  :hints (("Goal" :in-theory (e/d* (wm-low-32
                                    rm-low-32
                                    xw-xr
                                    unsigned-byte-p)
                                   ()))))

(defthmd wm-low-32-and-rm-low-32-writing-the-read
  (implies (and (equal (rm-low-32 addr x86-2)
                       (rm-low-32 addr x86-1))
                (x86p x86-1)
                (x86p x86-2))
           (equal (wm-low-32 addr (rm-low-32 addr x86-1) x86-2)
                  x86-2))
  :hints (("Goal" :in-theory (e/d* (wm-low-32-and-rm-low-32-writing-the-read-simple)
                                   ()))))

(defthmd wm-low-64-and-rm-low-64-writing-the-read-simple
  (implies (x86p x86)
           (equal (wm-low-64 addr (rm-low-64 addr x86) x86)
                  x86))
  :hints (("Goal" :in-theory (e/d* (wm-low-64
                                    rm-low-64
                                    wm-low-32-and-rm-low-32-writing-the-read)
                                   ()))))

(defthmd wm-low-64-and-rm-low-64-writing-the-read
  (implies (and (equal (rm-low-64 addr x86-2)
                       (rm-low-64 addr x86-1))
                (x86p x86-1)
                (x86p x86-2))
           (equal (wm-low-64 addr (rm-low-64 addr x86-1) x86-2)
                  x86-2))
  :hints (("Goal" :in-theory (e/d* (wm-low-64-and-rm-low-64-writing-the-read-simple)
                                   ()))))

;; ======================================================================

(define update-a/d-bits (p-addrs
                         (r-w-x  :type (member :r :w :x))
                         x86)
  ;; We expect p-addrs to be members of
  ;; xlate-governing-qword-addresses addresses of some linear address
  ;; on whose behalf a page walk is being done.

  ;; Don't use anything other than the output of
  ;; xlate-governing-qword-addresses* functions as input for p-addrs.
  :guard (and (not (app-view x86))
              (mult-8-qword-paddr-listp p-addrs))
  :enabled t
  (if (endp p-addrs)
      (mv nil x86)
    (b* ((p-addr (car p-addrs))
         ((when (not (physical-address-p (+ 7 p-addr))))
          (mv t x86))
         (entry (rm-low-64 p-addr x86))
         (new-entry (set-accessed-bit entry))
         (new-entry
          (if (and (equal (len p-addrs) 1)
                   (equal r-w-x :w))
              ;; If the entry maps a page and translation is occurring
              ;; on behalf of a write, set the dirty bit too.
              (set-dirty-bit new-entry)
            new-entry))
         (x86 (wm-low-64 p-addr new-entry x86)))
      (update-a/d-bits (cdr p-addrs) r-w-x x86)))

  ///

  (defthm x86p-mv-nth-1-update-a/d-bits
    (implies (and (x86p x86)
                  (physical-address-listp p-addrs))
             (x86p (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86))))))

(defthm xr-mem-from-update-a/d-bits-disjoint
  (implies (and (disjoint-p (list index)
                            (open-qword-paddr-list p-addrs))
                (mult-8-qword-paddr-listp p-addrs))
           (equal (xr :mem index (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
                  (xr :mem index x86))))

(defthm rm-low-64-from-update-a/d-bits-disjoint
  (implies (and (disjoint-p (addr-range 8 index)
                            (open-qword-paddr-list p-addrs))
                (mult-8-qword-paddr-listp p-addrs)
                (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
                  (rm-low-64 index x86))))

(defthm xw-mem-from-update-a/d-bits-disjoint-commute
  (implies (disjoint-p (list index)
                       (open-qword-paddr-list p-addrs))
           (equal (xw :mem index val (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
                  (mv-nth 1 (update-a/d-bits p-addrs r-w-x (xw :mem index val x86))))))

(defthm wm-low-64-from-update-a/d-bits-disjoint-commute
  (implies (and (disjoint-p (addr-range 8 index)
                            (open-qword-paddr-list p-addrs))
                (mult-8-qword-paddr-listp p-addrs)
                (integerp index))
           (equal (wm-low-64 index val (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
                  (mv-nth 1 (update-a/d-bits p-addrs r-w-x (wm-low-64 index val x86))))))

;; ======================================================================

;; Locally adding rm-low-64/wm-low-64 RoW rule that will allow
;; splitting based on whether addr-1 and addr-2 are equal or
;; completely disjoint:

(local
 (defthm |(rm-low-64 addr-2 (wm-low-64 addr-1 val x86)) --- split|
   (implies (and (force (n64p val))
                 (not (app-view x86)))
            (equal (rm-low-64 addr-2 (wm-low-64 addr-1 val x86))
                   (if (equal addr-1 addr-2)
                       val
                     (if (disjoint-p (addr-range 8 addr-1)
                                     (addr-range 8 addr-2))
                         (rm-low-64 addr-2 x86)
                       ;; This lemma is tailored for paging entries,
                       ;; where addr-1 and addr-2 are the physical
                       ;; addresses of two paging entries.  The hide
                       ;; below is because I don't care about the case
                       ;; where addr-1 and addr-2 overlap --- it's not
                       ;; going to come up here because all paging
                       ;; entries are quadword aligned.  Moreover,
                       ;; putting this hide here avoids stack
                       ;; overflows on value stack.
                       (hide (rm-low-64 addr-2 (wm-low-64 addr-1 val x86)))))))
   :hints (("Goal"
            :expand ((:free (x) (hide x)))
            :in-theory (e/d* (unsigned-byte-p) ())))))

(local (in-theory (e/d ()
                       (|(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- same addr|
                        |(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- disjoint addr|))))

;; ======================================================================

;; !! TODO: I should probably replace xlation-governing-entries-paddrs*
;; !! with xlate-governing-qword-addresses* eventually...

;; xlate-governing-qword-addresses are similar to
;; xlation-governing-entries-paddrs, except that they output quadword
;; addresses of the paging entries instead of byte addresses.

(define xlate-governing-qword-addresses-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :ignore-ok t

  (b* ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr))
       (page-table-entry
        (rm-low-64 page-table-entry-addr x86)))
    ;; 4K pages
    (list page-table-entry-addr))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-table
    (equal (open-qword-paddr-list
            (xlate-governing-qword-addresses-for-page-table
             lin-addr base-addr x86))
           (xlation-governing-entries-paddrs-for-page-table
            lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                                     ()))))

  (defthm xlate-governing-qword-addresses-for-page-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlate-governing-qword-addresses-for-page-table lin-addr base-addr (xw fld index value x86))
                    (xlate-governing-qword-addresses-for-page-table lin-addr base-addr (double-rewrite x86)))))

  (defthm xlate-governing-qword-addresses-for-page-table-and-xw-mem-not-member
    (implies (not (member-p index
                            (open-qword-paddr-list
                             (xlate-governing-qword-addresses-for-page-table
                              lin-addr base-addr (double-rewrite x86)))))
             (equal (xlate-governing-qword-addresses-for-page-table
                     lin-addr base-addr (xw :mem index value x86))
                    (xlate-governing-qword-addresses-for-page-table
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     ())))))

(define xlate-governing-qword-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlate-governing-qword-addresses-for-page-table
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
        (list page-directory-entry-addr))

       ;; 4K pages:
       (page-table-base-addr
        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-address
        (xlate-governing-qword-addresses-for-page-table
         lin-addr page-table-base-addr x86)))

    (cons page-directory-entry-addr page-table-address))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-directory
    (equal (open-qword-paddr-list
            (xlate-governing-qword-addresses-for-page-directory
             lin-addr base-addr x86))
           (xlation-governing-entries-paddrs-for-page-directory
            lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory)
                                     ()))))

  (defthm xlate-governing-qword-addresses-for-page-directory-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlate-governing-qword-addresses-for-page-directory lin-addr base-addr (xw fld index value x86))
                    (xlate-governing-qword-addresses-for-page-directory lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses-for-page-table)))))

  (defthm xlate-governing-qword-addresses-for-page-directory-and-xw-mem-not-member
    (implies (not (member-p index
                            (open-qword-paddr-list
                             (xlate-governing-qword-addresses-for-page-directory
                              lin-addr base-addr (double-rewrite x86)))))
             (equal (xlate-governing-qword-addresses-for-page-directory
                     lin-addr base-addr (xw :mem index value x86))
                    (xlate-governing-qword-addresses-for-page-directory
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlate-governing-qword-addresses-for-page-table))))))

(define xlate-governing-qword-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlate-governing-qword-addresses-for-page-directory
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (page-size page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
        (list page-dir-ptr-table-entry-addr))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
        (xlate-governing-qword-addresses-for-page-directory
         lin-addr page-directory-base-addr x86)))

    (cons page-dir-ptr-table-entry-addr page-directory-addresses))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-dir-ptr-table
    (equal (open-qword-paddr-list
            (xlate-governing-qword-addresses-for-page-dir-ptr-table
             lin-addr base-addr x86))
           (xlation-governing-entries-paddrs-for-page-dir-ptr-table
            lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                     ()))))

  (defthm xlate-governing-qword-addresses-for-page-dir-ptr-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlate-governing-qword-addresses-for-page-dir-ptr-table
                     lin-addr base-addr (xw fld index value x86))
                    (xlate-governing-qword-addresses-for-page-dir-ptr-table
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses-for-page-directory)))))

  (defthm xlate-governing-qword-addresses-for-page-dir-ptr-table-and-xw-mem-not-member
    (implies (not (member-p
                   index
                   (open-qword-paddr-list
                    (xlate-governing-qword-addresses-for-page-dir-ptr-table
                     lin-addr base-addr (double-rewrite x86)))))
             (equal (xlate-governing-qword-addresses-for-page-dir-ptr-table
                     lin-addr base-addr (xw :mem index value x86))
                    (xlate-governing-qword-addresses-for-page-dir-ptr-table
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlate-governing-qword-addresses-for-page-directory))))))

(define xlate-governing-qword-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (app-view x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlate-governing-qword-addresses-for-page-dir-ptr-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))
       (pml4te-ps? (equal (page-size pml4-entry) 1))

       ((when pml4te-ps?) (list pml4-entry-addr))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
        (xlate-governing-qword-addresses-for-page-dir-ptr-table
         lin-addr ptr-table-base-addr x86)))

    (cons pml4-entry-addr ptr-table-addresses))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-pml4-table
    (equal (open-qword-paddr-list
            (xlate-governing-qword-addresses-for-pml4-table
             lin-addr base-addr x86))
           (xlation-governing-entries-paddrs-for-pml4-table
            lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table)
                                     ()))))

  (defthm xlate-governing-qword-addresses-for-pml4-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlate-governing-qword-addresses-for-pml4-table
                     lin-addr base-addr (xw fld index value x86))
                    (xlate-governing-qword-addresses-for-pml4-table
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses-for-page-table)))))

  (defthm xlate-governing-qword-addresses-for-pml4-table-and-xw-mem-not-member
    (implies (not (member-p
                   index
                   (open-qword-paddr-list
                    (xlate-governing-qword-addresses-for-pml4-table
                     lin-addr base-addr (double-rewrite x86)))))
             (equal (xlate-governing-qword-addresses-for-pml4-table
                     lin-addr base-addr (xw :mem index value x86))
                    (xlate-governing-qword-addresses-for-pml4-table
                     lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlate-governing-qword-addresses-for-page-dir-ptr-table))))))

(define xlate-governing-qword-addresses
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('xlate-governing-qword-addresses') returns a
  @('true-listp') of qword physical addresses that govern the
  translation of a linear address @('lin-addr') to its corresponding
  physical address @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

 <ol>
 <li>The qword address of the relevant PML4 entry</li>

 <li>The qword address of the relevant PDPT entry</li>

 <li>The qword address of the relevant PD entry</li>

 <li>The qword addresses of the relevant PT entry</li>

 </ol>

 <p>The following rule shows the relationship between @(see
 xlation-governing-entries-paddrs) and
 @('xlate-governing-qword-addresses'):</p>

 @(def xlate-governing-qword-and-byte-addresses)"

  :guard (not (xr :app-view 0 x86))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlate-governing-qword-addresses-for-pml4-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (if (mbt (not (app-view x86)))
      (b* ((cr3       (ctri *cr3* x86))
           ;; PML4 Table:
           (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

        (xlate-governing-qword-addresses-for-pml4-table
         lin-addr pml4-base-addr x86))
    nil)

  ///

  (defthm xlate-governing-qword-and-byte-addresses
    (equal (open-qword-paddr-list
            (xlate-governing-qword-addresses lin-addr x86))
           (xlation-governing-entries-paddrs lin-addr x86))
    :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs)
                                     ()))))

  (defthm xlate-governing-qword-addresses-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (xlate-governing-qword-addresses lin-addr (xw fld index value x86))
                    (xlate-governing-qword-addresses lin-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses-for-pml4-table)))))

  (defthm xlate-governing-qword-addresses-and-xw-mem-not-member
    (implies (not (member-p index (open-qword-paddr-list
                                   (xlate-governing-qword-addresses lin-addr (double-rewrite x86)))))
             (equal (xlate-governing-qword-addresses lin-addr (xw :mem index value x86))
                    (xlate-governing-qword-addresses lin-addr (double-rewrite x86))))
    :hints (("Goal"
             :in-theory (e/d* () (xlate-governing-qword-addresses-for-pml4-table))))))

(define all-xlate-governing-qword-addresses
  ((n        natp)
   (lin-addr canonical-address-p)
   x86)
  :guard (and (not (xr :app-view 0 x86))
              (canonical-address-p (+ n lin-addr)))
  :guard-hints (("Goal" :in-theory (e/d* (signed-byte-p) ())))
  :enabled t
  (if (zp n)
      nil
    (append (xlate-governing-qword-addresses lin-addr x86)
            (all-xlate-governing-qword-addresses (1- n) (1+ lin-addr) x86)))
  ///

  (defthm all-xlate-governing-qword-and-byte-addresses
    (equal (open-qword-paddr-list
            (all-xlate-governing-qword-addresses n lin-addr x86))
           (all-xlation-governing-entries-paddrs n lin-addr x86))
    :hints (("Goal" :in-theory (e/d* (all-xlation-governing-entries-paddrs)
                                     ()))))

  (defthm all-xlate-governing-qword-addresses-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (all-xlate-governing-qword-addresses
                     n lin-addr (xw fld index value x86))
                    (all-xlate-governing-qword-addresses
                     n lin-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses)))))

  (defthm all-xlate-governing-qword-addresses-and-xw-mem-not-member
    (implies (and (not (member-p index
                                 (open-qword-paddr-list
                                  (all-xlate-governing-qword-addresses
                                   n lin-addr (double-rewrite x86)))))
                  (integerp index))
             (equal (all-xlate-governing-qword-addresses
                     n lin-addr (xw :mem index value x86))
                    (all-xlate-governing-qword-addresses
                     n lin-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlate-governing-qword-addresses))))))

;; ======================================================================

;; Page Table:

(defthm mv-nth-2-ia32e-la-to-pa-page-table-in-terms-of-updates-no-errors
  (implies
   (and
    (case-split
     (not (mv-nth 0
                  (ia32e-la-to-pa-page-table
                   lin-addr base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))))
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0)
    (x86p x86))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86))
          (if (or (xr :app-view 0 x86)
                  (not (xr :marking-view 0 x86)))
              x86
            (mv-nth 1
                    (update-a/d-bits
                     (xlate-governing-qword-addresses-for-page-table
                      lin-addr base-addr x86)
                     r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
                                    wm-low-64-and-rm-low-64-writing-the-read
                                    xlate-governing-qword-addresses-for-page-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

(defthm xw-mem-mv-nth-2-ia32e-la-to-pa-page-table-errors-commute
  (implies
   (and (mv-nth 0
                (ia32e-la-to-pa-page-table
                 lin-addr base-addr u/s-acc r/w-acc x/d-acc
                 wp smep smap ac nxe r-w-x cpl x86))
        (disjoint-p (list index)
                    (open-qword-paddr-list
                     (xlate-governing-qword-addresses-for-page-table
                      lin-addr base-addr x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl (xw :mem index val x86)))
          (xw :mem index val
              (mv-nth
               2
               (ia32e-la-to-pa-page-table
                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
                                    xlate-governing-qword-addresses-for-page-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

;; ======================================================================

;; Page Directory:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-2M-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86))
            1)
     (not (mv-nth 0
                  (ia32e-la-to-pa-page-directory
                   lin-addr base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86)))
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0)
     (x86p x86))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-page-directory
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-page-directory
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                     wm-low-64-and-rm-low-64-writing-the-read
                                     xlate-governing-qword-addresses-for-page-directory)
                                    (bitops::logand-with-negated-bitmask
                                     accessed-bit
                                     dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-4K-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                        x86))
            0)
     (not
      (mv-nth 0
              (ia32e-la-to-pa-page-directory
               lin-addr
               base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86)))
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0)
     (x86p x86))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-page-directory
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-page-directory
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-directory
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-page-directory
                              xlate-governing-qword-addresses-for-page-table)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit))))))

(defthm mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-no-errors
  (implies
   (and
    (case-split
     (not
      (mv-nth 0
              (ia32e-la-to-pa-page-directory
               lin-addr
               base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))))
    (x86p x86)
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-directory
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86))
          (if (or (xr :app-view 0 x86)
                  (not (xr :marking-view 0 x86)))
              x86
            (mv-nth 1
                    (update-a/d-bits
                     (xlate-governing-qword-addresses-for-page-directory
                      lin-addr base-addr x86)
                     r-w-x x86)))))
  :hints (("Goal"
           :cases ((equal (page-size
                           (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                      x86))
                          0))
           :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-4K-pages-no-errors
                             mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-2M-pages-no-errors)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit)))))

(defthm xw-mem-mv-nth-2-ia32e-la-to-pa-page-directory-errors-commute
  (implies
   (and (mv-nth 0
                (ia32e-la-to-pa-page-directory
                 lin-addr base-addr u/s-acc r/w-acc x/d-acc
                 wp smep smap ac nxe r-w-x cpl x86))
        (disjoint-p (list index)
                    (open-qword-paddr-list
                     (xlate-governing-qword-addresses-for-page-directory
                      lin-addr base-addr x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-directory
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl (xw :mem index val x86)))
          (xw :mem index val
              (mv-nth
               2
               (ia32e-la-to-pa-page-directory
                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                    xlate-governing-qword-addresses-for-page-directory)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

;; ======================================================================

;; Page directory pointer table:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-1G-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
            1)
     (not (mv-nth
           0
           (ia32e-la-to-pa-page-dir-ptr-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-page-dir-ptr-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                     wm-low-64-and-rm-low-64-writing-the-read
                                     xlate-governing-qword-addresses-for-page-dir-ptr-table)
                                    (bitops::logand-with-negated-bitmask
                                     accessed-bit
                                     dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-2M-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
            0)
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail
                            12
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                       x86)))
                          12))
                        x86))
            1)
     (not (mv-nth
           0
           (ia32e-la-to-pa-page-dir-ptr-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-page-dir-ptr-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-page-dir-ptr-table
                              xlate-governing-qword-addresses-for-page-directory)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-4K-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
            0)
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail
                            12
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                       x86)))
                          12))
                        x86))
            0)
     (not
      (mv-nth 0
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr
               base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr base-addr u/s-acc r/w-acc x/d-acc
             wp smep smap ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-page-dir-ptr-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-page-dir-ptr-table
                              xlate-governing-qword-addresses-for-page-directory
                              xlate-governing-qword-addresses-for-page-table)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              force (force)))))))

(defthm mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-no-errors
  (implies
   (and
    (case-split
     (not
      (mv-nth 0
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))))
    (x86p x86)
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-dir-ptr-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl x86))
          (if (or (xr :app-view 0 x86)
                  (not (xr :marking-view 0 x86)))
              x86
            (mv-nth 1
                    (update-a/d-bits
                     (xlate-governing-qword-addresses-for-page-dir-ptr-table
                      lin-addr base-addr x86)
                     r-w-x x86)))))
  :hints (("Goal"
           :cases (
                   ;; 1G pages
                   (equal (page-size
                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
                          1)
                   ;; 2M pages
                   (and
                    (equal (page-size
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
                           0)
                    (equal (page-size
                            (rm-low-64 (page-directory-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail
                                           12
                                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                                      x86)))
                                         12))
                                       x86))
                           1))
                   ;; 4K pages
                   (and
                    (equal (page-size
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
                           0)
                    (equal (page-size
                            (rm-low-64 (page-directory-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail
                                           12
                                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                                      x86)))
                                         12))
                                       x86))
                           0)))
           :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-4K-pages-no-errors
                             mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-2M-pages-no-errors
                             mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-1G-pages-no-errors)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit)))))

(defthm xw-mem-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-errors-commute
  (implies
   (and (mv-nth 0
                (ia32e-la-to-pa-page-dir-ptr-table
                 lin-addr base-addr u/s-acc r/w-acc x/d-acc
                 wp smep smap ac nxe r-w-x cpl x86))
        (disjoint-p (list index)
                    (open-qword-paddr-list
                     (xlate-governing-qword-addresses-for-page-dir-ptr-table
                      lin-addr base-addr x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-page-dir-ptr-table
            lin-addr base-addr u/s-acc r/w-acc x/d-acc
            wp smep smap ac nxe r-w-x cpl (xw :mem index val x86)))
          (xw :mem index val
              (mv-nth
               2
               (ia32e-la-to-pa-page-dir-ptr-table
                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    xlate-governing-qword-addresses-for-page-dir-ptr-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

;; ======================================================================

;; PML4 Table:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-1G-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail 12
                                    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                               x86)))
                          12))
                        x86))
            1)
     (not
      (mv-nth 0
              (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
                                         smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
                                       ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-pml4-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-pml4-table
                              xlate-governing-qword-addresses-for-page-dir-ptr-table)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              force (force)))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-2M-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail 12
                                    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                               x86)))
                          12))
                        x86))
            0)
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail
                            12
                            (rm-low-64 (page-dir-ptr-table-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail 12
                                                   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                              x86)))
                                         12))
                                       x86)))
                          12))
                        x86))
            1)
     (not
      (mv-nth 0
              (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
                                         smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
                                       ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-pml4-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-pml4-table
                              xlate-governing-qword-addresses-for-page-dir-ptr-table
                              xlate-governing-qword-addresses-for-page-directory)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              force (force)))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-4K-pages-no-errors
   (implies
    (and
     (equal (page-size
             (rm-low-64 (page-dir-ptr-table-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail 12
                                    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                               x86)))
                          12))
                        x86))
            0)
     (equal (page-size
             (rm-low-64 (page-directory-entry-addr
                         lin-addr
                         (ash
                          (loghead
                           40
                           (logtail
                            12
                            (rm-low-64 (page-dir-ptr-table-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail 12
                                                   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                              x86)))
                                         12))
                                       x86)))
                          12))
                        x86))
            0)
     (not
      (mv-nth 0
              (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
                                         smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
            2
            (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
                                       ac nxe r-w-x cpl x86))
           (if (or (xr :app-view 0 x86)
                   (not (xr :marking-view 0 x86)))
               x86
             (mv-nth 1
                     (update-a/d-bits
                      (xlate-governing-qword-addresses-for-pml4-table
                       lin-addr base-addr x86)
                      r-w-x x86)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                              wm-low-64-and-rm-low-64-writing-the-read
                              xlate-governing-qword-addresses-for-pml4-table
                              xlate-governing-qword-addresses-for-page-dir-ptr-table
                              xlate-governing-qword-addresses-for-page-directory
                              xlate-governing-qword-addresses-for-page-table)
                             (bitops::logand-with-negated-bitmask
                              accessed-bit
                              dirty-bit
                              force (force)))))))

(defthm mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-no-errors
  (implies
   (and
    (case-split
     (not
      (mv-nth 0
              (ia32e-la-to-pa-pml4-table
               lin-addr base-addr wp smep
               smap ac nxe r-w-x cpl x86))))
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0)
    (x86p x86))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-pml4-table
            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86))
          (if (or (xr :app-view 0 x86)
                  (not (xr :marking-view 0 x86)))
              x86
            (mv-nth 1
                    (update-a/d-bits
                     (xlate-governing-qword-addresses-for-pml4-table
                      lin-addr base-addr x86)
                     r-w-x x86)))))
  :hints (("Goal"
           :cases (
                   ;; 1g pages
                   (equal (page-size
                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
                                                                               (loghead
                                                                                40
                                                                                (logtail 12
                                                                                         (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                                                                    x86)))
                                                                               12)) x86))
                          1)
                   ;; 2m pages
                   (and
                    (equal (page-size
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
                                                                                (loghead
                                                                                 40
                                                                                 (logtail 12
                                                                                          (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                                                                     x86)))
                                                                                12)) x86))
                           0)
                    (equal (page-size
                            (rm-low-64 (page-directory-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail
                                           12
                                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
                                                                                               (loghead
                                                                                                40
                                                                                                (logtail 12
                                                                                                         (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                                                                                    x86)))
                                                                                               12))
                                                      x86)))
                                         12))
                                       x86))
                           1))
                   ;; 4k pages
                   (and
                    (equal (page-size
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
                                                                                (loghead
                                                                                 40
                                                                                 (logtail 12
                                                                                          (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                                                                     x86)))
                                                                                12)) x86))
                           0)
                    (equal (page-size
                            (rm-low-64 (page-directory-entry-addr
                                        lin-addr
                                        (ash
                                         (loghead
                                          40
                                          (logtail
                                           12
                                           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
                                                                                               (loghead
                                                                                                40
                                                                                                (logtail 12
                                                                                                         (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                                                                                                    x86)))
                                                                                               12))
                                                      x86)))
                                         12))
                                       x86))
                           0)))
           :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-1G-pages-no-errors
                             mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-2M-pages-no-errors
                             mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-4K-pages-no-errors)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit)))))

(defthm xw-mem-mv-nth-2-ia32e-la-to-pa-pml4-table-errors-commute
  (implies
   (and (mv-nth 0
                (ia32e-la-to-pa-pml4-table
                 lin-addr base-addr wp smep
                 smap ac nxe r-w-x cpl x86))
        (disjoint-p (list index)
                    (open-qword-paddr-list
                     (xlate-governing-qword-addresses-for-pml4-table
                      lin-addr base-addr x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
           2
           (ia32e-la-to-pa-pml4-table
            lin-addr base-addr wp smep smap
            ac nxe r-w-x cpl (xw :mem index val x86)))
          (xw :mem index val
              (mv-nth
               2
               (ia32e-la-to-pa-pml4-table
                lin-addr base-addr wp smep
                smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    xlate-governing-qword-addresses-for-pml4-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

;; ======================================================================

;; Top-level page walk function:

(defthm mv-nth-2-ia32e-la-to-pa-in-terms-of-updates-no-errors
  (implies
   (and
    (case-split (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
    (canonical-address-p lin-addr)
    (x86p x86))
   (equal (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
          (if (or (xr :app-view 0 x86)
                  (not (xr :marking-view 0 x86)))
              x86
            (mv-nth 1
                    (update-a/d-bits
                     (xlate-governing-qword-addresses lin-addr x86)
                     r-w-x x86)))))
  :hints (("Goal"
           :in-theory (e/d* (xlate-governing-qword-addresses
                             ia32e-la-to-pa)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit)))))

(defthm xw-mem-mv-nth-2-ia32e-la-to-pa-errors-commute
  (implies
   (and (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))
        (disjoint-p (list index)
                    (open-qword-paddr-list
                     (xlate-governing-qword-addresses
                      lin-addr x86)))
        (canonical-address-p lin-addr))
   (equal (mv-nth
           2
           (ia32e-la-to-pa lin-addr r-w-x (xw :mem index val x86)))
          (xw :mem index val
              (mv-nth
               2
               (ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    xlate-governing-qword-addresses)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit)))))

;; ======================================================================
