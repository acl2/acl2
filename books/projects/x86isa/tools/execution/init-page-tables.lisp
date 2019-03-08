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
; Robert Krug         <rkrug@cs.utexas.edu>

(in-package "X86ISA")

(include-book "init-state"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d () (unsigned-byte-p))))

;; ======================================================================

(defsection Setting-up-Page-Tables
  :parents (Program-Execution)
  :short "Setting up the page tables for a user-level program's run"
  :long "<p>Recall that when the value of the field @('app-view') is
  <tt>nil</tt>, the x86 model offers the system-level view of x86
  machines.  It's only in this view that memory read and write
  functions like @(see rml08) and @(see wml08) will do a page-table
  walk.  See section @(see app-view) for details.</p>" )

;; ======================================================================

;; These functions that take the physical memory address, but
;; otherwise look pretty similar to those defined in
;; x86-init-state.lisp...

(define physical-addr-qword-alistp (alst)
  :parents (Setting-up-Page-Tables)
  :enabled t
  :short "Recognizer for a list of pairs of up to 52-bit wide physical address and byte"
  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((addr  (caar alst))
            (qword (cdar alst))
            (rest  (cdr alst)))
        (and (integerp addr)
             (<= 0 addr)
             (< addr #.*mem-size-in-bytes-7*)
             (n64p qword)
             (physical-addr-qword-alistp rest))))))

(define load-qwords-into-physical-memory
  ((addr-qword-lst "Required to be a @(see physical-addr-qword-alistp)")
   x86)

  :guard (and (not (app-view x86))
              (physical-addr-qword-alistp addr-qword-lst))

  :parents (Setting-up-Page-Tables)
  :short "Load 64-bit entries into the physical memory"
  :returns (x86 x86p :hyp :guard)

  (cond ((endp addr-qword-lst) x86)
        (t (b* ((addr  (caar addr-qword-lst))
                (qword (cdar addr-qword-lst))
                (x86 (wm-low-64 addr qword x86)))
             (load-qwords-into-physical-memory
              (cdr addr-qword-lst) x86))))

  ///
  (defthm app-view-unchanged-after-load-qwords-into-physical-memory
    (equal (xr :app-view 0 (load-qwords-into-physical-memory addr-qword-lst x86))
           (xr :app-view 0 x86))))

(define physical-addr-qword-alist-listp (list)
  :parents (Setting-up-Page-Tables)
  :short "Recognizer for a list of @(see physical-addr-qword-alistp)"
  :enabled t
  (if (atom list)
      (equal list nil)
    (and (physical-addr-qword-alistp (car list))
         (physical-addr-qword-alist-listp (cdr list)))))

(define load-qwords-into-physical-memory-list
  ((addr-qword-list-list "Required to be @(see physical-addr-qword-alist-listp)")
   x86)
  :parents (Setting-up-Page-Tables)
  :short "Load lists of @(see physical-addr-qword-alistp) into the
  physical memory"
  :long "This function can be used to initialize the page tables."
  :guard (and (not (app-view x86))
              (physical-addr-qword-alist-listp addr-qword-list-list))
  :returns (x86 x86p :hyp :guard)
  (if (endp addr-qword-list-list)
      x86
    (b* ((x86 (load-qwords-into-physical-memory (car addr-qword-list-list) x86)))
      (load-qwords-into-physical-memory-list (cdr addr-qword-list-list) x86)))
  ///
  (defthm app-view-unchanged-after-load-qwords-into-physical-memory-list
    (equal (xr :app-view 0 (load-qwords-into-physical-memory-list addr-qword-lst-lst x86))
           (xr :app-view 0 x86))))

;; ======================================================================

#||

Page table set up plan (1GB pages, one-to-one map):

1 page-map level-4 (PML4) table:           512 entries of 8 bytes
                                           each

512 page-directory pointer tables (PDPTs): each has 512 entries of
                                           8 bytes each

Total size: (+ (* 512 8) (* 512 (* 512 8))) = 2,101,248 bytes
                                              (around 2MB)


Here's a description of how the function construct-page-tables sets up the PML4
table and the 512 PDPTs, assuming that the base address of the PML4 is 0, i.e.,
CR3[40:12] = 0. All these 513 tables are placed contiguously in the memory.

     ==================================================
                        PML4 Table
     --------------------------------------------------
           PML4E Address        Aligned PDPT Base Address

                0                       1 (Base address of PDPT # 1   = (ash 1 12))
                8                       2 (Base address of PDPT # 2   = (ash 2 12))
               16                       3 (Base address of PDPT # 3   = (ash 3 12))
                .                       .
                .                       .
                .                       .
                .                       .
             4088                     512 (Base address of PDPT # 512 = (ash 512 12))
     **************************************************

     ==================================================
                       PDPT # 1
     --------------------------------------------------
           PDPTE Address       Aligned Page Frame Address

 (ash 1 12)  4096                       0
             4104                       1
                .                       .
                .                       .
                .                       .
                .                       .
             8184                       511
     **************************************************

     ==================================================
                       PDPT # 2
     --------------------------------------------------
           PDPTE Address       Aligned Page Frame Address

 (ash 2 12) 8192                     512
            8200                     513
               .                       .
               .                       .
               .                       .
           12280                     1023
     **************************************************

                          .
                          .
                          .
                          .

     ==================================================
                     PDPT # 512
     --------------------------------------------------
           PDPTE Address       Aligned Page Frame Address

 (ash 512 12) 2097152                    261632 (= (512 * 511))
              2097160                    261633
                 .                       .
                 .                       .
                 .                       .
             2101240                     262143 (= ((512 * 512) - 1))
     **************************************************

 Note that 2101240 is (+ (ash 512 12) (* 511 8)).

 Here's an example of a virtual address translation, given the above page map
 and CR3[40:12] = 0. Let the virtual address be #x140000000, which is (ash 5
 30).

 (a). Index for PML4E = (part-select (ash 5 30) :low 39 :width 9) = 0
 (b). Corresponding Aligned PDPT Base Address = 1
 (c). Corresponding PDPT Base Address = (ash <value from Step b> 12) = (ash 1 12) = 4096
 (d). Index for PDPTE = (part-select (ash 5 30) :low 30 :width 9) = 5
 (e). Address of the PDPTE = <value from Step c> + <value from Step d>*8 = 4096 + 5*8 = 4136
 (f). Corresponding Aligned Page Frame Address = 5
 (g). Offset from the virtual address = (part-select (ash 5 30) :low 0 :width 30) = 0
 (h). Physical Address = (logior <value from Step g> (ash 5 30)) = (logior 0 (ash 5 30)) = (ash 5 30)

||#


(defthm logand-and-bottom-few-bits-zero
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep p))
                (natp x)
                (natp y)
                (natp p)
                (< 0 p))
           (equal (logand x (ash y p))
                  (ash (logand (logtail p x) y) p)))
  :hints (("Goal" :in-theory (e/d*
                              (acl2::ihsext-inductions
                               acl2::ihsext-recursive-redefs)
                              (bitmaskp**
                               unsigned-byte-p**
                               fty::bitp-when-unsigned-byte-p-1)))))

;; (defthm logand-ash
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (natp p))
;;            (equal (ash (logand x y) p)
;;                   (logand (ash x p) (ash y p))))
;;   :hints (("Goal" :in-theory (e/d*
;;                               (acl2::ihsext-inductions
;;                                acl2::ihsext-recursive-redefs)
;;                               ()))))


(define add-pml4-entry
  ((pdpt-base-addr :type (unsigned-byte 40)))

  :parents (Setting-up-Page-Tables)
  :short "Add a PML4 entry that references a Page-Directory-Pointer
  Table"
  (b* ((64-bit-entry
        ;; Physical address of 4K-aligned PDPT referenced by this
        ;; entry
        (!ia32e-pml4eBits->pdpt pdpt-base-addr 0))
       (64-bit-entry
        ;; Page present
        (!ia32e-pml4eBits->p 1 64-bit-entry))
       (64-bit-entry
        ;; Writes allowed to the 512 GB region controlled by this
        ;; entry
        (!ia32e-pml4eBits->r/w 1 64-bit-entry))
       (64-bit-entry
        ;; User mode accesses allowed in the 512 GB region controlled
        ;; by this entry
        (!ia32e-pml4eBits->u/s 1 64-bit-entry)))

    64-bit-entry)

  ///

  (local (in-theory (e/d (!ia32e-pml4ebits->u/s
                          !ia32e-pml4ebits->r/w
                          !ia32e-pml4ebits->p
                          !ia32e-pml4ebits->pdpt)
                         ())))

  (defthm-unsigned-byte-p n64p-add-pml4-entry
    :hyp t 
    :bound 64
    :concl (add-pml4-entry pdpt-base-addr)
    :gen-linear t
    :gen-type t))

(define construct-pml4-table
  ((entry-number   :type (unsigned-byte 10))
   (entry-addr     :type (unsigned-byte #.*physical-address-size*))
   (pdpt-base-addr :type (unsigned-byte 40))
   acc)

  :guard (physical-addr-qword-alistp acc)

  :measure (nfix (- 512 entry-number))

  :parents (Setting-up-Page-Tables)

  :short "Construct a PML4 table, one entry at a time, each of which
  references a Page-Directory-Pointer Table"

  :long "<p>A PML4 table comprises 512 64-bit entries.</p>"

  (cond ((or (not (integerp entry-number))
             (< entry-number 0)
             (not (unsigned-byte-p 40 (1+ pdpt-base-addr)))
             (not (unsigned-byte-p 10 (1+ entry-number)))
             (not (unsigned-byte-p 52 (+ 8 entry-addr))))
         acc)

        ((< entry-number 512)
         (construct-pml4-table (+ 1 entry-number)
                               (+ 8 entry-addr)
                               (+ 1 pdpt-base-addr)
                               (acons
                                entry-addr
                                (add-pml4-entry pdpt-base-addr)
                                acc)))
        (t acc))

  ///

  (defthm true-listp-construct-pml4-table
    (implies (true-listp acc)
             (true-listp (construct-pml4-table entry-number entry-addr pdpt-base-addr acc)))
    :hints (("Goal" :in-theory (e/d () (force))))
    :rule-classes :type-prescription)

  (defthm consp-construct-pml4-table-helper
    (implies (and (unsigned-byte-p 40 (+ 1 pdpt-base-addr))
                  (unsigned-byte-p 52 (+ 8 entry-addr)))
             (consp (construct-pml4-table 511 entry-addr pdpt-base-addr acc)))
    :hints (("Goal" :expand (construct-pml4-table 511 entry-addr pdpt-base-addr acc))))

  (defthm consp-construct-pml4-table
    (implies (and (unsigned-byte-p 10 entry-number)
                  (< entry-number 512)
                  (unsigned-byte-p 40 (1+ pdpt-base-addr))
                  (unsigned-byte-p 10 (1+ entry-number))
                  (unsigned-byte-p 52 (+ 8 entry-addr)))
             (consp (construct-pml4-table entry-number entry-addr pdpt-base-addr acc)))
    :rule-classes (:type-prescription :rewrite))

  (defthm physical-addr-qword-alistp-construct-pml4-table-helper
    (implies (and (natp entry-addr)
                  (unsigned-byte-p 40 pdpt-base-addr)
                  (physical-addr-qword-alistp acc))
             (physical-addr-qword-alistp
              (construct-pml4-table 511 entry-addr pdpt-base-addr acc)))
    :hints
    (("Goal" :expand (construct-pml4-table 511 entry-addr pdpt-base-addr acc))))

  (defthm physical-addr-qword-alistp-construct-pml4-table
    (implies (and (unsigned-byte-p 40 pdpt-base-addr)
                  (unsigned-byte-p 52 entry-addr)
                  (physical-addr-qword-alistp acc))
             (physical-addr-qword-alistp
              (construct-pml4-table entry-number entry-addr pdpt-base-addr acc)))
    :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (force))))
    :rule-classes :type-prescription))

(define add-pdp-entry
  ((page-base-addr :type (unsigned-byte 22)))

  :parents (Setting-up-Page-Tables)
  :short "Add a PDP entry that maps a 1GB page"

  (b* ((64-bit-entry
        ;; Physical address of 4K-aligned page directory referenced by
        ;; this entry
        (!ia32e-pdpte-1GB-pageBits->page page-base-addr 0))
       (64-bit-entry
        ;; Page present
        (!ia32e-pdpte-1GB-pageBits->p 1 64-bit-entry))
       (64-bit-entry
        ;; Writes allowed to the 512 GB region controlled by this
        ;; entry
        (!ia32e-pdpte-1GB-pageBits->r/w 1 64-bit-entry))
       (64-bit-entry
        ;; User mode accesses allowed in the 512 GB region controlled
        ;; by this entry
        (!ia32e-pdpte-1GB-pageBits->u/s 1 64-bit-entry))
       (64-bit-entry
        ;; Page size = 1: this PDP entry maps a 1 GB page.
        (!ia32e-pdpte-1GB-pageBits->ps 1 64-bit-entry)))

      64-bit-entry)

  ///

  (defthm-unsigned-byte-p n64p-add-pdp-entry
    :hyp t
    :bound 64
    :concl (add-pdp-entry page-base-addr)
    :gen-linear t
    :gen-type t))

(define construct-pdp-table
  ((entry-number   :type (unsigned-byte 10))
   (entry-addr     :type (unsigned-byte #.*physical-address-size*))
   (page-base-addr :type (unsigned-byte 22))
   acc)

  :guard (alistp acc)

  :parents (Setting-up-Page-Tables)
  :short "Construct a PDP table, one entry at a time, each of which
  map a 1GB page"

  :long "<p>A PDP table comprises 512 64-bit entries.</p>"

  :measure (nfix (- 512 entry-number))

  (cond ((or (not (integerp entry-number))
             (< entry-number 0)
             (not (unsigned-byte-p 22 (1+ page-base-addr)))
             (not (unsigned-byte-p 10 (1+ entry-number)))
             (not (unsigned-byte-p 52 (+ 8 entry-addr))))
         acc)
        ((< entry-number 512)
         (construct-pdp-table (+ 1 entry-number)
                              (+ 8 entry-addr)
                              (+ 1 page-base-addr)
                              (acons entry-addr
                                     (add-pdp-entry page-base-addr)
                                     acc)))
        (t acc))

  ///

  (defthm true-listp-construct-pdp-table
    (implies (true-listp acc)
             (true-listp (construct-pdp-table
                          entry-number entry-addr page-base-addr acc))))

  (defthm consp-construct-pdp-table-helper
    (implies (and (unsigned-byte-p 52 (+ 8 entry-addr))
                  (unsigned-byte-p 22 (+ 1 page-base-addr)))
             (consp (construct-pdp-table 511 entry-addr page-base-addr acc)))
    :hints (("Goal" :expand (construct-pdp-table 511 entry-addr page-base-addr acc))))

  (defthm consp-construct-pdp-table
    (implies (and (< entry-number 512)
                  (unsigned-byte-p 10 entry-number)
                  (unsigned-byte-p 10 (+ 1 entry-number))
                  (unsigned-byte-p 52 (+ 8 entry-addr))
                  (unsigned-byte-p 22 (+ 1 page-base-addr)))
             (consp (construct-pdp-table entry-number entry-addr page-base-addr acc)))
    :rule-classes (:type-prescription :rewrite))

  (defthm physical-addr-qword-alistp-construct-pdp-table-helper
    (implies(and (natp entry-addr)
                 (physical-addr-qword-alistp acc)
                 (unsigned-byte-p 22 page-base-addr))
            (physical-addr-qword-alistp (construct-pdp-table 511 entry-addr page-base-addr acc)))
    :hints (("Goal" :expand (construct-pdp-table 511 entry-addr page-base-addr acc))))

  (defthm physical-addr-qword-alistp-construct-pdp-table
    (implies (and (natp entry-addr)
                  (physical-addr-qword-alistp acc)
                  (unsigned-byte-p 22 page-base-addr))
             (physical-addr-qword-alistp
              (construct-pdp-table entry-number entry-addr page-base-addr acc)))
    :rule-classes (:type-prescription :rewrite)))

(define construct-pdp-tables
  ((table-number   :type (unsigned-byte 10))
   (pdpt-base-addr :type (unsigned-byte 40))
   acc)

  :guard (alistp acc)

  :parents (Setting-up-Page-Tables)
  :short "Construct PDP tables, where each table has entries that map
  a 1GB page"

  :long "<p>PML4 tables contain 512 64-bit entries, and in our current
  setup, each of those 512 entries point to a PDP table. Thus, we need
  to construct 512 PDP tables. In our current setup, each PDPTE maps a
  1GB page.</p>"

  :measure (nfix (- 512 table-number))

  (cond ((not (and (natp table-number)
                   (unsigned-byte-p 22 (* 512 table-number))
                   (unsigned-byte-p 40 (+ 1 pdpt-base-addr))
                   (unsigned-byte-p 10 (+ 1 table-number))
                   (unsigned-byte-p 22 (+ 1 (* 512 table-number)))
                   (unsigned-byte-p 52 (+ 8 (ash pdpt-base-addr 12)))))
         acc)
        ((< table-number 512)
         (b* ((table (construct-pdp-table 0
                                          (ash pdpt-base-addr 12)
                                          (* 512 table-number)
                                          nil))
              (acc (cons table acc)))
           (construct-pdp-tables (+ 1 table-number)
                                 (+ 1 pdpt-base-addr)
                                 acc)))
        (t acc))
  ///

  (defthm physical-addr-qword-alist-listp-construct-pdp-tables
    (implies (and (physical-addr-qword-alist-listp acc)
                  (unsigned-byte-p 40 pdpt-base-addr))
             (physical-addr-qword-alist-listp
              (construct-pdp-tables table-number pdpt-base-addr acc)))
    :rule-classes (:type-prescription :rewrite)))

(define construct-page-tables
  ;; cr3 register's pdb field is 40 bits. (ash pdb 12) should be the
  ;; constant passed to construct-page-tables.
  ((pml4-base-address :type (unsigned-byte 52)))

  :parents (Setting-up-Page-Tables)

  :short "Construct page tables that do linear address translation to
  1GB page using IA32e paging"

  (let*
      ((pml4-base-address40 (loghead 40 (logtail 12 pml4-base-address))))
    (if
        ;; We must have enough room for all the tables.
        ;; (< (+ 4096 (* 512 4096) pml4-base-address)
        ;;    #.*mem-size-in-bytes*)
        (and (unsigned-byte-p 40 (1+ (+ 1 pml4-base-address40)))
             (unsigned-byte-p 40 (1+ pml4-base-address40))
             (unsigned-byte-p 52 (+ 8 pml4-base-address)))

        (let* ((table (construct-pml4-table 0
                                            pml4-base-address
                                            (+ 1 pml4-base-address40)
                                            nil))
               (acc (list table)))
          (construct-pdp-tables 0
                                (+ 1 pml4-base-address40)
                                acc))
      nil))

  ///

  (defthm physical-addr-qword-alist-listp-construct-page-tables
    (implies (unsigned-byte-p 52 pml4-base-address)
             (physical-addr-qword-alist-listp
              (construct-page-tables pml4-base-address)))
    :rule-classes (:type-prescription :rewrite)))

(defconst *1-gig-page-tables* (construct-page-tables 0))

(defthm test-of-const
  (and (true-listp *1-gig-page-tables*)
       (physical-addr-qword-alist-listp *1-gig-page-tables*))
  :rule-classes nil)

(defun is-la-mapped-to-pa? (n)
  ;; Note that cr3 is 0, which is where the page tables are located.
  (with-local-stobj
    x86
    (mv-let
      (result x86)
      (b* ((x86 (xw :app-view 0 nil x86))
           (x86
            (load-qwords-into-physical-memory-list *1-gig-page-tables* x86))

           (cr0        (ctri *cr0*       x86))
           (cr4        (ctri *cr4*       x86))
           (ia32e-efer (msri *ia32_efer-idx* x86))

           (cr0        (!cr0Bits->pg        1 cr0))
           (cr4        (!cr4Bits->pae       1 cr4))
           (ia32e-efer (!ia32_eferBits->lme 1 ia32e-efer))

           (x86 (!ctri *cr0*           cr0        x86))
           (x86 (!ctri *cr4*           cr4        x86))
           (x86 (!msri *ia32_efer-idx* ia32e-efer x86))
           (r-w-x :r))
        (mv-let (flag addr x86)
          (la-to-pa n r-w-x x86)
          (mv (and (equal flag nil)
                   (equal addr n))
              x86)))
      result)))

(defthm is-la-mapped-to-pa?-thm-1
  (is-la-mapped-to-pa? 2047))

(defthm is-la-mapped-to-pa?-thm-2
  (is-la-mapped-to-pa? (+ 2047 (expt 2 35) (expt 2 40))))

(defthm is-la-mapped-to-pa?-thm-3
  (and (canonical-address-p 0)
       (is-la-mapped-to-pa? 0)))

(defthm is-la-mapped-to-pa?-thm-4
  (and (canonical-address-p (1- (expt 2 47)))
       (is-la-mapped-to-pa? (1- (expt 2 47)))))

;; (defthm is-la-mapped-to-pa?-thm-5
;; ;; Note that is-la-mapped-to-pa?-thm-5 is not a theorem because
;; ;; *1-gig-page-tables* map 0 to 2^47-1 only. The higher address
;; ;; space is unmapped.
;;   (and (canonical-address-p (n64-to-i64 (- (expt 2 64) (expt 2 47))))
;;        (is-la-mapped-to-pa? (n64-to-i64 (- (expt 2 64) (expt 2 47))))))

;; ======================================================================
