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

;; When modifying this to accomodate the TLB, I made some changes to how these
;; lemmas are structured. Originally, most of these lemmas had page table
;; accesses performed in terms of rb/wb (i.e. virtual memory) which required
;; many disjoint-p($) hypotheses. This made these lemmas difficult to work
;; with. When updating this file to accomodate the TLB, I changed the majority
;; of this file to perform page table accesses in terms of rm-low-64/wm-low-64
;; (i.e. physical memory) which simplified them greatly. At the end of this
;; file, I used these lemmas to prove the same facts in terms of virtual
;; memory.

(in-package "X86ISA")

(include-book "zeroCopy-init")

(local (in-theory (e/d* (x86-operation-mode)
                        (unsigned-byte-p signed-byte-p))))

;; ACL2's default ancestors-check kills me --- for instance, it
;; doesn't let the hyps of ia32e-la-to-pa-values-for-same-1G-page be
;; relieved.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

;; ----------------------------------------------------------------------

;; Rewriting (mv-nth 1 (rb ...)) to rm-low-64 if the lin-addr is
;; direct-mapped:

(defthm-using-gl rb-and-rm-low-64-for-direct-map-helper-1
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl
  (equal (logior a (ash b 8)
                 (ash (logior c (ash d 8)) 16)
                 (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
         (logior a (ash (logior b
                                (ash (logior c
                                             (ash (logior d
                                                          (ash (logior
                                                                e
                                                                (ash (logior
                                                                      f
                                                                      (ash (logior
                                                                            g (ash h 8))
                                                                           8))
                                                                     8))
                                                               8))
                                                  8))
                                     8))
                        8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(defthm-using-gl rb-and-rm-low-64-for-direct-map-helper-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal (loghead
                 64
                 (logior a
                         (ash b 8)
                         (ash (logior c (ash d 8)) 16)
                         (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32)))
                (logior a
                        (ash b 8)
                        (ash (logior c (ash d 8)) 16)
                        (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(defthm-using-gl rml64-direct-map-helper
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior
           a
           (ash (logior
                 b
                 (ash (logior
                       c
                       (ash (logior
                             d
                             (ash (logior
                                   e
                                   (ash (logior f (ash (logior g (ash h 8)) 8))
                                        8))
                                  8))
                            8))
                      8))
                8))
          (logior a (ash b 8)
                  (ash (logior c (ash d 8)) 16)
                  (ash (logior e (ash f 8) (ash (logior g (ash h 8)) 16)) 32)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(in-theory (e/d* () (rb-and-rm-low-64-for-direct-map-helper-1
                     rb-and-rm-low-64-for-direct-map-helper-2
                     rml64-direct-map-helper)))

(defthm rb-and-rm-low-64-for-direct-map
  (implies (and
            (64-bit-modep x86) ; added
            (direct-map-p 8 direct-mapped-addr r-w-x  (double-rewrite x86))
            ;; The physical addresses corresponding to
            ;; direct-mapped-addr to (+ 7 direct-mapped-addr) are
            ;; disjoint from their own translation-governing
            ;; addresses.
            (disjoint-p$
             (mv-nth 1 (las-to-pas 8 direct-mapped-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs
              8 direct-mapped-addr (double-rewrite x86)))
            (not (mv-nth 0 (las-to-pas 8 direct-mapped-addr r-w-x (double-rewrite x86))))
            (physical-address-p direct-mapped-addr)
            (canonical-address-p (+ 7 direct-mapped-addr))
            (not (app-view x86))
            (x86p x86))
           (equal (mv-nth 1 (rb 8 direct-mapped-addr r-w-x x86))
                  (rm-low-64 direct-mapped-addr (double-rewrite x86))))
  :hints (("Goal"
           :use ((:instance rewrite-read-from-physical-memory-to-rm-low-64
                            (p-addrs (addr-range 8 direct-mapped-addr))
                            (index direct-mapped-addr)
                            (x86 x86))
                 (:instance rb-and-rm-low-64-for-direct-map-helper-2
                            (a (xr :mem      direct-mapped-addr  x86))
                            (b (xr :mem (+ 1 direct-mapped-addr) x86))
                            (c (xr :mem (+ 2 direct-mapped-addr) x86))
                            (d (xr :mem (+ 3 direct-mapped-addr) x86))
                            (e (xr :mem (+ 4 direct-mapped-addr) x86))
                            (f (xr :mem (+ 5 direct-mapped-addr) x86))
                            (g (xr :mem (+ 6 direct-mapped-addr) x86))
                            (h (xr :mem (+ 7 direct-mapped-addr) x86))))
           :in-theory (e/d* (rb
                             disjoint-p$
                             direct-map-p
                             rm-low-64
                             rm-low-32
                             n08p
                             unsigned-byte-p
                             signed-byte-p
                             rml64-direct-map-helper)
                            (rb-and-rm-low-64-for-direct-map-helper-1
                             rb-and-rm-low-64-for-direct-map-helper-2
                             xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                             bitops::loghead-of-logior
                             (:linear bitops::logior-<-0-linear-2)
                             (:rewrite bitops::ash-<-0)
                             (:rewrite acl2::ash-0)
                             (:rewrite acl2::zip-open)
                             (:linear <=-logior)
                             (:linear bitops::logior->=-0-linear)
                             (:linear bitops::logior-<-0-linear-1))))))

;; ======================================================================

;; We now compute the physical address corresponding to (+ n lin-addr)
;; that is returned by ia32e-la-to-pa, given that (+ n lin-addr) lies
;; in the same 1G page as lin-addr.  We then generalize this result to
;; las-to-pas (from ia32e-la-to-pa).

(defthm-using-gl same-pml4-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (physical-address-p pml4-table-base-addr)
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (pml4-table-entry-addr (+ n lin-addr) pml4-table-base-addr)
                (pml4-table-entry-addr lin-addr pml4-table-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pml4-table-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl same-pdp-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (unsigned-byte-p 30 n)
            (physical-address-p pdpt-base-addr)
            (canonical-address-p lin-addr)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (page-dir-ptr-table-entry-addr (+ n lin-addr) pdpt-base-addr)
                (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pdpt-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl loghead-30-of-1G-aligned-lin-addr-+-n-1
  :hyp (and (canonical-address-p lin-addr)
            (canonical-address-p (+ n lin-addr))
            (equal (loghead 30 lin-addr) 0)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 (+ n lin-addr)) n)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl loghead-30-of-1G-aligned-lin-addr-+-n-2
  :hyp (and (equal (loghead 30 (+ n lin-addr)) n)
            (canonical-address-p (+ n lin-addr))
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 lin-addr) 0)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl logior-to-+-for-ash-x-30
  :hyp (and (unsigned-byte-p 22 x)
            (unsigned-byte-p 30 n))
  :concl (equal (logior n (ash x 30)) (+ n (ash x 30)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64) (:nat x 64))))

(defthmd ia32e-la-to-pa-page-dir-ptr-table-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa-page-dir-ptr-table for the linear address (+ n
  ;; lin-addr), where this address lies in the same 1G page as
  ;; lin-addr.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal page-dir-ptr-table-entry
           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
    (not
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr base-addr u/s-acc r/w-acc x/d-acc
       wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86)))

    (equal (page-size page-dir-ptr-table-entry) 1)
    (canonical-address-p (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 lin-addr) 0)
    (unsigned-byte-p 30 n)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    (+ n lin-addr) base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))
           nil)
    (equal (mv-nth 1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    (+ n lin-addr) base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86))
           (+ n
              (ash
               (loghead 22 (logtail
                            30
                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86)))
               30)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    ia32e-pdpte-1gb-pagebits->page)
                                   (commutativity-of-+
                                    not
                                    bitops::logand-with-negated-bitmask)))))

(defthmd ia32e-la-to-pa-pml4-table-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa-pml4-table for the linear address (+ n lin-addr),
  ;; where this address lies in the same 1G page as lin-addr.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (rm-low-64 page-dir-ptr-table-entry-addr x86))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0
                 (ia32e-la-to-pa-pml4-table
                  lin-addr pml4-table-base-addr wp smep smap ac nxe implicit-supervisor-access :r cpl x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 lin-addr) 0)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0
                   (ia32e-la-to-pa-pml4-table (+ n lin-addr) pml4-table-base-addr
                                              wp smep smap ac nxe implicit-supervisor-access :r cpl x86))
           nil)
    (equal (mv-nth 1
                   (ia32e-la-to-pa-pml4-table (+ n lin-addr) pml4-table-base-addr
                                              wp smep smap ac nxe implicit-supervisor-access :r cpl x86))
           (+ n (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
                     30)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                             pdpt-base-addr
                             ia32e-la-to-pa-page-dir-ptr-table-values-for-same-1G-page
                             cr3bits->pdb
                             ia32e-pml4ebits->pdpt)
                            (commutativity-of-+
                             not
                             bitops::logand-with-negated-bitmask)))))

(defthmd ia32e-la-to-pa-without-tlb-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa-pml4-table for the linear address (+ n lin-addr),
  ;; where this address lies in the same 1G page as lin-addr.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (rm-low-64 page-dir-ptr-table-entry-addr x86))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 lin-addr) 0)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa-without-tlb (+ n lin-addr) :r x86))
           nil)
    (equal (mv-nth 1 (ia32e-la-to-pa-without-tlb (+ n lin-addr) :r x86))
           (+ n (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
                     30)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-without-tlb
                             pdpt-base-addr
                             pml4-table-base-addr
                             ia32e-la-to-pa-pml4-table-values-for-same-1G-page
                             cr3bits->pdb)
                            (commutativity-of-+
                             not
                             bitops::logand-with-negated-bitmask)))))

;; Now generalizing ia32e-la-to-pa-values-for-same-1G-page to
;; las-to-pas:

(defthm-using-gl open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 lin-addr m))
            (integerp m)
            (<= m *2^30*)
            (natp iteration)
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (loghead 30 (+ iteration lin-addr)) iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(defthm-using-gl open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
  :hyp (and (< iteration m)
            (integerp m)
            (<= m *2^30*)
            (natp iteration))
  :concl (unsigned-byte-p 30 iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat iteration 64) (:nat m 64))))

(defthm-using-gl open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 lin-addr m))
            (integerp m)
            (<= m 1073741824)
            (natp iteration)
            (equal (loghead 30 lin-addr) 0))
  :concl (canonical-address-p (+ iteration lin-addr))
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(defthm-using-gl open-mv-nth-1-las-to-pas-for-same-1G-page-general-2
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 30 lin-addr) 0))
  :concl
  ;; (canonical-address-p (+ -1 *2^30* lin-addr))
  (canonical-address-p (+ 1073741823 lin-addr))
  :g-bindings (gl::auto-bindings (:nat lin-addr 64)))

;; ======================================================================

(defthm unsigned-byte-p-52-of-pdpt-base-addr
  (unsigned-byte-p 52 (pdpt-base-addr lin-addr x86))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr) ()))))

(defthm same-pdpt-base-addr-for-n-+-lin-addrs
  (implies (and (canonical-address-p lin-addr)
                (unsigned-byte-p 30 iteration)
                (equal (loghead 30 lin-addr) 0)
                (x86p x86))
           (equal (pdpt-base-addr (+ iteration lin-addr) x86)
                  (pdpt-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr) (not)))))

;; We define las-to-pas-without-tlb because it makes it easier to apply the
;; later theorems to our program
(define las-to-pas-without-tlb
    ((iteration natp)
     (n        natp "Number of bytes to be read")
     (lin-addr integerp "First linear address")
     (r-w-x    :type (member :r :w :x) "Type of memory access: read, write, or execute")
     x86)
    :guard  (and (not (app-view x86))
                 (<= iteration n)) ;; Not x86 "flat" mode or ``app(lication) mode''
    :guard-hints (("Goal" :in-theory (enable canonical-address-p)))
    :measure (nfix (- n iteration))
    :verify-guards t
    :returns (mv flg
                 (p-addrs  true-listp :rule-classes (:rewrite :type-prescription))
                 (x86      x86p :hyp (x86p x86) :hints (("Goal" :in-theory (e/d () (x86p))))))

    (if (zp (- n iteration))
        (mv nil nil x86)
      (b* (((unless (canonical-address-p (+ iteration lin-addr)))
            (mv t nil x86))
           ((mv flg p-addr x86)
            (ia32e-la-to-pa-without-tlb (+ iteration lin-addr) r-w-x x86))
           ((when flg) (mv flg nil x86))
           ((mv flgs p-addrs x86)
            (las-to-pas-without-tlb (1+ iteration) n lin-addr r-w-x x86)))
        (mv flgs (if flgs nil (cons p-addr p-addrs)) x86)))

    ///
    (defthm mv-nth-0-las-to-pas-without-tlb-xlate-equiv-memory-cong
            (implies (xlate-equiv-memory x86-1 x86-2)
                     (equal (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-1))
                            (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-2))))
            :rule-classes :congruence)

    (defthm mv-nth-1-las-to-pas-without-tlb-xlate-equiv-memory-cong
            (implies (xlate-equiv-memory x86-1 x86-2)
                     (equal (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-1))
                            (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-2))))
            :rule-classes :congruence)

    (defthm mv-nth-2-las-to-pas-without-tlb-xlate-equiv-memory-cong
            (implies (xlate-equiv-memory x86-1 x86-2)
                     (xlate-equiv-memory (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-1))
                                         (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86-2))))
            :rule-classes :congruence)

    (defthm mv-nth-2-las-to-pas-without-tlb-xlate-equiv-memory
            (implies (64-bit-modep x86)
                     (xlate-equiv-memory (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86))
                                         x86)))

    (make-event
      (generate-xr-over-write-thms
        (remove-elements-from-list
          '(:mem :fault)
          *x86-field-names-as-keywords*)
        'las-to-pas-without-tlb
        (acl2::formals 'las-to-pas-without-tlb (w state))
        :output-index 2))

    (local
      (defun-nx las-to-pas-without-tlb-xw-rflags-not-ac-hint (iteration lin-addr n r-w-x value x86)
                (declare (xargs :measure (nfix (- n iteration))))
                (if (zp (- n iteration))
                  x86
                  (if (not (canonical-address-p lin-addr))
                    x86
                    (if (mv-nth 0 (ia32e-la-to-pa-without-tlb (+ iteration lin-addr) r-w-x x86))
                      x86
                      (las-to-pas-without-tlb-xw-rflags-not-ac-hint
                        (1+ iteration) lin-addr n r-w-x value
                        (mv-nth 2 (ia32e-la-to-pa-without-tlb (+ iteration lin-addr) r-w-x x86))))))))

    (defthm xr-rflags-las-to-pas-without-tlb
            (implies (not (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x (double-rewrite x86))))
                     (equal (xr :rflags nil (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))
                            (xr :rflags nil (double-rewrite x86))))
            :hints (("Goal"
                     :induct (las-to-pas-without-tlb-xw-rflags-not-ac-hint
                               iteration lin-addr n r-w-x value x86)
                     :in-theory (e/d* () (force (force))))))

    (defthm xr-fault-las-to-pas-without-tlb
            (implies (not (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x (double-rewrite x86))))
                     (equal (xr :fault nil (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))
                            (xr :fault nil (double-rewrite x86))))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (make-event
      (generate-read-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas-without-tlb
        (acl2::formals 'las-to-pas-without-tlb (w state))
        :output-index 0))

    (make-event
      (generate-read-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas-without-tlb
        (acl2::formals 'las-to-pas-without-tlb (w state))
        :output-index 1))

    (defrule 64-bit-modep-of-las-to-pas-without-tlb
             (equal (64-bit-modep (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))
                    (64-bit-modep x86))
             :hints (("Goal" :in-theory (e/d* (64-bit-modep) (force (force))))))

    (defrule x86-operation-mode-of-las-to-pas-without-tlb
             (equal (x86-operation-mode (mv-nth 2 (las-to-pas-without-tlb iteratio n lin-addr r-w-x x86)))
                    (x86-operation-mode x86))
             :hints (("Goal" :in-theory (e/d* (x86-operation-mode) ()))))

    (make-event
      (generate-write-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas-without-tlb
        (acl2::formals 'las-to-pas-without-tlb (w state))
        :output-index 2))

    (defthm las-to-pas-without-tlb-xw-rflags-not-ac
            (implies (and (equal (rflagsBits->ac value)
                                 (rflagsBits->ac (rflags (double-rewrite x86))))
                          ;; These are since I chose to use xlate-equiv-memory
                          ;; instead of induction to prove this since induction
                          ;; was hard and I can live with these hypotheses
                          (64-bit-modep x86)
                          (not (app-view x86)))
                     (and
                       (equal (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x (xw :rflags nil value x86)))
                              (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x (double-rewrite x86))))
                       (equal (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x (xw :rflags nil value x86)))
                              (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x (double-rewrite x86))))))
            :hints (("Goal" :in-theory (e/d () (las-to-pas-without-tlb force (force))))))

    (defthm las-to-pas-without-tlb-xw-rflags-state-not-ac
            (implies (equal (rflagsBits->ac value)
                            (rflagsBits->ac (rflags x86)))
                     (equal (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x (xw :rflags nil value x86)))
                            (xw :rflags nil value (mv-nth 2 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthmd las-to-pas-without-tlb-when-tlb-consistent
             (implies (and (64-bit-modep x86)
                           (tlb-consistent-n (- n iteration) (+ iteration lin-addr) r-w-x x86))
                      (and (equal (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86))
                                  (mv-nth 0 (las-to-pas (- n iteration) (+ iteration lin-addr) r-w-x x86)))
                           (equal (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86))
                                  (mv-nth 1 (las-to-pas (- n iteration) (+ iteration lin-addr) r-w-x x86)))))
             :hints (("Goal"
                      :in-theory (enable las-to-pas tlb-consistent-n)
                      :expand ((las-to-pas (+ (- iteration) n) (+ iteration lin-addr) r-w-x x86)))))

    (defthmd las-to-pas-values-are-las-to-pas-without-tlb-when-tlb-consistent
             (implies (and (64-bit-modep x86)
                           (natp n)
                           (canonical-address-p (+ lin-addr n -1))
                           (canonical-address-p lin-addr)
                           (tlb-consistent-n n lin-addr r-w-x x86))
                      (and (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x x86))
                                  (mv-nth 0 (las-to-pas-without-tlb 0 n lin-addr r-w-x x86)))
                           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))
                                  (mv-nth 1 (las-to-pas-without-tlb 0 n lin-addr r-w-x x86)))))
             :hints (("Goal"
                      :use (:instance las-to-pas-without-tlb-when-tlb-consistent
                                      (iteration 0)))))

    (defthm las-to-pas-without-tlb-values-wb-disjoint-p
            (implies (and (disjoint-p (all-xlation-governing-entries-paddrs (- n iteration)
                                                                            (+ iteration lin-addr) x86)
                                      (mv-nth 1 (las-to-pas n-w lin-addr-w :w x86)))
                          (integerp iteration)
                          (canonical-address-p lin-addr)
                          (64-bit-modep x86))
                     (and (equal (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x
                                                                   (mv-nth 1 (wb n-w lin-addr-w w wval x86))))
                                 (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))
                          (equal (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x
                                                                   (mv-nth 1 (wb n-w lin-addr-w w wval x86))))
                                 (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))))
            :hints (("Goal"
                     :do-not '(generalize)
                     :induct (las-to-pas-without-tlb iteration n lin-addr r-w-x
                                                     (mv-nth 1 (wb n-w lin-addr-w w wval x86))))
                    (and (consp (car id))
                         (< 1 (len (car id)))
                         '(:in-theory (enable disjoint-p disjoint-p-commutative all-xlation-governing-entries-paddrs)
                                      :expand ((all-xlation-governing-entries-paddrs (+ (- iteration) n)
                                                                                     (+ iteration lin-addr)
                                                                                     x86)
                                               (las-to-pas-without-tlb iteration n lin-addr r-w-x x86))
                                      :use (:instance disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs
                                                      (n (- n iteration))
                                                      (addr (+ iteration lin-addr))
                                                      (a (+ iteration lin-addr))
                                                      (other-p-addrs (mv-nth 1 (las-to-pas n-w lin-addr-w :w x86))))))))

    (defthm las-to-pas-without-tlb-values-las-to-pas
            (implies (64-bit-modep x86)
                     (and (equal (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x
                                                                   (mv-nth 2 (las-to-pas n2 lin-addr2 r-w-x2 x86))))
                                 (mv-nth 0 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))
                          (equal (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x
                                                                   (mv-nth 2 (las-to-pas n2 lin-addr2 r-w-x2 x86))))
                                 (mv-nth 1 (las-to-pas-without-tlb iteration n lin-addr r-w-x x86)))))))

(defthmd las-to-pas-without-tlb-values-for-same-1G-page
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size (rm-low-64 page-dir-ptr-table-entry-addr x86)) 1)

    (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas-without-tlb iteration m lin-addr :r x86)) nil)
    (equal (mv-nth 1 (las-to-pas-without-tlb iteration m lin-addr :r x86))
           (addr-range
            (+ (- iteration) m)
            (+ iteration
               (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
                    30))))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64
                                   (page-dir-ptr-table-entry-addr
                                     lin-addr
                                     (ash
                                       (loghead
                                         40
                                         (logtail
                                           12
                                           (rm-low-64
                                             (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                                             x86)))
                                       12))
                                   (mv-nth 2
                                           (ia32e-la-to-pa-without-tlb (+ iteration lin-addr)
                                                                       :r x86))))
                            (e-2 (rm-low-64
                                   (page-dir-ptr-table-entry-addr
                                     lin-addr
                                     (ash
                                       (loghead
                                         40
                                         (logtail
                                           12
                                           (rm-low-64
           ;; :induct (las-to-pas-alt iteration m lin-addr :r x86)
           ;; :expand ((:free (x) (addr-range (+ (- iteration) m) x)))
                                             (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                                             x86)))
                                       12))
                                   x86))))
           :in-theory (e/d* (las-to-pas-without-tlb
                              ia32e-la-to-pa-without-tlb-values-for-same-1G-page
                              open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                              open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                              open-mv-nth-1-las-to-pas-for-same-1G-page-general-1)
                            (rewrite-rb-to-rb-alt
                              not
                              mv-nth-0-las-to-pas-subset-p
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                              mv-nth-1-las-to-pas-returns-nil-when-error
                              mv-nth-1-las-to-pas-when-error
                              marking-view
                              pml4-table-entry-addr
                              page-dir-ptr-table-entry-addr
                              page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

(define las-to-pas-alt (iteration count lin-addr r-w-x x86)
  :enabled t
  :measure (nfix (- count iteration))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p
                                          signed-byte-p)
                                         ())))
  :guard (and (natp count)
              (natp iteration)
              (<= iteration count)
              (canonical-address-p lin-addr)
              (canonical-address-p (+ (- count iteration) lin-addr))
              (member-equal r-w-x '(:r :w :x))
              (not (app-view x86)))
  (if (zp (- count iteration))
      (mv nil nil x86)
    (b* (((unless (canonical-address-p (+ iteration lin-addr)))
          (mv t nil x86))
           ;; :induct (las-to-pas-alt iteration m lin-addr :r x86)
           ;; :expand ((:free (x) (addr-range (+ (- iteration) m) x)))
         ((mv flg p-addr x86)
          (ia32e-la-to-pa (+ iteration lin-addr) r-w-x x86))
         ((when flg) (mv flg nil x86))
         ((mv flgs p-addrs x86)
          (las-to-pas-alt (1+ iteration) count lin-addr r-w-x x86)))
      (mv flgs (if flgs nil (cons p-addr p-addrs)) x86)))
  ///

  (defthmd las-to-pas-alt-is-las-to-pas
    (implies (64-bit-modep x86) ; added
             (equal (las-to-pas-alt iteration count lin-addr r-w-x x86)
                    (las-to-pas (- count iteration) (+ iteration lin-addr) r-w-x x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

  (defthm paging-equiv-memory-and-mv-nth-0-las-to-pas-alt-cong
    (implies (paging-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x x86-1))
                    (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (las-to-pas-alt-is-las-to-pas) ())))
    :rule-classes :congruence)

  (defthm paging-equiv-memory-and-mv-nth-1-las-to-pas-alt-cong
    (implies (paging-equiv-memory x86-1 x86-2)
             (equal (mv-nth 1 (las-to-pas-alt iteration count lin-addr r-w-x x86-1))
                    (mv-nth 1 (las-to-pas-alt iteration count lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (las-to-pas-alt-is-las-to-pas) ())))
    :rule-classes :congruence)

  (defthm paging-equiv-memory-with-mv-nth-2-las-to-pas-alt
    (implies (64-bit-modep x86) ; added
             (paging-equiv-memory
              (mv-nth 2 (las-to-pas-alt iteration count lin-addr r-w-x x86))
              (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas-alt-is-las-to-pas) ()))))

  (defthm paging-equiv-memory-with-two-mv-nth-2-las-to-pas-alt-cong
    (implies (paging-equiv-memory x86-1 x86-2)
             (paging-equiv-memory
              (mv-nth 2 (las-to-pas-alt iteration count lin-addr r-w-x x86-1))
              (mv-nth 2 (las-to-pas-alt iteration count lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (las-to-pas-alt-is-las-to-pas) ())))
    :rule-classes :congruence)

  ;; Should follow from the above, but for some reason in some contexts
  ;; ACL2 does not figure this out
  (defthm las-to-pas-alt-and-mv-nth-2-ia32e-la-to-pa
    (implies (64-bit-modep x86)
             (equal (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x
                                              (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 x86))))
                    (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x x86)))))

  ;; Again, should follow from above
  (defthm las-to-pas-alt-and-mv-nth-2-las-to-pas
    (implies (64-bit-modep x86)
             (equal (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x
                                              (mv-nth 2 (las-to-pas n addr r-w-x-2 x86))))
                    (mv-nth 0 (las-to-pas-alt iteration count lin-addr r-w-x x86))))))

(defthmd las-to-pas-values-for-same-1G-page-general
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size (rm-low-64 page-dir-ptr-table-entry-addr x86)) 1)

    (tlb-consistent-n m lin-addr :r x86)
    (not (mv-nth 0 (las-to-pas m lin-addr :r x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas-alt iteration m lin-addr :r x86)) nil)
    (equal (mv-nth 1 (las-to-pas-alt iteration m lin-addr :r x86))
           (addr-range
            (+ (- iteration) m)
            (+ iteration
               (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
                    30))))))
  :hints (("Goal"
           ;; :induct (las-to-pas-alt iteration m lin-addr :r x86)
           ;; :expand ((:free (x) (addr-range (+ (- iteration) m) x)))
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64
                                   (page-dir-ptr-table-entry-addr
                                     lin-addr
                                     (ash
                                       (loghead
                                         40
                                         (logtail
                                           12
                                           (rm-low-64
                                             (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                                             x86)))
                                       12))
                                   (mv-nth 2
                                           (ia32e-la-to-pa (+ iteration lin-addr)
                                                           :r x86))))
                            (e-2 (rm-low-64
                                   (page-dir-ptr-table-entry-addr
                                     lin-addr
                                     (ash
                                       (loghead
                                         40
                                         (logtail
                                           12
                                           (rm-low-64
                                             (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                                             x86)))
                                       12))
                                   x86))))
           :expand ((las-to-pas m lin-addr :r x86))
           :in-theory (e/d* (las-to-pas-alt
                              ia32e-la-to-pa-without-tlb-values-for-same-1G-page
                              open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                              open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                              open-mv-nth-1-las-to-pas-for-same-1G-page-general-1)
                            (rewrite-rb-to-rb-alt
                              not
                              mv-nth-0-las-to-pas-subset-p
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                              mv-nth-1-las-to-pas-returns-nil-when-error
                              mv-nth-1-las-to-pas-when-error
                              marking-view
                              pml4-table-entry-addr
                              page-dir-ptr-table-entry-addr
                              page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

(defthmd las-to-pas-values-for-same-1G-page
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size (rm-low-64 page-dir-ptr-table-entry-addr x86)) 1)

    (tlb-consistent-n *2^30* lin-addr :r x86)
    (not (mv-nth 0 (las-to-pas *2^30* lin-addr :r x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas *2^30* lin-addr :r x86)) nil)
    (equal (mv-nth 1 (las-to-pas *2^30* lin-addr :r x86))
           (addr-range
            *2^30*
            (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
             30)))))
  :hints (("Goal"
           :use ((:instance las-to-pas-values-for-same-1G-page-general
                            (iteration 0)
                            (m *2^30*)))
           :in-theory (e/d* (las-to-pas-alt-is-las-to-pas)
                            (not
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

;; ======================================================================

;; Begin proof of
;; all-xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr:

;; First, we compute the translation-governing addresses corresponding
;; to (+ n lin-addr), given that (+ n lin-addr) lies in the same 1G
;; page as lin-addr.  We then generalize this result to
;; all-xlation-governing-entries-paddrs (from
;; xlation-governing-entries-paddr).

(defthmd xlation-governing-entries-paddrs-for-same-1G-page
  ;; Similar to ia32e-la-to-pa-values-for-same-1G-page, but for
  ;; xlation-governing-entries-paddrs.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 lin-addr) 0)
    (unsigned-byte-p 30 n)
    (x86p x86))
   (equal (xlation-governing-entries-paddrs (+ n lin-addr) x86)
          (xlation-governing-entries-paddrs lin-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs
                             xlation-governing-entries-paddrs-for-pml4-table
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             disjoint-p$
                             direct-map-p
                             pdpt-base-addr
                             pml4-table-base-addr
                             cr3bits->pdb
                             ia32e-pml4ebits->pdpt)
                            (commutativity-of-+
                             subset-p
                             (:linear acl2::loghead-upper-bound)
                             unsigned-byte-p-of-logtail
                             member-p
                             member-p-canonical-address-listp
                             unsigned-byte-p-of-logtail
                             mv-nth-0-las-to-pas-subset-p
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             bitops::logand-with-negated-bitmask)))))

(local
 (defun repeat (n x)
   ;; This is similar to acl2::repeat, except that it is in terms of
   ;; append instead of cons.
   (declare (xargs :guard (and (natp n) (true-listp x))))
   (if (zp n) nil (append x (repeat (- n 1) x)))))

(define all-xlation-governing-entries-paddrs-alt ((iteration natp)
                                                  (count natp)
                                                  (lin-addr canonical-address-p)
                                                  x86)
  :measure (nfix (- count iteration))
  :verify-guards nil
  :enabled t
  (if (zp (- count iteration))
      nil
    (append (xlation-governing-entries-paddrs (+ iteration lin-addr) x86)
            (all-xlation-governing-entries-paddrs-alt (1+ iteration) count lin-addr x86)))
  ///

  (defthmd all-xlation-governing-entries-paddrs-alt-is-all-xlation-governing-entries-paddrs
    (equal (all-xlation-governing-entries-paddrs-alt
            iteration count lin-addr x86)
           (all-xlation-governing-entries-paddrs
            (- count iteration) (+ iteration lin-addr) x86))
    :hints (("Goal" :in-theory (e/d* (all-xlation-governing-entries-paddrs) ())))))


(local
 (defthmd all-xlation-governing-entries-paddrs-1G-pages-general
   (implies
    (and
     (64-bit-modep x86) ; added
     (equal (page-size
             (rm-low-64
               (page-dir-ptr-table-entry-addr
                 lin-addr (page-dir-ptr-table-base-addr lin-addr x86))
               x86))
            1)
     (canonical-address-p (+ 7 (pml4-table-entry-addr
                                lin-addr (pml4-table-base-addr x86))))
     (canonical-address-p (+ 7 (page-dir-ptr-table-entry-addr
                                lin-addr (page-dir-ptr-table-base-addr lin-addr x86))))
     (canonical-address-p lin-addr)
     (canonical-address-p (+ -1 m lin-addr))
     (natp m)
     (<= m *2^30*)
     (natp iteration)
     (equal (loghead 30 lin-addr) 0)
     (not (app-view x86))
     (x86p x86))
    (equal
     (all-xlation-governing-entries-paddrs-alt
      iteration m lin-addr x86)
     (repeat (- m iteration) (xlation-governing-entries-paddrs lin-addr x86))))
   :hints (("Goal"
            :do-not '(preprocess)
            :in-theory (e/d* (xlation-governing-entries-paddrs-for-same-1G-page)
                             (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                              bitops::logand-with-negated-bitmask
                              force (force)
                              not))))))

(local
 (defthmd all-xlation-governing-entries-paddrs-1G-pages
   (implies
    (and
     (64-bit-modep x86) ; added
     (equal pml4-table-base-addr (pml4-table-base-addr (double-rewrite x86)))
     (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr (double-rewrite x86)))
     (equal page-dir-ptr-table-entry-addr
            (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
     (equal page-dir-ptr-table-entry
            (rm-low-64 page-dir-ptr-table-entry-addr (double-rewrite x86)))

     (equal (page-size page-dir-ptr-table-entry) 1)

     (canonical-address-p (+ 7 pml4-table-entry-addr))
     (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

     (canonical-address-p lin-addr)
     (equal (loghead 30 lin-addr) 0)
     (canonical-address-p (+ -1 m lin-addr))
     (natp m)
     (<= m *2^30*)
     (not (app-view x86))
     (x86p x86))
    (equal
     (all-xlation-governing-entries-paddrs m lin-addr x86)
     (repeat m (xlation-governing-entries-paddrs lin-addr x86))))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(preprocess)
            :use ((:instance all-xlation-governing-entries-paddrs-1G-pages-general
                             (iteration 0)))
            :in-theory (e/d* (all-xlation-governing-entries-paddrs-alt-is-all-xlation-governing-entries-paddrs)
                             (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                              las-to-pas
                              rewrite-rb-to-rb-alt
                              not
                              mv-nth-0-las-to-pas-subset-p
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                              mv-nth-1-las-to-pas-returns-nil-when-error
                              mv-nth-1-las-to-pas-when-error
                              marking-view
                              ;; mv-nth-1-rb-after-mv-nth-2-ia32e-la-to-pa
                              pml4-table-base-addr pml4-table-entry-addr
                              page-dir-ptr-table-entry-addr
                              page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                              bitops::logand-with-negated-bitmask
                              force (force)
                              not))))))

;; Reading the new translation-governing addresses of a lin-addr,
;; given that its PDPTE has been modified:
(local
 (defthmd rm-low-64-and-write-to-physical-memory-disjoint-commuted
   (implies (disjoint-p p-addrs-2 (addr-range 8 p-addr-1))
            (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                   (rm-low-64 p-addr-1 x86)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p-commutative) ())))))

(defthmd xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr
  ;; Similar to
  ;; ia32e-la-to-pa-values-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr
  ;; for
  ;; xlation-governing-entries-paddrs.
  (implies
   (and
    (64-bit-modep x86) ; added
    ;; Restricting this rule so that it doesn't apply when lin-addr
    ;; points to a paging entry.
    (syntaxp (not (and (consp lin-addr)
                       (or (eq (car lin-addr) 'car)
                           (eq (car lin-addr) 'pml4-table-entry-addr$inline)
                           (eq (car lin-addr) 'page-dir-ptr-table-entry-addr$inline)))))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (rm-low-64 page-dir-ptr-table-entry-addr x86))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (canonical-address-p write-addr)
    (canonical-address-p (+ 7 write-addr))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (not (app-view x86))
    (x86p x86))
   (equal (xlation-governing-entries-paddrs lin-addr (wm-low-64 page-dir-ptr-table-entry-addr write-val x86))
          (xlation-governing-entries-paddrs lin-addr x86)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (ia32e-pml4ebits->pdpt
                     xlation-governing-entries-paddrs
                     xlation-governing-entries-paddrs-for-pml4-table
                     xlation-governing-entries-paddrs-for-page-dir-ptr-table) ()))))

(local
  (defthm-using-gl logtail-49-sum-unsigned-byte-p-30-ident
                   :hyp (and (unsigned-byte-p 30 x)
                             (canonical-address-p z)
                             (equal (loghead 30 z) 0))
                   :concl (equal (logtail 39 (+ z x))
                                 (logtail 39 z))
                   :g-bindings (gl::auto-bindings (:mix (:int z #.*max-linear-address-size*)
                                                        (:int x #.*max-linear-address-size*)))))

(defthmd xlation-governing-entries-paddrs-for-same-1g-page-and-wm-low-64-to-page-dir-ptr-table-entry-addr
         (implies
           (and
             (64-bit-modep x86) ; added
             ;; Restricting this rule so that it doesn't apply when lin-addr
             ;; points to a paging entry.
             (syntaxp (not (and (consp lin-addr)
                                (or (eq (car lin-addr) 'car)
                                    (eq (car lin-addr) 'pml4-table-entry-addr$inline)
                                    (eq (car lin-addr) 'page-dir-ptr-table-entry-addr$inline)))))
             (equal pml4-table-base-addr (pml4-table-base-addr x86))
             (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
             (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
             (equal page-dir-ptr-table-entry-addr
                    (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
             (equal page-dir-ptr-table-entry
                    (rm-low-64 page-dir-ptr-table-entry-addr x86))

             (disjoint-p (addr-range 8 pml4-table-entry-addr)
                         (addr-range 8 page-dir-ptr-table-entry-addr))

             (equal (page-size page-dir-ptr-table-entry)
                    (page-size write-val))
             (equal (page-size page-dir-ptr-table-entry) 1)
             (canonical-address-p write-addr)
             (canonical-address-p (+ 7 write-addr))
             (unsigned-byte-p 64 write-val)
             (canonical-address-p (+ 7 pml4-table-entry-addr))
             (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
             (unsigned-byte-p 30 n)
             (canonical-address-p lin-addr)
             (equal (loghead 30 lin-addr) 0)
             (not (app-view x86))
             (x86p x86))
           (equal (xlation-governing-entries-paddrs (+ n lin-addr)
                                                    (wm-low-64 page-dir-ptr-table-entry-addr write-val x86))
                  (xlation-governing-entries-paddrs lin-addr x86)))
         :hints (("Goal"
                  :do-not-induct t
                  :use ((:instance logtail-49-sum-unsigned-byte-p-30-ident
                                   (z lin-addr)
                                   (x n)))
                  :in-theory (e/d* (xlation-governing-entries-paddrs-for-same-1G-page
                                     xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr
                                     xlation-governing-entries-paddrs
                                     xlation-governing-entries-paddrs-for-pml4-table
                                     xlation-governing-entries-paddrs-for-page-dir-ptr-table
                                     pml4-table-base-addr
                                     pml4-table-entry-addr
                                     cr3bits->pdb
                                     ia32e-pml4ebits->pdpt)
                                   (subset-p
                                     member-p
                                     mv-nth-0-las-to-pas-subset-p
                                     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                                     r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
                                     member-p-canonical-address-listp
                                     mv-nth-1-las-to-pas-subset-p
                                     car-create-canonical-address-list
                                     consp-of-create-canonical-address-list
                                     commutativity-of-+
                                     pml4-table-entry-addr-to-c-program-optimized-form
                                     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                     bitops::logand-with-negated-bitmask
                                     force (force)
                                     not
                                     bitops::logand-with-negated-bitmask)))))

(defthmd all-xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr-general
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (rm-low-64 page-dir-ptr-table-entry-addr x86))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (addr-range 8 pml4-table-entry-addr)
     (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))

    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 m lin-addr))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (equal
    (all-xlation-governing-entries-paddrs-alt
     iteration m lin-addr (wm-low-64 page-dir-ptr-table-entry-addr write-val x86))
    (all-xlation-governing-entries-paddrs-alt
     iteration m lin-addr x86)))
  :hints (("Goal"
           :induct (cons
                    (all-xlation-governing-entries-paddrs-alt
                     iteration m lin-addr x86)
                    (all-xlation-governing-entries-paddrs-alt
                     iteration m lin-addr (wm-low-64 page-dir-ptr-table-entry-addr write-val x86)))
           :do-not '(preprocess)
           :in-theory (e/d* (64-bit-modep
                             all-xlation-governing-entries-paddrs
                             xlation-governing-entries-paddrs-for-same-1G-page
                             xlation-governing-entries-paddrs-for-same-1G-page-and-wm-low-64-to-page-dir-ptr-table-entry-addr
                             xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr
                             all-xlation-governing-entries-paddrs-1G-pages-general)
                            (mv-nth-0-las-to-pas-subset-p
                             member-p
                             subset-p
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

(defthm all-xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (64-bit-modep (double-rewrite x86)) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr (double-rewrite x86)))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (page-dir-ptr-table-base-addr lin-addr (double-rewrite x86)))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (rm-low-64 page-dir-ptr-table-entry-addr (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (addr-range 8 pml4-table-entry-addr)
     (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))

    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 m lin-addr))
    (natp m)
    (<= m *2^30*)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view (double-rewrite x86)))
    (x86p (double-rewrite x86)))
   (equal
    (all-xlation-governing-entries-paddrs
     m lin-addr (wm-low-64 page-dir-ptr-table-entry-addr write-val x86))
    (all-xlation-governing-entries-paddrs
     m lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :use ((:instance all-xlation-governing-entries-paddrs-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr-general
                            (iteration 0)))
           :in-theory (e/d* (all-xlation-governing-entries-paddrs-alt-is-all-xlation-governing-entries-paddrs)
                            (all-xlation-governing-entries-paddrs-alt
                             all-xlation-governing-entries-paddrs
                             mv-nth-0-las-to-pas-subset-p
                             subset-p
                             member-p
                             rewrite-rb-to-rb-alt
                             rb-and-rm-low-64-for-direct-map
                             xlation-governing-entries-paddrs-for-same-1G-page
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

;; ======================================================================

;; Begin proof of las-to-pas-values-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr:
;; Reading the new mapping (i.e., phy-addr) of a lin-addr, given that
;; its PDPTE has been modified:

(defthmd ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa-page-dir-ptr-table returns the
  ;; physical address corresponding to lin-addr after the PDPTE
  ;; corresponding to this lin-addr has been modified --- the new
  ;; PDPTE is value.
  (implies (and
            (64-bit-modep x86) ; added
            (equal pdpt-entry-addr
                   (page-dir-ptr-table-entry-addr lin-addr base-addr))
            (equal page-dir-ptr-table-entry
                   (rm-low-64 pdpt-entry-addr (double-rewrite x86)))

            (not
             (mv-nth
              0
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe implicit-supervisor-access r-w-x cpl x86)))

            (equal (page-present page-dir-ptr-table-entry)
                   (page-present value))
            (equal (page-read-write page-dir-ptr-table-entry)
                   (page-read-write value))
            (equal (page-user-supervisor page-dir-ptr-table-entry)
                   (page-user-supervisor value))
            (equal (page-execute-disable page-dir-ptr-table-entry)
                   (page-execute-disable value))
            (equal (page-size page-dir-ptr-table-entry)
                   (page-size value))
            (equal (page-size page-dir-ptr-table-entry) 1)
            (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                   (part-select value :low 13 :high 29))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
            (unsigned-byte-p 64 value)
            (canonical-address-p lin-addr)
            (physical-address-p base-addr)
            (equal (loghead 12 base-addr) 0)
            (x86p x86))
           (and (equal
                 (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe implicit-supervisor-access r-w-x cpl
                            (wm-low-64 pdpt-entry-addr value x86)))
                 nil)
                (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                  wp smep smap ac nxe implicit-supervisor-access r-w-x cpl
                                  (wm-low-64 pdpt-entry-addr value x86)))
                       (logior (loghead 30 lin-addr)
                               (ash (loghead 22 (logtail 30 value)) 30)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
                             ia32e-pdpte-1gb-pagebits->page) 
                           (mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries))
           :use (:instance mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
                           (structure-type 2)
                           (entry-1 page-dir-ptr-table-entry)
                           (entry-2 value)
                           (u/s-acc (logand u/s-acc (page-user-supervisor value)))
                           (r/w-acc (logand r/w-acc (page-read-write value)))
                           (x/d-acc (logand x/d-acc (page-execute-disable value)))))))

(defthmd ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa-pml4-table returns the physical
  ;; address corresponding to lin-addr after the PDPTE corresponding
  ;; to this lin-addr has been modified --- the new PDPTE is
  ;; value.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal page-dir-ptr-table-addr-base-addr (page-dir-ptr-table-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-addr-base-addr))
    (equal page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

    (disjoint-p (addr-range 8 page-dir-ptr-table-entry-addr)
                (addr-range 8 pml4-table-entry-addr))

    (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-table-base-addr wp smep smap ac nxe implicit-supervisor-access :r cpl x86)))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present value))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write value))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor value))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable value))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size value))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select value :low 13 :high 29))

    (unsigned-byte-p 64 value)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr pml4-table-base-addr)))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (x86p x86))
   (and
    (equal
     (mv-nth 0
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-table-base-addr wp smep smap ac nxe implicit-supervisor-access :r cpl
              (wm-low-64 page-dir-ptr-table-entry-addr value x86)))
     nil)
    (equal
     (mv-nth 1
             (ia32e-la-to-pa-pml4-table
              lin-addr pml4-table-base-addr wp smep smap ac nxe implicit-supervisor-access :r cpl
              (wm-low-64 page-dir-ptr-table-entry-addr value x86)))
     (logior (loghead 30 lin-addr)
             (ash (loghead 22 (logtail 30 value))
                  30)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                              ia32e-pml4ebits->pdpt
                              ia32e-la-to-pa-pml4-table
                              pml4-table-entry-addr))))

(defthmd ia32e-la-to-pa-without-tlb-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa-without-tlb returns the physical address
  ;; corresponding to lin-addr after the PDPTE corresponding to this
  ;; lin-addr has been modified --- the new PDPTE is write-val. The
  ;; write is expressed in terms of wm-low-64, i.e., at the level of
  ;; physical memory.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr (double-rewrite x86)))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal page-dir-ptr-table-addr-base-addr (page-dir-ptr-table-base-addr lin-addr (double-rewrite x86)))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-addr-base-addr))
    (equal page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr (double-rewrite x86)))

    (disjoint-p (addr-range 8 page-dir-ptr-table-entry-addr)
                (addr-range 8 pml4-table-entry-addr))

    (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))

    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))

    (unsigned-byte-p 64 write-val)
    (canonical-address-p
      (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (x86p x86))
   (and
     (equal (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r
                                                  (wm-low-64 page-dir-ptr-table-entry-addr write-val x86)))
            nil)
     (equal (mv-nth 1 (ia32e-la-to-pa-without-tlb lin-addr :r
                                                  (wm-low-64 page-dir-ptr-table-entry-addr write-val x86)))
            (logior (loghead 30 lin-addr) (ash (loghead 22 (logtail 30 write-val)) 30)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                              ia32e-la-to-pa-without-tlb))))

(defthmd las-to-pas-without-tlb-values-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr-general
  ;; las-to-pas-without-tlb returns the physical addresses corresponding to
  ;; linear addresses after the PDPTE corresponding to these linear addresses
  ;; have been modified and the tlb has been cleared --- the new PDPTE is
  ;; write-val.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal pml4-table-base-addr (pml4-table-base-addr (double-rewrite x86)))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal page-dir-ptr-table-addr-base-addr (page-dir-ptr-table-base-addr lin-addr (double-rewrite x86)))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-addr-base-addr))
    (equal page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr (double-rewrite x86)))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
                (addr-range 8 page-dir-ptr-table-entry-addr))

    (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))

    (unsigned-byte-p 64 write-val)
    (canonical-address-p (+ 7 (pml4-table-entry-addr
                               lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 m lin-addr))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is write-val.
   (and
    (equal
     (mv-nth 0 (las-to-pas-without-tlb iteration m lin-addr :r
                                       (wm-low-64 page-dir-ptr-table-entry-addr write-val x86)))
     nil)
    (equal
     (mv-nth 1 (las-to-pas-without-tlb iteration m lin-addr :r
                                       (wm-low-64 page-dir-ptr-table-entry-addr write-val x86)))
     (addr-range
      (+ (- iteration) m)
      (+ iteration (ash (loghead 22 (logtail 30 write-val)) 30))))))
  :hints (("Goal"
           :expand ((:free (x) (las-to-pas-without-tlb iteration m lin-addr :r x)))
           :in-theory (e/d*
                       (las-to-pas-without-tlb
                        disjoint-p-commutative
                        64-bit-modep
                        page-dir-ptr-table-entry-addr
                        pdpt-base-addr
                        open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                        ia32e-la-to-pa-without-tlb-values-for-same-1G-page
                        ia32e-la-to-pa-without-tlb-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                        xlation-governing-entries-paddrs-for-same-1G-page)
                       (page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

(defthmd read-from-physical-memory-unwrap
         (implies (and (not (app-view x86))
                       (physical-address-p addr)
                       (x86p x86))
                  (equal (read-from-physical-memory (addr-range 8 addr) x86)
                         (rm-low-64 addr x86)))
         :hints (("Goal"
                  :use (:instance rewrite-read-from-physical-memory-to-rm-low-64
                                  (p-addrs (addr-range 8 addr))
                                  (index addr)))))

(local (in-theory (enable read-from-physical-memory-unwrap)))

(defthmd las-to-pas-values-for-same-1G-page-virt-mem-pt-accesses
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr
            lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8 page-dir-ptr-table-entry-addr (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (mv-nth 1 (las-to-pas
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                :r (double-rewrite x86))))

    (not (mv-nth 0 (las-to-pas *2^30* lin-addr :r (double-rewrite x86))))

    (equal (page-size page-dir-ptr-table-entry) 1)
    (tlb-consistent-n *2^30* lin-addr :r x86)
    (canonical-address-p
     (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas *2^30* lin-addr :r x86)) nil)
    (equal (mv-nth 1 (las-to-pas *2^30* lin-addr :r x86))
           (addr-range
            *2^30*
            (ash
              (loghead 22
                       (logtail 30
                                (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr
                                              :r (double-rewrite x86)))))
              30)))))
  :hints (("Goal"
           :in-theory (e/d* (las-to-pas-values-for-same-1G-page rb direct-map-p pml4-table-entry-addr
                             64-bit-modep disjoint-p-commutative disjoint-p$)
                            (;; ACL2 tries to execute addr-range, which overflows the stack
                             ;; since it attempts to recurse 2^30 times. I'm kind of surprised
                             ;; that we don't run into this issue anywhere else given this
                             ;; rune is enabled
                             (:executable-counterpart addr-range)
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

(local (defthm wb-unwrap
               (implies (and (equal (mv-nth 1 (las-to-pas 8 vaddr :w x86))
                                    (mv-nth 1 (las-to-pas 8 vaddr2 r-w-x x86)))
                             (direct-map-p 8 vaddr2 r-w-x x86)
                             (not (app-view x86)))
                        (equal (mv-nth 1 (wb 8 vaddr w val x86))
                               (wm-low-64 vaddr2
                                          val
                                          (mv-nth 2 (las-to-pas 8 vaddr :w x86)))))
               :hints (("Goal"
                        :in-theory (e/d (wb
                                         direct-map-p
                                         rewrite-wm-low-64-to-write-to-physical-memory)
                                        (addr-range))))))

(defthm read-from-physical-memory-wm-low-64-disjoint
        (implies (disjoint-p paddrs
                             (addr-range 8 x))
                 (equal (read-from-physical-memory paddrs (wm-low-64 x val x86))
                        (read-from-physical-memory paddrs x86))))

(defthm all-xlation-governing-entries-paddrs-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr
            lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8 page-dir-ptr-table-entry-addr (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (mv-nth 1 (las-to-pas
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                :r (double-rewrite x86))))

    (equal
     (mv-nth 1 (las-to-pas 8 write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (disjoint-p
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))) :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))

    (not (mv-nth 0 (las-to-pas-without-tlb 0 *2^30* lin-addr :r (double-rewrite x86))))

    (disjoint-p$
     (addr-range *2^30* (ash (loghead 22 (logtail 30 write-val)) 30))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p write-addr)
    (canonical-address-p (+ 7 write-addr))
    (canonical-address-p
      (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (equal
    (all-xlation-governing-entries-paddrs
     *2^30* lin-addr (mv-nth 1 (wb 8 write-addr w write-val x86)))
    (all-xlation-governing-entries-paddrs
     *2^30* lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory (e/d* (rb direct-map-p pml4-table-entry-addr las-to-pas 64-bit-modep disjoint-p$ disjoint-p-commutative)
                            (disjoint-p
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
                              gl::conds-match-and-no-duplicate-conds
                              rb-returns-no-error-app-view
                              (:linear size-of-read-from-physical-memory)
                              subset-p
                              mv-nth-0-las-to-pas-subset-p
                              member-p
                              disjoint-p-subset-p
                              mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                              member-p-canonical-address-listp
                              page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                              bitops::logand-with-negated-bitmask
                              force (force)
                              not)))))

(defthm las-to-pas-without-tlb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  ;; las-to-pas-without-tlb returns the physical addresses corresponding to
  ;; linear addresses after the PDPTE corresponding to these linear addresses
  ;; have been modified and the tlb has been cleared --- the new PDPTE is
  ;; write-val.
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr
            lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8 page-dir-ptr-table-entry-addr (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (mv-nth 1 (las-to-pas
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                :r (double-rewrite x86))))

    (equal
     (mv-nth 1 (las-to-pas 8 write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (disjoint-p
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))) :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))

    (not (mv-nth 0 (las-to-pas-without-tlb 0 *2^30* lin-addr :r (double-rewrite x86))))

    (disjoint-p$
     (addr-range *2^30* (ash (loghead 22 (logtail 30 write-val)) 30))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p write-addr)
    (canonical-address-p (+ 7 write-addr))
    (canonical-address-p
      (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is write-val.
   (and
     (equal
       (mv-nth 0 (las-to-pas-without-tlb 0 *2^30* lin-addr :r
                                         (mv-nth 1 (wb 8 write-addr w write-val x86))))
       nil)
     (equal
       (mv-nth 1 (las-to-pas-without-tlb 0 *2^30* lin-addr :r
                                         (mv-nth 1 (wb 8 write-addr w write-val x86))))
       (addr-range
         *2^30*
         (ash (loghead 22 (logtail 30 write-val)) 30)))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((las-to-pas-without-tlb 0 *2^30* lin-addr :r x86))
           :in-theory (e/d* (rb direct-map-p pml4-table-entry-addr las-to-pas 64-bit-modep disjoint-p$ disjoint-p-commutative
                             las-to-pas-without-tlb-values-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr-general)
                            (disjoint-p
                              mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                              infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
                              gl::conds-match-and-no-duplicate-conds
                              rb-returns-no-error-app-view
                              (:linear size-of-read-from-physical-memory)
                              subset-p
                              mv-nth-0-las-to-pas-subset-p
                              member-p
                              disjoint-p-subset-p
                              mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                              member-p-canonical-address-listp
                              page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                              bitops::logand-with-negated-bitmask
                              force (force)
                              not)))))

(defthm rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (64-bit-modep x86) ; added
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr
            lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
       :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8 page-dir-ptr-table-entry-addr (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                :r (double-rewrite x86)))
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (equal
     (mv-nth 1 (las-to-pas 8 write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86))))

    (disjoint-p
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))) :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs 8 write-addr (double-rewrite x86)))

    (not (mv-nth 0 (ia32e-la-to-pa-without-tlb lin-addr :r (double-rewrite x86))))

    (disjoint-p$
     (addr-range *2^30* (ash (loghead 22 (logtail 30 write-val)) 30))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))

    (disjoint-p
     (addr-range *2^30* (ash (loghead 22 (logtail 30 write-val)) 30))
     (mv-nth 1 (las-to-pas 8 write-addr :w (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
           (page-present write-val))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write write-val))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor write-val))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable write-val))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size write-val))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select write-val :low 13 :high 29))
    (tlb-consistent-n *2^30* lin-addr :r (mv-nth 1 (wb 8 write-addr w write-val x86)))
    (unsigned-byte-p 64 write-val)
    (canonical-address-p write-addr)
    (canonical-address-p (+ 7 write-addr))
    (canonical-address-p
     (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p page-dir-ptr-table-entry-addr)
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (rb *2^30* lin-addr :r (mv-nth 1 (wb 8 write-addr w write-val x86))))
           nil)
    (equal (mv-nth 1 (rb *2^30* lin-addr :r (mv-nth 1 (wb 8 write-addr w write-val x86))))
           (read-from-physical-memory
            (addr-range *2^30* (ash (loghead 22 (logtail 30 write-val)) 30))
            (double-rewrite x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (las-to-pas-values-are-las-to-pas-without-tlb-when-tlb-consistent
                             rb direct-map-p pml4-table-entry-addr las-to-pas 64-bit-modep
                             las-to-pas-without-tlb-values-1G-pages-and-wm-low-64-to-page-dir-ptr-table-entry-addr-general)
                            (disjoint-p
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                             infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                             infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
                             gl::conds-match-and-no-duplicate-conds
                             rb-returns-no-error-app-view
                             (:linear size-of-read-from-physical-memory)
                             subset-p
                             mv-nth-0-las-to-pas-subset-p
                             member-p
                             disjoint-p-subset-p
                             mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                             member-p-canonical-address-listp
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

;; ----------------------------------------------------------------------
