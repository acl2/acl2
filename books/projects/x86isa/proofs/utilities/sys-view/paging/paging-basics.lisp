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
(include-book "../physical-memory-utils")
(local (include-book "../gl-lemmas"))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

;; ======================================================================

(defsection paging-basics
  :parents (reasoning-about-page-tables)

  :short "Definitions of translation-governing addresses for paging
  structure entries"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents paging-basics))

;; ======================================================================

;; Some helper rules:

(local (in-theory (e/d* () (greater-logbitp-of-unsigned-byte-p not))))

(encapsulate
  ()

  (defrule loghead-1-bool->bit-rule
    (equal (loghead 1 (bool->bit x))
           (bool->bit x)))

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defrule low-3-bits-0-add-7-preserve-bound
      (implies (and (equal (loghead 3 x) 0)
                    (< x *mem-size-in-bytes*)
                    (integerp x))
               (< (+ 7 x) *mem-size-in-bytes*))
      :in-theory (e/d* (loghead) ())))

  (defthm-unsigned-byte-p rm-low-64-logand-logior-helper-1
    :hyp (and (n64p x)
              (syntaxp (quotep n))
              (natp n)
              (<= n 64)
              (equal m (- (1+ n))))
    :bound 64
    :concl (logior n (logand m x))
    :gen-type t
    :gen-linear t))

(in-theory (e/d* (low-3-bits-0-add-7-preserve-bound) ()))

;; ======================================================================

;; Page table base address functions:

(defun-nx pml4-table-base-addr (x86)
  (ash (cr3Bits->pdb (ctri *cr3* x86)) 12))

(defthm-unsigned-byte-p n52p-of-pml4-table-base-addr
  :hyp (x86p x86)
  :bound 52
  :concl (pml4-table-base-addr x86))

(defthm pml4-table-base-addr-and-mv-nth-1-wb
  (equal (pml4-table-base-addr (mv-nth 1 (wb n addr w value x86)))
         (pml4-table-base-addr x86)))

(defun-nx page-dir-ptr-table-base-addr (lin-addr x86)
  (ash (loghead 40
                (logtail 12
                         (rm-low-64
                          (pml4-table-entry-addr
                           lin-addr
                           (pml4-table-base-addr x86))
                          x86)))
       12))

(defun-nx page-directory-base-addr (lin-addr x86)
  (ash
   (loghead
    40
    (logtail
     12
     (rm-low-64
      (page-dir-ptr-table-entry-addr
       lin-addr (page-dir-ptr-table-base-addr lin-addr x86))
      x86)))
   12))

(defun-nx page-table-base-addr (lin-addr x86)
  (ash
   (loghead
    40
    (logtail
     12
     (rm-low-64
      (page-directory-entry-addr
       lin-addr (page-directory-base-addr lin-addr x86))
      x86)))
   12))

;; ======================================================================

;; Lemmas about set-accessed-bit, etc.:

(defthmd loghead-smaller-equality
  (implies (and (equal (loghead n x) (loghead n y))
                (natp n)
                (<= m n))
           (equal (loghead m x) (loghead m y)))
  :hints
  (("Goal"
    :in-theory (e/d* (acl2::ihsext-recursive-redefs acl2::ihsext-inductions)
                     nil))))

(defthm logbitp-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 5)))
           (equal (logbitp n (set-accessed-bit entry))
                  (logbitp n (loghead 64 entry)))) ;; ia32e-page-tablesbits-fix?
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    not
                                    !ia32e-page-tablesbits->a
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm logbitp-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 6)))
           (equal (logbitp n (set-dirty-bit entry))
                  (logbitp n (loghead 64 entry)))) ;; ia32e-page-tablesbits-fix?
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit
                                    not
                                    !ia32e-page-tablesbits->d
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm logbitp-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (not (equal n 5))
                (not (equal n 6)))
           (equal (logbitp n (set-dirty-bit (set-accessed-bit entry)))
                  (logbitp n (loghead 64 entry)))) ;; ia32e-page-tablesbits-fix?
  :hints (("Goal" :in-theory (e/d* ()
                                   (logbitp-n-of-set-accessed-bit
                                    logbitp-n-of-set-dirty-bit))
           :use ((:instance logbitp-n-of-set-accessed-bit)
                 (:instance logbitp-n-of-set-dirty-bit
                            (entry (set-accessed-bit entry)))))))

(defthm logtail-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 5 n))
           (equal (logtail n (set-accessed-bit entry))
                  (logtail n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    !ia32e-page-tablesbits->a
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm logtail-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 6 n))
           (equal (logtail n (set-dirty-bit entry))
                  (logtail n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit
                                    !ia32e-page-tablesbits->d
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm logtail-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (< 6 n))
           (equal (logtail n (set-dirty-bit (set-accessed-bit entry)))
                  (logtail n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (logtail-n-of-set-dirty-bit
                                    logtail-n-of-set-accessed-bit))
           :use ((:instance logtail-n-of-set-dirty-bit
                            (n n)
                            (entry (set-accessed-bit entry)))
                 (:instance logtail-n-of-set-accessed-bit
                            (n n)
                            (entry entry))))))

(defthm loghead-n-of-set-accessed-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 5))
           (equal (loghead n (set-accessed-bit entry))
                  (loghead n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                    not
                                    !ia32e-page-tablesbits->a
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm loghead-n-of-set-dirty-bit
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 6))
           (equal (loghead n (set-dirty-bit entry))
                  (loghead n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* (set-dirty-bit
                                    not
                                    !ia32e-page-tablesbits->d
                                    ia32e-page-tablesbits-fix)
                                   ()))
          (bitops::logbitp-reasoning)))

(defthm loghead-n-of-set-dirty-and-accessed-bits
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= n 5))
           (equal (loghead n (set-dirty-bit (set-accessed-bit entry)))
                  (loghead n (loghead 64 entry))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (loghead-n-of-set-dirty-bit
                                    loghead-n-of-set-accessed-bit))
           :use ((:instance loghead-n-of-set-dirty-bit
                            (n n)
                            (entry (set-accessed-bit entry)))
                 (:instance loghead-n-of-set-accessed-bit
                            (n n)
                            (entry entry))))))

(defthm accessed-bit-set-accessed-bit
  (equal (accessed-bit (set-accessed-bit e)) 1)
  :hints (("Goal" :in-theory (e/d* (accessed-bit set-accessed-bit) ()))))

(defthm accessed-bit-set-dirty-bit
  (equal (accessed-bit (set-dirty-bit e))
         (accessed-bit e))
  :hints (("Goal" :in-theory (e/d* (accessed-bit set-dirty-bit) ()))))

(defthm dirty-bit-set-dirty-bit
  (equal (dirty-bit (set-dirty-bit e)) 1)
  :hints (("Goal" :in-theory (e/d* (dirty-bit set-dirty-bit) ()))))

(defthm dirty-bit-set-accessed-bit
  (equal (dirty-bit (set-accessed-bit e))
         (dirty-bit e))
  :hints (("Goal" :in-theory (e/d* (dirty-bit set-accessed-bit) ()))))

(defthm page-size-set-accessed-bit
  (equal (page-size (set-accessed-bit e))
         (page-size e))
  :hints (("Goal" :in-theory (e/d* (page-size set-accessed-bit) ()))))

(defthm page-size-set-dirty-bit
  (equal (page-size (set-dirty-bit e))
         (page-size e))
  :hints (("Goal" :in-theory (e/d* (page-size set-dirty-bit) ()))))

(defthm page-present-set-accessed-bit
  (equal (page-present (set-accessed-bit e))
         (page-present e))
  :hints (("Goal" :in-theory (e/d* (page-present set-accessed-bit) ()))))

(defthm page-present-set-dirty-bit
  (equal (page-present (set-dirty-bit e))
         (page-present e))
  :hints (("Goal" :in-theory (e/d* (page-present set-dirty-bit) ()))))

(defthm page-read-write-set-accessed-bit
  (equal (page-read-write (set-accessed-bit e))
         (page-read-write e))
  :hints (("Goal" :in-theory (e/d* (page-read-write set-accessed-bit) ()))))

(defthm page-read-write-set-dirty-bit
  (equal (page-read-write (set-dirty-bit e))
         (page-read-write e))
  :hints (("Goal" :in-theory (e/d* (page-read-write set-dirty-bit) ()))))

(defthm page-user-supervisor-set-accessed-bit
  (equal (page-user-supervisor (set-accessed-bit e))
         (page-user-supervisor e))
  :hints (("Goal" :in-theory (e/d* (page-user-supervisor set-accessed-bit) ()))))

(defthm page-user-supervisor-set-dirty-bit
  (equal (page-user-supervisor (set-dirty-bit e))
         (page-user-supervisor e))
  :hints (("Goal" :in-theory (e/d* (page-user-supervisor set-dirty-bit) ()))))

(defthm page-execute-disable-set-accessed-bit
  (equal (page-execute-disable (set-accessed-bit e))
         (page-execute-disable e))
  :hints (("Goal" :in-theory (e/d* (page-execute-disable set-accessed-bit) ()))))

(defthm page-execute-disable-set-dirty-bit
  (equal (page-execute-disable (set-dirty-bit e))
         (page-execute-disable e))
  :hints (("Goal" :in-theory (e/d* (page-execute-disable set-dirty-bit) ()))))

;; ======================================================================
