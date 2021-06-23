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
(include-book "paging-basics")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "std/lists/remove-duplicates" :dir :system))

;; ======================================================================

(defsection gather-paging-structures
  :parents (reasoning-about-page-tables)

  :short "Gather physical addresses where paging data structures are located"
  )

(local (xdoc::set-default-parents gather-paging-structures))

;; ======================================================================

;; Some misc. lemmas:

(defthmd loghead-smaller-and-logbitp
  (implies (and (equal (loghead n e-1) (loghead n e-2))
                (natp n)
                (natp m)
                (< m n))
           (equal (logbitp m e-1) (logbitp m e-2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger
  (implies (and (equal (logtail m e-1) (logtail m e-2))
                (integerp e-2)
                (natp n)
                (<= m n))
           (equal (logtail n e-1) (logtail n e-2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthmd logtail-bigger-and-logbitp
  (implies (and (equal (logtail m e-1) (logtail m e-2))
                (integerp e-2)
                (natp n)
                (<= m n))
           (equal (logbitp n e-1) (logbitp n e-2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

;; ======================================================================

(define qword-paddr-listp (xs)
  :parents (reasoning-about-page-tables)
  :enabled t
  :short "Recognizer for a list of physical addresses that can
  accommodate a quadword"
  (if (consp xs)
      (and (physical-address-p (car xs))
           (physical-address-p (+ 7 (car xs)))
           (qword-paddr-listp (cdr xs)))
    (equal xs nil))

  ///

  (defthm qword-paddr-listp-implies-true-listp
    (implies (qword-paddr-listp xs)
             (true-listp xs))
    :rule-classes :forward-chaining)

  (defthm qword-paddr-listp-and-append
    (implies (and (qword-paddr-listp a)
                  (qword-paddr-listp b))
             (qword-paddr-listp (append a b))))

  (defthm qword-paddr-listp-and-remove-duplicates-equal
    (implies (qword-paddr-listp a)
             (qword-paddr-listp (remove-duplicates-equal a))))

  (defthm-unsigned-byte-p qword-paddrp-element-of-qword-paddr-listp
    :hyp (and (qword-paddr-listp xs)
              (natp m)
              (< m (len xs)))
    :bound 52
    :concl (nth m xs)
    :gen-linear t
    :gen-type t)

  (defthm nthcdr-qword-paddr-listp
    (implies (qword-paddr-listp xs)
             (qword-paddr-listp (nthcdr n xs)))
    :rule-classes (:rewrite :type-prescription)))

(define mult-8-qword-paddr-listp (xs)
  :enabled t
  :parents (reasoning-about-page-tables)
  :short "Recognizer for a list of physical addresses that can
  accommodate a quadword"
  (if (consp xs)
      (and (physical-address-p (car xs))
           (physical-address-p (+ 7 (car xs)))
           ;; Multiple of 8
           (equal (loghead 3 (car xs)) 0)
           (mult-8-qword-paddr-listp (cdr xs)))
    (equal xs nil))

  ///

  (defthm mult-8-qword-paddr-listp-implies-true-listp
    (implies (mult-8-qword-paddr-listp xs)
             (true-listp xs))
    :rule-classes :forward-chaining)

  (defthm mult-8-qword-paddr-listp-and-append
    (implies (and (mult-8-qword-paddr-listp a)
                  (mult-8-qword-paddr-listp b))
             (mult-8-qword-paddr-listp (append a b))))

  (defthm mult-8-qword-paddr-listp-remove-duplicates-equal
    (implies (mult-8-qword-paddr-listp addrs)
             (mult-8-qword-paddr-listp (remove-duplicates-equal addrs))))

  (defthm-unsigned-byte-p qword-paddrp-element-of-mult-8-qword-paddr-listp
    :hyp (and (mult-8-qword-paddr-listp xs)
              (natp m)
              (< m (len xs)))
    :bound 52
    :concl (nth m xs)
    :gen-linear t
    :gen-type t)

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defthm nthcdr-mult-8-qword-paddr-listp
    (implies (mult-8-qword-paddr-listp xs)
             (mult-8-qword-paddr-listp (nthcdr n xs)))
    :rule-classes (:rewrite :type-prescription))

  (defthm member-p-and-mult-8-qword-paddr-listp
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs))
             (and (physical-address-p index)
                  (equal (loghead 3 index) 0)))
    :rule-classes (:rewrite :forward-chaining)))

(encapsulate
  ()

  (local
   (defthm open-addr-range
     (implies (natp x)
              (equal (addr-range 8 x)
                     (list x (+ 1 x) (+ 2 x) (+ 3 x)
                           (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x))))))

  (local
   (encapsulate
     ()

     (local (include-book "arithmetic-5/top" :dir :system))

     (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-1
       (implies (and (equal (loghead 3 x) 0)
                     (equal (loghead 3 y) 0)
                     (posp n)
                     (<= n 7)
                     (natp x)
                     (natp y))
                (not (equal (+ n x) y)))
       :hints (("Goal" :in-theory (e/d* (loghead)
                                        ()))))

     (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-2
       (implies (and (equal (loghead 3 x) 0)
                     (equal (loghead 3 y) 0)
                     (not (equal x y))
                     (posp n)
                     (<= n 7)
                     (posp m)
                     (<= m 7)
                     (natp x)
                     (natp y))
                (not (equal (+ n x) (+ m y))))
       :hints (("Goal" :in-theory (e/d* (loghead)
                                        ()))))))

  (defthm multiples-of-8-and-disjointness-of-physical-addresses-1
    (implies (and (equal (loghead 3 addr-1) 0)
                  (equal (loghead 3 addr-2) 0)
                  (not (equal addr-2 addr-1))
                  (natp addr-1)
                  (natp addr-2))
             (disjoint-p (addr-range 8 addr-2)
                         (addr-range 8 addr-1))))

  (defthm multiples-of-8-and-disjointness-of-physical-addresses-2
    (implies (and (equal (loghead 3 addr-1) 0)
                  (equal (loghead 3 addr-2) 0)
                  (not (equal addr-2 addr-1))
                  (natp addr-1)
                  (natp addr-2))
             (disjoint-p (cons addr-2 nil)
                         (addr-range 8 addr-1))))

  (defthm mult-8-qword-paddr-listp-and-disjoint-p
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp (cons addr addrs))
                  (no-duplicates-p (cons addr addrs)))
             (disjoint-p (addr-range 8 index)
                         (addr-range 8 addr)))
    :hints (("Goal" :in-theory (e/d* () (open-addr-range))))
    :rule-classes :forward-chaining))

(define open-qword-paddr-list (xs)
  :guard (qword-paddr-listp xs)
  :enabled t
  (if (endp xs)
      nil
    (append (addr-range 8 (car xs))
            (open-qword-paddr-list (cdr xs))))
  ///

  (defthm open-qword-paddr-list-and-member-p
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (member-p index addrs))
             (member-p index (open-qword-paddr-list addrs)))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthm open-qword-paddr-list-and-subset-p
    (implies (member-p index addrs)
             (subset-p (addr-range 8 index) (open-qword-paddr-list addrs)))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm open-qword-paddr-list-and-append
    (equal (open-qword-paddr-list (append xs ys))
           (append (open-qword-paddr-list xs)
                   (open-qword-paddr-list ys)))))

(define create-qword-address-list
  ((count natp)
   (addr :type (unsigned-byte #.*physical-address-size*)))

  :parents (reasoning-about-page-tables)
  :guard (physical-address-p (+ -1 (ash count 3) addr))

  :prepwork
  ((local (include-book "arithmetic-5/top" :dir :system))

   (local (in-theory (e/d* (ash unsigned-byte-p) ())))

   (defthm-unsigned-byte-p n52p-left-shifting-a-40-bit-natp-by-12
     :hyp (unsigned-byte-p 40 x)
     :bound 52
     :concl (+ 4095 (ash x 12)))

   (defthm-unsigned-byte-p n52p-left-shifting-a-40-bit-natp-by-12-+-7
     :hyp (unsigned-byte-p 40 x)
     :bound 52
     :concl (+ 7 (ash x 12)))

   (defthm loghead-3-+8-addr
     (implies (equal (loghead 3 addr) 0)
              (equal (loghead 3 (+ 8 addr)) 0))
     :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs
                                       loghead
                                       ifix)
                                      ())))))

  :enabled t

  (if (or (zp count)
          (not (physical-address-p addr))
          (not (physical-address-p (+ 7 addr))))
      nil
    (if (equal count 1)
        (list addr)
      (cons addr (create-qword-address-list (1- count) (+ 8 addr)))))

  ///

  (defthm nat-listp-create-qword-address-list
    (nat-listp (create-qword-address-list count addr))
    :rule-classes :type-prescription)

  (defthm qword-paddr-listp-create-qword-address-list
    (qword-paddr-listp (create-qword-address-list count addr)))

  (defthm mult-8-qword-paddr-listp-create-qword-address-list
    (implies (equal (loghead 3 addr) 0)
             (mult-8-qword-paddr-listp (create-qword-address-list count addr))))

  (defthm create-qword-address-list-1
    (implies (and (physical-address-p (+ 7 addr))
                  (physical-address-p addr))
             (equal (create-qword-address-list 1 addr)
                    (list addr)))
    :hints (("Goal" :expand (create-qword-address-list 1 addr))))

  (defthm non-nil-create-qword-address-list
    (implies (and (posp count)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr)))
             (create-qword-address-list count addr)))

  (defthm consp-create-qword-address-list
    (implies (and (physical-address-p addr)
                  (physical-address-p (+ 7 addr))
                  (posp count))
             (consp (create-qword-address-list count addr)))
    :rule-classes (:type-prescription :rewrite))

  (defthm car-of-create-qword-address-list
    (implies (and (posp count)
                  (physical-address-p addr)
                  (physical-address-p (+ 7 addr)))
             (equal (car (create-qword-address-list count addr))
                    addr)))

  (defthm member-p-create-qword-address-list
    (implies (and (<= addr x)
                  (< x (+ (ash count 3) addr))
                  (equal (loghead 3 addr) 0)
                  (equal (loghead 3 x) 0)
                  (physical-address-p x)
                  (physical-address-p addr))
             (equal (member-p x (create-qword-address-list count addr))
                    t))
    :hints (("Goal"
             :induct (create-qword-address-list count addr)
             :in-theory (e/d* (loghead) ()))))

  (defthm not-member-p-create-qword-address-list
    (implies (or (not (<= addr x))
                 (not (< x (+ (ash count 3) addr))))
             (equal (member-p x (create-qword-address-list count addr))
                    nil))
    :hints (("Goal"
             :induct (create-qword-address-list count addr)
             :in-theory (e/d* (loghead) ()))))

  (defthm no-duplicates-p-create-qword-address-list
    (no-duplicates-p (create-qword-address-list count addr))))

(local (in-theory (e/d* () (unsigned-byte-p))))

;; ======================================================================

(define xlate-equiv-entries
  ((e-1 :type (unsigned-byte 64))
   (e-2 :type (unsigned-byte 64)))
  :parents (xlate-equiv-structures)
  :long "<p>Two paging structure entries are @('xlate-equiv-entries')
  if they are equal for all bits except the accessed and dirty
  bits (bits 5 and 6, respectively).</p>"
  ;; (and (equal (part-select e-1 :low 0 :high 4)
  ;;             (part-select e-2 :low 0 :high 4))
  ;;      ;; Bits 5 (accessed bit) and 6 (dirty bit) missing here.
  ;;      (equal (part-select e-1 :low 7 :high 63)
  ;;             (part-select e-2 :low 7 :high 63)))
  (and (equal (ia32e-page-tablesBits->p e-1)
              (ia32e-page-tablesBits->p e-2))
       (equal (ia32e-page-tablesBits->r/w e-1)
              (ia32e-page-tablesBits->r/w e-2))
       (equal (ia32e-page-tablesBits->u/s e-1)
              (ia32e-page-tablesBits->u/s e-2))
       (equal (ia32e-page-tablesBits->pwt e-1)
              (ia32e-page-tablesBits->pwt e-2))
       (equal (ia32e-page-tablesBits->pcd e-1)
              (ia32e-page-tablesBits->pcd e-2))
       ;; A and D bits missing here.
       (equal (ia32e-page-tablesBits->ps e-1)
              (ia32e-page-tablesBits->ps e-2))
       (equal (ia32e-page-tablesBits->res1 e-1)
              (ia32e-page-tablesBits->res1 e-2))
       (equal (ia32e-page-tablesBits->reference-addr e-1)
              (ia32e-page-tablesBits->reference-addr e-2))
       (equal (ia32e-page-tablesBits->res2 e-1)
              (ia32e-page-tablesBits->res2 e-2))
       (equal (ia32e-page-tablesBits->xd e-1)
              (ia32e-page-tablesBits->xd e-2)))


  ///
  
  (defequiv xlate-equiv-entries)

  (def-ruleset xlate-equiv-entries-enables
    '(!ia32e-page-tablesBits->p-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->r/w-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->u/s-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->pwt-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->pcd-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->ps-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->res1-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->reference-addr-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->res2-is-ia32e-page-tablesbits
      !ia32e-page-tablesBits->xd-is-ia32e-page-tablesbits))

  (defthm xlate-equiv-entries-self-set-accessed-bit
    (and (xlate-equiv-entries e (set-accessed-bit (double-rewrite e)))
         (xlate-equiv-entries (set-accessed-bit e) (double-rewrite e)))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit) ()))))

  (defthm xlate-equiv-entries-self-set-dirty-bit
    (and (xlate-equiv-entries e (set-dirty-bit (double-rewrite e)))
         (xlate-equiv-entries (set-dirty-bit e) (double-rewrite e)))
    :hints (("Goal" :in-theory (e/d* (set-dirty-bit) ()))))

  (defun find-xlate-equiv-entries (e-1-equiv e-2-equiv)
    ;; [Shilpi]: This is a quick and dirty function to bind the
    ;; free-vars of
    ;; xlate-equiv-entries-and-set-accessed-and/or-dirty-bit. It makes
    ;; the assumption that e-1-equiv and e-2-equiv will have one of the
    ;; following forms:

    ;; e-1-equiv == e-2-equiv (any form as long as they're both equal)
    ;; (set-accessed-bit (rm-low-64 index x86))
    ;; (set-dirty-bit (rm-low-64 index x86))
    ;; (set-accessed-bit (set-dirty-bit (rm-low-64 index x86)))
    ;; (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))

    ;; I haven't considered deeper nesting of set-accessed-bit and
    ;; set-dirty-bit, mainly because at this point, I'm reasonably
    ;; confident that that's a situation that won't occur.
    (cond ((equal e-1-equiv e-2-equiv)
           `((e-1 . ,e-1-equiv)
             (e-2 . ,e-2-equiv)))
          ((equal (first e-1-equiv) 'rm-low-64)
           (cond ((equal (first e-2-equiv) 'rm-low-64)
                  `((e-1 . ,e-1-equiv)
                    (e-2 . ,e-2-equiv)))
                 ((equal (first e-2-equiv) 'set-accessed-bit)
                  (b* ((e-2
                        (if (equal (car (second e-2-equiv)) 'set-dirty-bit)
                            (second (second e-2-equiv))
                          (second e-2-equiv))))
                    `((e-1 . ,e-1-equiv)
                      (e-2 . ,e-2))))
                 ((equal (first e-2-equiv) 'set-dirty-bit)
                  (b* ((e-2
                        (if (equal (car (second e-2-equiv)) 'set-accessed-bit)
                            (second (second e-2-equiv))
                          (second (second e-2-equiv)))))
                    `((e-1 . ,e-1-equiv)
                      (e-2 . ,e-2))))
                 (t
                  `((e-1 . ,e-1-equiv)
                    (e-2 . ,e-2-equiv)))))
          ((equal (first e-2-equiv) 'rm-low-64)
           (cond ((equal (first e-1-equiv) 'rm-low-64)
                  `((e-2 . ,e-2-equiv)
                    (e-1 . ,e-1-equiv)))
                 ((equal (first e-1-equiv) 'set-accessed-bit)
                  (b* ((e-1
                        (if (equal (car (second e-1-equiv)) 'set-dirty-bit)
                            (second (second e-1-equiv))
                          (second e-1-equiv))))
                    `((e-2 . ,e-2-equiv)
                      (e-1 . ,e-1))))
                 ((equal (first e-1-equiv) 'set-dirty-bit)
                  (b* ((e-1
                        (if (equal (car (second e-1-equiv)) 'set-accessed-bit)
                            (second (second e-1-equiv))
                          (second e-1-equiv))))
                    `((e-2 . ,e-2-equiv)
                      (e-1 . ,e-1))))
                 (t
                  `((e-2 . ,e-2-equiv)
                    (e-1 . ,e-1-equiv)))))))

  (defthm xlate-equiv-entries-and-set-accessed-and/or-dirty-bit
    (implies
     (and (bind-free (find-xlate-equiv-entries e-1-equiv e-2-equiv) (e-1 e-2))
          (xlate-equiv-entries e-1 e-2)
          (or (equal e-1-equiv e-1)
              (equal e-1-equiv (set-accessed-bit e-1))
              (equal e-1-equiv (set-dirty-bit e-1))
              (equal e-1-equiv
                     (set-dirty-bit (set-accessed-bit e-1))))
          (or (equal e-2-equiv e-2)
              (equal e-2-equiv (set-accessed-bit e-2))
              (equal e-2-equiv (set-dirty-bit e-2))
              (equal e-2-equiv
                     (set-dirty-bit (set-accessed-bit e-2)))))
     (xlate-equiv-entries e-1-equiv e-2-equiv))
    :hints (("Goal" :in-theory (e/d* (set-accessed-bit
                                      set-dirty-bit)
                                     ()))))

  (defthm xlate-equiv-entries-and-page-present-cong
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-present e-1) (page-present e-2)))
    :hints (("Goal"
             :in-theory (e/d* (page-present) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-read-write-cong
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-read-write e-1) (page-read-write e-2)))
    :hints (("Goal"
             :in-theory (e/d* (page-read-write) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-user-supervisor-cong
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-user-supervisor e-1) (page-user-supervisor e-2)))
    :hints (("Goal"
             :in-theory (e/d* (page-user-supervisor) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-reference-addr
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (ia32e-page-tablesbits->reference-addr e-1)
                    (ia32e-page-tablesbits->reference-addr e-2)))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-size
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-size e-1) (page-size e-2)))
    :hints (("Goal" :in-theory (e/d* (page-size) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-and-page-execute-disable
    (implies (xlate-equiv-entries e-1 e-2)
             (equal (page-execute-disable e-1) (page-execute-disable e-2)))
    :hints (("Goal"
             :in-theory (e/d* (page-execute-disable) ())))
    :rule-classes :congruence)

  (defthm xlate-equiv-entries-with-loghead-64-1
    (equal (xlate-equiv-entries (loghead 64 e-1) e-2)
           (xlate-equiv-entries e-1 e-2))
    :hints (("Goal" :in-theory (e/d (xlate-equiv-entries
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
                                    ()))))

  (defthm xlate-equiv-entries-with-loghead-64-2
    (equal (xlate-equiv-entries e-1 (loghead 64 e-2))
           (xlate-equiv-entries e-1 e-2))
    :hints (("Goal" :in-theory (e/d (xlate-equiv-entries
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
                                    ()))))

  (defthm xlate-equiv-entries-with-loghead-64-cong
    (implies (xlate-equiv-entries e-1 e-2)
             (xlate-equiv-entries (loghead 64 e-1) (loghead 64 e-2)))
    :hints (("Goal" :in-theory (e/d (ia32e-page-tablesbits->xd
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

  (local (include-book "centaur/gl/gl" :dir :system))

  (local
   (def-gl-thm xlate-equiv-entries-and-loghead-gl
     :hyp (and (xlate-equiv-entries e-1 e-2)
               (unsigned-byte-p 64 e-1)
               (unsigned-byte-p 64 e-2)
               (natp n)
               (<= n 5)
               (<= n 64))
     :concl (equal (loghead n e-1) (loghead n e-2))
     :g-bindings
     (gl::auto-bindings
      (:mix (:nat e-1 65)
            (:nat e-2 65)
            (:nat n   65)))))

  (defthmd xlate-equiv-entries-and-loghead
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= n 5))
             (equal (loghead n e-1) (loghead n e-2)))
    :hints (("Goal" :in-theory (e/d (xlate-equiv-entries-with-loghead-64-1
                                     xlate-equiv-entries-with-loghead-64-2)
                                    (xlate-equiv-entries-and-loghead-gl))
             :use ((:instance xlate-equiv-entries-and-loghead-gl
                              (e-1 (loghead 64 e-1))
                              (e-2 (loghead 64 e-2)))))))

  (local
   (def-gl-thm xlate-equiv-entries-and-logtail-gl
     :hyp (and (xlate-equiv-entries e-1 e-2)
               (unsigned-byte-p 64 e-1)
               (unsigned-byte-p 64 e-2)
               (natp n)
               (<= 7 n)
               (<= n 64))
     :concl (equal (logtail n e-1) (logtail n e-2))
     :g-bindings
     (gl::auto-bindings
      (:mix (:nat e-1 65)
            (:nat e-2 65)
            (:nat n   65)))))

  (defthmd xlate-equiv-entries-and-logtail
    (implies (and (xlate-equiv-entries e-1 e-2)
                  (syntaxp (quotep n))
                  (natp n)
                  (<= 7 n)
                  (<= n 64))
             (equal (logtail n (loghead 64 e-1))
                    (logtail n (loghead 64 e-2))))
    :hints (("Goal" :in-theory (e/d (xlate-equiv-entries-with-loghead-64-1
                                     xlate-equiv-entries-with-loghead-64-2)
                                    (xlate-equiv-entries-and-logtail-gl
                                     xlate-equiv-entries
                                     xlate-equiv-entries-with-loghead-64-cong))
             :use ((:instance xlate-equiv-entries-and-logtail-gl
                              (e-1 (loghead 64 e-1))
                              (e-2 (loghead 64 e-2)))
                   (:instance xlate-equiv-entries-with-loghead-64-cong))))))

;; ======================================================================

;; Gathering the physical addresses where paging structures are
;; located:

(define gather-pml4-table-qword-addresses (x86)
  :parents (gather-paging-structures)
  :returns (list-of-addresses qword-paddr-listp)

  (b* ((cr3 (ctri *cr3* x86))
       ;; PML4 Table, all 4096 bytes of it, will always fit into the
       ;; physical memory; pml4-table-base-addr is 52-bit wide, with
       ;; low 12 bits = 0.
       (pml4-table-base-addr (ash (cr3Bits->pdb cr3) 12)))
    (create-qword-address-list 512 pml4-table-base-addr))
  ///
  (std::more-returns (list-of-addresses true-listp))

  (defthm consp-gather-pml4-table-qword-addresses
    (consp (gather-pml4-table-qword-addresses x86))
    :rule-classes (:type-prescription :rewrite))

  (defthm mult-8-qword-paddr-listp-gather-pml4-table-qword-addresses
    (mult-8-qword-paddr-listp (gather-pml4-table-qword-addresses x86)))

  (defthm no-duplicates-p-gather-pml4-table-qword-addresses
    (no-duplicates-p (gather-pml4-table-qword-addresses x86)))

  (defthm gather-pml4-table-qword-addresses-xw-fld!=ctr
    (implies (not (equal fld :ctr))
             (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
                    (gather-pml4-table-qword-addresses x86)))
    :hints (("Goal"
             :cases ((equal fld :ctr))
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ()))))

  (defthm gather-pml4-table-qword-addresses-wm-low-64
    (equal (gather-pml4-table-qword-addresses (wm-low-64 index val x86))
           (gather-pml4-table-qword-addresses x86))
    :hints (("Goal"
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ()))))

  (defthm gather-pml4-table-qword-addresses-xw-fld=ctr
    (implies (and (equal fld :ctr)
                  (not (equal index *cr3*)))
             (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
                    (gather-pml4-table-qword-addresses x86)))
    :hints (("Goal"
             :cases ((equal fld :ctr))
             :in-theory (e/d* (gather-pml4-table-qword-addresses)
                              ())))))

(define gather-qword-addresses-corresponding-to-1-entry
  ((superior-structure-paddr natp)
   x86)

  :parents (gather-paging-structures)

  :guard (and (not (app-view x86))
              (physical-address-p superior-structure-paddr)
              (physical-address-p (+ 7 superior-structure-paddr)))

  :returns (list-of-addresses qword-paddr-listp)

  :long "<p>This function returns all qword addresses of the inferior
  paging structure referred to by a paging entry at address
  @('superior-structure-paddr').</p>"

  (b* ((superior-structure-entry (rm-low-64 superior-structure-paddr x86)))
    (if (and
         (equal (page-size superior-structure-entry) 0))
        ;; Gather the qword addresses of a paging structure only if a
        ;; superior structure points to it, i.e., the
        ;; superior-structure-entry should be present (P=1) and it
        ;; should reference an inferior structure (PS=0).
        (b* ((this-structure-base-addr
              (ash (ia32e-page-tablesBits->reference-addr superior-structure-entry) 12))
             ;; The inferior table will always fit into the physical
             ;; memory.
             )
          (create-qword-address-list 512 this-structure-base-addr))
      nil))

  ///
  (std::more-returns (list-of-addresses true-listp))

  (defthm mult-8-qword-paddr-listp-gather-qword-addresses-corresponding-to-1-entry
    (mult-8-qword-paddr-listp
     (gather-qword-addresses-corresponding-to-1-entry entry x86)))

  (defthm no-duplicates-p-gather-qword-addresses-corresponding-to-1-entry
    (no-duplicates-p
     (gather-qword-addresses-corresponding-to-1-entry entry x86)))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     n (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry n x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-xw-fld=mem-disjoint
    (implies (disjoint-p (addr-range 1 index)
                         (addr-range 8 addr))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              (addr-range
                               addr-range-1)))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
    (implies (disjoint-p (addr-range 8 index)
                         (addr-range 8 addr))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-superior-entry-addr
    (implies (and (equal index addr)
                  (xlate-equiv-entries (double-rewrite val)
                                       (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (not (xr :app-view nil x86)))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :in-theory (e/d* (member-p)
                              (xlate-equiv-entries)))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-with-different-x86-entries
    (implies (xlate-equiv-entries (rm-low-64 addr x86-equiv)
                                  (rm-low-64 addr x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     (unsigned-byte-p)))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86-disjoint
    (implies (and (disjoint-p (addr-range 8 index) (addr-range 8 addr))
                  (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                         (gather-qword-addresses-corresponding-to-1-entry addr x86)))
             ;; (xlate-equiv-entries (rm-low-64 addr x86-equiv)
             ;;                      (rm-low-64 addr x86))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     (gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
                                      unsigned-byte-p))
             :use ((:instance gather-qword-addresses-corresponding-to-1-entry-wm-low-64-disjoint
                              (x86 x86-equiv))))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86
    ;; This is a surprising theorem. Even if we write an
    ;; xlate-equiv-entries value to addr in x86-equiv (a state that may
    ;; be different from x86), there's no guarantee that the qword
    ;; addresses of the inferior structure entry pointed to by this new
    ;; value will be the same in x86 and x86-equiv. However, that's
    ;; exactly what this theorem says, and this is because of the way
    ;; gather-qword-addresses-corresponding-to-1-entry is defined ---
    ;; simply in terms of create-qword-address-list once the entry at
    ;; addr is read from the x86 (or x86-equiv) state.
    (implies (and (xlate-equiv-entries (double-rewrite val)
                                       (rm-low-64 addr x86))
                  (unsigned-byte-p 64 val)
                  (not (xr :app-view nil x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-1-entry
                     addr (wm-low-64 addr val x86-equiv))
                    (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                     ()))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-subset-p-with-wm-low-64
    (implies (and (equal (page-size value) 1)
                  (physical-address-p index)
                  (equal (loghead 3 index) 0)
                  (physical-address-p addr)
                  (equal (loghead 3 addr) 0)
                  (unsigned-byte-p 64 value)
                  (not (app-view x86)))
             (subset-p (gather-qword-addresses-corresponding-to-1-entry addr (wm-low-64 index value x86))
                       (gather-qword-addresses-corresponding-to-1-entry addr x86)))
    :hints (("Goal"
             :cases ((equal index addr))
             :in-theory (e/d* (member-p
                               subset-p)
                              ())))))

(local
 (defthm member-p-mult-8-qword-paddr-listp-lemma
   (implies (and (mult-8-qword-paddr-listp addrs)
                 (not (member-p index addrs))
                 (physical-address-p index)
                 (equal (loghead 3 index) 0))
            (disjoint-p (addr-range 8 index)
                        (open-qword-paddr-list addrs)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p
                                     member-p)
                                    ())))))

(local
 (defthm member-p-and-mult-8-qword-paddr-listp-more
   (implies (and (member-p index addrs)
                 (mult-8-qword-paddr-listp addrs))
            (physical-address-p (+ 7 index)))))

(local
 (defthm member-p-no-duplicates-p-lemma
   (implies (and (member-p index (cdr addrs))
                 (no-duplicates-p addrs))
            (not (equal index (car addrs))))))

(define gather-qword-addresses-corresponding-to-entries-aux
  (superior-structure-paddrs x86)

  :parents (gather-qword-addresses-corresponding-to-entries)

  :guard (and (not (app-view x86))
              (qword-paddr-listp superior-structure-paddrs))

  :short "Returns a list of qword addresses of inferior paging
  structures referred by the entries located at addresses
  @('superior-structure-paddrs') of a given superior structure"

  :returns (list-of-addresses qword-paddr-listp)

  (if (endp superior-structure-paddrs)
      nil
    (b* ((superior-structure-paddr-1 (car superior-structure-paddrs))
         (superior-structure-paddrs-rest (cdr superior-structure-paddrs))
         (inferior-addresses
          (gather-qword-addresses-corresponding-to-1-entry
           superior-structure-paddr-1 x86))
         ((when (not inferior-addresses))
          (gather-qword-addresses-corresponding-to-entries-aux
           superior-structure-paddrs-rest x86)))
      (append
       inferior-addresses
       (gather-qword-addresses-corresponding-to-entries-aux
        superior-structure-paddrs-rest x86))))
  ///
  (std::more-returns (list-of-addresses true-listp))

  (defthm mult-8-qword-paddr-listp-gather-qword-addresses-corresponding-to-entries-aux
    (implies (mult-8-qword-paddr-listp addrs)
             (mult-8-qword-paddr-listp
              (gather-qword-addresses-corresponding-to-entries-aux addrs x86))))

  (defthm gather-qword-addresses-corresponding-to-1-entry-and-entries-aux-subset-p
    (implies (member-p addr addrs)
             (subset-p (gather-qword-addresses-corresponding-to-1-entry addr x86)
                       (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal" :in-theory (e/d* (member-p)
                                     ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-subset-and-superset
    (implies (subset-p sub super)
             (subset-p
              (gather-qword-addresses-corresponding-to-entries-aux sub x86)
              (gather-qword-addresses-corresponding-to-entries-aux super x86)))
    :hints (("Goal"
             :in-theory (e/d* (subset-p
                               member-p
                               disjoint-p)
                              (force
                               (force)
                               (:meta acl2::mv-nth-cons-meta))))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-xw-fld=mem-disjoint
    (implies (and (not (member-p index (open-qword-paddr-list addrs)))
                  (physical-address-p index))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux
                               ifix
                               disjoint-p)
                              (addr-range
                               (addr-range))))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-wm-low-64-disjoint
    (implies (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux
                               ifix)
                              ()))))

  (local
   (defthm gather-qword-addresses-corresponding-to-entries-aux-wm-low-64-superior-entry-addr-helper-2
     (implies (and (member-p index addrs)
                   (mult-8-qword-paddr-listp addrs)
                   (no-duplicates-p addrs)
                   (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                   (unsigned-byte-p 64 val)
                   (physical-address-p index)
                   (not (xr :app-view nil x86)))
              (equal (gather-qword-addresses-corresponding-to-entries-aux
                      addrs (wm-low-64 index val x86))
                     (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
     :hints (("Goal"
              :in-theory (e/d* (member-p) (xlate-equiv-entries))))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-wm-low-64-superior-entry-addr
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (not (xr :app-view nil x86)))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* ()
                              (xlate-equiv-entries
                               gather-qword-addresses-corresponding-to-entries-aux
                               member-p-and-mult-8-qword-paddr-listp))
             :use ((:instance member-p-and-mult-8-qword-paddr-listp
                              (index index)
                              (addrs addrs))))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries-aux addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries-aux addrs x86))
                  (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs)))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux
                               ifix
                               disjoint-p)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-wm-low-64-with-different-x86
    (implies (and
              (equal
               (gather-qword-addresses-corresponding-to-entries-aux addrs x86-equiv)
               (gather-qword-addresses-corresponding-to-entries-aux addrs x86))
              (member-p index addrs)
              (mult-8-qword-paddr-listp addrs)
              (no-duplicates-p addrs)
              (xlate-equiv-entries (double-rewrite val)
                                   (rm-low-64 index x86-equiv))
              (unsigned-byte-p 64 val)
              (not (xr :app-view nil x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-entries-aux
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries-aux addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux
                               member-p)
                              (unsigned-byte-p)))))

  (defthm gather-qword-addresses-corresponding-to-entries-aux-and-wm-low-64-subset-and-superset-general
    (implies
     (and (subset-p sub super)
          (equal (page-size value) 1)
          (mult-8-qword-paddr-listp super)
          (physical-address-p index)
          (equal (loghead 3 index) 0)
          (not (app-view x86))
          (unsigned-byte-p 64 value))
     (subset-p
      (gather-qword-addresses-corresponding-to-entries-aux
       sub
       (wm-low-64 index value x86))
      (gather-qword-addresses-corresponding-to-entries-aux
       super
       x86)))
    :hints (("Goal"
             :in-theory (e/d* (subset-p
                               member-p
                               gather-qword-addresses-corresponding-to-entries-aux
                               mult-8-qword-paddr-listp)
                              (force (force)
                                     physical-address-p
                                     (:meta acl2::mv-nth-cons-meta))))
            (if (and (consp (car id))
                     (< 1 (len (car id))))
                '(:use ((:instance gather-qword-addresses-corresponding-to-1-entry-subset-p-with-wm-low-64
                                   (addr (car sub)))
                        (:instance gather-qword-addresses-corresponding-to-1-entry-and-entries-aux-subset-p
                                   (addr (car sub))
                                   (addrs super)))
                       :in-theory (e/d* (subset-p
                                         member-p
                                         gather-qword-addresses-corresponding-to-entries-aux)
                                        (physical-address-p
                                         gather-qword-addresses-corresponding-to-1-entry-subset-p-with-wm-low-64
                                         gather-qword-addresses-corresponding-to-1-entry-and-entries-aux-subset-p
                                         force
                                         (force)
                                         (:meta acl2::mv-nth-cons-meta))))
              nil))))

(define gather-qword-addresses-corresponding-to-entries
  (superior-structure-paddrs x86)

  :parents (gather-all-paging-structure-qword-addresses)

  :guard (and (not (app-view x86))
              (qword-paddr-listp superior-structure-paddrs))

  :short "Returns a list --- with no duplicates --- of qword addresses
  of inferior paging structures referred by the entries located at
  addresses @('superior-structure-paddrs') of a given superior
  structure"

  :returns (list-of-addresses qword-paddr-listp)

  (remove-duplicates-equal
   (gather-qword-addresses-corresponding-to-entries-aux
    superior-structure-paddrs x86))

  ///
  (std::more-returns (list-of-addresses true-listp))

  (defthm mult-8-qword-paddr-listp-gather-qword-addresses-corresponding-to-entries
    (implies (mult-8-qword-paddr-listp addrs)
             (mult-8-qword-paddr-listp
              (gather-qword-addresses-corresponding-to-entries addrs x86))))

  (defthm no-duplicates-p-gather-qword-addresses-corresponding-to-entries
    (no-duplicates-p
     (gather-qword-addresses-corresponding-to-entries addrs x86))
    :hints (("Goal" :in-theory (e/d* (no-duplicates-p-to-no-duplicatesp-equal)
                                     (no-duplicates-p)))))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw fld index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-xw-fld=mem-disjoint
    (implies (and (not (member-p index (open-qword-paddr-list addrs)))
                  (physical-address-p index))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (xw :mem index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix
                               disjoint-p)
                              (addr-range
                               (addr-range))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-disjoint
    (implies (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix)
                              ()))))

  (local
   (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-superior-entry-addr-helper-2
     (implies (and (member-p index addrs)
                   (mult-8-qword-paddr-listp addrs)
                   (no-duplicates-p addrs)
                   (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                   (unsigned-byte-p 64 val)
                   (not (xr :app-view nil x86)))
              (equal (gather-qword-addresses-corresponding-to-entries
                      addrs (wm-low-64 index val x86))
                     (gather-qword-addresses-corresponding-to-entries addrs x86)))
     :hints (("Goal"
              :in-theory (e/d* (member-p) (xlate-equiv-entries))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-superior-entry-addr
    (implies (and (member-p index addrs)
                  (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (not (xr :app-view nil x86)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* ()
                              (xlate-equiv-entries
                               gather-qword-addresses-corresponding-to-entries
                               member-p-and-mult-8-qword-paddr-listp))
             :use ((:instance member-p-and-mult-8-qword-paddr-listp
                              (index index)
                              (addrs addrs))))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86-disjoint
    (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                         (gather-qword-addresses-corresponding-to-entries addrs x86))
                  (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               ifix
                               disjoint-p)
                              ()))))

  (defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86
    (implies (and
              (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                     (gather-qword-addresses-corresponding-to-entries addrs x86))
              (member-p index addrs)
              (mult-8-qword-paddr-listp addrs)
              (no-duplicates-p addrs)
              (xlate-equiv-entries (double-rewrite val)
                                   (rm-low-64 index x86-equiv))
              (unsigned-byte-p 64 val)
              (not (xr :app-view nil x86-equiv)))
             (equal (gather-qword-addresses-corresponding-to-entries
                     addrs (wm-low-64 index val x86-equiv))
                    (gather-qword-addresses-corresponding-to-entries addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               member-p)
                              (unsigned-byte-p)))))

  (defthm gather-qword-addresses-corresponding-to-entries-and-wm-low-64-subset-and-superset-general
    (implies
     (and (subset-p sub super)
          (equal (page-size value) 1)
          (mult-8-qword-paddr-listp super)
          (physical-address-p index)
          (equal (loghead 3 index) 0)
          (not (app-view x86))
          (unsigned-byte-p 64 value))
     (subset-p
      (gather-qword-addresses-corresponding-to-entries
       sub
       (wm-low-64 index value x86))
      (gather-qword-addresses-corresponding-to-entries
       super
       x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                               subset-p-transitive
                               subset-p-and-remove-duplicates-equal-both)
                              (force
                               (force)
                               physical-address-p
                               (:meta acl2::mv-nth-cons-meta)))))))
(local
 (defthm member-p-and-disjoint-p-with-open-qword-paddr-list-and-addr-range
   (implies (and (member-p index a)
                 (mult-8-qword-paddr-listp a))
            (equal (disjoint-p (addr-range 8 index) (open-qword-paddr-list a))
                   nil))
   :hints (("Goal" :in-theory (e/d* (member-p disjoint-p)
                                    ())))))

(define gather-all-paging-structure-qword-addresses (x86)

  :parents (gather-paging-structures)

  :short "Returns a list of qword addresses of all the active paging
  structures"

  :guard (not (app-view x86))

  :returns (list-of-addresses qword-paddr-listp)

  (b* ( ;; One Page Map Level-4 (PML4) Table:
       (pml4-table-qword-addresses
        (gather-pml4-table-qword-addresses x86))
       ;; Up to 512 Page Directory Pointer Tables (PDPT):
       (pdpt-table-qword-addresses
        (gather-qword-addresses-corresponding-to-entries
         pml4-table-qword-addresses x86))
       ;; Up to 512*512 Page Directories (PD):
       (pd-qword-addresses
        (gather-qword-addresses-corresponding-to-entries
         pdpt-table-qword-addresses x86))
       ;; Up to 512*512*512 Page Tables (PT):
       (pt-qword-addresses
        (gather-qword-addresses-corresponding-to-entries
         pd-qword-addresses x86)))

    (remove-duplicates-equal
     (append
      ;; Each item below is a qword-paddr-listp.
      pml4-table-qword-addresses
      pdpt-table-qword-addresses
      pd-qword-addresses
      pt-qword-addresses)))
  ///
  (std::more-returns (list-of-addresses true-listp))

  (defthm mult-8-qword-paddr-listp-gather-all-paging-structure-qword-addresses
    (mult-8-qword-paddr-listp (gather-all-paging-structure-qword-addresses x86)))

  (defthm no-duplicates-p-gather-all-paging-structure-qword-addresses
    (no-duplicates-p (gather-all-paging-structure-qword-addresses x86))
    :hints (("Goal" :in-theory (e/d* (no-duplicates-p-to-no-duplicatesp-equal)
                                     (no-duplicates-p)))))

  (defthmd gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw fld index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (make-event

   ;; This make-event generates rules for each fld except mem, ctr,
   ;; and app-view, and all these rules together say what
   ;; the rule
   ;; gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr
   ;; says.  However, this rule is pretty expensive because it matches
   ;; so often.  Hence, I'd rather define individual rules and keep
   ;; gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr
   ;; disabled.

   (generate-read-fn-over-xw-thms
    (remove-elements-from-list '(:app-view :ctr :mem) *x86-field-names-as-keywords*)
    'gather-all-paging-structure-qword-addresses
    (acl2::formals 'gather-all-paging-structure-qword-addresses (w state))
    :double-rewrite? t))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=ctr
    (implies (not (equal index *cr3*))
             (equal (gather-all-paging-structure-qword-addresses
                     (xw :ctr index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (local
   (defthmd not-member-p-of-open-qword-paddr-list-and-remove-duplicates-equal
     (implies (not (member-p index (open-qword-paddr-list (remove-duplicates-equal a))))
              (not (member-p index (open-qword-paddr-list a))))
     :hints (("Goal" :in-theory (e/d* (member-p) ())))))

  (local
   (defthm gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint-helper
     (implies (not (member-p index (open-qword-paddr-list (remove-duplicates-equal (append a b c d)))))
              (and (not (member-p index (open-qword-paddr-list a)))
                   (not (member-p index (open-qword-paddr-list b)))
                   (not (member-p index (open-qword-paddr-list c)))
                   (not (member-p index (open-qword-paddr-list d)))))
     :hints (("Goal" :in-theory (e/d* () ())
              :use ((:instance not-member-p-of-open-qword-paddr-list-and-remove-duplicates-equal
                               (a (append a b c d))))))))

  (defthm gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
    (implies (and (not (member-p index
                                 (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86))))
                  (physical-address-p index))
             (equal (gather-all-paging-structure-qword-addresses (xw :mem index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (local
   (defthmd disjoint-p-of-open-qword-paddr-list-and-remove-duplicates-equal
     (implies (disjoint-p index (open-qword-paddr-list (remove-duplicates-equal a)))
              (disjoint-p index (open-qword-paddr-list a)))
     :hints (("Goal" :in-theory (e/d* (disjoint-p) ())))))

  (local
   (defthm gather-all-paging-structure-qword-addresses-wm-low-64-disjoint-helper
     (implies (and (disjoint-p index (open-qword-paddr-list (remove-duplicates-equal (append a b c d))))
                   (true-listp d))
              (and (disjoint-p index (open-qword-paddr-list a))
                   (disjoint-p index (open-qword-paddr-list b))
                   (disjoint-p index (open-qword-paddr-list c))
                   (disjoint-p index (open-qword-paddr-list d))))
     :hints (("Goal" :in-theory (e/d* () (disjoint-p-of-open-qword-paddr-list-and-remove-duplicates-equal))
              :use ((:instance disjoint-p-of-open-qword-paddr-list-and-remove-duplicates-equal
                               (a (append a b c d))))))))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
    (implies (disjoint-p (addr-range 8 index)
                         (open-qword-paddr-list
                          (gather-all-paging-structure-qword-addresses x86)))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86))))

  (local
   (defthmd member-p-of-remove-duplicates-equal
     (implies (member-p index (remove-duplicates-equal a))
              (member-p index a))
     :hints (("Goal" :in-theory (e/d* (member-p-iff-member-equal) (member-p))))))

  (local
   (defthm gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr-helper
     (implies (and (member-p index (remove-duplicates-equal (append a b c d)))
                   (mult-8-qword-paddr-listp a)
                   (mult-8-qword-paddr-listp b)
                   (mult-8-qword-paddr-listp c)
                   (mult-8-qword-paddr-listp d))
              (and
               (not (and (disjoint-p (addr-range 8 index) (open-qword-paddr-list a))
                         (disjoint-p (addr-range 8 index) (open-qword-paddr-list b))
                         (disjoint-p (addr-range 8 index) (open-qword-paddr-list c))
                         (disjoint-p (addr-range 8 index) (open-qword-paddr-list d))))
               (or (member-p index a)
                   (disjoint-p (addr-range 8 index) (open-qword-paddr-list a)))
               (or (member-p index b)
                   (disjoint-p (addr-range 8 index) (open-qword-paddr-list b)))
               (or (member-p index c)
                   (disjoint-p (addr-range 8 index) (open-qword-paddr-list c)))
               (or (member-p index d)
                   (disjoint-p (addr-range 8 index) (open-qword-paddr-list d)))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d* () (member-p-of-remove-duplicates-equal))
              :use ((:instance member-p-of-remove-duplicates-equal
                               (a (append a b c d))))))
     :rule-classes nil))

  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
    (implies (and (member-p index (gather-all-paging-structure-qword-addresses x86))
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                  (unsigned-byte-p 64 val)
                  (not (xr :app-view nil x86)))
             (equal (gather-all-paging-structure-qword-addresses
                     (wm-low-64 index val x86))
                    (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal" :use
             ((:instance
               gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr-helper
               (index index)
               (a (gather-pml4-table-qword-addresses x86))
               (b (gather-qword-addresses-corresponding-to-entries
                   (gather-pml4-table-qword-addresses x86)
                   x86))
               (c (gather-qword-addresses-corresponding-to-entries
                   (gather-qword-addresses-corresponding-to-entries
                    (gather-pml4-table-qword-addresses x86)
                    x86)
                   x86))
               (d (gather-qword-addresses-corresponding-to-entries
                   (gather-qword-addresses-corresponding-to-entries
                    (gather-qword-addresses-corresponding-to-entries
                     (gather-pml4-table-qword-addresses x86)
                     x86)
                    x86)
                   x86)))))))

  (defthm gather-all-paging-structure-qword-addresses-and-wm-low-64-subset-p
    (implies
     (and (equal (page-size value) 1)
          (physical-address-p index)
          (equal (loghead 3 index) 0)
          (unsigned-byte-p 64 value)
          (not (app-view x86)))
     (subset-p
      (gather-all-paging-structure-qword-addresses (wm-low-64 index value x86))
      (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                               subset-p-and-remove-duplicates-equal-both)
                              (force
                               (force)
                               (:meta acl2::mv-nth-cons-meta))))))

  (defthm gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p
    (implies
     (and (equal p-addrs (addr-range 8 index))
          (equal (page-size value) 1)
          (physical-address-p index)
          (equal (loghead 3 index) 0)
          (unsigned-byte-p 64 value)
          (not (app-view x86)))
     (subset-p
      (gather-all-paging-structure-qword-addresses
       (write-to-physical-memory p-addrs value x86))
      (gather-all-paging-structure-qword-addresses x86)))
    :hints (("Goal"
             :in-theory (e/d* () (gather-all-paging-structure-qword-addresses))
             :use ((:instance rewrite-wm-low-64-to-write-to-physical-memory))))))

;; ======================================================================

(define xlate-equiv-entries-at-qword-addresses
  (list-of-addresses-1 list-of-addresses-2 x86-1 x86-2)
  :parents (xlate-equiv-structures)
  :non-executable t
  :guard (and (qword-paddr-listp list-of-addresses-1)
              (qword-paddr-listp list-of-addresses-2)
              (equal (len list-of-addresses-1)
                     (len list-of-addresses-2))
              (x86p x86-1)
              (x86p x86-2))

  (if (equal (xr :app-view nil x86-1) nil)
      (if (equal (xr :app-view nil x86-2) nil)

          (if (endp list-of-addresses-1)
              t
            (b* ((addr-1 (car list-of-addresses-1))
                 (addr-2 (car list-of-addresses-2))
                 (qword-1 (rm-low-64 addr-1 x86-1))
                 (qword-2 (rm-low-64 addr-2 x86-2))
                 ((when (not (xlate-equiv-entries qword-1 qword-2)))
                  nil))
              (xlate-equiv-entries-at-qword-addresses
               (cdr list-of-addresses-1) (cdr list-of-addresses-2)
               x86-1 x86-2)))

        nil)
    ;; I choose to say the following instead of (equal (xr
    ;; :app-view 0 x86-2) t) so that I can prove that
    ;; this function unconditionally returns a boolean, as opposed to
    ;; returning a boolean only if x86-2 is known to satisfy x86p.
    (equal (xr :app-view nil x86-2)
           (xr :app-view nil x86-1)))

  ///

  (defthm booleanp-of-xlate-equiv-entries-at-qword-addresses
    (booleanp (xlate-equiv-entries-at-qword-addresses addrs addrs x y))
    :rule-classes :type-prescription)

  (defthm xlate-equiv-entries-at-qword-addresses-reflexive
    (implies (qword-paddr-listp a)
             (xlate-equiv-entries-at-qword-addresses a a x x)))

  (defthm xlate-equiv-entries-at-qword-addresses-commutative
    (implies (equal (len a) (len b))
             (equal (xlate-equiv-entries-at-qword-addresses a b x y)
                    (xlate-equiv-entries-at-qword-addresses b a y x)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm xlate-equiv-entries-at-qword-addresses-transitive
    (implies (and (equal (len a) (len b))
                  (equal (len b) (len c))
                  (xlate-equiv-entries-at-qword-addresses a b x y)
                  (xlate-equiv-entries-at-qword-addresses b c y z))
             (xlate-equiv-entries-at-qword-addresses a c x z)))

  (defthm xlate-equiv-entries-at-qword-addresses-with-xw-fld!=mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (xlate-equiv-entries-at-qword-addresses
                     addrs-1 addrs-2
                     x86-1
                     (xw fld index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses
                     addrs-1 addrs-2 x86-1 x86-2))))

  (defthm xlate-equiv-entries-at-qword-addresses-implies-xlate-equiv-entries
    (implies (and (xlate-equiv-entries-at-qword-addresses
                   addrs addrs x86-1 x86-2)
                  (member-p index addrs)
                  (not (xr :app-view nil x86-1)))
             (xlate-equiv-entries (rm-low-64 index x86-1)
                                  (rm-low-64 index x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p)
                                     (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-with-xw-mem-disjoint
    (implies (disjoint-p (list index)
                         (open-qword-paddr-list addrs))
             (equal (xlate-equiv-entries-at-qword-addresses
                     addrs addrs
                     x86-1
                     (xw :mem index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses
                     addrs addrs
                     x86-1
                     x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p) (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-with-wm-low-64-disjoint
    (implies (disjoint-p (addr-range 8 index)
                         (open-qword-paddr-list addrs))
             (equal (xlate-equiv-entries-at-qword-addresses
                     addrs addrs
                     x86-1
                     (wm-low-64 index val x86-2))
                    (xlate-equiv-entries-at-qword-addresses
                     addrs addrs
                     x86-1
                     x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p) (xlate-equiv-entries)))))

  (defthm xlate-equiv-entries-at-qword-addresses-with-wm-low-64-entry-addr
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (member-p index addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-1))
                  (unsigned-byte-p 64 val)
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86-1 x86-2))
             (xlate-equiv-entries-at-qword-addresses
              addrs addrs
              x86-1
              (wm-low-64 index val x86-2)))
    :hints (("Goal" :in-theory (e/d* (member-p)
                                     (xlate-equiv-entries)))))

  (local
   (defthmd xlate-equiv-entries-at-qword-addresses-with-wm-low-64-different-x86-helper-1
     (implies
      (and (bind-free '((index . index) (val . val)))
           (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                (rm-low-64 (car addrs) x86-2))
           (unsigned-byte-p 52 index)
           (unsigned-byte-p 52 (car addrs))
           (equal (loghead 3 (car addrs)) 0)
           (mult-8-qword-paddr-listp (cdr addrs))
           (not (member-p (car addrs) (cdr addrs)))
           (no-duplicates-p (cdr addrs))
           (member-p index (cdr addrs))
           (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                     (rm-low-64 (car addrs)
                                                (wm-low-64 index val x86-2)))))
      (not (xlate-equiv-entries-at-qword-addresses (cdr addrs)
                                                   (cdr addrs)
                                                   x86-1 x86-2)))
     :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
              :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                               (index index)
                               (addrs (cdr addrs))
                               (addr (car addrs))))))))

  (local
   (defthmd xlate-equiv-entries-at-qword-addresses-with-wm-low-64-different-x86-helper-2
     (implies (and (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                             (rm-low-64 (car addrs) x86-2)))
                   (unsigned-byte-p 52 index)
                   (unsigned-byte-p 52 (car addrs))
                   (equal (loghead 3 (car addrs)) 0)
                   (mult-8-qword-paddr-listp (cdr addrs))
                   (not (member-p (car addrs) (cdr addrs)))
                   (no-duplicates-p (cdr addrs))
                   (member-p index (cdr addrs))
                   (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                        (rm-low-64 (car addrs)
                                                   (wm-low-64 index val x86-2))))
              (not (xlate-equiv-entries-at-qword-addresses
                    (cdr addrs)
                    (cdr addrs)
                    x86-1 (wm-low-64 index val x86-2))))
     :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
              :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                               (index index)
                               (addrs (cdr addrs))
                               (addr (car addrs))))))))

  (local
   (defthm unsigned-byte-p-lemma-about-member-of-mult-8-qword-paddr-listp
     (implies (and (mult-8-qword-paddr-listp addrs)
                   (member-p index addrs))
              (unsigned-byte-p 52 index))))

  (defthmd xlate-equiv-entries-at-qword-addresses-with-wm-low-64-different-x86
    (implies (and (mult-8-qword-paddr-listp addrs)
                  (no-duplicates-p addrs)
                  (member-p index addrs)
                  (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-2))
                  (unsigned-byte-p 64 val))
             (equal
              (xlate-equiv-entries-at-qword-addresses
               addrs addrs
               x86-1
               (wm-low-64 index val x86-2))
              (xlate-equiv-entries-at-qword-addresses addrs addrs x86-1 x86-2)))
    :hints (("Goal"
             :use ((:instance member-p-and-mult-8-qword-paddr-listp))
             :in-theory (e/d* (member-p
                               xlate-equiv-entries-at-qword-addresses
                               xlate-equiv-entries-at-qword-addresses-with-wm-low-64-different-x86-helper-1
                               xlate-equiv-entries-at-qword-addresses-with-wm-low-64-different-x86-helper-2)
                              (xlate-equiv-entries))))))

;; ======================================================================

;; Defining xlate-equiv-structures:

;; First, some bind-free and other misc. stuff:

(defun find-xlate-equiv-structures-from-occurrence
    (bound-x86-term mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((call (acl2::find-call-lst 'xlate-equiv-structures (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; xlate-equiv-structures term not encountered.
        nil)
       (x86-1-var (second call))
       (x86-2-var (third call))

       (x86-var
        (if (equal bound-x86-term x86-1-var)
            x86-2-var
          x86-1-var)))
    x86-var))

(defun find-an-xlate-equiv-x86-aux (thm-name x86-term mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm-name state))

  ;; Finds a "smaller" x86 that is xlate-equiv to x86-term.
  (if (atom x86-term)

      (b* ((equiv-x86-term
            (find-xlate-equiv-structures-from-occurrence
             x86-term ;; bound-x86-term
             mfc state))
           ((when (not equiv-x86-term))
            x86-term))
        equiv-x86-term)

    (b* ((outer-fn (car x86-term))
         ((when (and (not (equal outer-fn 'MV-NTH))
                     (not (equal outer-fn 'WM-LOW-64))
                     ;; (not (equal outer-fn '!FLGI))
                     (not (and (equal outer-fn 'XW)
                               (equal (second x86-term) '':MEM)))))
          ;; (cw "~%~p0: Unexpected x86-term encountered:~p1~%" thm-name x86-term)
          x86-term))
      (cond ((equal outer-fn 'MV-NTH)
             ;; We expect x86-term to be a function related to page
             ;; traversals.
             (b* ((mv-nth-index (second x86-term))
                  (inner-fn-call (third x86-term))
                  (inner-fn (first inner-fn-call))
                  ((when (if (equal mv-nth-index ''2)
                             (not (member-p inner-fn
                                            '(IA32E-LA-TO-PA-PAGE-TABLE
                                              IA32E-LA-TO-PA-PAGE-DIRECTORY
                                              IA32E-LA-TO-PA-PAGE-DIR-PTR-TABLE
                                              IA32E-LA-TO-PA-PML4-TABLE
                                              IA32E-LA-TO-PA
                                              LAS-TO-PAS
                                              PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE
                                              RM08
                                              RB
                                              GET-PREFIXES
                                              RB-ALT
                                              GET-PREFIXES-ALT)))
                           (if (equal mv-nth-index ''1)
                               (not (member-p inner-fn '(WM08 WB)))
                             t)))
                   ;; (cw "~%~p0: Unexpected mv-nth x86-term encountered:~p1~%" thm-name x86-term)
                   x86-term)
                  (sub-x86
                   (if (equal inner-fn 'PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE)
                       ;; x86 is the next to last argument for these functions.
                       (first (last (butlast inner-fn-call 1)))
                     (first (last inner-fn-call)))))
               sub-x86))
            ((or (equal outer-fn 'WM-LOW-64)
                 (equal outer-fn 'XW)
                 ;; (equal outer-fn '!FLGI)
                 )
             ;; We expect x86-term to be of the form (wm-low-64 index
             ;; val sub-x86) or (xw :mem val index).
             (b* ((sub-x86 (first (last x86-term))))
               sub-x86))))))

(defun find-an-xlate-equiv-x86 (thm-name bound-x86-term free-x86-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm-name state))
  ;; bind-free for an x86 in xlate-equiv-structures: should check just
  ;; for the page traversal functions and wm-low-64.
  (declare (xargs :mode :program))
  (b* ((equiv-x86 (find-an-xlate-equiv-x86-aux thm-name bound-x86-term mfc state)))
    `((,free-x86-var . ,equiv-x86))))

(defun find-equiv-x86-for-components-aux (var calls)
  (if (endp calls)
      nil
    (b* ((call (car calls))
         (var-val (third call)))
      (append `((,var . ,var-val))
              (find-equiv-x86-for-components-aux var (cdr calls))))))

(defun find-equiv-x86-for-components (var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-of-fns-lst
               '(ALL-MEM-EXCEPT-PAGING-STRUCTURES-EQUAL)
               (acl2::mfc-clause mfc))))
    (find-equiv-x86-for-components-aux var calls)))

(define all-mem-except-paging-structures-equal
  (x86-1 x86-2)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t

  :prepwork
  ((define all-mem-except-paging-structures-equal-aux
     (i paging-qword-addresses x86-1 x86-2)
     :parents (all-mem-except-paging-structures-equal)
     :guard (and (natp i)
                 (<= i *mem-size-in-bytes*)
                 (mult-8-qword-paddr-listp paging-qword-addresses)
                 (x86p x86-1)
                 (x86p x86-2))
     :non-executable t
     :enabled t

     (if (zp i)

         (if (disjoint-p
              (list i)
              (open-qword-paddr-list paging-qword-addresses))
             ;; i does not point to paging data, hence the contents of i
             ;; must be exactly equal.

             (equal (xr :mem i x86-1) (xr :mem i x86-2))

           t)

       (if (disjoint-p
            (list (1- i))
            (open-qword-paddr-list paging-qword-addresses))

           ;; i does not point to paging data, hence the contents of i
           ;; must be exactly equal.
           (and (equal (xr :mem (1- i) x86-1) (xr :mem (1- i) x86-2))
                (all-mem-except-paging-structures-equal-aux
                 (1- i) paging-qword-addresses x86-1 x86-2))

         ;; i points to paging data, and hence we can't expect its
         ;; contents to be exactly equal. This case is dealt with by the
         ;; function xlate-equiv-entries-at-qword-addresses?.
         (all-mem-except-paging-structures-equal-aux
          (1- i) paging-qword-addresses x86-1 x86-2)))

     ///

     (defthm all-mem-except-paging-structures-equal-aux-and-xr-mem-from-rest-of-memory
       (implies (and (all-mem-except-paging-structures-equal-aux i addrs x86-1 x86-2)
                     (disjoint-p (list j) (open-qword-paddr-list addrs))
                     (natp i)
                     (natp j)
                     (< j i))
                (equal (xr :mem j x86-1) (xr :mem j x86-2))))

     (defthm all-mem-except-paging-structures-equal-aux-and-rm-low-32-from-rest-of-memory
       (implies (and (all-mem-except-paging-structures-equal-aux i addrs x86-1 x86-2)
                     (disjoint-p (addr-range 4 j) (open-qword-paddr-list addrs))
                     (natp i)
                     (natp j)
                     (< (+ 3 j) i)
                     (not (app-view x86-1))
                     (not (app-view x86-2)))
                (equal (rm-low-32 j x86-1) (rm-low-32 j x86-2)))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d* (rm-low-32 disjoint-p) (force (force))))))

     (defthm all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory
       (implies (and (all-mem-except-paging-structures-equal-aux i addrs x86-1 x86-2)
                     (disjoint-p (addr-range 8 j) (open-qword-paddr-list addrs))
                     (natp i)
                     (natp j)
                     (< (+ 7 j) i)
                     (not (app-view x86-1))
                     (not (app-view x86-2)))
                (equal (rm-low-64 j x86-1) (rm-low-64 j x86-2)))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d* (rm-low-64 disjoint-p) (force (force))))))

     (defthm all-mem-except-paging-structures-equal-aux-is-reflexive
       (all-mem-except-paging-structures-equal-aux i addrs x x))

     (defthm all-mem-except-paging-structures-equal-aux-is-commutative
       (implies (all-mem-except-paging-structures-equal-aux i addrs x y)
                (all-mem-except-paging-structures-equal-aux i addrs y x)))

     (defthm all-mem-except-paging-structures-equal-aux-is-transitive
       (implies (and (all-mem-except-paging-structures-equal-aux i addrs x y)
                     (all-mem-except-paging-structures-equal-aux i addrs y z))
                (all-mem-except-paging-structures-equal-aux i addrs x z)))

     (defthm all-mem-except-paging-structures-equal-aux-and-xw-1
       (implies (not (equal fld :mem))
                (equal (all-mem-except-paging-structures-equal-aux i addrs (xw fld index val x) y)
                       (all-mem-except-paging-structures-equal-aux i addrs x y))))

     (defthm all-mem-except-paging-structures-equal-aux-and-xw-2
       (implies (not (equal fld :mem))
                (equal (all-mem-except-paging-structures-equal-aux i addrs x (xw fld index val y))
                       (all-mem-except-paging-structures-equal-aux i addrs x y))))

     (defthm all-mem-except-paging-structures-equal-aux-and-xw-mem
       (implies (all-mem-except-paging-structures-equal-aux i addrs x y)
                (all-mem-except-paging-structures-equal-aux
                 i addrs
                 (xw :mem index val x)
                 (xw :mem index val y))))

     (defthm xr-mem-wm-low-64
       (implies (not (member-p index (addr-range 8 addr)))
                (equal (xr :mem index (wm-low-64 addr val x86))
                       (xr :mem index x86)))
       :hints (("Goal" :in-theory (e/d* (wm-low-64
                                         wm-low-32
                                         ifix)
                                        (force (force))))))

     (local
      (defthm all-mem-except-paging-structures-equal-aux-and-wm-low-64-paging-entry-helper
        (implies (and (member-p index a)
                      (disjoint-p (list i) (open-qword-paddr-list a)))
                 (equal (member-p i (addr-range 8 index))
                        nil))
        :hints (("Goal" :in-theory (e/d* (member-p disjoint-p)
                                         ())))))

     (defthm all-mem-except-paging-structures-equal-aux-and-wm-low-64-paging-entry
       (implies (member-p index addrs)
                (equal (all-mem-except-paging-structures-equal-aux i addrs (wm-low-64 index val x) y)
                       (all-mem-except-paging-structures-equal-aux i addrs x y)))
       :hints (("Goal" :in-theory (e/d* (member-p) ()))))

     (defthm all-mem-except-paging-structures-equal-aux-and-wm-low-64
       (implies (and (all-mem-except-paging-structures-equal-aux i addrs x y)
                     (not (xr :app-view nil x))
                     (not (xr :app-view nil y)))
                (all-mem-except-paging-structures-equal-aux
                 i addrs
                 (wm-low-64 index val x)
                 (wm-low-64 index val y)))
       :hints (("Goal" :do-not-induct t
                :in-theory (e/d* (wm-low-64 wm-low-32) ()))))

     (defthm all-mem-except-paging-structures-equal-aux-and-xw-mem-commute-writes
       (implies (not (equal index-1 index-2))
                (all-mem-except-paging-structures-equal-aux
                 i addrs
                 (xw :mem index-1 val-1 (xw :mem index-2 val-2 x))
                 (xw :mem index-2 val-2 (xw :mem index-1 val-1 x)))))))

  (if (equal (app-view x86-1) nil)

      (if (equal (app-view x86-2) nil)

          (and (equal (gather-all-paging-structure-qword-addresses x86-1)
                      (gather-all-paging-structure-qword-addresses x86-2))
               (all-mem-except-paging-structures-equal-aux
                *mem-size-in-bytes*
                (gather-all-paging-structure-qword-addresses x86-1)
                x86-1 x86-2))

        nil)

    (equal (app-view x86-2) (app-view x86-1)))

  ///

  (defequiv all-mem-except-paging-structures-equal)

  (defthm all-mem-except-paging-structures-equal-and-xr-mem-from-rest-of-memory
    (implies (and (all-mem-except-paging-structures-equal x86-1 x86-2)
                  (disjoint-p
                   (list j)
                   (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86-1)))
                  (natp j)
                  (< j *mem-size-in-bytes*)
                  (not (app-view x86-1)))
             (equal (xr :mem j x86-1) (xr :mem j x86-2)))
    :hints (("Goal" :in-theory (e/d* (all-mem-except-paging-structures-equal) ()))))

  (defthm all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory
    (implies (and (all-mem-except-paging-structures-equal x86-1 x86-2)
                  (disjoint-p (addr-range 8 j)
                              (open-qword-paddr-list
                               (gather-all-paging-structure-qword-addresses x86-1)))
                  (natp j)
                  (< (+ 7 j) *mem-size-in-bytes*))
             (equal (rm-low-64 j x86-1) (rm-low-64 j x86-2)))
    :hints (("Goal"
             :use ((:instance all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory
                              (i *mem-size-in-bytes*)
                              (j j)
                              (addrs (gather-all-paging-structure-qword-addresses x86-1))))
             :in-theory (e/d* (all-mem-except-paging-structures-equal)
                              (all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)))))

  (defthm all-mem-except-paging-structures-equal-and-xw-1
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (all-mem-except-paging-structures-equal (xw fld index val x) y)
                    (all-mem-except-paging-structures-equal (double-rewrite x) y)))
    :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr)
                                     (all-mem-except-paging-structures-equal-aux)))))

  (defthm all-mem-except-paging-structures-equal-and-xw-2
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (all-mem-except-paging-structures-equal x (xw fld index val y))
                    (all-mem-except-paging-structures-equal x (double-rewrite y))))
    :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr)
                                     ()))))

  (defthm all-mem-except-paging-structures-equal-and-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :app-view)))
             (equal (all-mem-except-paging-structures-equal (xw fld index val x) (xw fld index val y))
                    (all-mem-except-paging-structures-equal x y)))
    :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr)
                                     ()))))

  (defthm all-mem-except-paging-structures-equal-and-xw-mem-except-paging-structure
    (implies (and (bind-free (find-equiv-x86-for-components y mfc state))
                  (all-mem-except-paging-structures-equal x y)
                  (physical-address-p index)
                  (disjoint-p
                   (list index)
                   (open-qword-paddr-list (gather-all-paging-structure-qword-addresses y))))
             (all-mem-except-paging-structures-equal (xw :mem index val x)
                                                     (xw :mem index val y)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm all-mem-except-paging-structures-equal-and-wm-low-64-paging-entry
    (implies (and (member-p index (gather-all-paging-structure-qword-addresses x))
                  (equal (gather-all-paging-structure-qword-addresses (wm-low-64 index val x))
                         (gather-all-paging-structure-qword-addresses x)))
             (equal (all-mem-except-paging-structures-equal (wm-low-64 index val x) y)
                    (all-mem-except-paging-structures-equal (double-rewrite x) y)))
    :hints (("Goal" :in-theory (e/d* () (all-mem-except-paging-structures-equal-aux)))))

  (defthm all-mem-except-paging-structures-equal-and-wm-low-64-entry-addr
    (implies (and (xlate-equiv-entries (double-rewrite entry)
                                       (rm-low-64 entry-addr x86))
                  (member-p entry-addr (gather-all-paging-structure-qword-addresses x86))
                  (unsigned-byte-p 64 entry))
             (all-mem-except-paging-structures-equal
              (wm-low-64 entry-addr entry x86)
              (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (all-mem-except-paging-structures-equal-aux)
                                     ()))))

  (defthm all-mem-except-paging-structures-equal-and-wm-low-64-except-paging-structure
    (implies (and
              (bind-free (find-equiv-x86-for-components y mfc state))
              (all-mem-except-paging-structures-equal x y)
              (disjoint-p
               (addr-range 8 index)
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses y))))
             (all-mem-except-paging-structures-equal (wm-low-64 index val x)
                                                     (wm-low-64 index val y)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm all-mem-except-paging-structures-equal-and-xw-mem-commute-writes
    (implies (not (equal index-1 index-2))
             (all-mem-except-paging-structures-equal
              (xw :mem index-1 val-1 (xw :mem index-2 val-2 x))
              (xw :mem index-2 val-2 (xw :mem index-1 val-1 x))))
    :hints (("Goal" :in-theory (e/d* () (force (force)))))))

(define xlate-equiv-structures (x86-1 x86-2)
  :guard (and (x86p x86-1)
              (x86p x86-2))
  :non-executable t
  :long "<p>Two x86 states are @('xlate-equiv-structures') if their
  paging structures are equal, modulo the accessed and dirty bits (See
  @(see xlate-equiv-entries)).</p>"

  (if (and (equal (xr :app-view nil x86-1) nil)
           (equal (xr :app-view nil x86-2) nil))

      (let* ((paging-qword-addresses-1
              (gather-all-paging-structure-qword-addresses x86-1))
             (paging-qword-addresses-2
              (gather-all-paging-structure-qword-addresses x86-2)))

        (and (equal (segment-selectorBits->rpl (seg-visiblei *cs* x86-1))
                    (segment-selectorBits->rpl (seg-visiblei *cs* x86-2)))
             (equal (cr0Bits->wp (n32 (ctri *cr0* x86-1)))
                    (cr0Bits->wp (n32 (ctri *cr0* x86-2))))
             (equal (cr3Bits->pdb (ctri *cr3* x86-1))
                    (cr3Bits->pdb (ctri *cr3* x86-2)))
             (equal (cr4Bits->smep (loghead 22 (ctri *cr4* x86-1)))
                    (cr4Bits->smep (loghead 22 (ctri *cr4* x86-2))))
             (equal (cr4Bits->smap (loghead 22 (ctri *cr4* x86-1)))
                    (cr4Bits->smap (loghead 22 (ctri *cr4* x86-2))))
             (equal (ia32_eferBits->nxe (n12 (msri *ia32_efer-idx* x86-1)))
                    (ia32_eferBits->nxe (n12 (msri *ia32_efer-idx* x86-2))))
             (equal (rflagsBits->ac (rflags x86-1))
                    (rflagsBits->ac (rflags x86-2)))
             (equal (xr :marking-view nil x86-1)
                    (xr :marking-view nil x86-2))
             (equal paging-qword-addresses-1 paging-qword-addresses-2)
             (xlate-equiv-entries-at-qword-addresses
              paging-qword-addresses-1 paging-qword-addresses-2 x86-1 x86-2)))

    (and (equal (xr :app-view nil x86-2)
                (xr :app-view nil x86-1))))

  ///

  (local
   (defthm xlate-equiv-structures-is-reflexive
     (xlate-equiv-structures x x)
     :hints (("Goal"
              :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses-reflexive))
              :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses-reflexive
                (a (gather-all-paging-structure-qword-addresses x))
                (x x)))))))

  (local
   (defthm xlate-equiv-structures-is-commutative
     (implies (xlate-equiv-structures x y)
              (xlate-equiv-structures y x))
     :hints (("Goal"
              :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses-commutative))
              :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses-commutative
                (a (gather-all-paging-structure-qword-addresses x))
                (b (gather-all-paging-structure-qword-addresses y))
                (x x)
                (y y)))))))

  (local
   (defthm xlate-equiv-structures-is-transitive
     (implies (and (xlate-equiv-structures x y)
                   (xlate-equiv-structures y z))
              (xlate-equiv-structures x z))
     :hints (("Goal"
              :in-theory (e/d* () (xlate-equiv-entries-at-qword-addresses-transitive))
              :use
              ((:instance
                xlate-equiv-entries-at-qword-addresses-transitive
                (a (gather-all-paging-structure-qword-addresses x))
                (b (gather-all-paging-structure-qword-addresses y))
                (c (gather-all-paging-structure-qword-addresses z))))))))

  (defequiv xlate-equiv-structures
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-structures)))))

  (defthm xlate-equiv-structures-and-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :seg-visible))
                  (not (equal fld :msr))
                  (not (equal fld :ctr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view)))
             (xlate-equiv-structures (xw fld index val x86)
                                     (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr)
                                     ()))))

  (defthm xlate-equiv-structures-and-app-view-cong
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (xr :app-view nil x86-1)
                    (xr :app-view nil x86-2)))
    :rule-classes :congruence))

(define xlate-equiv-memory (x86-1 x86-2)
  :non-executable t
  :guard (and (x86p x86-1) (x86p x86-2))

  (if (and (equal (xr :app-view nil x86-1) nil)
           (equal (xr :app-view nil x86-2) nil)
           (64-bit-modep x86-1)
           (64-bit-modep x86-2))

      (and (xlate-equiv-structures x86-1 x86-2)
           (all-mem-except-paging-structures-equal x86-1 x86-2))

    (equal x86-1 x86-2))
  ///
  (defequiv xlate-equiv-memory)

  (defthm xlate-equiv-memory-refines-xlate-equiv-structures
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-structures x86-1 x86-2))
    :rule-classes :refinement)

  (defthm xlate-equiv-memory-refines-all-mem-except-paging-structures-equal
    (implies (xlate-equiv-memory x86-1 x86-2)
             (all-mem-except-paging-structures-equal x86-1 x86-2))
    :rule-classes :refinement)

  (defcong xlate-equiv-memory equal (64-bit-modep x86) 1))

;; =====================================================================

;; gather-all-paging-structure-qword-addresses and wm-low-64, with
;; equiv x86s:

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
  (implies
   (and
    (bind-free
     (find-an-xlate-equiv-x86
      'gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
      x86-1 'x86-2
      mfc state)
     (x86-2))
    (xlate-equiv-structures (double-rewrite x86-1)
                            (double-rewrite x86-2))
    (equal (app-view (double-rewrite x86-1)) nil)
    (disjoint-p (addr-range 8 index)
                (open-qword-paddr-list
                 (gather-all-paging-structure-qword-addresses x86-1))))
   (equal (gather-all-paging-structure-qword-addresses
           (wm-low-64 index val x86-1))
          (gather-all-paging-structure-qword-addresses x86-2)))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
                            (x86 x86-1)))
           :in-theory (e/d* (xlate-equiv-structures)
                            (open-qword-paddr-list
                             gather-all-paging-structure-qword-addresses-wm-low-64-disjoint
                             gather-all-paging-structure-qword-addresses
                             force (force))))))

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
  (implies (and (xlate-equiv-structures x86 (double-rewrite x86-equiv))
                (equal (app-view x86) nil)
                (member-p index (gather-all-paging-structure-qword-addresses x86))
                (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                (unsigned-byte-p 64 val))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures)
                                   (gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr))
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86-equiv))
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86))))))

;; ======================================================================

;; xlate-equiv-structures and write(s) to physical memory:

(defthm xlate-equiv-structures-and-xw-mem-disjoint
  (implies (and (disjoint-p
                 (list index)
                 (open-qword-paddr-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (xlate-equiv-structures (xw :mem index val x86) (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ()))))

(defthm xlate-equiv-structures-and-wm-low-64-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'xlate-equiv-structures-and-wm-low-64-disjoint x86-2 'x86-1 mfc state)
             (x86-1))
            (xlate-equiv-structures x86-1 (double-rewrite x86-2))
            (disjoint-p (addr-range 8 index)
                        (open-qword-paddr-list
                         (gather-all-paging-structure-qword-addresses x86-1))))
           (xlate-equiv-structures (wm-low-64 index val x86-2) x86-1))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ()))))

(local
 (defthm dumb-disjointness-rule
   (implies (and (disjoint-p xs y) (consp xs))
            (disjoint-p (list (car xs)) y))
   :hints (("Goal" :in-theory (e/d* (disjoint-p member-p) ())))))

(defthm xlate-equiv-structures-and-write-to-physical-memory-disjoint
  (implies
   (and
    (bind-free
     (find-an-xlate-equiv-x86
      'xlate-equiv-structures-and-write-to-physical-memory-disjoint
      x86-2 'x86-1 mfc state)
     (x86-1))
    (xlate-equiv-structures x86-1 (double-rewrite x86-2))
    (disjoint-p
     p-addrs
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses x86-1)))
    (physical-address-listp p-addrs))
   (xlate-equiv-structures (write-to-physical-memory p-addrs val x86-2) x86-1))
  :hints (("Goal"
           :induct (cons (write-to-physical-memory p-addrs val x86-2)
                         (physical-address-listp p-addrs))
           :in-theory (e/d* (write-to-physical-memory xlate-equiv-structures)
                            ()))))

(defthm xlate-equiv-structures-and-wm-low-64-entry-addr
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'xlate-equiv-structures-and-wm-low-64-entry-addr
              x86-equiv 'x86 mfc state)
             (x86))
            (xlate-equiv-structures x86 (double-rewrite x86-equiv))
            (xlate-equiv-entries (double-rewrite val)
                                 (rm-low-64 index x86))
            (member-p index (gather-all-paging-structure-qword-addresses x86))
            (unsigned-byte-p 64 val))
           (xlate-equiv-structures (wm-low-64 index val x86-equiv) x86))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ()))))

;; ======================================================================

;; Some misc. lemmas:

;; (defthmd xlate-equiv-entries-open
;;   (implies (and (xlate-equiv-entries e-1 e-2)
;;                 (unsigned-byte-p 64 e-1)
;;                 (unsigned-byte-p 64 e-2))
;;            (and (equal (loghead 5 e-1) (loghead 5 e-2))
;;                 (equal (logtail 7 e-1) (logtail 7 e-2))))
;;   :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries) ()))))

(defthm xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (equal (app-view x86) nil)
                ;; (equal (marking-view x86) t)
                (xlate-equiv-structures (double-rewrite x86) (double-rewrite x86-equiv)))
           (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86-equiv))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures xlate-equiv-structures)
                                   ()))))

(defthmd xlate-equiv-structures-and-xlate-equiv-entries
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p index (gather-all-paging-structure-qword-addresses x86-1))
                ;; (equal (marking-view x86-1) t)
                (equal (app-view x86-1) nil))
           (xlate-equiv-entries (rm-low-64 index x86-1) (rm-low-64 index x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures xlate-equiv-structures)
                                   ()))))

;; ======================================================================
