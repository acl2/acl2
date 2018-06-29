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

(include-book "basics" :ttags :all :dir :proof-utils)
(include-book "disjoint" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;; ======================================================================

(defsection general-memory-utils
  :parents (proof-utilities)
  )

(local (xdoc::set-default-parents general-memory-utils))

;; ===================================================================

;; Some lemmas for constructing a number from its constituent parts:

(defthm combining-logior-of-loghead-and-ash-logtail
  (implies (and (natp x)
                (natp n))
           (equal (logior (loghead n x)
                          (ash (logtail n x) n))
                  x))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs)
                                   ()))))

(defthmd combining-logior-of-loghead-and-ash-loghead-logtail-1
  (implies (and (natp n)
                (natp m))
           (equal (loghead m (logtail n x))
                  (ash (loghead (+ m n) x) (- n))))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    zip)
                                   ()))))

(defthmd combining-logior-of-loghead-and-ash-loghead-logtail-2
  (implies (and (natp n)
                (natp m))
           (equal (loghead n x)
                  (loghead n (loghead (+ m n) x))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (ihsext-recursive-redefs
                                    ihsext-inductions)))))


(defthm combining-logior-of-loghead-and-ash-loghead-logtail
  (implies (and (natp n)
                (natp m))
           (equal (logior (loghead n x)
                          (ash (loghead m (logtail n x)) n))
                  (loghead (+ m n) x)))
  :hints (("Goal"
           :use ((:instance combining-logior-of-loghead-and-ash-loghead-logtail-2))
           :in-theory (e/d* (combining-logior-of-loghead-and-ash-loghead-logtail-1)
                            (bitops::logtail-of-loghead
                             bitops::loghead-of-loghead-1)))))

(defthm combining-logior-of-loghead-logtail-and-ash-logtail
  (implies (and (natp n)
                (natp m)
                (equal m+n (+ m n))
                (integerp x))
           (equal (logior (loghead n (logtail m x))
                          (ash (logtail m+n x) n))
                  (logtail m x)))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs)
                                   ()))))

(defthm combining-logior-of-loghead-logtail-and-ash-loghead-logtail
  (implies (and (natp m)
                (natp n)
                (natp o)
                (equal m+n (+ m n)))
           (equal (logior (loghead n (logtail m x))
                          (ash (loghead o (logtail m+n x)) n))
                  (loghead (+ n o) (logtail m x))))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    zip)
                                   ()))))


(defthm greater-logbitp-of-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (natp m)
                (< n m))
           (equal (logbitp m x) nil))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    unsigned-byte-p)
                                   ())))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (< x (expt 2 m))
                                         (natp x)
                                         (natp m))
                                    (equal (logbitp m x) nil)))))

(defthm loghead-of-non-integerp
  (implies (not (integerp x))
           (equal (loghead n x) 0))
  :hints (("Goal" :in-theory (e/d* (loghead mod) ()))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm ash-and-plus
    (implies (posp n)
             (equal (+ 8 (ash (+ -1 n) 3))
                    (ash n 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ()))))

  (defthm ash-and-minus
    (implies (posp n)
             (equal (+ -8 (ash n 3))
                    (ash (+ -1 n) 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ()))))  

  (defthm ash-n-3-bound
    (implies (and (integerp n)
                  (< 0 n))
             (<= 8 (ash n 3)))
    :hints (("Goal" :in-theory (e/d* (ash) ())))
    :rule-classes :linear)

  (defthm ash-separate-out
    (implies (natp n)
             (equal (ash (+ 1 n) 3)
                    (+ 8 (ash n 3))))
    :hints (("Goal" :in-theory (e/d* (ash) ())))))

;; ======================================================================

;; Lemmas about combine-bytes and part-select:

(defthmd logtail-n>=8-of-byte
   (implies (and (unsigned-byte-p 8 byte)
                 (natp n)
                 (<= 8 n))
            (equal (logtail n byte) 0))
   :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                     bitops::ihsext-inductions)
                                    ()))))

(defthmd loghead-n->=8-of-a-byte
  (implies (and (unsigned-byte-p 8 byte)
                (natp n)
                (<= 8 n))
           (equal (loghead n byte) byte))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                    bitops::ihsext-inductions)
                                   ()))))

(local (in-theory (e/d* (logtail-n>=8-of-byte
                         loghead-n->=8-of-a-byte)
                        ())))

(defthm break-loghead-and-ash
  (implies (natp i)
           (equal (loghead (+ i j) (ash x i))
                  (ash (loghead j x) i)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(local
 (defthm combine-bytes-take-and-loghead-helper
   (implies (natp n)
            (equal (loghead (ash n 3) (ash x 8))
                   (ash (loghead (ash (+ -1 n) 3) x) 8)))
   :hints (("Goal" :use ((:instance ash-and-plus (n n)))
            :in-theory (e/d* () (ash-and-plus))))))


(defthm combine-bytes-take-and-loghead
  (implies (and (natp num)
                (byte-listp xs))
           (equal (combine-bytes (take num xs))
                  (loghead (ash num 3)
                           (combine-bytes xs)))))

(defthm combine-bytes-nthcdr-and-logtail
  (implies (and (natp i)
                (byte-listp xs))
           (equal (combine-bytes (nthcdr i xs))
                  (logtail (ash i 3) (combine-bytes xs)))))

(defthmd relating-combine-bytes-and-part-select
  (implies (and
            (natp i) (natp num)
            (byte-listp bytes))
           (equal (combine-bytes (take num (nthcdr i bytes)))
                  (part-select (combine-bytes bytes)
                               :low   (ash i 3)
                               :width (ash num 3))
                  ;; (loghead (ash n 3)
                  ;;          (logtail (ash (+ addr (- prog-addr)) 3)
                  ;;                   (combine-n-bytes 0 (len bytes) bytes)))
                  )))

;; ======================================================================

;; Lemmas about canonical-address-p:

;; Relating rip and canonical-address-p: We don't want the rule
;; rip-is-i48p to be active anymore. Anything to do with rip and !rip
;; should now be reasoned about in terms of canonical-address-p, even
;; though canonical-address-p and i48p are the same, really.

(defthm canonical-address-p-rip
  (implies (x86p x86)
           (canonical-address-p (xr :rip index x86)))
  :rule-classes (:type-prescription :rewrite))

(defthm rip-is-integerp
  (implies (x86p x86)
           (integerp (xr :rip index x86)))
  :rule-classes :type-prescription)

(defthm x86p-!rip-when-val-is-canonical-address-p
  (implies (forced-and (x86p x86)
                       (canonical-address-p v))
           (x86p (xw :rip index v x86)))
  :hints (("Goal" :in-theory (enable ripp))))

(in-theory (disable (:type-prescription rip-is-i48p)))

(defthm canonical-address-p-to-integerp-thm
  (implies (canonical-address-p x)
           (integerp x))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p) ())))
  :rule-classes :forward-chaining)

(defthm canonical-address-p-limits-thm-0
  ;; addr <= (+ k addr) < (+ i addr)
  ;; i is positive, k is positive, k < i
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p addr)
                (< k i)
                (<= 0 k)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-1
  ;; (+ -i addr) < (+ -k addr) < addr
  ;; i is negative, k is negative, k > i
  (implies (and (< k 0)
                (canonical-address-p (+ i addr))
                (< i 0)
                (< i k)
                (canonical-address-p addr)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-2
  ;; (+ i addr) < (+ k addr) < (+ j addr)
  ;; i < k < j
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p (+ j addr))
                (< i k)
                (< k j)
                (integerp addr)
                (integerp k))
           (canonical-address-p (+ k addr))))

(defthm canonical-address-p-limits-thm-3
  ;; (+ -i addr) <= addr <= (+ j addr)
  (implies (and (canonical-address-p (+ j addr))
                (canonical-address-p (+ (- i) addr))
                (natp i)
                (natp j)
                (integerp addr))
           (canonical-address-p addr))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm canonical-address-p-limits-thm-4
  ;; addr <= (+ -j i addr) <= (addr + i)
  (implies (and (canonical-address-p (+ i addr))
                (canonical-address-p addr)
                (< j 0)
                (<= (- i) j)
                (natp i)
                (integerp j))
           (canonical-address-p (+ j (+ i addr))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:rewrite :forward-chaining))

(encapsulate
  ()

  ;; The following rules come in useful when we know that a canonical
  ;; memory address is stored in a register.  These rules establish
  ;; that the value being written to a register is signed-byte-p 64, a fact we need
  ;; to know to relieve the hypotheses of rules like x86p-!rgfi.

  (defthm canonical-address-p-and-signed-byte-p-64-limits-0
    (implies (and (syntaxp (and (consp x)
                                (eq (car x) 'rgfi)))
                  (canonical-address-p x))
             (signed-byte-p 64 x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

  (defthm canonical-address-p-and-signed-byte-p-64p-limits-1
    (implies (and (syntaxp (and (consp x)
                                (eq (car x) 'rgfi)))
                  (canonical-address-p (+ a x)))
             (signed-byte-p 64 (+ a x)))
    :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

  (defthm canonical-address-p-+-signed-byte-p-16-is-signed-byte-p-64
    (implies (and (canonical-address-p y)
                  (signed-byte-p 16 x))
             (signed-byte-p 64 (+ x y)))
    :hints (("Goal" :in-theory (e/d (canonical-address-p) ()))))

  (local (include-book "centaur/gl/gl" :dir :system))

  (local
   (def-gl-thm canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64-helper
     :hyp (and (canonical-address-p y)
               (signed-byte-p 16 x))
     :concl (equal (n64-to-i64
                    (part-select
                     (+ x (part-select
                           y
                           :low 0
                           :width 64))
                     :low 0 :width 64))
                   (+ x y))
     :g-bindings
     `((x   (:g-number ,(gl-int 0 2 64)))
       (y   (:g-number ,(gl-int 1 2 64))))))

  (defthm canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64
    (implies (and (canonical-address-p y)
                  (signed-byte-p 16 x))
             (equal (n64-to-i64
                     (part-select
                      (+ x (part-select
                            y
                            :low 0
                            :width 64))
                      :low 0 :width 64))
                    (+ x y)))
    :hints (("Goal" :use
             canonical-address-p-+-signed-byte-p-16-with-loghead-and-n64-to-i64-helper)))

  (defthm loghead-64-n64-to-i64-canonical-address
    (implies (canonical-address-p x)
             (equal (n64-to-i64 (loghead 64 x))
                    x))
    :hints (("Goal" :in-theory (e/d (canonical-address-p n64-to-i64) ()))))

  (defthm n64-to-i64-logead-64-x
    (implies (signed-byte-p 64 x)
             (equal (n64-to-i64 (loghead 64 x))
                    x))
    :hints (("Goal" :in-theory (e/d (canonical-address-p n64-to-i64) ())))))

;; ======================================================================

;; Some lemmas to reason about lists:

(defthm append-x-nil-is-x
  (equal (append nil x) x))

(defthm cdr-append-is-append-cdr
  (implies (consp x)
           (equal (cdr (append x y))
                  (append (cdr x) y))))

(defthm car-of-append
  (equal (car (append x y))
         (if (consp x) (car x) (car y))))

(defthm consp-append
  (implies (consp x)
           (consp (append x y)))
  :rule-classes :type-prescription)

(local
 (defthm append-equal
   (implies (equal (append x a) (append x b))
            (equal a b))
   :rule-classes :forward-chaining))

(local
 (defthm append-3
   (equal (append (append x y) z)
          (append x y z))))

(defthm canonical-address-listp-append
  (implies (and (canonical-address-listp x)
                (canonical-address-listp y))
           (canonical-address-listp (append x y)))
  :rule-classes (:rewrite :type-prescription))

(define addr-range (count addr)
  :guard (natp count)

  :enabled t

  (if (zp count)
      nil
    (cons (ifix addr)
          (addr-range (1- count) (1+ (ifix addr)))))

  ///

  (defthm neg-addr-range=nil
    (implies (negp i) (equal (addr-range i n) nil)))

  (defthm true-listp-addr-range
    (true-listp (addr-range count addr))
    :rule-classes :type-prescription)

  (defthm addr-range-1
    (equal (addr-range 1 x)
           (list (ifix x)))
    :hints (("Goal" :expand (addr-range 1 x))))

  (defthm len-of-addr-range
    (implies (natp n)
             (equal (len (addr-range n val)) n))
    :hints (("Goal" :in-theory (e/d (addr-range) ()))))

  (defthm canonical-address-listp-addr-range
    (implies (and (canonical-address-p lin-addr)
                  (canonical-address-p (+ -1 n lin-addr)))
             (canonical-address-listp (addr-range n lin-addr)))
    :hints (("Goal" :in-theory (e/d (addr-range) ()))))

  (defthm physical-address-listp-addr-range
    (implies (and (physical-address-p lin-addr)
                  (physical-address-p (+ -1 n lin-addr)))
             (physical-address-listp (addr-range n lin-addr)))
    :hints (("Goal" :in-theory (e/d (addr-range) ()))))

  (defthm member-p-addr-range
    (implies (and (<= prog-addr addr)
                  (< addr (+ n prog-addr))
                  (integerp n)
                  (integerp addr)
                  (integerp prog-addr))
             (equal (member-p addr (addr-range n prog-addr))
                    t)))

  (defthm member-p-addr-range-from-member-p-addr-range
    (implies (and (member-p x (addr-range j y))
                  (integerp l)
                  (< j l))
             (equal (member-p x (addr-range l y))
                    t)))

  (defthm not-member-p-addr-range
    (implies (and (or (< addr prog-addr)
                      (<= (+ n prog-addr) addr))
                  (integerp prog-addr))
             (equal (member-p addr (addr-range n prog-addr))
                    nil)))

  (defthm not-member-p-addr-range-from-not-member-p-addr-range
    (implies (and (not (member-p x (addr-range j y)))
                  (integerp j)
                  (<= l j))
             (equal (member-p x (addr-range l y))
                    nil)))

  (defthm subset-p-two-addr-ranges
    (implies (and (integerp x)
                  (integerp y)
                  (<= y x)
                  (<= (+ i x) (+ j y))
                  (integerp j))
             (subset-p (addr-range i x)
                       (addr-range j y)))
    :hints (("Goal" :in-theory (e/d (subset-p) nil))))

  (defthm not-disjoint-p-two-addr-ranges-thm
    (implies (and (integerp x)
                  (integerp y)
                  (integerp i)
                  (integerp j)
                  (<= x y)
                  (< y (+ i x))
                  (<= (+ i x) (+ j y)))
             (equal (disjoint-p (addr-range i x)
                                (addr-range j y))
                    nil))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

  (defthm disjoint-p-two-addr-ranges-thm-0
    (implies (and (integerp x)
                  (integerp y)
                  (integerp j)
                  (< 0 j)
                  (<= (+ i x) y))
             (disjoint-p (addr-range i x)
                         (addr-range j y)))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

  (defthm disjoint-p-two-addr-ranges-thm-1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp j)
                  (< 0 j)
                  (<= (+ j y) x))
             (disjoint-p (addr-range i x)
                         (addr-range j y)))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

  ;; (defthm disjoint-p-two-addr-ranges-thm-2
  ;;   (implies (and (disjoint-p (addr-range i x)
  ;;                             (addr-range j y))
  ;;                 (integerp i)
  ;;                 (integerp j)
  ;;                 (<= k i)
  ;;                 (<= l j))
  ;;            (disjoint-p (addr-range k x)
  ;;                        (addr-range l y)))
  ;;   :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

  (defthm disjoint-p-two-addr-ranges-thm-2
    (implies (and (disjoint-p (addr-range i x)  (addr-range j y))
                  (subset-p   (addr-range ia a) (addr-range i x))
                  (subset-p   (addr-range jb b) (addr-range j y)))
             (disjoint-p (addr-range ia a) (addr-range jb b)))
    :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

  (defthm disjoint-p-two-addr-ranges-thm-3
    (implies (and (disjoint-p (addr-range j y)  (addr-range i x))
                  (subset-p   (addr-range ia a) (addr-range i x))
                  (subset-p   (addr-range jb b) (addr-range j y)))
             (disjoint-p (addr-range ia a) (addr-range jb b)))
    :hints (("Goal" :use ((:instance disjoint-p-commutative
                                     (a (addr-range j y))
                                     (b (addr-range i x)))))))

  (defthm consp-addr-range
    (implies (posp n)
             (consp (addr-range n val)))
    :rule-classes (:type-prescription :rewrite))

  (defthm car-addr-range
    (implies (posp n)
             (equal (car (addr-range n val))
                    (ifix val))))

  (defthm cdr-addr-range
    (implies (and (posp n)
                  (integerp val))
             (equal (cdr (addr-range n val))
                    (addr-range (1- n) (1+ val)))))

  (defthm no-duplicates-p-and-addr-range
    (no-duplicates-p (addr-range n x))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthm instance-of-pos-1-accumulator-thm
    (implies (and (member-p e x)
                  (natp acc))
             (equal (pos-1 e x (+ 1 acc))
                    (+ 1 (pos-1 e x acc)))))

  (defthm pos-and-create-canonical-address-list
    (implies (member-p addr
                       (create-canonical-address-list n prog-addr))
             (equal (pos addr
                         (create-canonical-address-list n prog-addr))
                    (- addr prog-addr)))
    :hints (("Goal" :in-theory (e/d (pos) ()))))

  ;; (defthm nth-pos-of-addr-range-first
  ;;   (implies (and (integerp index)
  ;;                 (posp n))
  ;;            (equal (pos index (addr-range n index)) 0))
  ;;   :hints (("Goal" :in-theory (e/d* (pos) ()))))

  (defthm nth-pos-of-addr-range
    (implies (and (<= index i) (< i (+ n index))
                  (integerp index) (integerp i) (posp n))
             (equal (pos i (addr-range n index))
                    (- i index)))
    :hints (("Goal" :in-theory (e/d* (pos) ())))))

;; ======================================================================

;; Lemmas about canonical-address-p, canonical-address-listp, and
;; create-canonical-address-list:

(defthm canonical-address-listp-fwd-chain-true-listp
  (implies (canonical-address-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defthm member-p-canonical-address-p
  (implies (and (canonical-address-listp x)
                (member-p e x))
           (canonical-address-p e))
  :rule-classes (:forward-chaining))

(defthm create-canonical-address-list-of-0
  (equal (create-canonical-address-list 0 addr) nil))

(defthm member-p-canonical-address-p-canonical-address-listp
  (implies (member-p e (create-canonical-address-list n prog-addr))
           (canonical-address-p e))
  :rule-classes :forward-chaining)

(defthm subset-p-canonical-address-listp
  (implies (and (canonical-address-listp y)
                (subset-p x y)
                (true-listp x))
           (canonical-address-listp x))
  :hints (("Goal" :in-theory (e/d (subset-p) ())))
  :rule-classes :forward-chaining)

(defthm subset-p-canonical-address-listp-create-canonical-address-list
  (implies (and (subset-p x (create-canonical-address-list n prog-addr))
                (true-listp x))
           (canonical-address-listp x))
  :hints (("Goal" :in-theory (e/d ()
                                  (subset-p-canonical-address-listp))
           :use ((:instance subset-p-canonical-address-listp
                            (y
                             (create-canonical-address-list
                              n prog-addr))))))
  :rule-classes :forward-chaining)

(local
 (defthmd member-p-canonical-address-listp-helper
   (implies (and (< 0 n)
                 (canonical-address-p prog-addr)
                 (canonical-address-p (+ -1 n prog-addr)))
            (equal (member-p addr
                             (create-canonical-address-list n prog-addr))
                   (and (integerp addr)
                        (<= prog-addr addr)
                        (< addr (+ n prog-addr)))))))

(defthm member-p-canonical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the canonical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (<= prog-addr addr)
                (< addr (+ n prog-addr))
                (canonical-address-p prog-addr)
                (canonical-address-p (+ -1 n prog-addr))
                (integerp addr))
           (equal (member-p addr (create-canonical-address-list n prog-addr))
                  t))
  :hints (("Goal" :in-theory (e/d (member-p-canonical-address-listp-helper)
                                  ()))))

(defthm not-member-p-canonical-address-listp
  (implies (or (< addr prog-addr)
               (<= (+ n prog-addr) addr))
           (equal (member-p addr (create-canonical-address-list n prog-addr))
                  nil)))

(defthm not-member-p-canonical-address-listp-when-disjoint-p
  (implies (and (disjoint-p (create-canonical-address-list n prog-addr)
                            (create-canonical-address-list m addr))
                (member-p e (create-canonical-address-list m addr)))
           (equal (member-p e (create-canonical-address-list n prog-addr))
                  nil)))

(defthm no-duplicates-p-create-canonical-address-list
  (no-duplicates-p (create-canonical-address-list n x)))

(defthm subset-p-two-create-canonical-address-lists-general
  (implies (and (canonical-address-p y)
                (canonical-address-p (+ -1 j y))
                (<= y x)
                (<= (+ i x) (+ j y)))
           (subset-p (create-canonical-address-list i x)
                     (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))

(defthm subset-p-two-create-canonical-address-lists-same-base-address
  (implies (and (canonical-address-p (+ m x))
                (natp m)
                (<= i m))
           (subset-p (create-canonical-address-list i x)
                     (create-canonical-address-list m x)))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm subset-p-addr-range-of-create-canonical-address-list
  (implies (and (canonical-address-p val2)
                (canonical-address-p (+ -1 m val2))
                (integerp val1)
                (<= val2 val1)
                (<= (+ n val1) (+ m val2)))
           (subset-p (addr-range n val1)
                     (create-canonical-address-list m val2)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))

(defthm disjoint-p-two-create-canonical-address-lists-thm-0
  (implies (<= (+ i x) y)
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-create-canonical-address-lists-thm-1
  (implies (<= (+ j y) x)
           (disjoint-p (create-canonical-address-list i x)
                       (create-canonical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-create-canonical-address-list-and-append
  (equal (disjoint-p (create-canonical-address-list i x)
                     (append (create-canonical-address-list j y)
                             (create-canonical-address-list k z)))
         (and (disjoint-p (create-canonical-address-list i x)
                          (create-canonical-address-list j y))
              (disjoint-p (create-canonical-address-list i x)
                          (create-canonical-address-list k z))))
  :hints (("Goal" :in-theory (e/d (disjoint-p
                                   create-canonical-address-list)
                                  ()))))

;; Other misc. lemmas about pos, nth, etc.:

(defthmd create-canonical-address-list-end-addr-is-canonical
  (implies (and (equal (len (create-canonical-address-list count addr)) count)
                (posp count)
                (equal end-addr (+ -1 addr count)))
           (canonical-address-p end-addr)))

(local
 (defthm nth-pos-1-and-cdr
   (implies (and (not (equal e (car x)))
                 (member-p e x)
                 (natp n))
            (equal (nth (pos-1 e x n) y)
                   (nth (pos-1 e (cdr x) n) (cdr y))))))

(defthm nth-pos-and-cdr
  (implies (and (not (equal e (car x)))
                (member-p e x))
           (equal (nth (pos e x) y)
                  (nth (pos e (cdr x)) (cdr y))))
  :hints (("Goal" :in-theory (e/d* (pos) ()))))

(local
 (defthm nth-pos-1-and-cdr-and-minus
   (implies (and (not (equal e (car x)))
                 (member-p e x)
                 (natp n))
            (equal (nth (- (pos-1 e x n) n) y)
                   (nth (- (pos-1 e (cdr x) n) n) (cdr y))))))


;; ======================================================================

#||

;; Lemmas about byte-ify and combine-bytes:

(local
 (defthmd byte-ify-general-acc-helper-thm
   (implies (and (byte-listp acc1)
                 (byte-listp acc2)
                 (integerp val)
                 (natp n))
            (equal (byte-ify-general n val (append acc1 acc2))
                   (append (acl2::rev acc2) (byte-ify-general n val acc1))))
   :hints (("Goal" :in-theory (e/d* (byte-ify-general) ())))))

(defthm byte-ify-general-acc-thm
  (implies (and (syntaxp (not (and (quotep acc)
                                   (eq (car (unquote acc)) nil))))
                (byte-listp acc)
                (integerp val)
                (natp n))
           (equal (byte-ify-general n val acc)
                  (append (acl2::rev acc) (byte-ify-general n val nil))))
  :hints (("Goal" :use ((:instance byte-ify-general-acc-helper-thm
                                   (acc2 acc)
                                   (acc1 nil))))))


(defthm combine-bytes-and-byte-ify
  (implies (natp n)
           (equal (combine-bytes (byte-ify n x))
                  (loghead (ash n 3) x)))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    byte-ify-and-byte-ify-general
                                    byte-ify-general)
                                   ()))))

(defthmd remove-loghead-from-byte-ify
  ;; We keep this rule disabled because most of the times, removing loghead
  ;; from within byte-ify isn't really necessary.
  (implies (equal m (ash n 3))
           (equal (byte-ify n (loghead m x))
                  (byte-ify n x)))
  :hints (("Goal" :in-theory (e/d* (byte-ify-and-byte-ify-general
                                    byte-ify-general
                                    ihsext-recursive-redefs
                                    ihsext-inductions)
                                   ()))))

(defthmd combine-bytes-and-byte-ify-inequality-lemma
  ;; This is an expensive rule, so we keep it disabled. As it is, we don't need
  ;; this rule very often.
  (implies (and (equal bytes (byte-ify n x))
                (natp n)
                (not (equal (loghead (ash n 3) x) val)))
           (equal (equal (combine-bytes bytes) val) nil))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    byte-ify-and-byte-ify-general
                                    byte-ify-general)
                                   ()))))

(defthmd remove-loghead-from-combine-bytes
  ;; This is an expensive rule, so we keep it disabled. As it is, we don't need
  ;; this rule very often.
  (implies (and (equal m (ash (len bytes) 3))
                (byte-listp bytes))
           (equal (loghead m (combine-bytes bytes))
                  (combine-bytes bytes)))
  :hints (("Goal" :in-theory (e/d* (combine-bytes
                                    ihsext-recursive-redefs
                                    ihsext-inductions)
                                   ()))))

(defthm byte-ify-and-combine-bytes
  ;; [Shilpi]: Generalize this to remove the len hyp...
  (implies (and (equal (len byte-list) n)
                (byte-listp byte-list))
           (equal (byte-ify n (combine-bytes byte-list))
                  byte-list))
  :hints (("Goal"
           :in-theory (e/d* (combine-bytes
                             byte-ify-and-byte-ify-general
                             byte-ify-general)
                            ()))))

;; ======================================================================

||#
