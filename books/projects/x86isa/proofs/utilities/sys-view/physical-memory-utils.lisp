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

(include-book "row-wow-thms" :ttags :all :dir :proof-utils)
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)

(local (include-book "gl-lemmas"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; Lemmas about physical-address-p, physical-address-listp, and
;; create-physical-address-list: these are very similar to lemmas
;; about canonical addresses.

(defthm create-physical-address-list-open-1
  (implies (and (physical-address-p (+ n x))
                (natp n))
           (equal (create-physical-address-list 1 (+ n x))
                  (list (+ n x))))
  :hints (("Goal" :expand (create-physical-address-list 1 (+ n x)))))

(defthm physical-address-listp-fwd-chain-true-listp
  (implies (physical-address-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defthm member-p-physical-address-p
  (implies (and (physical-address-listp x)
                (member-p e x))
           (physical-address-p e))
  :rule-classes (:type-prescription :forward-chaining))

(defthm member-p-physical-address-p-physical-address-listp
  (implies (member-p e (create-physical-address-list n prog-addr))
           (physical-address-p e))
  :rule-classes (:type-prescription :forward-chaining))

(defthm subset-p-physical-address-listp
  (implies (and (physical-address-listp y)
                (subset-p x y)
                (true-listp x))
           (physical-address-listp x))
  :hints (("Goal" :in-theory (e/d (subset-p) ())))
  :rule-classes :forward-chaining)

(defthm subset-p-physical-address-listp-create-physical-address-list
  (implies (and (subset-p x (create-physical-address-list n prog-addr))
                (true-listp x))
           (physical-address-listp x))
  :hints (("Goal" :in-theory (e/d ()
                                  (subset-p-physical-address-listp))
           :use ((:instance subset-p-physical-address-listp
                            (y
                             (create-physical-address-list
                              n prog-addr))))))
  :rule-classes :forward-chaining)

(local
 (defthmd member-p-physical-address-listp-helper
   (implies (and (integerp n)
                 (< 0 n)
                 (physical-address-p prog-addr)
                 (physical-address-p (+ -1 n prog-addr)))
            (equal (member-p addr
                             (create-physical-address-list n prog-addr))
                   (and (integerp addr)
                        (<= prog-addr addr)
                        (< addr (+ n prog-addr)))))))

(defthm member-p-physical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the physical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (<= prog-addr addr)
                (< addr (+ n prog-addr))
                (integerp n)
                (physical-address-p prog-addr)
                (physical-address-p (+ -1 n prog-addr))
                (integerp addr))
           (equal (member-p addr (create-physical-address-list n prog-addr))
                  t))
  :hints (("Goal" :in-theory (e/d (member-p-physical-address-listp-helper)
                                  ()))))

(defthm not-member-p-physical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the physical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (or (< addr prog-addr)
                    (<= (+ n prog-addr) addr))
                (integerp n)
                (< 0 n)
                (physical-address-p prog-addr)
                (physical-address-p (+ -1 n prog-addr)))
           (equal (member-p addr
                            (create-physical-address-list n prog-addr))
                  nil))
  :hints (("Goal" :in-theory (e/d
                              (member-p-physical-address-listp-helper)
                              ()))))

(defthm subset-p-two-create-physical-address-lists
  (implies (and (physical-address-p y)
                (physical-address-p (+ j y))
                (<= y x)
                (<= (+ i x) (+ j y))
                (integerp j))
           (subset-p (create-physical-address-list i x)
                     (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))


(defthm disjoint-p-two-create-physical-address-lists-thm-0
  (implies (and (physical-address-p y)
                (physical-address-p (+ j y))
                (integerp j)
                (< 0 j)
                (<= (+ i x) y))
           (disjoint-p (create-physical-address-list i x)
                       (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-create-physical-address-lists-thm-1
  (implies (and (physical-address-p x)
                (physical-address-p y)
                (physical-address-p (+ i x))
                (integerp j)
                (< 0 j)
                (<= (+ j y) x))
           (disjoint-p (create-physical-address-list i x)
                       (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm physical-address-p-limits-thm-0
  (implies (and (physical-address-p x)
                (natp m)
                (< m n)
                (physical-address-p (+ n x)))
           (physical-address-p (+ m x))))

(defthm physical-address-p-limits-thm-1
  ;; i is positive, k is positive, k < i
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p addr)
                (integerp k)
                (<= 0 k)
                (< k i))
           (physical-address-p (+ k addr))))

(defthm physical-address-p-limits-thm-2
  ;; i is negative, k is negative, k > i
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p addr)
                (integerp k)
                (< i 0)
                (< k 0)
                (< i k))
           (physical-address-p (+ k addr))))

(defthm physical-address-p-limits-thm-3
  ;; i is negative, j is positive, i < k < j
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p (+ j addr))
                (integerp addr)
                (integerp k)
                (< i k)
                (< k j))
           (physical-address-p (+ k addr))))

;; ======================================================================

;; RoW and WoW theorems:

;; First, some arithmetic lemmas for proving RoW/WoW theorems:

(defthm n32p-lower-16-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  (loghead 16 val))))

(defthm n32p-upper-16-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 (logtail 16 val))
                          (ash (logtail 24 val) 8))
                  (logtail 16 val))))

(local
 (defthm n32p-upper-16-in-8s-val-logior-loghead-ash-helper
   (implies (n32p val)
            (equal (logior (loghead 8 val)
                           (ash (logtail 16 val) 16)
                           (ash (loghead 8 (logtail 8 val)) 8))
                   (logior (loghead 16 val)
                           (ash (logtail 16 val) 16))))
   :hints (("Goal"
            :in-theory (e/d ()
                            (n32p-lower-16-val-logior-loghead-ash
                             combining-logior-of-loghead-and-ash-loghead-logtail
                             combining-logior-of-loghead-and-ash-logtail
                             putting-logior-loghead-ash-logtail-together))
            :use ((:instance n32p-lower-16-val-logior-loghead-ash))))))


(defthm n32p-upper-16-in-8s-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (logtail 16 val) 16)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  val)))

;; ======================================================================

;; Misc. lemmas:

(defthm xr-mem-write-to-physical-memory-disjoint
  (implies (not (member-p index p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (xr :mem index x86)))
  :hints (("Goal"
           :in-theory (e/d* (write-to-physical-memory member-p) (force (force))))))

(local
 (defthmd write-to-physical-memory-xw-mem-member-p-helper
   (implies (equal (write-to-physical-memory (cdr p-addrs)
                                             (logtail 8 bytes)
                                             (xw :mem index byte
                                                 (xw :mem (car p-addrs)
                                                     (loghead 8 bytes)
                                                     x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (logtail 8 bytes)
                                             (xw :mem (car p-addrs)
                                                 (loghead 8 bytes)
                                                 x86)))
            (equal (write-to-physical-memory (cdr p-addrs)
                                             (logtail 8 bytes)
                                             (xw :mem (car p-addrs)
                                                 (loghead 8 bytes)
                                                 (xw :mem index byte x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (logtail 8 bytes)
                                             (xw :mem (car p-addrs)
                                                 (loghead 8 bytes)
                                                 x86))))
   :hints (("Goal" :cases ((equal index (car p-addrs)))))))

(defthm write-to-physical-memory-xw-mem-member-p
  (implies (member-p index p-addrs)
           (equal (write-to-physical-memory p-addrs bytes (xw :mem index byte x86))
                  (write-to-physical-memory p-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (member-p write-to-physical-memory-xw-mem-member-p-helper)
                                   ()))))

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             rm-low-32
                             disjoint-p)
                            (force (force))))))

(defthm xr-mem-write-to-physical-memory-member
  (implies (and (member-p index p-addrs)
                (no-duplicates-p p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs value x86))
                  ;; (nth (pos index p-addrs) bytes)
                  (part-select value :low (ash (pos index p-addrs) 3) :width 8)))
  :hints (("Goal" :in-theory (e/d* (member-p pos) (force (force))))))

(defthm rm-low-64-and-write-to-physical-memory-equal
  (implies (and (equal p-addrs-2 (addr-range 8 p-addr-1))
                (integerp p-addr-1)
                (not (app-view x86)))
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 value x86))
                  (loghead 64 value)))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             rm-low-32 member-p
                             rm-low-64-and-write-to-physical-memory-equal-helper-2)
                            (addr-range
                             write-to-physical-memory
                             nth
                             force
                             (force)
                             member-p-cons
                             acl2::commutativity-of-logior
                             mv-nth-2-rcl-spec-16
                             write-to-physical-memory-xw-mem-member-p
                             (:linear bitops::logior-<-0-linear-2)
                             (:type-prescription bitops::logior-natp-type)
                             x86isa::combining-logior-of-loghead-and-ash-logtail
                             (:rewrite acl2::zip-open))))))

(defthm rm-low-32-and-xw-mem-disjoint
  (implies (disjoint-p (list index-2) (addr-range 4 index-1))
           (equal (rm-low-32 index-1 (xw :mem index-2 val-2 x86))
                  (rm-low-32 index-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) (force (force))))))

(defthm rm-low-64-and-xw-mem-disjoint
  (implies (disjoint-p (list index-2) (addr-range 8 index-1))
           (equal (rm-low-64 index-1 (xw :mem index-2 val-2 x86))
                  (rm-low-64 index-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32)
                                   (force (force))))))

(defthm xw-mem-and-wm-low-32-commute
  (implies (disjoint-p (list index-1) (addr-range 4 index-2))
           (equal (xw :mem index-1 val-1 (wm-low-32 index-2 val-2 x86))
                  (wm-low-32 index-2 val-2 (xw :mem index-1 val-1 x86))))
  :hints (("Goal" :in-theory (e/d* (wm-low-32)
                                   (force (force))))))

(defthm xw-mem-and-wm-low-64-commute
  (implies (disjoint-p (list index-1) (addr-range 8 index-2))
           (equal (xw :mem index-1 val-1 (wm-low-64 index-2 val-2 x86))
                  (wm-low-64 index-2 val-2 (xw :mem index-1 val-1 x86))))
  :hints (("Goal" :in-theory (e/d* (wm-low-64 wm-low-32)
                                   (force (force))))))

(defthm read-from-physical-memory-and-write-to-physical-memory-disjoint
  (implies (disjoint-p p-addrs-1 p-addrs-2)
           (equal (read-from-physical-memory
                   p-addrs-1
                   (write-to-physical-memory p-addrs-2 value x86))
                  (read-from-physical-memory p-addrs-1 x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p)
                                   (force (force))))))

(defthm read-from-physical-memory-and-write-to-physical-memory-equal
  (implies (and (no-duplicates-p p-addrs)
                (physical-address-listp p-addrs))
           (equal
            (read-from-physical-memory
             p-addrs
             (write-to-physical-memory p-addrs value x86))
            (loghead (ash (len p-addrs) 3) value)))
  :hints (("Goal"
           :induct (read-from-physical-memory
                    p-addrs (write-to-physical-memory p-addrs value x86))
           :in-theory (e/d* () (force (force))))))

;; ======================================================================

;; Relationship between wm-low-64 and write-to-physical-memory, and
;; rm-low-64 and read-from-physical-memory:

(defthmd rewrite-wm-low-64-to-write-to-physical-memory
  (implies (not (app-view x86))
           (equal (wm-low-64 index value x86)
                  (write-to-physical-memory
                   (addr-range 8 index) value x86)))
  :hints (("Goal"
           :in-theory (e/d* (write-to-physical-memory
                             wm-low-64
                             wm-low-32)
                            (force (force))))))

(local
 (defthmd rewrite-read-from-physical-memory-to-rm-low-64-helper
   (implies (and (equal p-addrs (addr-range 8 index))
                 (not (app-view x86))
                 (x86p x86))
            (equal (read-from-physical-memory p-addrs x86)
                   (rm-low-64 index x86)))
   :hints (("Goal"
            :in-theory (e/d* (read-from-physical-memory
                              rm-low-64 rm-low-32 addr-range
                              rm-low-64-and-write-to-physical-memory-equal-helper-1)
                             (force (force)))))))

(defthmd rewrite-read-from-physical-memory-to-rm-low-64
  (implies (and (equal p-addrs (addr-range 8 index))
                (not (app-view x86))
                (physical-address-p index)
                (x86p x86))
           (equal (read-from-physical-memory p-addrs x86)
                  (rm-low-64 (car p-addrs) x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rewrite-read-from-physical-memory-to-rm-low-64-helper
                            (index (car p-addrs))))
           :in-theory (e/d* (create-physical-address-list
                             physical-address-listp
                             unsigned-byte-p)
                            (force (force))))))

;; ======================================================================
