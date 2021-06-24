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
; Robert Krug         <rkrug@cs.utexas.edu>
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "modes")
(include-book "../proofs/utilities/disjoint")

;; ======================================================================

(defsection physical-memory

  :parents (machine)

  :short "Physical memory read and write functions"

  :long "<p>Note that the top-level memory accessor function is @(see
  rme08) and updater function is @(see wme08).  Their 16, 32, 64, and
  128 bit counterparts are also available.  These functions behave
  differently depending upon the value of
  @('app-view').</p>

<p>The functions defined here, like @(see rm-low-32) and @(see
wm-low-32), are low-level read and write functions that access
physical memory directly in the system-level view.  We do not
recommend using these functions at the top-level.</p>")

(local (xdoc::set-default-parents physical-memory))

;; ======================================================================

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/width-find-rule" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

;; ======================================================================

(define physical-address-p (phy-addr)
  :parents (physical-memory)
  :inline t
  :no-function t
  :enabled t
  (mbe :logic (unsigned-byte-p #.*physical-address-size* phy-addr)
       :exec  (and (integerp phy-addr)
                   (<= 0 phy-addr)
                   (< phy-addr #.*mem-size-in-bytes*))))

(define physical-address-listp (lst)
  :parents (physical-memory)
  :short "Recognizer of a list of physical addresses"
  :enabled t
  (if (equal lst nil)
      t
    (and (consp lst)
         (physical-address-p (car lst))
         (physical-address-listp (cdr lst)))))

(define create-physical-address-list (count addr)

  :guard (and (natp count)
              (physical-address-p addr)
              (physical-address-p (+ addr count)))
  :parents (physical-memory)

  :long "<p>Given a physical address @('addr'),
  @('create-physical-address-list') creates a list of physical
  addresses where the first address is @('addr') and the last address
  is the last physical address in the range @('addr') to @('addr +
  count').</p>"
  :enabled t

  (if (or (zp count)
          (not (physical-address-p addr)))
      nil
    (cons addr (create-physical-address-list (1- count)
                                             (1+ addr))))
  ///

  (defthm physical-address-listp-create-physical-address-list
    (physical-address-listp
     (create-physical-address-list count addr))
    :rule-classes (:rewrite :type-prescription)))

(define addr-range (count addr)
  :guard (natp count)

  :enabled t

  (if (zp count)
      nil
    ;; The ifix below is intentional --- it allows addr-range to be
    ;; used with both integer (canonical addresses, modeled as
    ;; signed-byte-p) as well as natp (physical addresses, modeled as
    ;; unsigned-byte-p) addresses.
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
    :hints (("Goal" :in-theory (e/d* (pos) ()))))

  (defthmd addr-range-ifix
    (equal (addr-range n (ifix x)) (addr-range n x))))

;; ======================================================================

;; Memory read functions:

;; These functions are very similar to their linear memory
;; counterparts, rvm* --- they just differ in guards and the number of
;; return values.

;; Memory write functions:

;; These functions are very similar to their linear memory
;; counterparts wvm* --- they differ in guards and the number of
;; return values.

;; ----------------------------------------------------------------------

(local (in-theory (e/d () (unsigned-byte-p))))
(local (in-theory (e/d (bitops::unsigned-byte-p-by-find-rule) ())))

(define rm-low-32
  ((addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (integerp addr)
              (<= 0 addr)
              (< (+ 3 addr) *mem-size-in-bytes*))
  :inline t
  :no-function t
  :parents (physical-memory)

  (if (mbt (not (app-view x86)))

      (let ((addr (mbe :logic (ifix addr)
                       :exec addr)))

        (b* (((the (unsigned-byte 8) byte0) (mbe :logic (loghead 8 (memi addr x86))
                                                 :exec (memi addr x86)))
             ((the (unsigned-byte 8) byte1) (mbe :logic (loghead 8 (memi (1+ addr) x86))
                                                 :exec (memi (1+ addr) x86)))
             ((the (unsigned-byte 16) word0)
              (logior (the (unsigned-byte 16) (ash byte1 8)) byte0))
             ((the (unsigned-byte 8) byte2) (mbe :logic (loghead 8 (memi (+ 2 addr) x86))
                                                 :exec (memi (+ 2 addr) x86)))
             ((the (unsigned-byte 8) byte3) (mbe :logic (loghead 8 (memi (+ 3 addr) x86))
                                                 :exec (memi (+ 3 addr) x86)))
             ((the (unsigned-byte 16) word1)
              (the (unsigned-byte 16) (logior (the (unsigned-byte 16) (ash byte3 8)) byte2)))
             ((the (unsigned-byte 32) dword) (logior (the (unsigned-byte 32) (ash word1 16)) word0)))
          dword))
    0)


  ///

  (defthm rm-low-32-in-app-view
    (implies (app-view x86)
             (equal (rm-low-32 p-addr x86) 0)))

  (defthm-unsigned-byte-p n32p-rm-low-32
    :bound 32
    :concl (rm-low-32 addr x86)
    :hints (("Goal" :in-theory (e/d () (force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm rm-low-32-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (rm-low-32 addr (xw fld index val x86))
                    (rm-low-32 addr x86)))
    :hints (("Goal" :in-theory (e/d* (rm-low-32) (force (force)))))))

(define wm-low-32
  ((addr :type (unsigned-byte #.*physical-address-size*))
   (val :type (unsigned-byte 32))
   (x86))
  :inline t
  :no-function t
  :guard (and (not (app-view x86))
              (< (+ 3 addr) *mem-size-in-bytes*))
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :parents (physical-memory)

  (if (mbt (not (app-view x86)))

      (let ((addr (mbe :logic (ifix addr)
                       :exec addr)))

        (b* (((the (unsigned-byte 8) byte0)
              (mbe :logic (part-select val :low 0 :width 8)
                   :exec  (logand #xff val)))
             ((the (unsigned-byte 8) byte1)
              (mbe :logic (part-select val :low 8 :width 8)
                   :exec  (logand #xff (ash val -8))))
             ((the (unsigned-byte 8) byte2)
              (mbe :logic (part-select val :low 16 :width 8)
                   :exec  (logand #xff (ash val -16))))
             ((the (unsigned-byte 8) byte3)
              (mbe :logic (part-select val :low 24 :width 8)
                   :exec  (logand #xff (ash val -24))))
             (x86 (!memi addr  byte0 x86))
             (x86 (!memi (+ 1 addr) byte1 x86))
             (x86 (!memi (+ 2 addr) byte2 x86))
             (x86 (!memi (+ 3 addr) byte3 x86)))
          x86))

    x86)

  ///

  (defthm x86p-wm-low-32
    (implies (x86p x86)
             (x86p (wm-low-32 addr val x86)))
    :rule-classes (:rewrite :type-prescription))

  (defthm xr-wm-low-32
    (implies (not (equal fld :mem))
             (equal (xr fld index (wm-low-32 addr val x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wm-low-32) (force (force))))))

  (defthm wm-low-32-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (wm-low-32 addr val (xw fld index value x86))
                    (xw fld index value (wm-low-32 addr val x86))))
    :hints (("Goal" :in-theory (e/d* (wm-low-32) (force (force)))))))

(defthmd put-logior-4-bytes-together
  (implies (unsigned-byte-p 32 val)
           (equal (logior (loghead 8 val)
                          (ash (loghead 8 (logtail 8 val)) 8)
                          (ash (logior (loghead 8 (logtail 16 val))
                                       (ash (logtail 24 val) 8))
                               16))
                  val))
  :hints ((bitops::logbitp-reasoning)))

;; rm-low-32/wm-low-32/xw RoW:

(defthm |(rm-low-32 addr2 (wm-low-32 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (force (n32p val))
                (not (app-view x86)))
           (equal (rm-low-32 addr2 (wm-low-32 addr1 val x86))
                  val))
  :hints (("Goal" :in-theory (e/d (rm-low-32 wm-low-32 nfix ifix put-logior-4-bytes-together)
                                  (unsigned-byte-p force (force))))))

(defthm |(rm-low-32 addr2 (wm-low-32 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (rm-low-32 addr2 (wm-low-32 addr1 val x86))
                  (rm-low-32 addr2 x86)))
  :hints (("Goal" :in-theory (e/d (rm-low-32 wm-low-32 nfix ifix)
                                  (unsigned-byte-p force (force))))))

(defthm |(rm-low-32 addr2 (xw :mem addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 1 addr1)
                       (addr-range 4 addr2))
           (equal (rm-low-32 addr2 (xw :mem addr1 val x86))
                  (rm-low-32 addr2 x86)))
  :hints (("Goal" :in-theory (e/d (rm-low-32) (force (force))))))

(defthm |(xr :mem addr1 (wm-low-32 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr2)
                       (addr-range 1 addr1))
           (equal (xr :mem addr1 (wm-low-32 addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (e/d (nfix wm-low-32) (force (force))))))

;; wm-low-32 WoW:

(defthm |(wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86))
                  (wm-low-32 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d (wm-low-32 nfix ifix) (force (force))))))

(defthm |(wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86))
                  (wm-low-32 addr1 val1 (wm-low-32 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d* (wm-low-32) ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

(defthm |(xw :mem addr1 (wm-low-32 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr2)
                       (addr-range 1 addr1))
           (equal (wm-low-32 addr2 val2 (xw :mem addr1 val1 x86))
                  (xw :mem addr1 val1 (wm-low-32 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d (nfix ifix wm-low-32) (force (force))))))

;; ======================================================================

(define rm-low-64
  ((addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (app-view x86))
              (integerp addr)
              (<= 0 addr)
              (< (+ 7 addr) *mem-size-in-bytes*))
  :guard-hints (("Goal" :in-theory (e/d (unsigned-byte-p)
                                        (rm-low-32 force (force)))))
  :parents (physical-memory)

  (if (mbt (not (app-view x86)))

      (b* ((addr (mbe :logic (ifix addr) :exec addr))
           ((the (unsigned-byte 32) dword0)
            (rm-low-32 addr x86))
           ((the (unsigned-byte 32) dword1)
            (rm-low-32 (+ 4 addr) x86))
           ((the (unsigned-byte 64) qword)
            (logior
             (the (unsigned-byte 64)
                  (ash dword1 32))
             dword0)))
        qword)

    0)

  ///

  (defthm rm-low-64-in-app-view
    (implies (app-view x86)
             (equal (rm-low-64 p-addr x86) 0)))

  (defthm-unsigned-byte-p n64p-rm-low-64
    :bound 64
    :concl (rm-low-64 addr x86)
    :hints (("Goal" :in-theory (e/d ()
                                    (rm-low-32
                                     force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm rm-low-64-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (rm-low-64 addr (xw fld index val x86))
                    (rm-low-64 addr x86)))
    :hints (("Goal" :in-theory (e/d* (rm-low-64) (force (force)))))))

(define wm-low-64
  ((addr :type (unsigned-byte #.*physical-address-size*))
   (val :type (unsigned-byte 64))
   (x86))
  :guard (and (not (app-view x86))
              (< (+ 7 addr) *mem-size-in-bytes*))
  :guard-hints (("Goal" :in-theory (e/d (logtail unsigned-byte-p)
                                        (x86p))))
  :parents (physical-memory)

  (if (mbt (not (app-view x86)))

      (b* ((addr (mbe :logic (ifix addr) :exec addr))
           (dword0 (mbe :logic (part-select val :low 0 :width 32)
                        :exec  (logand #xFFFFFFFF val)))
           (dword1 (mbe :logic (part-select val :low 32 :width 32)
                        :exec  (logand #xFFFFFFFF (ash val -32))))
           (x86 (wm-low-32 addr dword0 x86))
           (x86 (wm-low-32 (+ 4 addr) dword1 x86)))
        x86)
    x86)
  ///
  (defthm x86p-wm-low-64
    (implies (x86p x86)
             (x86p (wm-low-64 addr val x86)))
    :hints (("Goal" :in-theory (e/d () (x86p))))
    :rule-classes (:rewrite :type-prescription))

  (defthm xr-wm-low-64
    (implies (not (equal fld :mem))
             (equal (xr fld index (wm-low-64 addr val x86))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wm-low-64) (force (force))))))

  (defthm wm-low-64-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (equal (wm-low-64 addr val (xw fld index value x86))
                    (xw fld index value (wm-low-64 addr val x86))))
    :hints (("Goal" :in-theory (e/d* (wm-low-64) (force (force)))))))

;; rm-low-64/wm-low-64 RoW:

(defthmd put-logior-2-dwords-together
  (implies (unsigned-byte-p 64 val)
           (equal (logior (loghead 32 val)
                          (ash (logtail 32 val) 32))
                  val))
  :hints ((bitops::logbitp-reasoning)))

(defthm |(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (force (n64p val))
                (not (app-view x86)))
           (equal (rm-low-64 addr2 (wm-low-64 addr1 val x86))
                  val))
  :hints (("Goal" :in-theory (e/d (rm-low-64 wm-low-64 put-logior-2-dwords-together)
                                  ()))))

(defthm |(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr1)
                       (addr-range 8 addr2))
           (equal (rm-low-64 addr2 (wm-low-64 addr1 val x86))
                  (rm-low-64 addr2 x86)))
  :hints (("Goal"
           :expand ((:free (n x) (addr-range n x))) ;; ugh
           :in-theory (e/d (rm-low-64 wm-low-64 ifix)
                           (disjoint-p)))))

(defthm |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 1 addr1)
                       (addr-range 8 addr2))
           (equal (rm-low-64 addr2 (xw :mem addr1 val x86))
                  (rm-low-64 addr2 x86)))
  :hints (("Goal" :in-theory (e/d (rm-low-64 rm-low-32) (force (force))))))

(defthm |(xr :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr2)
                       (addr-range 1 addr1))
           (equal (xr :mem addr1 (wm-low-64 addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (e/d (ifix wm-low-32 wm-low-64) (force (force))))))

;; wm-low-64 WoW:

(defthm |(wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86))
                  (wm-low-64 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d (wm-low-64) (rm-low-32 wm-low-32)))))

(defthm |(wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr1)
                       (addr-range 8 addr2))
           (equal (wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86))
                  (wm-low-64 addr1 val1 (wm-low-64 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d (wm-low-64 wm-low-32) ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

(defthm |(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr2)
                       (addr-range 1 addr1))
           (equal (wm-low-64 addr2 val2 (xw :mem addr1 val1 x86))
                  (xw :mem addr1 val1 (wm-low-64 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d (ifix wm-low-64 wm-low-32) (force (force))))))

;; ======================================================================

(globally-disable '(rm-low-32 rm-low-64 wm-low-32 wm-low-64))

;; ======================================================================
