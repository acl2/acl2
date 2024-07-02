; BV Library: putbits, putbit, and putbyte
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Perhaps we should often leave these functions enabled for reasoning.

(include-book "bvcat")
(local (include-book "../library-wrappers/arithmetic-inequalities"))
(local (include-book "unsigned-byte-p"))

;; Set bits HIGH down to LOW to VAL in BV, returning a value of width WIDTH.
(defun putbits (width high low val bv)
  (declare (type (integer 0 *) high)
           (type (integer 0 *) low)
           (type (integer 0 *) width)
           (type integer bv)
           (type integer val)
           (xargs :guard (and (< high width)
                              (<= low high))))
  (let ((high (nfix high)))
    (bvcat (+ -1 (- width high))
           (slice (+ -1 width) (+ 1 high) bv)
           (min width (+ 1 high)) ;simplify?
           (bvcat (+ 1 (- high low))
                  val ;get chopped by the bvcat if needed
                  low
                  (bvchop low bv)))))

(defthm unsigned-byte-p-of-putbits
  (equal (unsigned-byte-p width (putbits width high low val bv))
         (natp width)))

;the usual case
(defthm slice-of-putbits
  (implies (and (natp width)
                (natp high)
                (natp low)
                (<= low high) ;gen
                (< high width) ;gen
                )
           (equal (slice high low (putbits width high low val bv))
                  (bvchop (+ 1 high (- low)) val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Set bit N to VAL in BV, returning a value of width WIDTH.
(defun putbit (width n val bv)
  (declare (type (integer 0 *) n)
           (type (integer 0 *) width)
           (type integer bv)
           (type integer val)
           (xargs :guard (< n width)))
  (putbits width n n val bv))

(defthm unsigned-byte-p-of-putbit
  (equal (unsigned-byte-p width (putbit width n val bv))
         (natp width)))

(defthm getbit-of-putbit
  (implies (and (natp width)
                (natp n))
           (equal (getbit n (putbit width n val bv))
                  (if (< n width)
                      ;; the normal case:
                      (bvchop 1 val)
                    ;; tried to set a bit that's too high, so when we read that bit we get 0
                    0))))

(defthm putbit-of-bvchop-same
  (implies (natp width)
           (equal (putbit width n val (bvchop width bv))
                  (putbit width n val bv)))
  :hints (("Goal" :in-theory (enable putbit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund putbyte (numbytes index byte x)
  (declare (xargs :guard (and (natp numbytes)
                              (natp index)
                              (< index numbytes)
                              (unsigned-byte-p 8 byte)
                              (unsigned-byte-p (* 8 numbytes) x))))
  (putbits (* 8 numbytes)
           (+ 7 (* 8 index))
           (* 8 index)
           (bvchop 8 byte)
           x))

(defthm putbyte-of-1-arg1
  (implies (natp index)
           (equal (putbyte 1 index byte x)
                  (if (equal index 0)
                      (bvchop 8 byte)
                    (bvchop 8 x))))
  :hints (("Goal" :in-theory (enable putbyte))))

(defthm putbyte-of-0-arg1
  (equal (putbyte 0 index byte x)
         0)
  :hints (("Goal" :in-theory (enable putbyte))))

(defthmd putbyte-unroll
  (implies (and (natp numbytes)
                (natp index)
                (< index numbytes))
           (equal (putbyte numbytes index byte x)
                  (if (equal index (+ -1 numbytes))
                      (bvcat 8 byte (* 8 (+ -1 numbytes)) (bvchop (* 8 (+ -1 numbytes)) x))
                    (bvcat 8
                           (slice (+ 7 (* 8 (+ -1 numbytes)))
                                  (* 8 (+ -1 numbytes))
                                  x)
                           (* 8 (+ -1 numbytes))
                           (putbyte (+ -1 numbytes) index byte x)))))
  :hints (("Goal" :in-theory (enable putbyte))))

(defthmd putbyte-unroll-once
  (implies (and (syntaxp (symbolp numbytes))
                (natp numbytes)
                (natp index)
                (< index numbytes))
           (equal (putbyte numbytes index byte x)
                  (if (equal index (+ -1 numbytes))
                      (bvcat 8 byte (* 8 (+ -1 numbytes)) (bvchop (* 8 (+ -1 numbytes)) x))
                    (bvcat 8
                           (slice (+ 7 (* 8 (+ -1 numbytes)))
                                  (* 8 (+ -1 numbytes))
                                  x)
                           (* 8 (+ -1 numbytes))
                           (putbyte (+ -1 numbytes) index byte x)))))
  :hints (("Goal" :by putbyte-unroll)))

(defthm putbyte-of-bvcat-of-8-low
  (implies (and (equal (* 8 n) (+ highsize 8))
                (natp highsize))
           (equal (putbyte n 0 val (bvcat highsize highval 8 lowval))
                  (bvcat highsize highval 8 val)))
  :hints (("Goal" :in-theory (enable putbyte))))

(defthm bvchop-8-of-putbyte
  (implies (and (natp numbytes)
                (natp index)
                (< index numbytes))
           (equal (bvchop 8 (putbyte numbytes index byte x))
                  (if (equal index 0)
                      (bvchop 8 byte)
                    (bvchop 8 x))))
  :hints (("Goal" :in-theory (enable putbyte))))

(defthm unsigned-byte-p-of-putbyte
  (implies (and (natp numbytes)
                (<= (* 8 numbytes) size)
                (natp size)
                )
           (unsigned-byte-p size (putbyte numbytes index byte x)))
  :hints (("Goal" :in-theory (enable putbyte))))

(defthm putbyte-of-bvchop-8
  (equal (putbyte n index (bvchop 8 byte) x)
         (putbyte n index byte x))
  :hints (("Goal" :in-theory (enable putbyte))))

(local
  (defthm slice-of-putbyte-all-but-low-helper
    (implies (and (posp n)
                  (natp index)
                  (unsigned-byte-p 8 byte) ; drop! but the proof hangs
;                (unsigned-byte-p (* 8 n) x)
                  (< index n))
             (equal (slice (+ -1 (* 8 n)) 8 (putbyte n index byte x))
                    (if (equal 0 index)
                        (slice (+ -1 (* 8 n)) 8 x)
                      (putbyte (+ -1 n) (+ -1 index) byte (slice (+ -1 (* 8 n)) 8 x)))))
    :hints (("Goal" :in-theory (e/d (putbyte) ((:e expt)))))))



(defthm slice-of-putbyte-all-but-low
  (implies (and (posp n)
                (natp index)
                (< index n))
           (equal (slice (+ -1 (* 8 n)) 8 (putbyte n index byte x))
                  (if (equal 0 index)
                      (slice (+ -1 (* 8 n)) 8 x)
                    (putbyte (+ -1 n) (+ -1 index) byte (slice (+ -1 (* 8 n)) 8 x)))))
  :hints (("Goal" :use (:instance slice-of-putbyte-all-but-low-helper (byte (bvchop 8 byte)))
           :in-theory (disable slice-of-putbyte-all-but-low-helper)
           )))
