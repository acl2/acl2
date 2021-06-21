; BV Library: putbits and putbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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

(defthm putbit-of-bvchop-same
  (implies (natp width)
           (equal (putbit width n val (bvchop width bv))
                  (putbit width n val bv)))
  :hints (("Goal" :in-theory (enable putbit))))
