; BV Library: set-bits and set-bit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Perhaps we should often leave these functions enabled for reasoning.

(include-book "bvcat")
(local (include-book "../library-wrappers/arithmetic-inequalities"))

;; Set bits HIGH down to LOW to VAL in BV, returning a value of width WIDTH.
(defun set-bits (width high low val bv)
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

(defthm unsigned-byte-p-of-set-bits
  (equal (unsigned-byte-p width (set-bits width high low val bv))
         (natp width)))

;; Set bit N to VAL in BV, returning a value of width WIDTH.
(defun set-bit (width n val bv)
  (declare (type (integer 0 *) n)
           (type (integer 0 *) width)
           (type integer bv)
           (type integer val)
           (xargs :guard (< n width)))
  (set-bits width n n val bv))

(defthm unsigned-byte-p-of-set-bit
  (equal (unsigned-byte-p width (set-bit width n val bv))
         (natp width)))

(defthm getbit-of-set-bit
  (implies (and (natp width)
                (natp n))
           (equal (getbit n (set-bit width n val bv))
                  (if (< n width)
                      ;; the normal case:
                      (bvchop 1 val)
                    ;; tried to set a bit that's too high, so when we read that bit we get 0
                    0))))

;the usual case
(defthm slice-of-set-bits
  (implies (and (natp width)
                (natp high)
                (natp low)
                (<= low high) ;gen
                (< high width) ;gen
                )
           (equal (slice high low (set-bits width high low val bv))
                  (bvchop (+ 1 high (- low)) val))))
