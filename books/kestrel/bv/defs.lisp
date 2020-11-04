; Cherry-pick the definitions of the BV functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is intended to be a light-weight book that just brings in the
;; definitions of the BV operators, without all the theorems, so they can be
;; used in programming.

;; The definitions in this file should be kept in sync with the definitions in
;; the individual books about each function.

(include-book "slice-def")
(include-book "getbit-def")
(include-book "bvsx-def")
(include-book "defs-bitwise")
(include-book "defs-shifts")
(include-book "defs-arith")
(include-book "leftrotate")
(include-book "rightrotate")
(include-book "ihs/basic-definitions" :dir :system) ;for logext
;(include-book "to-signed")
(include-book "bvcat2")
(include-book "kestrel/arithmetic-light/power-of-2p" :dir :system)

(local (include-book "sbvdiv")) ;; the verifies the guard of sbvdiv
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;we expect bit to be 0 or 1
;bozo this should probably be changed to chop bit down to a one bit quantity first
(defund repeatbit (n bit)
  (declare (type integer n)
           (type (integer 0 *) bit)) ;tighten to only allow 0 or 1?
  (if (not (natp n))
      0
    (if (= 0 bit)
        0
      (+ -1 (expt 2 n)))))

;perhaps this should be called xshr (for sign-extending shift), but jvm has a function or macro with that name already (get rid of it first!)
;ffixme this may be wrong if we shift all the way out! consider: (acl2::bvashr 32 -1 32)
(defun bvashr (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type integer x)
           (type integer width)
           (xargs :guard (< shift-amount width)  ;what happens if they're equal?
                  :guard-hints (("Goal" :in-theory (enable bvshr)))))
  (bvsx width
        (- width shift-amount)
        (bvshr width x shift-amount)))

;; ;trimming of the amount wasn't nice and tight when width is not a power of 2
;; ;fixme pass in the number of bits of amt to use?
;; (defun leftrotate (width amt val)
;;   (declare (type integer val amt)
;;            (type (integer 0 *) width)
;;            ;;            (xargs :guard (<= (bvchop (integer-length (+ -1 width)) amt) ;fixme think about this guard
;;            ;;                              width))
;;            )
;;   (if (= 0 width)
;;       0
;;     (let* ((amt (mod (nfix amt) width))) ;((amt (bvchop (integer-length (+ -1 width)) amt)))
;;       (bvcat (- width amt)
;;              (slice (+ -1 width (- amt)) 0 val)
;;              amt
;;              (slice (+ -1 width) (+ width (- amt)) val)))))

;; (defun leftrotate16 (amt val)
;;   (declare (type integer amt val))
;;   (leftrotate 16 amt val))

;; (defund leftrotate32 (amt val)
;;   (declare (type integer amt val))
;;   (leftrotate 32 amt val))

;; (defund leftrotate64 (amt val)
;;   (declare (type integer amt val))
;;   (leftrotate 64 amt val))

;; ;or could define in terms of leftrotate
;; (defun rightrotate (width amt val)
;;   (declare (type integer val amt)
;;            (type (integer 0 *) width)
;;            ;;            (xargs :guard (<= (bvchop (integer-length (+ -1 width)) amt) ;fixme think about this guard
;;            ;;                              width))
;;            )
;;   (if (= 0 width)
;;       0
;;     (let* ((amt (mod (nfix amt) width) ;(bvchop (integer-length (+ -1 width)) amt)
;;                 ))
;;       (bvcat amt
;;              (slice (+ -1 amt) 0 val)
;;              (- width amt)
;;              (slice (+ -1 width) amt val)))))

;; (defund rightrotate32 (amt val)
;;   (rightrotate 32 amt val))



;divide and round toward 0
;fixme what should this do if y is 0?
(defun bvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  ;;drop the outer bvchop?
  (bvchop n (floor (bvchop n x) (bvchop n y))))

;fixme what should this do if y is 0?
(defund bvmod (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y))))
           )
  (bvchop n (mod (bvchop n x) ;these two bvchops are new
                  (bvchop n y)
                  )))

;fixme make sure this is right
;this is like java's idiv
;takes and returns USBs
(defund sbvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  (bvchop n (truncate (logext n x) (logext n y))))

;fixme could call this sbvfloor
;this one rounds toward negative infinity
(defund sbvdivdown (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (logext n y))) ;simplify!
                  ))
  (bvchop n (floor (logext n x) (logext n y))))

;fixme make sure this is what i want and that it matches what java does
(defund sbvrem (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (equal (bvchop n y) 0))))
  (bvchop n (rem (logext n x) (logext n y)))
;  (bvchop n (- x (* (truncate (logext n x) (logext n y)) y)))
  )

;; (defund sbvmod (n x y)
;;   (bvchop n (rem (logext n x) (logext n y))))

(defund sbvmoddown (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (EQUAL (LOGEXT N Y) 0))) ;rephrase in terms of bvchop?
           )
  (bvchop n (mod (logext n x) (logext n y))))

;fixme some of these could be macros...
;unsigned less-than
(defund bvlt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (< (bvchop size x)
     (bvchop size y)))

;unsigned less-than-or-equal
(defun bvle (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size y x)))

;unsigned greater-than
(defun bvgt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (bvlt size y x))

;unsigned greater-than-or-equal
(defun bvge (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size x y)))

;;signed less-than
(defund sbvlt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (< (logext n x)
     (logext n y)))

;;signed greater-than
(defun sbvgt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (sbvlt n y x))

;;signed less-than-or-equal
(defun sbvle (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n y x)))

;;signed greater-than-or-equal
(defun sbvge (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n x y)))

;x and y should be single bits
;guards?
;todo: make a book on this
(defun bitxnor (x y)
  (declare (type integer x y))
  (if (= (getbit 0 x) (getbit 0 y))
      1
    0))


;note that the test is a boolean, not a bit vector
(defund bvif (size test thenpart elsepart)
  (declare (xargs :guard (and (natp size)
                              (integerp thenpart)
                              (integerp elsepart))))
  (if test
      (bvchop size thenpart)
    (bvchop size elsepart)))

;floor of log (base 2) of x
(defund lg (x)
  (declare (type integer x))
  (+ -1 (integer-length x)))

;just an alias for bvchop but only used for trimming (using bvchop caused loops if the rules weren't just right)
(defund trim (size i)
  (declare (type integer i)
           (type (integer 0 *) size))
  (bvchop size i))

;dup
;; (defun bool-fix (x)
;;   (declare (xargs :guard t))
;;   (and x t))

;Changed this to match the version in the std library.
;maybe this should not be hyphenated by analogy with nfix, etc.
(DEFUN BOOL-FIX$INLINE (X)
  (DECLARE (XARGS :GUARD T))
  (AND X T))

(DEFMACRO BOOL-FIX (X)
  (LIST 'BOOL-FIX$INLINE X))

; a totalized version of sbvdiv, where division by 0 yields 0
;logically this is equal to sbvdiv (see theorem sbvdiv-total-becomes-sbvdiv)
(defund sbvdiv-total (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (if (equal 0 (logext n y))
      (logext n 0)
    (sbvdiv n x y)))

;; TODO: Make books about the stuff below here?

;dups?

(defun xxxjoin2 (fn param args)
  (declare (xargs :guard (if (true-listp args) (cdr args) nil)
                  :mode :program))
  (if (cdr (cdr args))
      (cons fn
            (cons param
                  (cons (car args)
                        (cons (xxxjoin2 fn param (cdr args))
                              nil))))
    (cons fn (cons param args))))

;fixme similar macros for the other operators?
(defmacro bvxor2 (size &rest args)
  (cond ((null args) 0)
        ((null (cdr args)) `(bvchop size ,(car args)))
        (t (xxxjoin2 'bvxor size args))))

;leaving these two enabled for now:

;increment by 1 (possibly 'rolling over' to 0)
(defun bvinc (size x)
  (bvplus size 1 x))

;decrement by 1 (possibly 'rolling under' to all 1's)
(defun bvdec (size x)
  (bvminus size x 1))


;;; Conversions between bits and booleans

(defun bit-to-bool (x)
  (declare (xargs :guard (unsigned-byte-p 1 x)))
  (if (eql x 0) nil t))

(defund bool-to-bit (test)
  (declare (xargs :guard (booleanp test))) ;trying this
  (if test 1 0))
